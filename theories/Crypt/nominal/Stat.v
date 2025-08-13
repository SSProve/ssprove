From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal NominalPrelude.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Import PackageNotation.
#[local] Open Scope package_scope.

Section Proof.

Context (op : Op).

Definition IPICK := [interface [ 0%N ] : { 'unit ~> op.π1 }].

Definition cell : Location := (0%N, 'option (op.π1)).

Definition RAND : game IPICK :=
  [package [fmap cell] ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      mr ← get cell ;;
      match mr with
      | Some r => ret r
      | None =>
        r ← sample op ;;
        #put cell := Some r ;;
        ret r
      end
    } ].

Definition PICK (x : op.π1) : game IPICK :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      ret x
    } ].

Definition CELL : package IPICK IPICK :=
  [package [fmap cell ] ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      mc ← get cell ;;
      match mc with
      | Some c => ret c
      | None => 
        r ← call [ 0%N ] : { 'unit ~> op.π1 } tt ;;
        #put cell := Some r ;;
        ret r
      end
    } ].

(*Definition ops := mkopsig 0%N 'unit ('fin #|F|).*)
(*
Lemma testing {h} :
  Pr_op RAND ops tt h
  = realsum.psum (fun f => Pr_op (PICK f) ops tt h).
 *)

Lemma Pr_code_ret {A : choiceType} {x : A} {h} :
  Pr_code (ret x) h = dunit (x, h).
Proof.
  cbn.
  unfold SubDistr.SDistr_obligation_1, SubDistr.SDistr_obligation_2.
  rewrite 2!SDistr_rightneutral //.
Qed.

Lemma Pr_code_get {B : choiceType} {l : Location} {k : l → raw_code B} {h} :
  Pr_code (x ← get l ;; k x) h
    = Pr_code (k (get_heap h l)) h.
Proof. done. Qed.

Lemma Pr_code_put {B : choiceType} {l : Location} {a : l} {k : raw_code B} {h} :
  Pr_code (#put l := a ;; k) h
    = Pr_code k (set_heap h l a).
Proof. done. Qed.

Lemma Pr_code_call {B : choiceType} {o : opsig} {a : src o} {k : tgt o → raw_code B} {h} :
  Pr_code (x ← op o ⋅ a ;; k x) h
    = Pr_code (k (chCanonical _)) h.
Proof. done. Qed.

Lemma Pr_code_sample {A : choiceType} {op' : Op} {k : Arit op' → raw_code A} {h} :
  Pr_code (x ← sample op' ;; k x) h = (\dlet_(x <- op'.π2) Pr_code (k x) h). 
Proof.
  cbn.
  unfold SubDistr.SDistr_obligation_1, SubDistr.SDistr_obligation_2.
  rewrite 2!SDistr_rightneutral.
  done.
Qed.

Lemma dlet_commut {T S U : choiceType} {A B} {f : T → S → distr Axioms.R U} {z} :
  (\dlet_(x <- A) \dlet_(y <- B) f x y) z = 
  (\dlet_(y <- B) \dlet_(x <- A) f x y) z.
Proof.
  pose proof @RulesStateProb.SD_commutativity'.
  cbn in H.
  unfold SDistr_bind, SDistr_carrier in H.
  specialize (H T S U A).
  rewrite H //.
Qed.

(*
Lemma testing0 {T} {A : raw_code T} {M} {h} :
  NCalls 0 A h →
  Pr_code (code_link A M) h = Pr_code A h.
Proof.
  intros H.
  dependent induction H => //=.
  - rewrite Pr_code_get //.
  - rewrite Pr_code_put //.
  - rewrite 2!Pr_code_sample //.
    apply distr_ext.
    apply dlet_f_equal => //.
Qed.
 *)

Lemma testing0 {LA} {T} {A : raw_code T} {f f' : op.π1} {h} :
  fseparate LA [fmap cell] →
  ValidCode LA IPICK A →
  get_heap h cell = Some f' →
  Pr_code (code_link A RAND) h
  = Pr_code (code_link A (CELL ∘ PICK f)) h.
Proof.
  intros SEP VA.
  move: h; induction (VA) => h H'.
  - done.
  - fmap_invert H.
    destruct x.
    cbn [code_link].
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind code_link].
    rewrite 2!Pr_code_get H'.
    cbn [code_link bind].
    by apply H1.
  - cbn[code_link].
    rewrite 2!Pr_code_get.
    by apply H1.
  - cbn [code_link].
    rewrite 2!Pr_code_put.
    erewrite IHv => //.
    rewrite get_set_heap_neq //.
    apply fhas_in in H.
    destruct SEP as [SEP].
    move: SEP => /fdisjointP.
    intros H''.
    specialize (H'' _ H).
    rewrite domm_set domm0 in H''.
    apply /negP.
    move=> /eqP H'''.
    rewrite H''' in H''.
    rewrite in_fsetU in_fset1 eq_refl // in H''.
  - cbn [code_link].
    rewrite 2!Pr_code_sample.
    apply distr_ext.
    apply dlet_f_equal => x.
    by apply H0.
Qed.

Lemma testing1 {LA} {T} {A : raw_code T} {h} :
  fseparate LA [fmap cell] →
  LosslessOp op →
  ValidCode LA IPICK A →
  Pr_code (code_link A RAND) h
    = \dlet_(f <- op.π2) Pr_code (code_link A (CELL ∘ PICK f)) h.
Proof.
  intros SEP LL VA.
  apply distr_ext.
  move: h; induction VA.
  - intros h y.
    rewrite Pr_code_ret.
    rewrite dletC.
    rewrite pr_predT.
    rewrite LL.
    rewrite GRing.mul1r //.
  - intros h y.
    fmap_invert H.
    cbn [code_link].
    under dlet_f_equal.
    1: intros ?; repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]); over.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    destruct x.
    cbn [bind code_link].
    rewrite Pr_code_get.
    destruct (get_heap h cell) eqn:E.
    { cbn [code_link bind].
      under dlet_f_equal. {
        intros x.
        rewrite Pr_code_get E.
        rewrite -(testing0 SEP (H0 _) E).
        over.
      }
      cbn [bind].
      rewrite dletC.
      rewrite pr_predT.
      rewrite LL.
      rewrite GRing.mul1r //.
    }
    rewrite Pr_code_sample.
    apply dlet_f_equal => x.
    rewrite Pr_code_put.
    erewrite testing0.
    + rewrite Pr_code_get E.
      cbn [code_link].
      repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
      cbn [bind].
      rewrite Pr_code_put.
      reflexivity.
    + apply SEP.
    + apply H0.
    + rewrite get_set_heap_eq //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_get.
    rewrite H1 //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_put.
    rewrite IHVA //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_sample.
    under eq_in_dlet.
    1: intros ? ? ?; rewrite H0 //; reflexivity.
    1: reflexivity.
    symmetry.
    under eq_in_dlet.
    1: intros ? ? ?; rewrite Pr_code_sample //.
    1: reflexivity.
    rewrite dlet_commut //.
Qed.

Lemma testing {LA} {A : raw_package} :
  fseparate LA [fmap cell] →
  LosslessOp op →
  ValidPackage LA IPICK A_export A →
  Pr (A ∘ RAND) = \dlet_(x <- op.π2) Pr (A ∘ CELL ∘ PICK x).
Proof.
  intros SEP LL VA.
  apply distr_ext => b.
  unfold Pr, SDistr_bind, SDistr_unit, Pr_op.
  rewrite resolve_link.

  assert (H : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H).
  rewrite (testing1 SEP LL H0).
  rewrite dlet_dlet.
  apply dlet_f_equal => y.
  rewrite resolve_link => //.
Qed.

(*
Lemma CELL_PICK_perf x :
  perfect IPICK (CELL ∘ PICK x) (PICK x).
Proof.
Admitted.

Lemma testings' {LA} {A : nom_package} :
  LosslessOp op →
  ValidPackage LA IPICK A_export A →
  Pr' (A ∘ RAND)%sep = psum (fun x => op.π2 x * Pr' (A ∘ PICK x)%sep)%R.
Proof.
Admitted.
 *)


  

End Proof.


Lemma testing_uni {F : finType} {LA} {A : raw_package} {b} `{Positive #|F|} :
  fseparate LA [fmap cell (uniform #|F|) ] →
  ValidPackage LA (IPICK (uniform #|F|)) A_export A →
  Pr (A ∘ RAND (uniform #|F|)) b
      = (\sum_f Pr ((A ∘ CELL (uniform #|F|)) ∘ PICK (uniform #|F|) f) b / #|F|%:R)%R.
Proof.
  intros SEP VA.
  rewrite testing //.
  rewrite dletE.
  rewrite psum_fin.
  apply eq_bigr => x _.
  rewrite GRing.mulrC.
  replace ((uniform #|F|).π2 x) with (#|F|%:R^-1 : Axioms.R)%R.
  - rewrite link_assoc.
    apply Num.Theory.ger0_norm.
    apply Num.Theory.mulr_ge0.
    + unfold Pr, SDistr_bind; rewrite dletE; apply ge0_psum.
    + rewrite Num.Theory.invr_ge0.
      apply Num.Theory.ler0n.
  - simpl.
    unfold UniformDistrLemmas.r.
    rewrite GRing.Theory.div1r card_ord //.
Qed.


