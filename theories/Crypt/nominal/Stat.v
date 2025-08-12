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

Definition RAND : game IPICK :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      r ← sample op ;;
      ret r
    } ].

Definition PICK (x : op.π1) : game IPICK :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      ret x
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

Inductive NCalls {A} : nat → raw_code A → heap → Prop :=
| valid_ret :
    ∀ x n h,
      NCalls n (ret x) h

| valid_opr :
    ∀ (o : opsig) x k n h,
      (∀ v, NCalls n (k v) h) →
      NCalls (S n) (opr o x k) h

| valid_getr :
    ∀ l k n h,
      NCalls n (k (get_heap h l)) h →
      NCalls n (getr l k) h

| valid_putr :
    ∀ l v k n h,
      NCalls n k (set_heap h l v) →
      NCalls n (putr l v k) h

| valid_sampler :
    ∀ op k n h,
      (∀ v, NCalls n (k v) h) →
      NCalls n (pkg_core_definition.sampler op k) h
.

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

Lemma testing1 {LA} {T} {A : raw_code T} {h} :
  LosslessOp op →
  NCalls 1 A h →
  ValidCode LA IPICK A →
  Pr_code (code_link A RAND) h
    = \dlet_(f <- op.π2) Pr_code (code_link A (PICK f)) h.
Proof.
  intros LL NC VA.
  apply distr_ext.
  move: h NC; induction VA.
  - intros h NC y.
    rewrite Pr_code_ret.
    rewrite dletC.
    rewrite pr_predT.
    rewrite LL.
    rewrite GRing.mul1r //.
  - intros h NC y.
    fmap_invert H.
    cbn [code_link].
    under dlet_f_equal.
    1: intros ?; repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]); over.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    destruct x.
    rewrite Pr_code_sample.
    apply dlet_f_equal => x.
    cbn [bind].
    dependent destruction NC.
    rewrite testing0 // testing0 //.
  - intros h NC y.
    cbn [code_link].
    rewrite Pr_code_get.
    dependent destruction NC.
    rewrite H1 //.
  - intros h NC y.
    cbn [code_link].
    rewrite Pr_code_put.
    dependent destruction NC.
    rewrite IHVA //.
  - intros h NC y.
    cbn [code_link].
    rewrite Pr_code_sample.
    dependent destruction NC.
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
  LosslessOp op →
  NCalls 1 (resolve A RUN tt) empty_heap →
  ValidPackage LA IPICK A_export A →
  Pr (A ∘ RAND) =1 \dlet_(x <- op.π2) Pr (A ∘ PICK x).
Proof.
  intros LL NC VA b.
  unfold Pr, SDistr_bind, SDistr_unit, Pr_op.
  rewrite resolve_link.

  assert (H : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H).
  rewrite (testing1 LL NC H0).
  rewrite dlet_dlet.
  apply dlet_f_equal => y.
  rewrite resolve_link => //.
Qed.

Definition cell : Location := (0%N, 'option (op.π1)).

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

Lemma testings {LA} {A : raw_package} :
  fseparate LA [fmap cell] →
  LosslessOp op →
  ValidPackage LA IPICK A_export A →
  Pr (A ∘ CELL ∘ RAND) =1 \dlet_(x <- op.π2) Pr ((A ∘ CELL) ∘ PICK x).
Proof.
  intros SEP LL VA x.
  rewrite link_assoc.
  erewrite testing => //.
  2: ssprove_valid.
  rewrite resolve_link.

  assert (H : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H).

  move: empty_heap; induction H0.
  - intros h. apply valid_ret.
  - intros h.
    fmap_invert H0.
    cbn [code_link].
    destruct x0.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind].
    apply valid_getr.
    destruct (get_heap h cell) eqn:E.
    { cbn [bind]. apply H2. }
    cbn [bind].
    apply valid_opr => r.
    apply valid_putr.
    clear E.
    move: h.
    induction (H1 r).
    + intros h. apply valid_ret.
    + intros h.
      fmap_invert H0.
      destruct x0.
      cbn[code_link].
      repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
      cbn[bind].
      apply valid_getr.
      rewrite get_set_heap_eq.
      cbn[bind].
      apply H4.
    + intros h.
      cbn[code_link].
      apply valid_getr.
      apply H4.
    + intros h.
      cbn [code_link].
      apply valid_putr.
      rewrite set_heap_commut //.
      apply fhas_in in H0.
      destruct SEP as [SEP].
      move: SEP => /fdisjointP.
      intros H'.
      specialize (H' _ H0).
      rewrite domm_set domm0 in H'.
      apply /negP.
      move=> /eqP H''.
      rewrite H'' in H'.
      rewrite in_fsetU in_fset1 eq_refl // in H'.
    + intros h.
      cbn [code_link].
      apply valid_sampler => y.
      apply H3.
  - intros h.
    cbn [code_link].
    apply valid_getr.
    apply H2.
  - intros h.
    cbn [code_link].
    apply valid_putr.
    apply IHvalid_code.
  - intros h.
    cbn [code_link].
    apply valid_sampler => y.
    apply H1.
Qed.

End Proof.


Lemma testing_uni {F : finType} {LA} {A : raw_package} {b} `{Positive #|F|} :
  fseparate LA [fmap cell (uniform #|F|) ] →
  ValidPackage LA (IPICK (uniform #|F|)) A_export A →
  Pr (A ∘ CELL (uniform #|F|) ∘ RAND (uniform #|F|)) b
      = (\sum_f Pr ((A ∘ CELL (uniform #|F|)) ∘ PICK (uniform #|F|) f) b / #|F|%:R)%R.
Proof.
  intros SEP VA.
  rewrite testings //.
  rewrite dletE.
  rewrite psum_fin.
  apply eq_bigr => x _.
  rewrite GRing.mulrC.
  replace ((uniform #|F|).π2 x) with (#|F|%:R^-1 : Axioms.R)%R.
  - apply Num.Theory.ger0_norm.
    apply Num.Theory.mulr_ge0.
    + unfold Pr, SDistr_bind; rewrite dletE; apply ge0_psum.
    + rewrite Num.Theory.invr_ge0.
      apply Num.Theory.ler0n.
  - simpl.
    unfold UniformDistrLemmas.r.
    rewrite GRing.Theory.div1r card_ord //.
Qed.


