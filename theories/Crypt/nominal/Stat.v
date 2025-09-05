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

(* Preparation lemmas *)
Lemma Pr_code_ret {A : choiceType} {x : A} {h} :
  Pr_code (ret x) h = dunit (x, h).
Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

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
  Pr_code (x ← sample op' ;; k x) h = \dlet_(x <- op'.π2) Pr_code (k x) h. 
Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

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

Lemma AdvantageE_Pr {LA L L' I} {G G' A}
  `{ValidPackage LA I A_export A}
  `{ValidPackage L Game_import I G}
  `{ValidPackage L' Game_import I G'} :
  fseparate LA L →
  fseparate LA L' →
  G ≈₀ G' → Pr (A ∘ G) true = Pr (A ∘ G') true.
Proof.
  intros S1 S2 H'.
  apply GRing.Theory.subr0_eq.
  apply Num.Theory.normr0_eq0.
  eapply (H' LA); done.
Qed.

Lemma Adv_Pr {L I} {G G' A : nom_package} `{ValidPackage L I A_export A} :
  perfect I G G' → Pr (A ∘ G)%sep true = Pr (A ∘ G')%sep true.
Proof.
  intros H'.
  apply GRing.Theory.subr0_eq.
  apply Num.Theory.normr0_eq0.
  eapply H'.
  exact H.
Qed.

(* PICK game *)

Definition IPICK T := [interface [ 0%N ] : { 'unit ~> T }].

Definition PICK {T : choice_type} (x : T) : game (IPICK T) :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> T } 'tt {
      ret x
    } ].

Definition cell T : Location := (0%N, 'option T).

Definition CELL T : package (IPICK T) (IPICK T) :=
  [package [fmap cell T ] ;
    [ 0%N ] : { 'unit ~> T } 'tt {
      mc ← get cell T ;;
      match mc with
      | Some c => ret c
      | None => 
        r ← call [ 0%N ] : { 'unit ~> T } tt ;;
        #put cell T := Some r ;;
        ret r
      end
    } ].

Lemma CELL_PICK_perf {T : choice_type} (x : T) :
  CELL T ∘ PICK x ≈₀ PICK x.
Proof.
  pose (inv := (heap_ignore [fmap cell T] ⋊ couple_lhs (cell T) (cell T) (λ v _, v = None ∨ v = Some x))).
  apply (eq_rel_perf_ind _ _ inv);
    [ unfold inv; ssprove_invariant; [ fmap_solve | by left ] |].
  unfold inv.
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl; simpl.
  apply r_get_remember_lhs => y.
  eapply (r_rem_couple_lhs (cell T) (cell T)); try exact _.
  intros H.
  destruct H; subst.
  - apply r_put_lhs.
    ssprove_restore_mem.
    { ssprove_invariant. by right. }
    by apply r_ret.
  - apply r_forget_lhs.
    by apply r_ret.
Qed.


Section Proof.

Context (op : Op).

Definition RAND : game (IPICK op.π1) :=
  [package [fmap cell op.π1] ;
    [ 0%N ] : { 'unit ~> op.π1 } 'tt {
      mr ← get cell op.π1 ;;
      match mr with
      | Some r => ret r
      | None =>
        r ← sample op ;;
        #put cell op.π1 := Some r ;;
        ret r
      end
    } ].


Lemma testing0 {LA} {T} {A : raw_code T} {f f' : op.π1} {h} :
  fseparate LA [fmap cell op.π1] →
  ValidCode LA (IPICK op.π1) A →
  get_heap h (cell op.π1) = Some f' →
  Pr_code (code_link A RAND) h
  = Pr_code (code_link A (CELL op.π1 ∘ PICK f)) h.
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
  fseparate LA [fmap cell op.π1] →
  LosslessOp op →
  ValidCode LA (IPICK op.π1) A →
  Pr_code (code_link A RAND) h
    = \dlet_(f <- op.π2) Pr_code (code_link A (CELL op.π1 ∘ PICK f)) h.
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
    destruct (get_heap h (cell _)) eqn:E.
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
  fseparate LA [fmap cell op.π1] →
  LosslessOp op →
  ValidPackage LA (IPICK op.π1) A_export A →
  Pr (A ∘ RAND) = \dlet_(x <- op.π2) Pr (A ∘ CELL op.π1 ∘ PICK x).
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

Lemma testing' {LA} {A : raw_package} :
  fseparate LA [fmap cell op.π1] →
  LosslessOp op →
  ValidPackage LA (IPICK op.π1) A_export A →
  Pr (A ∘ RAND) true = (\dlet_(x <- op.π2) Pr (A ∘ PICK x)) true.
Proof.
  intros SEP LL VA.
  rewrite testing //.
  rewrite 2!dletE.
  apply eq_psum => x.
  f_equal.
  eapply AdvantageE_Pr.
  - fmap_solve.
  - fmap_solve.
  - apply CELL_PICK_perf.
Qed.

End Proof.


Lemma testing_uni n {LA} {A : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA (IPICK ('fin n)) A_export A →
  Pr (A ∘ RAND (uniform n)) true
      = (\sum_i Pr (A ∘ @PICK ('fin n) i) true / n%:R)%R.
Proof.
  intros SEP VA.
  rewrite testing' //.
  rewrite dletE.
  rewrite psum_fin.
  apply eq_bigr => x _.
  rewrite GRing.mulrC.
  replace ((uniform n).π2 x) with (n%:R^-1 : Axioms.R)%R.
  - apply Num.Theory.ger0_norm.
    apply Num.Theory.mulr_ge0.
    + unfold Pr, SDistr_bind; rewrite dletE; apply ge0_psum.
    + rewrite Num.Theory.invr_ge0.
      apply Num.Theory.ler0n.
  - simpl.
    unfold UniformDistrLemmas.r.
    rewrite GRing.Theory.div1r card_ord //.
Qed.

Lemma testing_uni2 {n} {LA} {A : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA (IPICK ('fin n)) A_export A →
  (Pr (A ∘ RAND (uniform n)) true *+ n
      = \sum_i Pr (A ∘ @PICK ('fin n) i) true)%R.
Proof.
  intros H' H''.
  rewrite testing_uni //.
  rewrite -(GRing.Theory.mulr_natr (\sum__ _) n).
  rewrite GRing.mulr_suml.
  apply eq_big => // i _.
  rewrite -GRing.mulrA GRing.mulVf ?GRing.mulr1 //.
  apply /eqP => H0.
  erewrite <- GRing.mul0rn in H0.
  apply Num.Theory.pmulrnI in H0 => //.
  move: (GRing.oner_eq0 R) => /eqP //.
Qed.

Definition unif n : code emptym emptym nat := {code
  match n with
  | 0 => ret 0%N
  | S m => f ← sample uniform (S m) ;; ret (nat_of_ord f)
  end }.

Definition RANDN n : game (IPICK nat) :=
  [package [fmap cell nat ] ;
    [ 0%N ] : { 'unit ~> 'nat } 'tt {
      mr ← get cell nat ;;
      match mr with
      | Some r => ret r
      | None =>
        r ← unif n ;;
        #put cell nat := Some r ;;
        ret r
      end
    } ].

Lemma testing_pick {n : nat} {A R R' : raw_package} :
  (∀ A i, Pr (A ∘ R' ∘ PICK i) true = Pr (A ∘ R ∘ PICK i.+1) true)
  → (AdvantageE (R ∘ PICK 0%N) (R ∘ PICK n) A
  = AdvantageE (R ∘ RANDN n) (R' ∘ RANDN n) A *+ n)%R.
Proof.
  intros IH.
  rewrite Advantage_sym.
  unfold AdvantageE.
  rewrite -(GRing.telescope_sumr (fun i => Pr (A ∘ R ∘ PICK i) true)) //.
  rewrite GRing.sumrB.
  under eq_big.
  1: intros; over.
  1: intros i _; rewrite -IH link_assoc; over.
Admitted.

Lemma testing_uni2_adv {n} {LA} {I} {A R R' : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA I A_export A →
  ValidPackage LA (IPICK 'fin n) I R →
  ValidPackage LA (IPICK 'fin n) I R' →
  (AdvantageE (R ∘ RAND (uniform n)) (R' ∘ RAND (uniform n)) A *+ n
    <= \sum_i AdvantageE
      (R ∘ @PICK 'fin n i)
      (R' ∘ PICK i) A)%R.
Proof.
  intros H' VA VG VG'.
  unfold AdvantageE.
  rewrite -Num.Theory.normrMn.
  rewrite -GRing.mulr_natr.
  rewrite GRing.mulrBl.
  rewrite 2!GRing.mulr_natr.
  rewrite 2!link_assoc.
  do 2 (rewrite testing_uni2; [| fmap_solve ]).
  rewrite -GRing.sumrB.
  eapply Order.POrderTheory.le_trans.
  { apply Num.Theory.ler_norm_sum. }
  apply Num.Theory.ler_sum => i _.
  rewrite 2!link_assoc //.
Qed.

