From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

(******************************************************************************)
(* This file shows that renaming is equivariant in the semantics of SSProve.  *)
(* This means that code may be freely replaced with alpha-equivalent code.    *)
(******************************************************************************)

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import PackageNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.


(* Code as nominal *)

#[non_forgetful_inheritance]
HB.instance Definition _ : DeclareDiscrete R := DeclareDiscrete.Build R.
HB.instance Definition _ : DeclareDiscrete Interface := DeclareDiscrete.Build Interface.

Program Definition Location_HasAction
  := HasAction.Build Location (λ π l, (natize (π (atomize l.1)), l.2)) _ _.
Obligation 1. by elim: x => [T n]. Qed.
Obligation 2. rewrite fpermM natizeK //. Qed.

HB.instance Definition _ : HasAction Location := Location_HasAction.


Fixpoint rename_code_def {A} π (c : raw_code A) := 
  match c with
  | ret x => ret x
  | opr o x k => opr o x (fun y => rename_code_def π (k y))
  | getr l k => getr (rename π l) (fun y => rename_code_def π (k y))
  | putr l v k => putr (rename π l) v (rename_code_def π k)
  | pkg_core_definition.sampler op k =>
      pkg_core_definition.sampler op (fun y => rename_code_def π (k y))
  end.

Program Definition code_HasAction {A}
  := HasAction.Build (raw_code A) rename_code_def _ _.
Obligation 1.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; reflexivity.
Qed.
Obligation 2.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; try reflexivity.
  1,2: unfold rename; simpl; rewrite fpermM natizeK //.
Qed.

HB.instance Definition _ {A} : HasAction (raw_code A) := code_HasAction.

Lemma mcode_bind {A B} : ∀ f (c : raw_code A) (k : A → raw_code B),
  rename f (a ← c ;; k a) = (a ← rename f c ;; rename f (k a)).
Proof.
  intros f c k.
  unfold rename.
  induction c;
    simpl; try setoid_rewrite H;
    try setoid_rewrite IHc; done.
Qed.


Program Definition Locations_HasAction : HasAction Locations
  := HasAction.Build Locations
    (λ π L, mapm2 (λ x, natize (π (atomize x))) id L) _ _.
Obligation 1. apply eq_fmap => y. rewrite mapm2E // omap_id //. Qed.
Obligation 2.
  apply eq_fmap => y.
  pose (na π x := natize (π (atomize x))).
  replace y with (na f (na g (na g^-1%fperm (na f^-1%fperm y)))).
  2: rewrite /na 2!natizeK fpermKV natizeK fpermKV atomizeK //.
  rewrite mapm2E ?mapm2E ?omap_id ?omap_id.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  replace (na f (na g (na g^-1%fperm (na f^-1%fperm y))))
    with (na (f * g)%fperm (na (f * g)^-1%fperm y)).
  2: rewrite /na 2!natizeK fpermKV natizeK fpermKV atomizeK //.
  2: rewrite natizeK fpermKV atomizeK //.
  rewrite mapm2E ?omap_id.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  rewrite Nominal.fperm_mul_inv /na natizeK fpermM //.
Qed.

HB.instance Definition _ : HasAction Locations
  := Locations_HasAction.

Lemma fhas_Location_equi :
  equivariant (λ (L : Locations) (l : Location), fhas L l).
Proof.
  apply equi2_prove => π L l.
  rewrite //= mapm2E.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  rewrite omap_id.
  by destruct l.
Qed.

Lemma fhas_rename {π} {L : Locations} {l : Location} :
  fhas L l → fhas (π ∙ L : Locations) (π ∙ l : Location).
Proof. by rewrite -(equi2_use _ fhas_Location_equi). Qed.

#[export]
Instance mcode_valid {L : Locations} {I A f} {c : raw_code A}
  : ValidCode L I c → ValidCode (f ∙ L) I (f ∙ c).
Proof.
  intros H.
  induction H.
  + apply valid_ret.
  + apply valid_opr; easy.
  + apply valid_getr.
    - by apply fhas_rename.
    - apply H1.
  + apply valid_putr.
    - by apply fhas_rename.
    - apply IHvalid_code.
  + apply valid_sampler.
    apply H0.
Qed.

(* Package as nominal *)

Definition mtyped f : typed_raw_function → typed_raw_function
  := fun t => match t with
              | (T; P; k) => (T; P; fun s => rename f (k s))
              end.

Program Definition typed_HasAction : HasAction typed_raw_function
  := HasAction.Build _ mtyped _ _.
Obligation 1.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_id.
Qed.
Obligation 2.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_comp.
Qed.

HB.instance Definition _ : HasAction typed_raw_function
  := typed_HasAction.

Program Definition raw_package_HasAction : HasAction raw_package
  := HasAction.Build _ (λ π, mapm (rename π)) _ _.
Obligation 1.
  apply eq_fmap => i.
  rewrite mapmE.
  destruct (x i); [| reflexivity ].
  rewrite //= rename_id //.
Qed.
Obligation 2.
  rewrite -mapm_comp.
  apply eq_mapm => t.
  rewrite //= rename_comp //.
Qed.

HB.instance Definition _ : HasAction raw_package
  := raw_package_HasAction.

Lemma fhas_rename_raw_package (n : nat) (A B : choice_type) π p g :
  fhas p (n, (A; B; g)) → fhas (π ∙ p : raw_package) (n, (A; B; λ x, π ∙ g x)).
Proof.
  intros H.
  rewrite //= mapmE H //=.
Qed.

#[export]
Instance rename_valid {L I E p} f :
  ValidPackage L I E p → ValidPackage (f ∙ L) I E (f ∙ p).
Proof.
  intros [Ve Vi].
  split; [ intros o; split |].
  - intros H.
    specialize (Ve o).
    rewrite Ve in H.
    destruct H as [g H].
    exists (λ x, f ∙ g x).
    apply fhas_rename_raw_package, H.
  - intros H.
    rewrite Ve.
    destruct H as [g H].
    exists (λ x, f^-1%fperm ∙ g x).
    rewrite -(renameK f p).
    apply fhas_rename_raw_package, H.
  - intros n [A [B g]] x H.
    simpl.
    rewrite -(renameKV f (g x)).
    apply mcode_valid.
    specialize (Vi n (A; B; λ x, f^-1%fperm ∙ g x)).
    apply Vi.
    rewrite -(renameK f p).
    apply fhas_rename_raw_package, H.
Qed.


(* Pr proof *)

Definition my_inv' π := fun '(s0, s1) =>
  ∀ l, get_heap s0 l = get_heap s1 (π ∙ l).

Fixpoint importless {A} (c : raw_code A) := 
  match c with
  | ret x => ret x
  | opr o _ k => importless (k (chCanonical (chtgt o)))
  | getr l k => getr l (fun x => importless (k x))
  | putr l v k => putr l v (importless k)
  | pkg_core_definition.sampler op k =>
      pkg_core_definition.sampler op (fun x => importless (k x))
  end.

Lemma r_rename {A} π (c : raw_code A) :
    ⊢ ⦃ λ '(h₀, h₁), my_inv' π (h₀, h₁) ⦄
        importless c ≈ importless (π ∙ c)
      ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ my_inv' π (s0, s1) ⦄.
Proof.
  induction c.
  - by apply r_ret.
  - unfold rename; simpl.
    apply H.
  - apply r_get_remember_lhs => x.
    destruct l as [n T]; simpl.
    eapply r_get_remind_rhs.
    2: apply r_forget_lhs, H.
    intros s0 s1 [h1 h2].
    unfold rem_lhs, rem_rhs in h2 |- *.
    subst; symmetry.
    apply (h1 (n, T)).
  - apply r_put_vs_put.
    ssprove_restore_pre; [| apply IHc ].
    intros s0 s1 H1.
    intros l'.
    elim: (eq_dec l.1 l'.1) => [H4|H4].
      + rewrite /rename //= H4 /get_heap /set_heap.
        rewrite 2!setmE H4 2!eq_refl //=.
      + rewrite !get_set_heap_neq.
        * by apply H1.
        * apply /eqP.
          intros H.
          apply (can_inj natizeK) in H.
          apply (can_inj (fpermK _)) in H.
          apply (can_inj atomizeK) in H.
          by apply H4.
        * apply /negP.
          move => /eqP E; subst.
          by apply H4.
  - eapply (rsame_head_cmd_alt (cmd_sample op)) ; [
        eapply cmd_sample_preserve_pre
      | idtac
      ].
    apply H.
Qed.

Lemma repr_importless {A} (c : raw_code A) : repr (importless c) = repr c.
Proof.
  induction c.
  + done.
  + simpl.
    rewrite H //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite H //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite IHc //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite H //.
Qed.

Lemma coerce_kleisli_rename {A A' B B'} π g x
  : π ∙ @coerce_kleisli A A' B B' g x
  = @coerce_kleisli A A' B B' (λ x, π ∙ g x) x.
Proof.
  rewrite /coerce_kleisli -2!lock.
  rewrite mcode_bind //.
Qed.

(* Proof heavily inspired by eq_upto_inv_perf_ind in SSProve *)
Lemma Pr_rename {π} {P : raw_package} {t} :
  Pr P t = Pr (π ∙ P) t.
Proof.
  unfold Pr, Pr_op.
  unfold rename, resolve; simpl.
  rewrite mapmE.
  destruct (P 0%N) eqn:req; [simpl | done ].
  destruct t0 as [A [B r]] => //=.
  unfold Pr_code.
  unfold Pr_code, SDistr_bind, SDistr_unit.
  rewrite 2!dletE.
  simpl.

  assert (
    ∀ y,
      (λ x : prod (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) t) =
      (λ x : prod (tgt RUN) heap_choiceType, (eq_op x.1 t)%:R * (y x))
  ) as Hrew.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite 2!Hrew.

  unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
  unfold SubDistr.SDistr_obligation_2. simpl.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite !SDistr_rightneutral. simpl.

  assert (
    ∀ x y : tgt RUN * heap_choiceType,
      (let '(b₀, s₀) := x in λ '(b₁, s₁), b₀ = b₁ ∧ my_inv' π (s₀, s₁)) y →
      (eq_op (fst x) t) ↔ (eq_op (fst y) t)
  ) as Ha.
  { intros [b₀ s₀] [b₁ s₁]. simpl.
    intros [e ?]. rewrite e. intuition auto.
  }

  pose (H := r_rename π (@coerce_kleisli A 'unit B 'bool r tt)).
  apply to_sem_jdg in H.
  epose proof (Heq := Pr_eq_empty (my_inv' π)
    (λ '(b0, s0) '(b1, s1), b0 = b1 /\ my_inv' π (s0, s1))
    _ _ H _ Ha).
  rewrite -(repr_importless (@coerce_kleisli A 'unit B 'bool r tt)).
  rewrite -(repr_importless (@coerce_kleisli A 'unit B 'bool (λ x, π ∙ r x) tt)).
  rewrite -coerce_kleisli_rename.
  apply Heq.
  Unshelve.
  done.
Qed.

Add Parametric Morphism : Pr with
  signature alpha ==> eq as Pr_mor.
Proof.
  intros x y [π' H0].
  apply distr_ext.
  intros b.
  rewrite -H0.
  apply Pr_rename.
Qed.
