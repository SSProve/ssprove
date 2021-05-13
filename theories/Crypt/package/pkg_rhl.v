(** Package Relational Hoar Logic

  This file connects packages to the relational Hoare logic and provides
  basic crypto-style reasoning notions.
*)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph chUniverse pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_lookup pkg_advantage
  pkg_invariants.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, who knows why. *)
From Crypt Require Import FreeProbProg.

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

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

Notation " r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄ " :=
  (semantic_judgement _ _ (repr c1) (repr c2) (fromPrePost pre post))
  : package_scope.

Theorem rbind_rule :
  ∀ {A1 A2 B1 B2 : ord_choiceType} {f1 f2} m1 m2
    (pre : precond) (mid : postcond A1 A2) (post : postcond B1 B2),
    r⊨ ⦃ pre ⦄ m1 ≈ m2 ⦃ mid ⦄ →
    (∀ a1 a2,
      r⊨ ⦃ λ '(s1, s2), mid (a1, s1) (a2, s2) ⦄ f1 a1 ≈ f2 a2 ⦃ post ⦄
    ) →
    r⊨ ⦃ pre ⦄ bind m1 f1 ≈ bind m2 f2 ⦃ post ⦄.
Proof.
  intros A1 A2 B1 B2 f1 f2 m1 m2 pre mid post hm hf.
  rewrite !repr_bind.
  apply (bind_rule_pp (repr m1) (repr m2) pre mid post hm hf).
Qed.

Lemma get_case :
  ∀ LA (I : heap_choiceType * heap_choiceType → Prop) ℓ,
    INV LA I →
    ℓ \in LA →
    r⊨ ⦃ λ '(s₀, s₃), I (s₀, s₃) ⦄
      x ← get ℓ ;; ret x ≈ x ← get ℓ ;; ret x
      ⦃ λ '(b₁, s₁) '(b₂, s₂), b₁ = b₂ ∧ I (s₁, s₂) ⦄.
Proof.
  intros LA I ℓ hinv hin. intros [s₁ s₂]. simpl.
  rewrite /SpecificationMonads.MonoCont_bind /=.
  rewrite /SpecificationMonads.MonoCont_order
    /SPropMonadicStructures.SProp_op_order
    /Morphisms.pointwise_relation /Basics.flip
    /SPropMonadicStructures.SProp_order /=.
  intuition auto.
  assert (get_heap s₁ ℓ = get_heap s₂ ℓ) as Hv.
  { unfold INV in hinv.
    specialize (hinv s₁ s₂). destruct hinv as [hinv _].
    eapply hinv. all: auto.
  }
  pose v := (SDistr_unit _ (((get_heap s₁ ℓ), s₁),
                            ((get_heap s₂ ℓ), s₂))).
  exists v. split.
  - apply SDistr_unit_F_choice_prod_coupling.
    reflexivity.
  - intros [b₁ s₃] [b₂ s₄]. intro hd.
    apply H1. rewrite dunit1E in hd.
    assert (
      (get_heap s₁ ℓ, s₁, (get_heap s₂ ℓ, s₂)) = (b₁, s₃, (b₂, s₄))
    ) as e.
    { destruct ((get_heap s₁ ℓ, s₁, (get_heap s₂ ℓ, s₂)) == (b₁, s₃, (b₂, s₄))) eqn:e.
      - move: e => /eqP e. assumption.
      - rewrite e in hd. cbn in hd.
        rewrite mc_1_10.Num.Theory.ltrr in hd. discriminate.
    }
    inversion e. subst. intuition auto.
Qed.

Lemma put_case :
  ∀ {LA} (I : heap_choiceType * heap_choiceType → Prop) l v,
    INV LA I →
    l \in LA →
    r⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
        putr l v (ret tt) ≈ putr l v (ret tt)
        ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
Proof.
  intros LA I l v hinv hin.
  intros [s1 s2]. simpl.
  rewrite /SpecificationMonads.MonoCont_bind /=.
  rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
          /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order /=.
  intuition eauto.
  eexists (SDistr_unit _ _).
  split.
  + apply SDistr_unit_F_choice_prod_coupling.
    reflexivity.
  + intros [b1 s3] [b2 s4].
    intros Hd.
    apply H1.
    unfold SDistr_unit in Hd.
    rewrite dunit1E in Hd.
    assert ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) = (b1, s3, (b2, s4))) as Heqs.
    { destruct ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) == (b1, s3, (b2, s4))) eqn:Heqd.
      - move: Heqd. move /eqP => Heqd. assumption.
      - rewrite Heqd in Hd. simpl in Hd.
        rewrite mc_1_10.Num.Theory.ltrr in Hd. discriminate.
    }
    inversion Heqs.
    intuition eauto.
    eapply hinv. all: eauto.
Qed.

(* TODO MOVE? *)

Lemma destruct_pair_eq {R : ringType} {A B : eqType} {a b : A} {c d : B} :
  ((a, c) == (b, d))%:R = (a == b)%:R * (c == d)%:R :> R.
Proof.
  destruct (a == b) eqn:ab, (c == d) eqn:cd.
  all: cbn; rewrite ab cd /=; try rewrite GRing.mulr1; try rewrite GRing.mulr0; reflexivity.
Qed.

Lemma summable_eq {A : choiceType} {s : A} :
  realsum.summable (T:=A) (R:=R) (λ x, (x == s)%:R).
Proof.
  match goal with
  | |- realsum.summable ?f => eassert (f = _) as Hf end.
  { extensionality x. rewrite eq_sym.
    rewrite -dunit1E. reflexivity. }
  rewrite Hf. clear Hf.
  apply summable_mu.
Qed.

Lemma summable_pair_eq {A : choiceType} {B C : eqType} (f1 f3 : A -> B) (f2 f4 : A -> C)
      (h1 : realsum.summable (T:=A) (R:=R) (λ x, (f1 x == f3 x)%:R))
      (h2 : realsum.summable (T:=_) (R:=R) (λ x, (f2 x == f4 x)%:R))
  :
    realsum.summable (T:=_) (R:=R) (λ x, ((f1 x, f2 x) == (f3 x, f4 x))%:R).
Proof.
  match goal with
  | |- realsum.summable ?f => eassert (f = _) as Hf end.
  { extensionality x.
    apply (destruct_pair_eq (a:= f1 x) (b:=f3 x) (c:= f2 x) (d := f4 x)). }
  rewrite Hf.
  apply realsum.summableM. all: assumption.
Qed.

Lemma psum_exists {R : realType} {A : choiceType} {f : A -> R}
      (H : 0 < realsum.psum (T:=A) (R:=R) f) (Hpos : forall x, 0 <= f x) :
  exists x, 0 < f x.
Proof.
  assert (realsum.psum f ≠ 0) as Hneq.
  { intros Hgt.
    rewrite Hgt in H.
    rewrite mc_1_10.Num.Theory.ltrr in H.
    auto. }
  destruct (realsum.neq0_psum (R:=R) Hneq) as [x Hx].
  exists x. specialize (Hpos x).
  rewrite mc_1_10.Num.Theory.ler_eqVlt in Hpos.
  move: Hpos. move /orP => [H1 | H2].
  - move: H1. move /eqP => H1. rewrite -H1.
    rewrite mc_1_10.Num.Theory.ltrr. auto.
  - assumption.
Qed.

Lemma pmulr_me (x y : R) : 0 <= y -> (0 < y * x) -> (0 < x).
Proof.
  rewrite le0r => /orP[/eqP->|].
  - by rewrite GRing.mul0r mc_1_10.Num.Theory.ltrr.
  - intros. by rewrite -(pmulr_rgt0 x b).
Qed.

Lemma ge0_eq {R : realType} {A : eqType} {x y : A} (H : 0 < ((x == y)%:R) :> R) :
  x = y.
Proof.
  destruct (x == y) eqn:Heq.
  - move: Heq. by move /eqP.
  - by rewrite mc_1_10.Num.Theory.ltrr in H.
Qed.

Lemma ne0_eq {R : ringType} {A : eqType} {x y : A} (H : ((x == y)%:R) ≠ (0 : R)) :
  x = y.
Proof.
  destruct (x == y) eqn:Heq.
  - move: Heq. by move /eqP.
  - cbn in H. intuition.
Qed.

(* TODO MOVE *)
Lemma dlet_f_equal :
  ∀ {R : realType} {T U : choiceType} (m : {distr T / R}) (f g : T → {distr U / R}),
    f =1 g →
    \dlet_(x <- m) f x =1 \dlet_(x <- m) g x.
Proof.
  intros R T U m f g e x.
  apply functional_extensionality in e. subst.
  reflexivity.
Qed.

(* TODO This proof is really the same as cmd_sample_preserve_pre *)
Lemma sampler_case :
  ∀ {LA} (I : heap_choiceType * heap_choiceType -> Prop) op,
    INV LA I →
    r⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
      sampler op [eta ret (A:=Arit op)] ≈ sampler op [eta ret (A:=Arit op)]
      ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
Proof.
  intros LA I op HINV.
  intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  destruct op as [opA opB].
  pose (d :=
    SDistr_bind (λ x, SDistr_unit _ ((x, s₀), (x, s₁)))
      (Theta_dens.unary_ThetaDens0 _ (ropr (opA ; opB) (λ x : chElement opA, retrFree x)))
  ).
  exists d. split.
  - unfold coupling. split.
    + unfold lmg. unfold dfst.
      apply distr_ext. intro. simpl.
      rewrite dlet_dlet.
      simpl.
      unfold SDistr_bind, SDistr_unit.
      rewrite dlet_dlet.
      apply dlet_f_equal. intro.
      apply distr_ext. intro.
      rewrite dlet_unit. rewrite dlet_unit. simpl. reflexivity.
    + unfold rmg. unfold dsnd.
      apply distr_ext. intro. simpl.
      rewrite dlet_dlet.
      simpl.
      unfold SDistr_bind, SDistr_unit.
      rewrite dlet_dlet.
      apply dlet_f_equal. intro.
      apply distr_ext. intro.
      rewrite dlet_unit. rewrite dlet_unit. simpl. reflexivity.
  - intros [] [] e. subst d. simpl in e.
    rewrite SDistr_rightneutral in e. simpl in e.
    unfold SDistr_bind, SDistr_unit in e.
    rewrite dletE in e.
    erewrite eq_psum in e.
    2:{
      intro. rewrite dunit1E. reflexivity.
    }
    apply psum_exists in e.
    2:{
      intro. apply mulr_ge0.
      - auto.
      - apply ler0n.
    }
    destruct e as [? e].
    apply pmulr_me in e. 2: auto.
    apply ge0_eq in e. noconf e.
    eapply hpost. intuition auto.
Qed.

(** Syntactic judgment *)

(* It's the same as the semantic one, but we're abstracting it away. *)
Inductive rel_jdg {A B : choiceType} (pre : precond) (post : postcond A B)
  (p : raw_code A) (q : raw_code B) :=
  _from_sem_jdg : locked (r⊨ ⦃ pre ⦄ p ≈ q ⦃ post ⦄) → rel_jdg pre post p q.

Notation "⊢ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
  (rel_jdg pre post c1 c2)
  (format "⊢  ⦃  pre  ⦄ '/  '  '[' c1  ']' '/' ≈ '/  '  '[' c2  ']' '/' ⦃  post  ⦄")
  : package_scope.

Lemma from_sem_jdg :
  ∀ {A B : choiceType} pre (post : postcond A B) p q,
    r⊨ ⦃ pre ⦄ p ≈ q ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ p ≈ q ⦃ post ⦄.
Proof.
  intros A B pre post p q h.
  constructor. rewrite -lock. auto.
Qed.

Lemma to_sem_jdg :
  ∀ {A B : choiceType} pre (post : postcond A B) p q,
    ⊢ ⦃ pre ⦄ p ≈ q ⦃ post ⦄ →
    r⊨ ⦃ pre ⦄ p ≈ q ⦃ post ⦄.
Proof.
  intros A B pre post p q [h].
  rewrite -lock in h.
  exact h.
Qed.

(** Equivalence of packages in the program logic *)

Definition eq_up_to_inv (E : Interface) (I : precond) (p₀ p₁ : raw_package) :=
  ∀ (id : ident) (S T : chUniverse) (x : S),
    (id, (S, T)) \in E →
    ⊢ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
      get_op_default p₀ (id, (S, T)) x ≈ get_op_default p₁ (id, (S, T)) x
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄.

Lemma Pr_eq_empty :
  ∀ {X Y : ord_choiceType}
    {A : pred (X * heap_choiceType)} {B : pred (Y * heap_choiceType)}
    Ψ ϕ
    (c1 : @FrStP heap_choiceType X) (c2 : @FrStP heap_choiceType Y),
    ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄ →
    Ψ (empty_heap, empty_heap) →
    (∀ x y, ϕ x y → (A x) ↔ (B y)) →
    \P_[ θ_dens (θ0 c1 empty_heap) ] A =
    \P_[ θ_dens (θ0 c2 empty_heap) ] B.
Proof.
  intros X Y A B Ψ Φ c1 c2 ? ? ?.
  apply (Pr_eq Ψ Φ). all: assumption.
Qed.

(* TODO Rename *)
Lemma some_lemma_for_prove_relational :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) {B} (A : raw_code B)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{@ValidCode LA E B A},
    INV LA I →
    eq_up_to_inv E I p₀ p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I B A vp₀ vp₁ vA hLA hp.
  induction A in vA |- *.
  - cbn - [semantic_judgement].
    eapply weaken_rule. 1: apply ret_rule.
    intros [h₀ h₁] post.
    cbn. unfold SPropMonadicStructures.SProp_op_order.
    unfold Basics.flip, SPropMonadicStructures.SProp_order.
    intros [HI Hp].
    apply Hp. intuition auto.
  - cbn - [semantic_judgement lookup_op].
    apply inversion_valid_opr in vA as hA. destruct hA as [hi vk].
    destruct o as [id [S T]].
    eapply from_valid_package in vp₀.
    specialize (vp₀ _ hi). simpl in vp₀.
    destruct vp₀ as [f₀ [e₀ h₀]].
    eapply from_valid_package in vp₁.
    specialize (vp₁ _ hi). simpl in vp₁.
    destruct vp₁ as [f₁ [e₁ h₁]].
    erewrite lookup_op_spec_inv. 2: eauto.
    erewrite lookup_op_spec_inv. 2: eauto.
    specialize (hp id S T x hi).
    erewrite get_op_default_spec in hp. 2: eauto.
    erewrite get_op_default_spec in hp. 2: eauto.
    rewrite !repr_bind.
    eapply bind_rule_pp. 1:{ eapply to_sem_jdg in hp. exact hp. }
    cbn - [semantic_judgement].
    intros a₀ a₁.
    apply pre_hypothesis_rule.
    intros s₀ s₁ [? ?]. subst.
    eapply pre_weaken_rule. 1: eapply H.
    + eapply vk.
    + cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_getr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (get_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply H.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_putr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (@put_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply IHA.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    eapply bind_rule_pp.
    + eapply (@sampler_case LA). auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply H.
      * eapply inversion_valid_sampler. eauto.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
Qed.

(* TODO RENAME *)
Lemma prove_relational :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV' L₀ L₁ I →
    I (empty_heap, empty_heap) →
    fdisjoint LA L₀ →
    fdisjoint LA L₁ →
    eq_up_to_inv E I p₀ p₁ →
    AdvantageE p₀ p₁ A = 0.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I A vp₀ vp₁ vA hI' hIe hd₀ hd₁ hp.
  unfold AdvantageE, Pr.
  pose r := get_op_default A RUN tt.
  assert (hI : INV LA I).
  { unfold INV. intros s₀ s₁. split.
    - intros hi l hin. apply hI'.
      + assumption.
      + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
      + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
    - intros hi l v hin. apply hI'.
      + assumption.
      + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
      + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
  }
  unshelve epose proof (some_lemma_for_prove_relational p₀ p₁ I r hI hp) as h.
  1:{
    eapply valid_get_op_default.
    - eauto.
    - auto_in_fset.
  }
  assert (
    ∀ x y : tgt RUN * heap_choiceType,
      (let '(b₀, s₀) := x in λ '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁)) y →
      (fst x == true) ↔ (fst y == true)
  ) as Ha.
  { intros [b₀ s₀] [b₁ s₁]. simpl.
    intros [e ?]. rewrite e. intuition auto.
  }
  unfold Pr_op.
  unshelve epose (rhs := thetaFstd _ (repr (code_link r p₀)) empty_heap).
  simpl in rhs.
  epose (lhs := Pr_op (A ∘ p₀) RUN tt empty_heap).
  assert (lhs = rhs) as he.
  { subst lhs rhs.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    rewrite get_op_default_link. reflexivity.
  }
  unfold lhs in he. unfold Pr_op in he.
  rewrite he.
  unshelve epose (rhs' := thetaFstd _ (repr (code_link r p₁)) empty_heap).
  simpl in rhs'.
  epose (lhs' := Pr_op (A ∘ p₁) RUN tt empty_heap).
  assert (lhs' = rhs') as e'.
  { subst lhs' rhs'.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    rewrite get_op_default_link. reflexivity.
  }
  unfold lhs' in e'. unfold Pr_op in e'.
  rewrite e'.
  unfold rhs', rhs.
  unfold SDistr_bind. unfold SDistr_unit.
  rewrite !dletE.
  assert (
    ∀ x : bool_choiceType * heap_choiceType,
      ((let '(b, _) := x in dunit (R:=R) (T:=bool_choiceType) b) true) ==
      (x.1 == true)%:R
  ) as h1.
  { intros [b s].
    simpl. rewrite dunit1E. apply/eqP. reflexivity.
  }
  assert (
    ∀ y,
      (λ x : prod_choiceType (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true) =
      (λ x : prod_choiceType (tgt RUN) heap_choiceType, (x.1 == true)%:R * (y x))
  ) as Hrew.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite !Hrew.
  unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
  unfold SubDistr.SDistr_obligation_2. simpl.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite !SDistr_rightneutral. simpl.
  pose proof (Pr_eq_empty _ _ _ _ h hIe Ha) as Heq.
  simpl in Heq.
  unfold θ_dens in Heq.
  simpl in Heq. unfold pr in Heq.
  simpl in Heq.
  rewrite Heq.
  rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
  assert (∀ (x : R), `|x - x| = 0) as Hzero.
  { intros x.
    assert (x - x = 0) as H3.
    { apply /eqP. rewrite GRing.subr_eq0. intuition. }
    rewrite H3. apply mc_1_10.Num.Theory.normr0.
  }
  apply Hzero.
Qed.

Lemma eq_rel_perf_ind :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package) (inv : precond)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    Invariant L₀ L₁ inv →
    eq_up_to_inv E inv p₀ p₁ →
    p₀ ≈₀ p₁.
Proof.
  intros L₀ L₁ E p₀ p₁ inv v₀ v₁ [? ?] he.
  intros LA A vA hd₀ hd₁.
  eapply prove_relational. all: eauto.
Qed.

(* Special case where the invariant is equality of state. *)
Corollary eq_rel_perf_ind_eq :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    eq_up_to_inv E (λ '(h₀, h₁), h₀ = h₁) p₀ p₁ →
    p₀ ≈₀ p₁.
Proof.
  intros L₀ L₁ E p₀ p₁ v₀ v₁ h.
  eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁).
  - exact _.
  - assumption.
Qed.

(* Special case where the invariant is heap_ignore. *)
Corollary eq_rel_perf_ind_ignore :
  ∀ L {L₀ L₁ E} (p₀ p₁ : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    fsubset L (L₀ :|: L₁) →
    eq_up_to_inv E (heap_ignore L) p₀ p₁ →
    p₀ ≈₀ p₁.
Proof.
  intros L L₀ L₁ E p₀ p₁ v₀ v₁ hs h.
  eapply eq_rel_perf_ind with (heap_ignore L).
  - ssprove_invariant.
  - assumption.
Qed.

(** Rules for packages *)
(* same as in RulesStateprob.v with `r` at the beginning *)

(* Alternative to rbind_rule *)
Lemma r_bind :
  ∀ {A₀ A₁ B₀ B₁ : ord_choiceType} m₀ m₁ f₀ f₁
    (pre : precond) (mid : postcond A₀ A₁) (post : postcond B₀ B₁),
    ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ mid ⦄ →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₀, s₁), mid (a₀, s₀) (a₁, s₁) ⦄ f₀ a₀ ≈ f₁ a₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ bind m₀ f₀ ≈ bind m₁ f₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ B₀ B₁ m₀ m₁ f₀ f₁ pre mid post hm hf.
  eapply from_sem_jdg. eapply rbind_rule.
  - eapply to_sem_jdg. exact hm.
  - intros a₀ a₁. eapply to_sem_jdg. eapply hf.
Qed.

(* Pre-condition manipulating rules *)

Theorem rpre_weaken_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre pre' : precond) post,
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
    (∀ s₀ s₁, pre' (s₀, s₁) → pre (s₀, s₁)) →
    ⊢ ⦃ pre' ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre pre' post he hi.
  eapply from_sem_jdg.
  eapply pre_weaken_rule.
  - eapply to_sem_jdg. eauto.
  - eauto.
Qed.

Theorem rpre_hypothesis_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁,
      pre (s₀, s₁) → ⊢ ⦃ λ s, s.1 = s₀ ∧ s.2 = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
    ) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post h.
  eapply from_sem_jdg.
  eapply pre_hypothesis_rule.
  intros. eapply to_sem_jdg.
  apply h. auto.
Qed.

Theorem rpre_strong_hypothesis_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁, pre (s₀, s₁)) →
    ⊢ ⦃ λ _, True ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post hs h.
  eapply from_sem_jdg.
  eapply pre_strong_hypothesis_rule.
  - eauto.
  - eapply to_sem_jdg. auto.
Qed.

Theorem rpost_weaken_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) (post1 post2 : postcond A₀ A₁),
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post1 ⦄ →
    (∀ a₀ a₁, post1 a₀ a₁ → post2 a₀ a₁) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post2 ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post1 post2 h hi.
  eapply from_sem_jdg.
  eapply post_weaken_rule.
  - eapply to_sem_jdg. eauto.
  - eauto.
Qed.

Lemma rreflexivity_rule :
  ∀ {A : ord_choiceType} (c : raw_code A),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ eq ⦄.
Proof.
  intros A c.
  eapply from_sem_jdg.
  apply (reflexivity_rule (repr c)).
Qed.

(* TODO MOVE? *)
(* bindrFree_and_ret is too constrained *)
Lemma bindrFree_ret :
  ∀ S P A (m : rFreeF S P A),
    bindrFree m (λ x, retrFree x) = m.
Proof.
  intros S P A m.
  induction m.
  - reflexivity.
  - cbn. f_equal. extensionality x. auto.
Qed.

Theorem rpost_conclusion_rule :
  ∀ {A₀ A₁ B : ord_choiceType} {pre : precond}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁}
    (f₀ : A₀ → B) (f₁ : A₁ → B),
    ⊢ ⦃ pre ⦄
      x₀ ← c₀ ;; ret x₀ ≈ x₁ ← c₁ ;; ret x₁
    ⦃ λ '(a₀, s₀) '(a₁, s₁), s₀ = s₁ ∧ f₀ a₀ = f₁ a₁ ⦄ →
    ⊢ ⦃ pre ⦄ x₀ ← c₀ ;; ret (f₀ x₀) ≈ x₁ ← c₁ ;; ret (f₁ x₁) ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B pre c₀ c₁ f₀ f₁ h.
  eapply from_sem_jdg. eapply to_sem_jdg in h.
  rewrite !repr_bind in h. rewrite !repr_bind.
  eapply bind_rule_pp.
  - simpl (repr (ret _)) in h.
    rewrite !bindrFree_ret in h. exact h.
  - intros a₀ a₁. eapply to_sem_jdg.
    eapply rpre_hypothesis_rule. intros s s' [? e]. subst s'.
    rewrite e. eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

Theorem rpost_conclusion_rule_cmd :
  ∀ {A₀ A₁ B : ord_choiceType} {pre : precond}
    {c₀ : command A₀} {c₁ : command A₁}
    (f₀ : A₀ → B) (f₁ : A₁ → B),
    ⊢ ⦃ pre ⦄
      x₀ ← cmd c₀ ;; ret x₀ ≈
      x₁ ← cmd c₁ ;; ret x₁
    ⦃ λ '(a₀, s₀) '(a₁, s₁), s₀ = s₁ ∧ f₀ a₀ = f₁ a₁ ⦄ →
    ⊢ ⦃ pre ⦄ x₀ ← cmd c₀ ;; ret (f₀ x₀) ≈ x₁ ← cmd c₁ ;; ret (f₁ x₁) ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B pre c₀ c₁ f₀ f₁ h.
  eapply from_sem_jdg. eapply to_sem_jdg in h.
  rewrite !repr_cmd_bind in h.  rewrite !repr_cmd_bind.
  eapply bind_rule_pp.
  - simpl (repr (ret _)) in h.
    rewrite !bindrFree_ret in h. exact h.
  - intros a₀ a₁. eapply to_sem_jdg.
    eapply rpre_hypothesis_rule. intros s s' [? e]. subst s'.
    rewrite e. eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

Lemma r_ret :
  ∀ {A₀ A₁ : ord_choiceType} u₀ u₁ (pre : precond) (post : postcond A₀ A₁),
    (∀ s₀ s₁, pre (s₀, s₁) → post (u₀, s₀) (u₁, s₁)) →
    ⊢ ⦃ pre ⦄ ret u₀ ≈ ret u₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ u₀ u₁ pre post h.
  eapply from_sem_jdg. simpl.
  eapply weaken_rule. 1: eapply ret_rule.
  intros [s₀ s₁] P [hpre hpost]. simpl.
  eapply hpost. eapply h. apply hpre.
Qed.

Theorem rif_rule :
  ∀ {A₀ A₁ : ord_choiceType}
    (c₀ c₀' : raw_code A₀) (c₁ c₁' : raw_code A₁)
    {b₀ b₁}
    {pre : precond} {post : postcond A₀ A₁},
    (∀ s, pre s → b₀ = b₁) →
    ⊢ ⦃ λ s, pre s ∧ b₀ = true ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ λ s, pre s ∧ b₀ = false ⦄ c₀' ≈ c₁' ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ if b₀ then c₀ else c₀' ≈ if b₁ then c₁ else c₁' ⦃ post ⦄.
Proof.
  intros A₀ A₁ c₀ c₀' c₁ c₁' b₀ b₁ pre post hb ht hf.
  eapply from_sem_jdg. eapply to_sem_jdg in ht, hf.
  rewrite !repr_if.
  eapply if_rule. all: eauto.
Qed.

(* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)

(* skipped for now:
Theorem bounded_do_while_rule *)

(*TODO: asymmetric variants of bounded_do_while --
  Rem.: low priority as not useful for our examples *)

Section For_loop_rule.

  (* for i = 0 to N : do c *)
  Fixpoint for_loop (c : nat → raw_code 'unit) (N : nat) : raw_code 'unit :=
    match N with
    | 0 => c 0%nat
    | S m => for_loop c m ;; c (S m)
    end.

  Context (I : nat → precond) (N : nat).

  Context (c₀ c₁ : nat → raw_code 'unit).

  (* hypothesis : *)
  (* body maintains the loop invariant I *)
  (* to ease the proof we forget about this condition (0 <= n <= N)%nat -> *)

  Lemma for_loop_rule :
    (∀ i, ⊢ ⦃ I i ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I i.+1 (s₀,s₁) ⦄) →
    ⊢ ⦃ I 0%nat ⦄
      for_loop c₀ N ≈ for_loop c₁ N
    ⦃ λ '(_,s₀) '(_,s₁), I N.+1 (s₀,s₁) ⦄.
  Proof.
    intros h.
    induction N as [| n ih].
    - simpl. apply h.
    - simpl. eapply r_bind.
      + eapply ih.
      + simpl. intros _ _.
        eapply rpre_weaken_rule. 1: eapply h.
        auto.
  Qed.

End For_loop_rule.

Lemma valid_for_loop :
  ∀ L I c N,
    (∀ i, valid_code L I (c i)) →
    valid_code L I (for_loop c N).
Proof.
  intros L I c N h.
  induction N. all: simpl.
  - eapply h.
  - eapply valid_bind. all: eauto.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (for_loop ?c ?N)) =>
  eapply valid_for_loop ;
  intro ; eapply valid_code_from_class
  : typeclass_instances packages.

Lemma rcoupling_eq :
  ∀ {A : ord_choiceType} (K₀ K₁ : raw_code A) (ψ : precond),
    ⊢ ⦃ ψ ⦄ K₀ ≈ K₁ ⦃ eq ⦄ →
    ∀ s₀ s₁,
      ψ (s₀, s₁) →
      θ_dens (θ0 (repr K₀) s₀) = θ_dens (θ0 (repr K₁) s₁).
Proof.
  intros A K₀ K₁ ψ h s₀ s₁ hψ.
  eapply to_sem_jdg in h.
  eapply coupling_eq. all: eauto.
Qed.

Lemma rrewrite_eqDistrL :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ c₀' : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    (∀ s, θ_dens (θ0 (repr c₀) s) = θ_dens (θ0 (repr c₀') s)) →
    ⊢ ⦃ P ⦄ c₀' ≈ c₁ ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₀' c₁ h hθ.
  eapply to_sem_jdg in h.
  eapply from_sem_jdg.
  eapply rewrite_eqDistrL. all: eauto.
Qed.

Lemma rrewrite_eqDistrR :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ : raw_code A₀) (c₁ c₁' : raw_code A₁),
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    (∀ s, θ_dens (θ0 (repr c₁) s) = θ_dens (θ0 (repr c₁') s)) →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁' ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₁ c₁' h hθ.
  eapply to_sem_jdg in h.
  eapply from_sem_jdg.
  eapply rewrite_eqDistrR. all: eauto.
Qed.

Theorem rswap_rule :
  ∀ {A₀ A₁ : ord_choiceType} {I : precond} {post : postcond A₀ A₁}
    (c₀ : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ I ⦄ c₀ ≈ c₁
      ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
    ⊢ ⦃ I ⦄ c₁ ≈ c₀
      ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
    ⊢ ⦃ I ⦄ c₀ ;; c₁ ≈ c₁ ;; c₀
      ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄.
Proof.
  intros A₀ A₁ I post c₀ c₁ h1 h2.
  eapply to_sem_jdg in h1. eapply to_sem_jdg in h2.
  eapply from_sem_jdg.
  rewrite !repr_bind.
  eapply (swap_rule (repr c₀) (repr c₁)). all: auto.
Qed.

(** TW: I guess this to allow going under binders.
  We might be better off defining some morphisms on semantic judgments
  to use setoid_rewrite.
*)
Theorem rswap_ruleL :
  ∀ {A₀ A₁ B : ord_choiceType} {pre I : precond} {post : postcond A₁ A₀}
  (l : raw_code B) (c₀ : raw_code A₀) (c₁ : raw_code A₁),
  ⊢ ⦃ pre ⦄ l ≈ l ⦃ λ '(b₀, s₀) '(b₁, s₁), I (s₀, s₁) ⦄ →
  ⊢ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
  ⊢ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
  ⊢ ⦃ pre ⦄ l ;; c₀ ;; c₁ ≈ l ;; c₁ ;; c₀ ⦃ post ⦄.
Proof.
  intros A₀ A₁ B pre I post l c₀ c₁ hl h0 h1.
  eapply to_sem_jdg in h0, h1, hl.
  eapply from_sem_jdg.
  rewrite !repr_bind.
  eapply swap_ruleL. all: eauto.
Qed.

Theorem rswap_ruleR :
  ∀ {A₀ A₁ B : ord_choiceType} {post : postcond B B}
    (c₀ : raw_code A₀) (c₁ : raw_code A₁) (r : A₀ → A₁ → raw_code B),
    (∀ b b', b = b' → post b b') →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁) ≈
      a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈
      a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
      ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r postr hr h.
  eapply from_sem_jdg.
  repeat setoid_rewrite repr_bind. simpl.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr c₀) (repr c₁)).
  - intros. eapply to_sem_jdg. apply hr.
  - apply postr.
  - intro s.
    unshelve eapply coupling_eq.
    + exact (λ '(h₀, h₁), h₀ = h₁).
    + eapply to_sem_jdg in h. repeat setoid_rewrite repr_bind in h.
      apply h.
    + reflexivity.
Qed.

Lemma rsym_pre :
  ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁},
    (∀ h₀ h₁, pre (h₀, h₁) → pre (h₁, h₀)) →
    ⊢ ⦃ λ '(h₀, h₁), pre (h₁, h₀) ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post c₀ c₁ pre_sym h.
  unshelve eapply rpre_weaken_rule. 2: eassumption.
  assumption.
Qed.

Lemma rsymmetry :
  ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁},
    ⊢ ⦃ λ '(h₁, h₀), pre (h₀, h₁) ⦄ c₁ ≈ c₀
      ⦃ λ '(a₁, h₁) '(a₀, h₀), post (a₀, h₀) (a₁, h₁) ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post c₀ c₁ h.
  eapply from_sem_jdg.
  eapply symmetry_rule. eapply to_sem_jdg. auto.
Qed.

Definition spl (o : Op) :=
  @callrFree (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) (op_iota o).

Lemma rsamplerC :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r) ≈
      r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rrewrite_eqDistrL.
  - eapply rreflexivity_rule.
  - intro s.
    assert (
      repr_sample_c :
        repr (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r)) =
        bindrFree (spl o) (λ r, bindrFree (repr c) (λ a, retrFree (a,r)))
    ).
    { rewrite !repr_bind. f_equal. extensionality r.
      rewrite !repr_bind. reflexivity.
    }
    assert (
      repr_c_sample :
        repr (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r)) =
        bindrFree (repr c) (λ a, bindrFree (spl o) (λ r, retrFree (a,r)))
    ).
    { rewrite repr_bind. reflexivity. }
    rewrite repr_c_sample repr_sample_c.
    pose proof (sample_c_is_c_sample o (repr c) s) as hlp.
    unfold sample_c in hlp. unfold c_sample in hlp.
    apply hlp.
Qed.

Lemma rsamplerC_sym' :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← c ;; r ← (r ← sample o ;; ret r) ;;  (ret (r, a)) ≈
      r ← (r ← sample o ;; ret r) ;; a ← c ;;  (ret (r, a))
    ⦃ eq ⦄.
Proof.
  intros A o c.
  unshelve eapply rswap_ruleR.
  - auto.
  - intros a r. apply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - apply rsamplerC.
Qed.

Lemma rsamplerC' :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (r, a) ≈
      a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (r, a)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - apply rsamplerC_sym'.
  - intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

(* TODO: generalize the corresponding rule in RulesStateProb.v  *)
Theorem rswap_rule_ctx :
∀ {A : ord_choiceType} {I pre} {post Q : postcond A A}
  (l r c₀ c₁ : raw_code A),
  ⊢ ⦃ pre ⦄ l ≈ l ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ⦄ →
  (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), Q (a₀,s₀) (a₁,s₁) ⦄ r ≈ r ⦃ post ⦄) →
  ⊢ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
  ⊢ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
  ⊢ ⦃ pre ⦄ l ;; c₀ ;; c₁ ;; r ≈ l ;; c₁ ;; c₀ ;; r ⦃ post ⦄.
Proof.
  intros A I pre post Q l r c₀ c₁ hl hr h₀ h₁.
  eapply from_sem_jdg.
  rewrite !repr_bind.
  eapply swap_rule_ctx.
  1:{ eapply to_sem_jdg. exact hl. }
  2:{ eapply to_sem_jdg. exact h₀. }
  2:{ eapply to_sem_jdg. exact h₁. }
  intros a₀ a₁. eapply to_sem_jdg. eapply hr.
Qed.

Theorem rsame_head :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
  (m : raw_code A) (post : postcond B B),
  (∀ a, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ bind m f₀ ≈ bind m f₁ ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m post h.
  eapply (r_bind m m).
  - eapply rreflexivity_rule.
  - intros a₀ a₁.
    eapply rpre_hypothesis_rule. intros s₀ s₁ e.
    noconf e.
    eapply rpre_weaken_rule. 1: eapply h.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

Lemma rf_preserves_eq :
  ∀ {A B : ord_choiceType} {c₀ c₁ : raw_code A}
    (f : A → B),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← c₀ ;; ret x ≈ x ← c₁ ;; ret x ⦃ eq ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← c₀ ;; ret (f x) ≈ x ← c₁ ;; ret (f x) ⦃ eq ⦄.
Proof.
  intros A B c₀ c₁ f h.
  eapply r_bind.
  - rewrite !bind_ret in h. exact h.
  - intros a₀ a₁.
    apply rpre_hypothesis_rule. intros s₀ s₁ e. noconf e.
    eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

(* Similar to rrewrite_eqDistr but with program logic. *)
Lemma r_transL :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ c₀' : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c₀ ≈ c₀' ⦃ eq ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    ⊢ ⦃ P ⦄ c₀' ≈ c₁ ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₀' c₁ he h.
  eapply rrewrite_eqDistrL. 1: exact h.
  intro s. eapply rcoupling_eq. 1: exact he.
  cbn. reflexivity.
Qed.

Lemma r_transR :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ : raw_code A₀) (c₁ c₁' : raw_code A₁),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c₁ ≈ c₁' ⦃ eq ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁' ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₁ c₁' he h.
  eapply rrewrite_eqDistrR. 1: exact h.
  intro s. eapply rcoupling_eq. 1: exact he.
  cbn. reflexivity.
Qed.

(* Rules using commands instead of bind *)

Theorem rsame_head_cmd :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
  (m : command A) (post : postcond B B),
  (∀ a, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← cmd m ;; f₀ x ≈ x ← cmd m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m post h.
  eapply from_sem_jdg. rewrite !repr_cmd_bind.
  eapply (bind_rule_pp (repr_cmd m) (repr_cmd m)).
  - apply (reflexivity_rule (repr_cmd m)).
  - intros a₀ a₁. eapply to_sem_jdg.
    unshelve eapply rpre_weaken_rule.
    + exact (λ '(h₀, h₁), a₀ = a₁ ∧ h₀ = h₁).
    + specialize (h a₀).
      eapply rpre_hypothesis_rule. simpl. intros s₀ s₁ [ea es]. subst.
      eapply rpre_weaken_rule. 1: exact h.
      simpl. intros h₀ h₁ [? ?]. subst. reflexivity.
    + simpl. intros s₀ s₁ e. noconf e. intuition auto.
Qed.

(* A slightly more general version where we don't fix the precondition *)
Theorem rsame_head_cmd_alt :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
    (m : command A) pre (post : postcond B B),
    ⊢ ⦃ pre ⦄
      x ← cmd m ;; ret x ≈ x ← cmd m ;; ret x
    ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄ →
    (∀ a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← cmd m ;; f₀ x ≈ x ← cmd m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m pre post hm hf.
  eapply from_sem_jdg. rewrite !repr_cmd_bind.
  eapply (bind_rule_pp (repr_cmd m) (repr_cmd m)).
  - eapply to_sem_jdg in hm. rewrite !repr_cmd_bind in hm.
    rewrite bindrFree_ret in hm. eauto.
  - intros a₀ a₁. eapply to_sem_jdg.
    eapply rpre_hypothesis_rule.
    intros s₀ s₁ [h e]. subst.
    eapply rpre_weaken_rule. 1: eapply hf.
    simpl. intros ? ? [? ?]. subst. auto.
Qed.

Lemma rsame_head_alt_pre :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
    (m : raw_code A) pre (post : postcond B B),
    ⊢ ⦃ pre ⦄ m ≈ m ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄ →
    (∀ a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← m ;; f₀ x ≈ x ← m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m pre post hm hf.
  eapply r_bind.
  - eapply hm.
  - intros ? ?. eapply rpre_hypothesis_rule. intros ? ? [hpre e]. subst.
    eapply rpre_weaken_rule.
    + eapply hf.
    + simpl. intuition subst. auto.
Qed.

Lemma cmd_sample_preserve_pre :
  ∀ (op : Op) pre,
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← cmd (cmd_sample op) ;; ret x ≈ x ← cmd (cmd_sample op) ;; ret x
    ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄.
Proof.
  intros op pre. simpl.
  eapply from_sem_jdg. simpl.
  intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  destruct op as [opA opB].
  pose (d :=
    SDistr_bind (λ x, SDistr_unit _ ((x, s₀), (x, s₁)))
      (Theta_dens.unary_ThetaDens0 _ (ropr (opA ; opB) (λ x : chElement opA, retrFree x)))
  ).
  exists d. split.
  - unfold coupling. split.
    + unfold lmg. unfold dfst.
      apply distr_ext. intro. simpl.
      rewrite dlet_dlet.
      simpl.
      unfold SDistr_bind, SDistr_unit.
      rewrite dlet_dlet.
      apply dlet_f_equal. intro.
      apply distr_ext. intro.
      rewrite dlet_unit. rewrite dlet_unit. simpl. reflexivity.
    + unfold rmg. unfold dsnd.
      apply distr_ext. intro. simpl.
      rewrite dlet_dlet.
      simpl.
      unfold SDistr_bind, SDistr_unit.
      rewrite dlet_dlet.
      apply dlet_f_equal. intro.
      apply distr_ext. intro.
      rewrite dlet_unit. rewrite dlet_unit. simpl. reflexivity.
  - intros [] [] e. subst d. simpl in e.
    rewrite SDistr_rightneutral in e. simpl in e.
    unfold SDistr_bind, SDistr_unit in e.
    rewrite dletE in e.
    erewrite eq_psum in e.
    2:{
      intro. rewrite dunit1E. reflexivity.
    }
    apply psum_exists in e.
    2:{
      intro. apply mulr_ge0.
      - auto.
      - apply ler0n.
    }
    destruct e as [? e].
    apply pmulr_me in e. 2: auto.
    apply ge0_eq in e. noconf e.
    eapply hpost. intuition auto.
Qed.

Lemma cmd_get_preserve_pre :
  ∀ ℓ (pre : precond),
    get_pre_cond ℓ pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← cmd (cmd_get ℓ) ;; ret x ≈ x ← cmd (cmd_get ℓ) ;; ret x
    ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄.
Proof.
  intros ℓ pre h. simpl.
  eapply from_sem_jdg. simpl.
  intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  exists (
    SDistr_unit _ (
      (get_heap s₀ ℓ, s₀),
      (get_heap s₁ ℓ, s₁)
    )
  ).
  split.
  - apply SDistr_unit_F_choice_prod_coupling. reflexivity.
  - intros [] [] e.
    unfold SDistr_unit in e.
    rewrite dunit1E in e.
    apply ge0_eq in e. noconf e.
    eapply hpost. intuition auto.
Qed.

Lemma cmd_put_preserve_pre :
  ∀ ℓ v (pre : precond),
    put_pre_cond ℓ v pre →
    ⊢ ⦃ λ '(s₀, s₁),  pre (s₀, s₁) ⦄
      x ← cmd (cmd_put ℓ v) ;; ret x ≈ x ← cmd (cmd_put ℓ v) ;; ret x
    ⦃ λ '(a₀, s₀) '(a₁, s₁), pre (s₀, s₁) ∧ a₀ = a₁ ⦄.
Proof.
  intros ℓ v pre h. simpl.
  eapply from_sem_jdg. simpl.
  intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  eexists (SDistr_unit _ _).
  split.
  - apply SDistr_unit_F_choice_prod_coupling.
    reflexivity.
  - intros [] [] e.
    unfold SDistr_unit in e. rewrite dunit1E in e.
    apply ge0_eq in e. noconf e.
    eapply hpost. intuition auto.
Qed.

Lemma r_reflexivity_alt :
  ∀ {A : choiceType} {L} pre (c : raw_code A),
    ValidCode L [interface] c →
    (∀ ℓ, ℓ \in L → get_pre_cond ℓ pre) →
    (∀ ℓ v, ℓ \in L → put_pre_cond ℓ v pre) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      c ≈ c
    ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
Proof.
  intros A L pre c h hget hput.
  induction h.
  - apply r_ret. auto.
  - eapply fromEmpty. rewrite fset0E. eauto.
  - eapply (rsame_head_cmd_alt (cmd_get _)).
    + eapply cmd_get_preserve_pre.
      apply hget. auto.
    + eauto.
  - eapply (@rsame_head_cmd_alt _ _ (λ z, _) (λ z, _) (cmd_put _ _)).
    + eapply cmd_put_preserve_pre.
      apply hput. auto.
    + eauto.
  - eapply (rsame_head_cmd_alt (cmd_sample _)).
    + eapply cmd_sample_preserve_pre with (pre := λ '(s₀, s₁), pre (s₀, s₁)).
    + eauto.
Qed.

Lemma rsame_head_alt :
  ∀ {A B : ord_choiceType} {L}
    (m : raw_code A) (f₀ f₁ : A → raw_code B) pre (post : postcond B B),
    ValidCode L [interface] m →
    (∀ (ℓ : Location), ℓ \in L → get_pre_cond ℓ pre) →
    (∀ (ℓ : Location) v, ℓ \in L → put_pre_cond ℓ v pre) →
    (∀ a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← m ;; f₀ x ≈ x ← m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B L m f₀ f₁ pre post hm hget hput hf.
  eapply rsame_head_alt_pre. 2: auto.
  eapply rpre_weaken_rule. 1: eapply rpost_weaken_rule.
  - eapply r_reflexivity_alt. all: eauto.
  - intros [] [] []. intuition eauto.
  - simpl. auto.
Qed.

Lemma r_get_remember_lhs :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ x) (s₀, s₁) ⦄
        r₀ x ≈ r₁
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← get ℓ ;; r₀ x ≈ r₁
    ⦃ post ⦄.
Proof.
  intros A B ℓ r₀ r₁ pre post h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← (x ← get ℓ ;; ret x) ;; r₀ x ≈
      ret Datatypes.tt ;; r₁
    ⦃ post ⦄
  ).
  eapply r_bind with (mid :=
    λ '(b₀, s₀) '(b₁, s₁),
      b₀ = get_heap s₀ ℓ ∧ pre (s₀, s₁)
  ).
  - apply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    eexists (dunit (_,_)). split.
    + unfold coupling. split.
      * unfold lmg, dfst. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
      * unfold rmg, dsnd. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
    + intros [] [] e.
      rewrite dunit1E in e.
      apply ge0_eq in e. noconf e.
      eapply hpost. intuition auto.
  - intros x _.
    apply rpre_hypothesis_rule. intros s₀ s₁ [? hpre]. subst.
    eapply rpre_weaken_rule.
    + eapply h.
    + simpl. intuition subst. split. 1: auto.
      simpl. reflexivity.
Qed.

Lemma r_get_remember_rhs :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_rhs ℓ x) (s₀, s₁) ⦄
        r₀ ≈ r₁ x
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      r₀ ≈
      x ← get ℓ ;; r₁ x
    ⦃ post ⦄.
Proof.
  intros A B ℓ r₀ r₁ pre post h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      ret Datatypes.tt ;; r₀ ≈
      x ← (x ← get ℓ ;; ret x) ;; r₁ x
    ⦃ post ⦄
  ).
  eapply r_bind with (mid :=
    λ '(b₀, s₀) '(b₁, s₁),
      b₁ = get_heap s₁ ℓ ∧ pre (s₀, s₁)
  ).
  - apply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    eexists (dunit (_,_)). split.
    + unfold coupling. split.
      * unfold lmg, dfst. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
      * unfold rmg, dsnd. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
    + intros [] [] e.
      rewrite dunit1E in e.
      apply ge0_eq in e. noconf e.
      eapply hpost. intuition auto.
  - intros _ x.
    apply rpre_hypothesis_rule. intros s₀ s₁ [? hpre]. subst.
    eapply rpre_weaken_rule.
    + eapply h.
    + simpl. intuition subst. split. 1: auto.
      simpl. reflexivity.
Qed.

Lemma r_get_vs_get_remember_lhs :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    Tracks ℓ pre →
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ x) (s₀, s₁) ⦄
        r₀ x ≈ r₁ x
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← get ℓ ;; r₀ x ≈
      x ← get ℓ ;; r₁ x
    ⦃ post ⦄.
Proof.
  intros A B ℓ r₀ r₁ pre post ht h.
  eapply r_get_remember_lhs. intro x.
  eapply r_get_remember_rhs. intro y.
  eapply rpre_hypothesis_rule. intros s₀ s₁ [[hpre e1] e2].
  simpl in e1, e2.
  eapply ht in hpre as e. rewrite -e in e2. subst.
  eapply rpre_weaken_rule.
  - eapply h.
  - simpl. intuition subst. split. 1: auto.
    reflexivity.
Qed.

Lemma r_get_vs_get_remember_rhs :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    Tracks ℓ pre →
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_rhs ℓ x) (s₀, s₁) ⦄
        r₀ x ≈ r₁ x
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← get ℓ ;; r₀ x ≈
      x ← get ℓ ;; r₁ x
    ⦃ post ⦄.
Proof.
  intros A B ℓ r₀ r₁ pre post ht h.
  eapply r_get_remember_lhs. intro x.
  eapply r_get_remember_rhs. intro y.
  eapply rpre_hypothesis_rule. intros s₀ s₁ [[hpre e1] e2].
  simpl in e1, e2.
  eapply ht in hpre as e. rewrite e in e1. subst.
  eapply rpre_weaken_rule.
  - eapply h.
  - simpl. intuition subst. split. 1: auto.
    reflexivity.
Qed.

Lemma r_get_vs_get_remember :
  ∀ {A B : choiceType} ℓ r₀ r₁ (pre : precond) (post : postcond A B),
    Tracks ℓ pre →
    (∀ x,
      ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ x ⋊ rem_rhs ℓ x) (s₀, s₁) ⦄
        r₀ x ≈ r₁ x
      ⦃ post ⦄
    ) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← get ℓ ;; r₀ x ≈
      x ← get ℓ ;; r₁ x
    ⦃ post ⦄.
Proof.
  intros A B ℓ r₀ r₁ pre post ht h.
  eapply r_get_remember_lhs. intro x.
  eapply r_get_remember_rhs. intro y.
  eapply rpre_hypothesis_rule. intros s₀ s₁ [[hpre e1] e2].
  simpl in e1, e2.
  eapply ht in hpre as e. rewrite e in e1. subst.
  eapply rpre_weaken_rule.
  - eapply h.
  - simpl. intuition subst. split. 1: split.
    + auto.
    + simpl. auto.
    + reflexivity.
Qed.

Lemma r_forget_lhs :
  ∀ {A B : choiceType} c₀ c₁ (pre : precond) (post : postcond A B) ℓ v,
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs ℓ v) (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A B c₀ c₁ pre post ℓ v h.
  eapply rpre_weaken_rule.
  - eapply h.
  - simpl. intros ? ? []. auto.
Qed.

Lemma r_forget_rhs :
  ∀ {A B : choiceType} c₀ c₁ (pre : precond) (post : postcond A B) ℓ v,
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_rhs ℓ v) (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A B c₀ c₁ pre post ℓ v h.
  eapply rpre_weaken_rule.
  - eapply h.
  - simpl. intros ? ? []. auto.
Qed.

Lemma r_get_remind_lhs :
  ∀ {A B : choiceType} ℓ v r₀ r₁ (pre : precond) (post : postcond A B),
    Remembers_lhs ℓ v pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ v ≈ r₁ ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ x ← get ℓ ;; r₀ x ≈ r₁ ⦃ post ⦄.
Proof.
  intros A B ℓ v r₀ r₁ pre post hr h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      x ← (x ← get ℓ ;; ret x) ;; r₀ x ≈ ret Datatypes.tt ;; r₁
    ⦃ post ⦄
  ).
  eapply r_bind with (mid :=
    λ '(b₀, s₀) '(b₁, s₁),
      b₀ = get_heap s₀ ℓ ∧ pre (s₀, s₁)
  ).
  - apply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    eexists (dunit (_,_)). split.
    + unfold coupling. split.
      * unfold lmg, dfst. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
      * unfold rmg, dsnd. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
    + intros [] [] e.
      rewrite dunit1E in e.
      apply ge0_eq in e. noconf e.
      eapply hpost. intuition auto.
  - intros x _.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [? hpre]. subst.
    eapply hr in hpre as e. simpl in e. rewrite e.
    eapply rpre_weaken_rule.
    + eapply h.
    + simpl. intuition subst. auto.
Qed.

Lemma r_get_remind_rhs :
  ∀ {A B : choiceType} ℓ v r₀ r₁ (pre : precond) (post : postcond A B),
    Remembers_rhs ℓ v pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ ≈ r₁ v ⦃ post ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ r₀ ≈ x ← get ℓ ;; r₁ x ⦃ post ⦄.
Proof.
  intros A B ℓ v r₀ r₁ pre post hr h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      ret Datatypes.tt ;; r₀ ≈ x ← (x ← get ℓ ;; ret x) ;; r₁ x
    ⦃ post ⦄
  ).
  eapply r_bind with (mid :=
    λ '(b₀, s₀) '(b₁, s₁),
      b₁ = get_heap s₁ ℓ ∧ pre (s₀, s₁)
  ).
  - apply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    eexists (dunit (_,_)). split.
    + unfold coupling. split.
      * unfold lmg, dfst. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
      * unfold rmg, dsnd. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
    + intros [] [] e.
      rewrite dunit1E in e.
      apply ge0_eq in e. noconf e.
      eapply hpost. intuition auto.
  - intros _ x.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [? hpre]. subst.
    eapply hr in hpre as e. simpl in e. rewrite e.
    eapply rpre_weaken_rule.
    + eapply h.
    + simpl. intuition subst. auto.
Qed.

Lemma r_rem_couple_lhs :
  ∀ {A B : choiceType} ℓ ℓ' v v' R (pre : precond) c₀ c₁ (post : postcond A B),
    Couples_lhs ℓ ℓ' R pre →
    Remembers_lhs ℓ v pre →
    Remembers_lhs ℓ' v' pre →
    (R v v' → ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A B ℓ ℓ' v v' R pre c₀ c₁ post hc hl hr h.
  apply rpre_hypothesis_rule.
  intros s₀ s₁ hpre.
  eapply rpre_weaken_rule.
  - eapply h.
    specialize (hc _ hpre). specialize (hl _ _ hpre). specialize (hr _ _ hpre).
    simpl in hl, hr. subst.
    apply hc.
  - simpl. intuition subst. auto.
Qed.

Lemma r_rem_couple_rhs :
  ∀ {A B : choiceType} ℓ ℓ' v v' R (pre : precond) c₀ c₁ (post : postcond A B),
    Couples_rhs ℓ ℓ' R pre →
    Remembers_rhs ℓ v pre →
    Remembers_rhs ℓ' v' pre →
    (R v v' → ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A B ℓ ℓ' v v' R pre c₀ c₁ post hc hl hr h.
  apply rpre_hypothesis_rule.
  intros s₀ s₁ hpre.
  eapply rpre_weaken_rule.
  - eapply h.
    specialize (hc _ hpre). specialize (hl _ _ hpre). specialize (hr _ _ hpre).
    simpl in hl, hr. subst.
    apply hc.
  - simpl. intuition subst. auto.
Qed.

Lemma r_put_put :
  ∀ {A} ℓ ℓ' v v' (r₀ r₁ : raw_code A) (pre : precond),
    preserve_set_set ℓ v ℓ' v' pre →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      r₀ ≈ r₁
    ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      put ℓ := v ;; put ℓ' := v' ;; r₀ ≈
      put ℓ := v ;; put ℓ' := v' ;; r₁
    ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄.
Proof.
  intros A ℓ ℓ' v v' r₀ r₁ pre hp h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      (put ℓ := v ;; put ℓ' := v' ;; ret Datatypes.tt) ;; r₀ ≈
      (put ℓ := v ;; put ℓ' := v' ;; ret Datatypes.tt) ;; r₁
    ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ pre (s₀, s₁) ⦄
  ).
  eapply r_bind with (mid :=
    λ '(b₀, s₀) '(b₁, s₁), pre (s₀, s₁)
  ).
  - apply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    eexists (dunit (_,_)). split.
    + unfold coupling. split.
      * unfold lmg, dfst. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
      * unfold rmg, dsnd. apply distr_ext. intro.
        rewrite dlet_unit. reflexivity.
    + intros [] [] e.
      rewrite dunit1E in e.
      apply ge0_eq in e. noconf e.
      eapply hpost. apply hp. auto.
  - intros _ _. auto.
Qed.

Lemma rswap_cmd :
  ∀ (A₀ A₁ B : choiceType) (post : postcond B B)
    (c₀ : command A₀) (c₁ : command A₁)
    (r : A₀ → A₁ → raw_code B),
    (∀ b, post b b) →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
    ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r hpost hr h.
  eapply from_sem_jdg.
  repeat setoid_rewrite repr_cmd_bind.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr_cmd c₀) (repr_cmd c₁)).
  + intros a₀ a₁. eapply to_sem_jdg. eapply hr.
  + intros ? ? []. eauto.
  + intro s. unshelve eapply coupling_eq.
    * exact: (λ '(h1, h2), h1 = h2).
    * eapply to_sem_jdg in h.
      repeat (setoid_rewrite repr_cmd_bind in h).
      auto.
    * reflexivity.
Qed.

(* Specialised version to use when post = eq *)
Lemma rswap_cmd_eq :
  ∀ (A₀ A₁ B : choiceType)
    (c₀ : command A₀) (c₁ : command A₁)
    (r : A₀ → A₁ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
      ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B c₀ c₁ r h.
  eapply rswap_cmd.
  - intro. reflexivity.
  - intros a₀ a₁. eapply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - auto.
Qed.

Theorem rswap_ruleR_cmd :
  ∀ {A₀ A₁ B : ord_choiceType} {post : postcond B B}
    (c₀ : command A₀) (c₁ : command A₁) (r : A₀ → A₁ → raw_code B),
    (∀ b b', b = b' → post b b') →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
      ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r postr hr h.
  eapply from_sem_jdg.
  repeat setoid_rewrite repr_cmd_bind. simpl.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr_cmd c₀) (repr_cmd c₁)).
  - intros. eapply to_sem_jdg. apply hr.
  - apply postr.
  - intro s.
    unshelve eapply coupling_eq.
    + exact (λ '(h₀, h₁), h₀ = h₁).
    + eapply to_sem_jdg in h. repeat setoid_rewrite repr_cmd_bind in h.
      apply h.
    + reflexivity.
Qed.

Lemma rsamplerC_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← cmd c ;; r ← sample o ;; ret (a, r) ≈
      r ← sample o ;; a ← cmd c ;; ret (a, r)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rrewrite_eqDistrL.
  - eapply rreflexivity_rule.
  - intro s.
    assert (
      repr_sample_c :
        repr (r ← sample o ;; a ← cmd c ;; ret (a, r)) =
        bindrFree (spl o) (λ r, bindrFree (repr_cmd c) (λ a, retrFree (a,r)))
    ).
    { simpl. f_equal. extensionality r. rewrite repr_cmd_bind. reflexivity. }
    assert (
      repr_c_sample :
        repr (a ← cmd c ;; r ← sample o ;; ret (a, r)) =
        bindrFree (repr_cmd c) (λ a, bindrFree (spl o) (λ r, retrFree (a,r)))
    ).
    { rewrite repr_cmd_bind. reflexivity. }
    rewrite repr_c_sample repr_sample_c.
    pose proof (sample_c_is_c_sample o (repr_cmd c) s) as hlp.
    unfold sample_c in hlp. unfold c_sample in hlp.
    apply hlp.
Qed.

Lemma rsamplerC_sym'_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    a ← cmd c ;; r ← sample o ;; ret (r, a) ≈
    r ← sample o ;; a ← cmd c ;; ret (r, a)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  unshelve eapply (rswap_ruleR_cmd _ (cmd_sample _)).
  - auto.
  - intros a r. apply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - apply rsamplerC_cmd.
Qed.

Lemma rsamplerC'_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    r ← sample o ;; a ← cmd c ;; ret (r, a) ≈
    a ← cmd c ;; r ← sample o ;; ret (r, a)
  ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - apply rsamplerC_sym'_cmd.
  - intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

Theorem rdead_sampler_elimL :
  ∀ {A : ord_choiceType} {D}
    (c₀ c₁ : raw_code A) (pre : precond) (post : postcond A A),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ (x ← sample D ;; ret x) ;; c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ pre post h.
  eapply rrewrite_eqDistrL. 1: exact h.
  admit.
Admitted.

Theorem rdead_sampler_elimR :
  ∀ {A : ord_choiceType} {D}
    (c₀ c₁ : raw_code A) (pre : precond) (post : postcond A A),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ (x ← sample D ;; ret x) ;; c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ pre post h.
  eapply rrewrite_eqDistrR. 1: exact h.
  admit.
Admitted.

(* One-sided sampling rule. *)
(* Removes the need for intermediate games in some cases. *)
Lemma rconst_samplerL :
  ∀ {A : ord_choiceType} {D : Op}
    (c₀ : Arit D -> raw_code A) (c₁ : raw_code A) (post : postcond A A),
    (∀ x, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← sample D ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ post h.
  eapply r_transR with (x ← sample D ;; (λ _, c₁) x).
  - apply rdead_sampler_elimL.
    apply rreflexivity_rule.
  - apply (rsame_head_cmd (cmd_sample D)).
    apply h.
Qed.

(** Uniform distributions  *)

Definition uniform (i : nat) `{Positive i} : Op :=
  existT _ ('fin i) (Uni_W (mkpos i)).

(** Some bijections

  These are useful when working with uniform distributions that can only
  land in 'fin n.

  TODO: Move? In Prelude?

*)

Definition fto {F : finType} : F → 'I_#|F|.
Proof.
  intro x. eapply enum_rank. auto.
Defined.

Definition otf {F : finType} : 'I_#|F| → F.
Proof.
  intro x. eapply enum_val. exact x.
Defined.

Lemma fto_otf :
  ∀ {F} x, fto (F := F) (otf x) = x.
Proof.
  intros F x.
  unfold fto, otf.
  apply enum_valK.
Qed.

Lemma otf_fto :
  ∀ {F} x, otf (F := F) (fto x) = x.
Proof.
  intros F x.
  unfold fto, otf.
  apply enum_rankK.
Qed.

Lemma card_prod_iprod :
  ∀ i j,
    #|prod_finType (ordinal_finType i) (ordinal_finType j)| = (i * j)%N.
Proof.
  intros i j.
  rewrite card_prod. simpl. rewrite !card_ord. reflexivity.
Qed.

Definition ch2prod {i j} `{Positive i} `{Positive j}
  (x : Arit (uniform (i * j))) :
  prod_choiceType (Arit (uniform i)) (Arit (uniform j)).
Proof.
  simpl in *.
  eapply otf. rewrite card_prod_iprod.
  auto.
Defined.

Definition prod2ch {i j} `{Positive i} `{Positive j}
  (x : prod_choiceType (Arit (uniform i)) (Arit (uniform j))) :
  Arit (uniform (i * j)).
Proof.
  simpl in *.
  rewrite -card_prod_iprod.
  eapply fto.
  auto.
Defined.

Definition ch2prod_prod2ch :
  ∀ {i j} `{Positive i} `{Positive j} (x : prod_choiceType (Arit (uniform i)) (Arit (uniform j))),
    ch2prod (prod2ch x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite -[RHS]otf_fto. f_equal.
  rewrite rew_opp_l. reflexivity.
Qed.

Definition prod2ch_ch2prod :
  ∀ {i j} `{Positive i} `{Positive j} (x : Arit (uniform (i * j))),
    prod2ch (ch2prod x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite fto_otf.
  rewrite rew_opp_r. reflexivity.
Qed.

(** Rules on uniform distributions  *)

Lemma r_uniform_bij :
  ∀ {A₀ A₁ : ord_choiceType} i j `{Positive i} `{Positive j} pre post f
    (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
    bijective f →
    (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄
      x ← sample uniform i ;; c₀ x ≈
      x ← sample uniform j ;; c₁ x
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ i j pi pj pre post f c₀ c₁ bijf h.
  eapply from_sem_jdg.
  change (repr (sampler (uniform ?i) ?k))
  with (bindrFree (@Uniform_F (mkpos i) heap_choiceType) (λ x, repr (k x))).
  eapply bind_rule_pp.
  - eapply Uniform_bij_rule. eauto.
  - intros a₀ a₁. simpl.
    eapply to_sem_jdg.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
    move: e => /eqP e. subst.
    eapply rpre_weaken_rule. 1: eapply h.
    intros h₀ h₁. simpl. intros [? ?]. subst. auto.
Qed.

Lemma repr_Uniform :
  ∀ i `{Positive i},
    repr (x ← sample uniform i ;; ret x) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma repr_cmd_Uniform :
  ∀ i `{Positive i},
    repr_cmd (cmd_sample (uniform i)) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma ordinal_finType_inhabited :
  ∀ i `{Positive i}, ordinal_finType i.
Proof.
  intros i hi.
  exists 0%N. auto.
Qed.

Section Uniform_prod.

  Let SD_bind
      {A B : choiceType}
      (m : SDistr_carrier A)
      (k : A -> SDistr_carrier B) :=
    SDistr_bind k m.

  Let SD_ret {A : choiceType} (a : A) :=
    SDistr_unit A a.

  Arguments r _ _ : clear implicits.
  Arguments r [_] _.
  Arguments uniform_F _ _ : clear implicits.
  Arguments uniform_F [_] _.

  Lemma uniform_F_prod_bij :
    ∀ i j `{Positive i} `{Positive j} (x : 'I_i) (y : 'I_j),
      mkdistr
        (mu := λ _ : 'I_i * 'I_j, r (x, y))
        (@is_uniform _ (x,y))
      =
      SDistr_bind
        (λ z : 'I_(i * j),
          SDistr_unit _ (ch2prod z)
        )
        (mkdistr
          (mu := λ f : 'I_(i * j), r f)
          (@is_uniform _ (F_w0 (mkpos (i * j))))
        ).
  Proof.
    intros i j pi pj x y.
    apply distr_ext. simpl. intros [a b].
    unfold SDistr_bind. rewrite dletE. simpl.
    rewrite psumZ.
    2:{
      unshelve eapply @r_nonneg. eapply ordinal_finType_inhabited.
      exact _.
    }
    unfold r. rewrite card_prod. simpl.
    rewrite !card_ord.
    unfold SDistr_unit. unfold dunit. unlock. unfold drat. unlock. simpl.
    unfold mrat. simpl.
    erewrite eq_psum.
    2:{
      simpl. intro u. rewrite GRing.divr1. rewrite addn0. reflexivity.
    }
    erewrite psum_finseq with (r := [:: prod2ch (a, b)]).
    2: reflexivity.
    2:{
      simpl. intros u hu. rewrite inE in hu.
      destruct (ch2prod u == (a,b)) eqn:e.
      2:{
        exfalso.
        move: hu => /negP hu. apply hu. apply eqxx.
      }
      move: e => /eqP e. rewrite -e.
      rewrite inE. apply /eqP. symmetry. apply prod2ch_ch2prod.
    }
    rewrite bigop.big_cons bigop.big_nil.
    rewrite ch2prod_prod2ch. rewrite eqxx. simpl.
    rewrite GRing.addr0. rewrite normr1.
    rewrite GRing.mulr1. reflexivity.
  Qed.

  Lemma SDistr_bind_unit_unit :
    ∀ (A B C : ord_choiceType) (f : A → B) (g : B → C) u,
      SDistr_bind (λ y, SDistr_unit _ (g y)) (SDistr_bind (λ x, SDistr_unit _ (f x)) u) =
      SDistr_bind (λ x, SDistr_unit _ (g (f x))) u.
  Proof.
    intros A B C f g u.
    apply distr_ext. simpl. intro z.
    unfold SDistr_bind. unfold SDistr_unit.
    rewrite dlet_dlet.
    eapply eq_in_dlet. 2:{ intro. reflexivity. }
    intros x hx y.
    rewrite dlet_unit. reflexivity.
  Qed.

  Lemma UniformIprod_UniformUniform :
    ∀ (i j : nat) `{Positive i} `{Positive j},
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
        xy ← sample uniform (i * j) ;; ret (ch2prod xy) ≈
        x ← sample uniform i ;; y ← sample uniform j ;; ret (x, y)
      ⦃ eq ⦄.
  Proof.
    intros i j pi pj.
    change (
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
        xy ← cmd (cmd_sample (uniform (i * j))) ;;
        ret (ch2prod xy)
        ≈
        x ← cmd (cmd_sample (uniform i)) ;;
        y ← cmd (cmd_sample (uniform j)) ;;
        ret (x, y)
      ⦃ eq ⦄
    ).
    eapply from_sem_jdg.
    repeat setoid_rewrite repr_cmd_bind.
    change (repr_cmd (cmd_sample (uniform ?i)))
    with (@Uniform_F (mkpos i) heap_choiceType).
    cbn - [semantic_judgement Uniform_F].
    eapply rewrite_eqDistrR. 1: apply: reflexivity_rule.
    intro s. cbn.
    pose proof @prod_uniform as h.
    specialize (h [finType of 'I_i] [finType of 'I_j]). simpl in h.
    unfold Uni_W'. unfold Uni_W.
    specialize (h (F_w0 (mkpos _)) (F_w0 (mkpos _))).
    unfold uniform_F in h.
    rewrite uniform_F_prod_bij in h.
    eapply (f_equal (SDistr_bind (λ x, SDistr_unit _ (x, s)))) in h.
    simpl in h.
    rewrite SDistr_bind_unit_unit in h. simpl in h.
    unfold uniform_F. unfold F_choice_prod_obj.
    rewrite h. clear h.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.
    cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xi.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.  cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xj.
    epose (bind_ret := ord_relmon_law2 SDistr _ _ _).
    eapply equal_f in bind_ret.
    cbn in bind_ret.
    unfold SubDistr.SDistr_obligation_2 in bind_ret.
    unfold SubDistr.SDistr_obligation_1 in bind_ret.
    erewrite bind_ret. reflexivity.
  Qed.

End Uniform_prod.

Lemma r_uniform_prod :
  ∀ {A : ord_choiceType} i j `{Positive i} `{Positive j}
    (r : fin_family (mkpos i) → fin_family (mkpos j) → raw_code A),
    (∀ x y, ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ r x y ≈ r x y ⦃ eq ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      xy ← sample uniform (i * j) ;; let '(x,y) := ch2prod xy in r x y ≈
      x ← sample uniform i ;; y ← sample uniform j ;; r x y
    ⦃ eq ⦄.
Proof.
  intros A i j pi pj r h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      '(x,y) ← (z ← sample (uniform (i * j)) ;; ret (ch2prod z)) ;; r x y ≈
      '(x,y) ← (x ← sample uniform i ;; y ← sample uniform j ;; ret (x, y)) ;; r x y
    ⦃ eq ⦄
  ).
  eapply r_bind.
  - eapply UniformIprod_UniformUniform.
  - intros [? ?] [? ?].
    eapply rpre_hypothesis_rule. intros ? ? e. noconf e.
    eapply rpre_weaken_rule.
    1: eapply h.
    simpl. intros ? ? [? ?]. subst. reflexivity.
Qed.

(** Fail and Assert *)

Definition fail_unit : raw_code 'unit :=
  x ← sample ('unit ; dnull) ;; ret x.

Definition assert b : raw_code 'unit :=
  if b then ret Datatypes.tt else fail_unit.

(* fail at any type in the chUniverse *)
Definition fail {A : chUniverse} : raw_code A :=
  x ← sample (A ; dnull) ;; ret x.

(* Dependent version of assert *)
Definition assertD {A : chUniverse} b (k : b = true → raw_code A) : raw_code A :=
  (if b as b' return b = b' → raw_code A then k else λ _, fail) erefl.

Lemma valid_fail_unit :
  ∀ L I, valid_code L I fail_unit.
Proof.
  intros L I.
  unfold fail_unit. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I fail_unit) =>
  eapply valid_fail_unit
  : typeclass_instances packages.

Lemma valid_assert :
  ∀ L I b, valid_code L I (assert b).
Proof.
  intros L I b. unfold assert. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (assert ?b)) =>
  eapply valid_assert
  : typeclass_instances packages.

Lemma valid_fail :
  ∀ A L I, valid_code L I (@fail A).
Proof.
  intros A L I. unfold fail. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I fail) =>
  eapply valid_fail
  : typeclass_instances packages.

Lemma valid_assertD :
  ∀ A L I b k,
    (∀ x, valid_code L I (k x)) →
    valid_code L I (@assertD A b k).
Proof.
  intros A L I b k h.
  destruct b.
  - simpl. eapply h.
  - simpl. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (@assertD ?A ?b ?k)) =>
  eapply (valid_assertD A _ _ b k) ;
  intro ; eapply valid_code_from_class
  : typeclass_instances packages.

Notation "'#assert' b 'as' id ;; k" :=
  (assertD b (λ id, k))
  (at level 100, id name, b at next level, right associativity,
  format "#assert  b  as  id  ;;  '/' k")
  : package_scope.

Notation "'#assert' b ;; k" :=
  (assertD b (λ _, k))
  (at level 100, b at next level, right associativity,
  format "#assert  b  ;;  '/' k")
  : package_scope.

Lemma r_fail_unit :
  ∀ pre post,
    ⊢ ⦃ pre ⦄ fail_unit ≈ fail_unit ⦃ post ⦄.
Proof.
  intros pre post.
  eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  exists dnull. split.
  - unfold coupling. split.
    + unfold lmg. apply distr_ext.
      intro. unfold dfst. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
    + unfold rmg. apply distr_ext.
      intro. unfold dsnd. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
  - intros [? ?] [? ?]. rewrite dnullE.
    rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Lemma r_assert' :
  ∀ b₀ b₁,
    ⊢ ⦃ λ _, b₀ = b₁ ⦄ assert b₀ ≈ assert b₁ ⦃ λ _ _, b₀ = true ∧ b₁ = true ⦄.
Proof.
  intros b₀ b₁.
  destruct b₀, b₁. all: simpl.
  - apply r_ret. auto.
  - eapply rpre_hypothesis_rule. intros ? ? e. discriminate e.
  - eapply rpre_hypothesis_rule. intros ? ? e. discriminate e.
  - apply r_fail_unit.
Qed.

Theorem r_assert :
  ∀ b₀ b₁ (pre : precond) (post : postcond _ _),
    (∀ s, pre s → b₀ = b₁) →
    (∀ s₀ s₁, b₀ = true ∧ b₁ = true → post s₀ s₁) →
    ⊢ ⦃ pre ⦄ assert b₀ ≈ assert b₁ ⦃ post ⦄.
Proof.
  intros b₀ b₁ pre post hpre hpost.
  eapply rpre_weaken_rule. 1: eapply rpost_weaken_rule.
  1: eapply r_assert'.
  - simpl. intros [? ?] [? ?]. eapply hpost.
  - simpl. intros ? ?. eapply hpre.
Qed.

Theorem r_assertL :
  ∀ b,
    ⊢ ⦃ λ _, b = true ⦄ assert b ≈ ret Datatypes.tt ⦃ λ _ _, b = true ⦄.
Proof.
  intros b.
  destruct b.
  - simpl. apply r_ret. auto.
  - simpl. apply rpre_hypothesis_rule. discriminate.
Qed.

Theorem r_assertR :
  ∀ b,
    ⊢ ⦃ λ _, b = true ⦄ ret Datatypes.tt ≈ assert b ⦃ λ _ _, b = true ⦄.
Proof.
  intros b.
  destruct b.
  - simpl. apply r_ret. auto.
  - simpl. apply rpre_hypothesis_rule. discriminate.
Qed.

Lemma r_fail :
  ∀ A₀ A₁ pre post,
    ⊢ ⦃ pre ⦄ @fail A₀ ≈ @fail A₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post.
  eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  exists dnull. split.
  - unfold coupling. split.
    + unfold lmg. apply distr_ext.
      intro. unfold dfst. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
    + unfold rmg. apply distr_ext.
      intro. unfold dsnd. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
  - intros [? ?] [? ?]. rewrite dnullE.
    rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Theorem r_assertD :
  ∀ {A₀ A₁ : chUniverse} b₀ b₁ (pre : precond) (post : postcond A₀ A₁) k₀ k₁,
    (∀ s, pre s → b₀ = b₁) →
    (∀ e₀ e₁, ⊢ ⦃ pre ⦄ k₀ e₀ ≈ k₁ e₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ #assert b₀ as x ;; k₀ x ≈ #assert b₁ as x ;; k₁ x ⦃ post ⦄.
Proof.
  intros A₀ A₁ b₀ b₁ pre post k₀ k₁ hpre h.
  destruct b₀, b₁. all: simpl.
  - eapply h.
  - eapply rpre_hypothesis_rule. intros ? ? hh.
    eapply hpre in hh. discriminate.
  - eapply rpre_hypothesis_rule. intros ? ? hh.
    eapply hpre in hh. discriminate.
  - eapply r_fail.
Qed.

(* Simpler version for same_head *)
Lemma r_assertD_same :
  ∀ (A : chUniverse) b (pre : precond) (post : postcond A A) k₀ k₁,
    (∀ e, ⊢ ⦃ pre ⦄ k₀ e ≈ k₁ e ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ #assert b as x ;; k₀ x ≈ #assert b as x ;; k₁ x ⦃ post ⦄.
Proof.
  intros A b pre post k₀ k₁ h.
  eapply r_assertD.
  - reflexivity.
  - intros e₀ e₁. assert (e₀ = e₁) by eapply eq_irrelevance. subst.
    eapply h.
Qed.

Lemma r_cmd_fail :
  ∀ A (B : chUniverse) (c : command A) (pre : precond) (post : postcond B B),
    ⊢ ⦃ pre ⦄ fail ≈ c ;' fail ⦃ post ⦄.
Proof.
  intros A B c pre post.
  eapply r_transR.
  - unfold fail.
    eapply rswap_cmd_eq with (c₀ := cmd_sample _) (c₁ := c).
    eapply rsamplerC'_cmd with (c0 := c).
  - simpl. unfold fail.
    eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    exists dnull. split.
    + unfold coupling. split.
      * unfold lmg. apply distr_ext.
        intro. unfold dfst. rewrite dlet_null.
        unfold SDistr_bind. rewrite dlet_null.
        reflexivity.
      * unfold rmg. apply distr_ext.
        intro. unfold dsnd. rewrite dlet_null.
        unfold SDistr_bind. rewrite dlet_null.
        reflexivity.
    + intros [? ?] [? ?]. rewrite dnullE.
      rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Lemma rswap_assertD_cmd_eq :
  ∀ A (B : chUniverse) b (c : command A) (r : _ → _ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      #assert b as e ;; x ← cmd c ;; r e x ≈
      x ← cmd c ;; #assert b as e ;; r e x
    ⦃ eq ⦄.
Proof.
  intros A B b c r.
  destruct b.
  - simpl. apply rreflexivity_rule.
  - simpl. apply r_cmd_fail.
Qed.

(* Symmetric of the above. *)
Lemma rswap_cmd_assertD_eq :
  ∀ A (B : chUniverse) b (c : command A) (r : _ → _ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      x ← cmd c ;; #assert b as e ;; r e x ≈
      #assert b as e ;; x ← cmd c ;; r e x
  ⦃ eq ⦄.
Proof.
  intros A B b c r.
  eapply rsymmetry.
  eapply rpost_weaken_rule. 1: eapply rpre_weaken_rule.
  - eapply rswap_assertD_cmd_eq.
  - simpl. intuition auto.
  - intros [] []. intuition auto.
Qed.

Lemma rswap_assertD_assertD_eq :
  ∀ (A : chUniverse) b₀ b₁ (r : _ → _ → raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      #assert b₀ as e₀ ;; #assert b₁ as e₁ ;; r e₀ e₁ ≈
      #assert b₁ as e₁ ;; #assert b₀ as e₀ ;; r e₀ e₁
    ⦃ eq ⦄.
Proof.
  intros A b₀ b₁ r.
  destruct b₀.
  - simpl. apply rreflexivity_rule.
  - simpl. destruct b₁.
    + simpl. apply r_fail.
    + simpl. apply r_fail.
Qed.

(* Unfortunately, this doesn't hold syntactically *)
Lemma r_bind_assertD :
  ∀ (A B : chUniverse) b k1 (k2 : _ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      x ← (@assertD A b (λ z, k1 z)) ;; k2 x ≈
      @assertD B b (λ z, x ← k1 z ;; k2 x)
    ⦃ eq ⦄.
Proof.
  intros A B b k1 k2.
  destruct b.
  - simpl. apply rreflexivity_rule.
  - simpl. unfold fail.
    eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
    intros [hpre hpost]. simpl.
    exists dnull. split.
    + unfold coupling. split.
      * unfold lmg. apply distr_ext.
        intro. unfold dfst. rewrite dlet_null.
        unfold SDistr_bind. rewrite dlet_null.
        reflexivity.
      * unfold rmg. apply distr_ext.
        intro. unfold dsnd. rewrite dlet_null.
        unfold SDistr_bind. rewrite dlet_null.
        reflexivity.
    + intros [? ?] [? ?]. rewrite dnullE.
      rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Lemma r_bind_assertD_sym :
  ∀ (A B : chUniverse) b k1 (k2 : _ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      @assertD B b (λ z, x ← k1 z ;; k2 x) ≈
      x ← (@assertD A b (λ z, k1 z)) ;; k2 x
    ⦃ eq ⦄.
Proof.
  intros A B b k1 k2.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - eapply r_bind_assertD.
  - intros [] []. auto.
Qed.

Lemma r_get_swap :
  ∀ ℓ ℓ',
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      x ← get ℓ ;; y ← get ℓ' ;; ret (x, y) ≈
      y ← get ℓ' ;; x ← get ℓ ;; ret (x, y)
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ'.
  eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  unfold SDistr_carrier. unfold F_choice_prod_obj. simpl.
  exists (dunit (get_heap s₀ ℓ, get_heap s₀ ℓ', s₀, (get_heap s₁ ℓ, get_heap s₁ ℓ', s₁))).
  split.
  - unfold coupling. split.
    + unfold lmg. unfold dfst.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      reflexivity.
    + unfold rmg. unfold dsnd.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      reflexivity.
  - intros [[] ?] [[] ?] hh.
    eapply hpost.
    rewrite dunit1E in hh.
    lazymatch type of hh with
    | context [ ?x == ?y ] =>
      destruct (x == y) eqn:e
    end.
    2:{
      rewrite e in hh. simpl in hh.
      rewrite mc_1_10.Num.Theory.ltrr in hh. discriminate.
    }
    move: e => /eqP e. inversion e.
    subst. reflexivity.
Qed.

Lemma contract_get :
  ∀ A ℓ (r : _ → _ → raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      z ← get ℓ ;; r z z ≈
      x ← get ℓ ;; y ← get ℓ ;; r x y
    ⦃ eq ⦄.
Proof.
  intros A ℓ r.
  eapply rrewrite_eqDistrR.
  1: eapply rreflexivity_rule.
  intros s. simpl.
  reflexivity.
Qed.

Lemma contract_put :
  ∀ A ℓ v v' (r : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      put ℓ := v' ;; r ≈
      put ℓ := v ;; put ℓ := v' ;; r
    ⦃ eq ⦄.
Proof.
  intros A ℓ v v' r.
  eapply rrewrite_eqDistrR.
  1: eapply rreflexivity_rule.
  intros s. simpl.
  unfold θ_dens, θ0. simpl.
  unfold Theta_dens.unary_theta_dens_obligation_1.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  simpl.
  unfold UniversalFreeMap.outOfFree_obligation_1.
  rewrite set_heap_contract. reflexivity.
Qed.

Lemma r_put_swap :
  ∀ ℓ ℓ' v v' (A : choiceType) (u : A),
    ℓ != ℓ' →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      put ℓ := v ;; put ℓ' := v' ;; ret u ≈
      put ℓ' := v' ;; put ℓ := v ;; ret u
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ' v v' A u ne.
  eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  unfold SDistr_carrier. unfold F_choice_prod_obj. simpl.
  eexists (dunit (_, _)).
  split.
  - unfold coupling. split.
    + unfold lmg. unfold dfst.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      reflexivity.
    + unfold rmg. unfold dsnd.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      reflexivity.
  - intros [] [] hh.
    eapply hpost.
    rewrite dunit1E in hh.
    lazymatch type of hh with
    | context [ ?x == ?y ] =>
      destruct (x == y) eqn:e
    end.
    2:{
      rewrite e in hh. simpl in hh.
      rewrite mc_1_10.Num.Theory.ltrr in hh. discriminate.
    }
    move: e => /eqP e. inversion e.
    subst.
    rewrite set_heap_commut. 2: auto.
    reflexivity.
Qed.

Lemma r_get_put_swap :
  ∀ ℓ ℓ' v,
    ℓ' != ℓ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      x ← get ℓ' ;; put ℓ := v ;; ret x ≈
      put ℓ := v ;; x ← get ℓ' ;; ret x
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ' v ne.
  eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl repr.
  Opaque get_heap. simpl. Transparent get_heap.
  eexists (dunit (_, _)).
  split.
  - unfold coupling. split.
    + unfold lmg. unfold dfst.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      cbn - [get_heap].
      reflexivity.
    + unfold rmg. unfold dsnd.
      unfold SDistr_unit.
      apply distr_ext. intro.
      rewrite dlet_unit.
      cbn - [get_heap].
      reflexivity.
  - intros [] [] hh.
    eapply hpost.
    rewrite dunit1E in hh.
    lazymatch type of hh with
    | context [ ?x == ?y ] =>
      destruct (x == y) eqn:e
    end.
    2:{
      rewrite e in hh. simpl in hh.
      rewrite mc_1_10.Num.Theory.ltrr in hh. discriminate.
    }
    move: e => /eqP e. noconf e.
    subst. f_equal.
    apply get_heap_set_heap.
    auto.
Qed.

Lemma r_put_get_swap :
  ∀ ℓ ℓ' v,
    ℓ' != ℓ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      put ℓ := v ;; x ← get ℓ' ;; ret x ≈
      x ← get ℓ' ;; put ℓ := v ;; ret x
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ' v ne.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - eapply r_get_put_swap. auto.
  - intros [] []. auto.
Qed.

Lemma r_get_put_swap' :
  ∀ ℓ ℓ' v,
    ℓ' != ℓ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      x ← get ℓ' ;; put ℓ := v ;; ret (x, Datatypes.tt) ≈
      put ℓ := v ;; x ← get ℓ' ;; ret (x, Datatypes.tt)
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ' v ne.
  eapply r_get_put_swap in ne.
  eapply r_bind with (f₁ := λ x, ret (x, Datatypes.tt)) in ne .
  - exact ne.
  - simpl. intros. apply r_ret.
    intros ? ? e. inversion e. reflexivity.
Qed.

Lemma r_put_get_swap' :
  ∀ ℓ ℓ' v,
    ℓ' != ℓ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      put ℓ := v ;; x ← get ℓ' ;; ret (Datatypes.tt, x) ≈
      x ← get ℓ' ;; put ℓ := v ;; ret (Datatypes.tt, x)
    ⦃ eq ⦄.
Proof.
  intros ℓ ℓ' v ne.
  eapply r_put_get_swap in ne.
  eapply r_bind with (f₁ := λ x, ret (Datatypes.tt, x)) in ne .
  - exact ne.
  - simpl. intros. apply r_ret.
    intros ? ? e. inversion e. reflexivity.
Qed.

Lemma r_put_get :
  ∀ A ℓ v (r : _ → raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      put ℓ := v ;; r v ≈
      put ℓ := v ;; x ← get ℓ ;; r x
    ⦃ eq ⦄.
Proof.
  intros A ℓ v r.
  eapply rrewrite_eqDistrR.
  1: eapply rreflexivity_rule.
  intros s. simpl.
  unfold θ_dens, θ0. simpl.
  unfold Theta_dens.unary_theta_dens_obligation_1.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  simpl.
  unfold UniversalFreeMap.outOfFree_obligation_1.
  rewrite get_set_heap_eq. reflexivity.
Qed.