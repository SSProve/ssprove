(** Useful instance of packages with uniform distributions and assert

  This module provides an instance to the functor for use in the examples.
  This is a temporary measure pending the removal of functors in packages.

  This also introduces useful lemmata and rules as well as syntax for uniform
  distributions and assert.

  When the large-scale refactoring is concluded, this file should go away,
  its contents distributed, mainly in pkg_rhl.

*)

From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.
From Crypt Require Import Prelude Package RulesStateProb SubDistr
  UniformStateProb ChoiceAsOrd FreeProbProg UniformDistrLemmas Axioms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.
Set Keyed Unification.

Import Num.Theory.
Import mc_1_10.Num.Theory.

#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

(* Empty instance for probE *)
Inductive probEmpty : Type → Type :=.

Module genparam <: RulesParam.

  Definition probE : Type → Type := probEmpty.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intros T v. inversion v.
  Defined.

End genparam.

Module Rules := DerivedRulesUniform genparam.
Export Rules.

Module Package := Package_Make myparamU.
Export Package.

Import PackageNotation.
#[local] Open Scope package_scope.

(** Syntax for uniform distributions

  TODO: See if we don't want something more explicit like [uniform].

*)
Definition U (i : nat) `{Positive i} : Op :=
  existT _ ('fin i) (inl (Uni_W (mkpos i))).

Definition i_prod i j := (i * j)%N.

(** Some bijections

  These are useful when working with uniform distributions that can only
  land in 'fin n.

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

Hint Extern 2 (Positive (i_prod ?n ?m)) =>
  eapply Positive_prod : typeclass_instances.

Lemma card_prod_iprod :
  ∀ i j,
    #|prod_finType (ordinal_finType i) (ordinal_finType j)| = i_prod i j.
Proof.
  intros i j.
  rewrite card_prod. simpl. rewrite !card_ord. reflexivity.
Qed.

Definition ch2prod {i j} `{Positive i} `{Positive j}
  (x : Arit (U (i_prod i j))) :
  prod_choiceType (Arit (U i)) (Arit (U j)).
Proof.
  simpl in *.
  eapply otf. rewrite card_prod_iprod.
  auto.
Defined.

Definition prod2ch {i j} `{Positive i} `{Positive j}
  (x : prod_choiceType (Arit (U i)) (Arit (U j))) :
  Arit (U (i_prod i j)).
Proof.
  simpl in *.
  rewrite -card_prod_iprod.
  eapply fto.
  auto.
Defined.

Definition ch2prod_prod2ch :
  ∀ {i j} `{Positive i} `{Positive j} (x : prod_choiceType (Arit (U i)) (Arit (U j))),
    ch2prod (prod2ch x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite -[RHS]otf_fto. f_equal.
  rewrite rew_opp_l. reflexivity.
Qed.

Definition prod2ch_ch2prod :
  ∀ {i j} `{Positive i} `{Positive j} (x : Arit (U (i_prod i j))),
    prod2ch (ch2prod x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite fto_otf.
  rewrite rew_opp_r. reflexivity.
Qed.

(** Rules on uniform distributions *)

Lemma r_uniform_bij :
  ∀ {A₀ A₁ : ord_choiceType} i j `{Positive i} `{Positive j} pre post f
    (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
    bijective f →
    (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄
      x ← sample U i ;; c₀ x ≈
      x ← sample U j ;; c₁ x
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ i j pi pj pre post f c₀ c₁ bijf h.
  rewrite rel_jdgE.
  change (repr (sampler (U ?i) ?k))
  with (bindrFree (@Uniform_F (mkpos i) heap_choiceType) (λ x, repr (k x))).
  eapply bind_rule_pp.
  - eapply Uniform_bij_rule. eauto.
  - intros a₀ a₁. simpl.
    rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
    move: e => /eqP e. subst.
    eapply rpre_weaken_rule. 1: eapply h.
    intros h₀ h₁. simpl. intros [? ?]. subst. auto.
Qed.

Lemma repr_Uniform :
  ∀ i `{Positive i},
    repr (x ← sample U i ;; ret x) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma repr_cmd_Uniform :
  ∀ i `{Positive i},
    repr_cmd (cmd_sample (U i)) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma ordinal_finType_inhabited :
  ∀ i `{Positive i}, ordinal_finType i.
Proof.
  intros i hi.
  exists 0%N. auto.
Qed.

(* TW: Can we rename this and explain what it is?
  Can we move it?
*)
Section Mkdistrd_nonsense.

  Context {T : choiceType}.
  Context (mu0 : T → R) (Hmu : isdistr mu0).

  Let mu := mkdistr Hmu.

  Lemma mkdistrd_nonsense :
    mkdistrd mu0 = mu.
  Proof.
    apply distr_ext. move=> t /=. rewrite /mkdistrd.
    destruct (@idP (boolp.asbool (@isdistr R T mu0))).
    - cbn. reflexivity.
    - rewrite boolp.asboolE in n. contradiction.
  Qed.

End Mkdistrd_nonsense.

Section Uniform_prod.

  Let SD_bind
      {A B : choiceType}
      (m : SDistr_carrier A)
      (k : A -> SDistr_carrier B) :=
    SDistr_bind k m.

  Let SD_ret {A : choiceType} (a : A) :=
    SDistr_unit A a.

  Arguments r _ _ : clear implicits.

  Lemma uniform_F_prod_bij :
    ∀ i j `{Positive i} `{Positive j} (x : 'I_i) (y : 'I_j),
      mkdistr
        (mu := λ _ : 'I_i * 'I_j, r (prod_finType [finType of 'I_i] [finType of 'I_j]) (x, y))
        (@is_uniform _ (x,y))
      =
      SDistr_bind
        (λ z : 'I_(i_prod i j),
          SDistr_unit _ (ch2prod z)
        )
        (mkdistr
          (mu := λ f : 'I_(i_prod i j), r (ordinal_finType (i_prod i j)) f)
          (@is_uniform _ (ordinal_finType_inhabited (i_prod i j)))
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
    rewrite !card_ord. unfold i_prod.
    unfold SDistr_unit. unfold dunit. unlock. unfold drat. unlock. simpl.
    unfold mrat. simpl.
    erewrite eq_psum.
    2:{
      simpl. intro u. rewrite divr1. rewrite addn0. reflexivity.
    }
    erewrite psum_finseq with (r := [:: prod2ch (a, b)]).
    2: reflexivity.
    2:{
      simpl. intros u hu. rewrite inE in hu.
      destruct (ch2prod u == (a,b)) eqn:e.
      2:{
        exfalso.
        rewrite e in hu. cbn in hu.
        move: hu => /negP hu. apply hu. apply eqxx.
      }
      move: e => /eqP e. rewrite -e.
      rewrite inE. apply /eqP. symmetry. apply prod2ch_ch2prod.
    }
    rewrite big_cons big_nil.
    rewrite ch2prod_prod2ch. rewrite eqxx. simpl.
    rewrite addr0. rewrite normr1.
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
        xy ← sample U (i_prod i j) ;; ret (ch2prod xy) ≈
        x ← sample U i ;; y ← sample U j ;; ret (x, y)
      ⦃ eq ⦄.
  Proof.
    intros i j pi pj.
    change (
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
        xy ← cmd (cmd_sample (U (i_prod i j))) ;;
        ret (ch2prod xy)
        ≈
        x ← cmd (cmd_sample (U i)) ;;
        y ← cmd (cmd_sample (U j)) ;;
        ret (x, y)
      ⦃ eq ⦄
    ).
    rewrite rel_jdgE.
    repeat setoid_rewrite repr_cmd_bind.
    change (repr_cmd (cmd_sample (U ?i)))
    with (@Uniform_F (mkpos i) heap_choiceType).
    cbn - [semantic_judgement Uniform_F i_prod].
    eapply rewrite_eqDistrR.
    1:{ apply: reflexivity_rule. }
    intro s. cbn - [i_prod].
    unshelve erewrite !mkdistrd_nonsense.
    1-3: unshelve eapply @is_uniform.
    1-3: apply ordinal_finType_inhabited.
    1-3: exact _.
    pose proof @prod_uniform as h.
    specialize (h [finType of 'I_i] [finType of 'I_j]). simpl in h.
    unfold uniform_F in h.
    specialize (h (ordinal_finType_inhabited _) (ordinal_finType_inhabited _)).
    rewrite uniform_F_prod_bij in h. simpl in h.
    eapply (f_equal (SDistr_bind (λ x, SDistr_unit _ (x, s)))) in h.
    simpl in h.
    rewrite SDistr_bind_unit_unit in h.
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
      xy ← sample U (i_prod i j) ;; let '(x,y) := ch2prod xy in r x y ≈
      x ← sample U i ;; y ← sample U j ;; r x y
    ⦃ eq ⦄.
Proof.
  intros A i j pi pj r h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      '(x,y) ← (z ← sample (U (i_prod i j)) ;; ret (ch2prod z)) ;; r x y ≈
      '(x,y) ← (x ← sample U i ;; y ← sample U j ;; ret (x, y)) ;; r x y
    ⦃ eq ⦄
  ).
  rewrite rel_jdgE.
  eapply rbind_rule.
  - rewrite -rel_jdgE. eapply UniformIprod_UniformUniform.
  - intros [? ?] [? ?]. rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros ? ? e. noconf e.
    eapply rpre_weaken_rule.
    1: eapply h.
    simpl. intros ? ? [? ?]. subst. reflexivity.
Qed.

(** assert

  Defined from the null sub-distribution.

*)

(* TODO Maybe a command instead? *)
Definition failr : raw_code unit_choiceType :=
  x ← sample ('unit ; inl Fail_Unit) ;; ret x.

Definition assert b : raw_code 'unit :=
  if b then ret Datatypes.tt else failr.