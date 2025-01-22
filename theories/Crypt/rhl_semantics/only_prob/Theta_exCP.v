Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra classical.boolp distr reals realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Mon Require Import SpecificationMonads SPropBase SPropMonadicStructures.
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Crypt Require Import ChoiceAsOrd SubDistr Couplings Axioms Casts.
From HB Require Import structures.

Import SPropNotations.
Import Num.Theory.
Import Order.POrderTheory.

Local Open Scope ring_scope.


(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.


(*
In this file we define θ: SDistr × SDistr ==> ×; Cont_Prop

   θ {A1 A2 : ChType} (c1 : A1 -> I, c2 : A2 -> I) =

         λ (π : A1 × A2 -> Prop) =

               ∃ d ~ < c1, c2 >. ∀ (a1 : A1) (a2 : A2). d(a1, a2) > 0 -> π(a1, a2)

    (
    some unverified intuition: ∃ d ~ < c1, c2 >. ∫_{¬ π} d = 0

    the expected value when sampling using d from the set of
    points that are not in the relation π is 0.

    if we imagine ¬π as describing a bad event, we are saying that
    there is a coupling such that this bad event happens with
    negligible probability
    )

 *)

Definition WProp := @MonoCont Prop _ _.

Definition WPropDiscr : ord_relativeMonad chDiscr :=
  relativeMonad_precomposition choice_incl (ordmonad_to_relmon WProp).

Definition WRelProp : ord_relativeMonad (ord_functor_comp (F_choice_prod) chDiscr) :=
  relativeMonad_precomposition F_choice_prod WPropDiscr.

Definition v0 (C1 C2 : Type) : C1 * C2 -> C1 × C2.
Proof.
  move => [c1 c2]. split; [exact c1 | exact c2].
Defined.

Definition v : forall C : (prod_cat ord_choiceType ord_choiceType),
    OrdCat ⦅ (ord_functor_comp (F_choice_prod) chDiscr) C ;
     (ord_functor_comp (prod_functor choice_incl choice_incl) Jprod) C ⦆.
Proof.
  move => [[C1 ch1] [C2 ch2]] /=.
  eexists (v0 C1 C2).
  move => [x11 x12] [x21 x22] x1_x2.
  destruct x1_x2. by constructor.
Defined.

Definition v_inv0 (C1 C2 : Type) : C1 × C2 -> C1 * C2.
Proof.
  move => [c1 c2]. split; [exact c1 | exact c2].
Defined.

Definition v_inv : forall C : (prod_cat ord_choiceType ord_choiceType),
    OrdCat ⦅ (ord_functor_comp (prod_functor choice_incl choice_incl) Jprod) C;
      (ord_functor_comp (F_choice_prod) chDiscr) C ⦆.
Proof.
  move => [[C1 ch1] [C2 ch2]] /=.
  eexists (v_inv0 C1 C2).
  move => [x11 x12] [x21 x22] x1_x2.
  by destruct x1_x2.
Defined.

Definition ϕ : natIso (ord_functor_comp (F_choice_prod) chDiscr)
                       (ord_functor_comp (prod_functor choice_incl choice_incl)
                                          Jprod).
Proof.
  exists v v_inv.
  - move =>  [[C11 ch11] [C12 ch12]] [[C21 ch21] [C22 ch22]] /= [f1 f2].
    apply: sig_eq. rewrite /=.
    apply: boolp.funext. by move => [c1 c2] /=.
  - move => [[C1 ch1] [C2 ch2]] /=.
    by apply: sig_eq.
  - move => [[C1 ch1] [C2 ch2]] /=.
    apply: sig_eq. rewrite /=.
    apply: boolp.funext. by move => [c1 c2] /=.
Defined.

Definition θ0 (A1 A2 : Type) (ch1 : Choice A1) (ch2 : Choice A2):
  (SDistr_carrier (Choice.Pack ch1)) × (SDistr_carrier (Choice.Pack ch2)) ->
  WProp (A1 * A2)%type.
Proof.
  rewrite /SDistr_carrier. move => [d1 d2].
  exists (fun π : A1 * A2 -> Prop => (exists d, (coupling d d1 d2)
                                     /\
                                    (forall (a1 : A1) (a2 : A2), (d (a1, a2)) > 0 -> π (a1, a2)))).
  move => π1 π2 leq12 [d [marg_d integral]].
  exists d. split.
  - assumption.
  - move => a1 a2 d_eq_0. apply: leq12. by apply: integral.
Defined.

Definition θ : forall A : prod_cat ord_choiceType ord_choiceType,
    OrdCat ⦅ Jprod (SDistr_squ A); WRelProp A ⦆.
Proof.
  move => [[A1 ch1] [A2 ch2]] /=.
  exists (θ0 A1 A2 ch1 ch2).
  move => [d11 d12] [d21 d22] leq12 π /=.
  inversion leq12. by subst.
Defined.

Definition kd {A1 A2 B1 B2 : Type} {chA1 : Choice A1} {chA2 : Choice A2}
                                   {chB1 : Choice B1} {chB2 : Choice B2}
              {f1 : TypeCat ⦅ nfst (prod_functor choice_incl choice_incl ⟨
                               Choice.Pack chA1, Choice.Pack chA2 ⟩);
                              nfst (SDistr_squ ⟨Choice.Pack chB1, Choice.Pack chB2 ⟩) ⦆}
              {f2 :  TypeCat ⦅ nsnd (prod_functor choice_incl choice_incl ⟨
                         Choice.Pack chA1, Choice.Pack chA2 ⟩);
                               nsnd (SDistr_squ ⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩) ⦆}
              {π : B1 * B2 -> Prop}
                 (dA : SDistr_carrier (F_choice_prod_obj ⟨ Choice.Pack chA1,
                                                                     Choice.Pack chA2 ⟩))
             (integral : forall (a1 : A1) (a2 : A2),
                         (0 < dA (a1, a2)) ->
                         exists d : SDistr_carrier (F_choice_prod_obj
                                                  ⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩),
                              (coupling d (f1 a1) (f2 a2))
                                        /\ (forall (a3 : B1) (a4 : B2), 0 < d (a3, a4) -> (π (a3, a4)))) :
  { kd : A1 * A2 -> SDistr (F_choice_prod ⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩) |
    (forall (x1 : A1 * A2), (dA x1 > 0) = true -> coupling (kd x1) (f1 (fst x1)) (f2 (snd x1)) /\ forall (a3 : B1) (a4 : B2), 0 < kd x1 (a3, a4) -> (π (a3, a4))) }.
Proof.
  apply (@schoice (A1 * A2) (SDistr (F_choice_prod ⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩))
                  (fun a b => (0 < dA _) = true -> (coupling b _ _) /\ (forall (a3 : B1) (a4 : B2), 0 < b (a3, a4) -> π (a3, a4)))).
  move => [a1 a2].
  destruct (0 < dA (a1, a2)) eqn: K.
  - move: (integral a1 a2 K) => H.
    (* apply Prop2SProp_truthMorphism_rightLeft. *)
    simpl. move: H=> [x s]. move: s=> [p π0].
    (* apply SProp2Prop_truthMorphism_rightLeft. *)
    (* rewrite PSP_retr. *)
    exists x. intro. split. assumption.
    + intros. specialize (π0 a3 a4 H0). (* apply Prop2SProp_truthMorphism_rightLeft. *)
      (* rewrite PSP_sect. *) assumption.
  - exists dnull. intro. inversion H.
Defined.

Lemma extract_positive : forall {A1 A2 B1 B2 : Type} {chA1 : Choice A1} {chA2 : Choice A2} {chB1 : Choice B1} {chB2 : Choice B2}  (dA : SDistr_carrier (F_choice_prod_obj ⟨ Choice.Pack chA1, Choice.Pack chA2 ⟩)) (FF1 : _ -> SDistr (F_choice_prod ⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩)) b1 b2, 0 < (\dlet_(i <- dA) (FF1 i)) (b1, b2) -> exists (a1 : Choice.Pack chA1) (a2 : Choice.Pack chA2), 0 < dA (a1, a2) /\ 0 < FF1 (a1, a2) (b1, b2).
Proof.
  intuition. rewrite /(\dlet_(i <- _) _) in H. unlock in H. simpl in H.
  rewrite /mlet in H.
  rewrite lt0r in H. move: H=> /andP [H1 H2].
  move: H1 => /negP H1.
  have H1prop : ~ (psum
         (fun (x : F_choice_prod_obj ⟨ Choice.Pack chA1, Choice.Pack chA2 ⟩) =>
          (dA x * FF1 x (b1, b2))) = 0).
  { move=> absrd. rewrite absrd in H1. apply H1. trivial. }
  apply neq0_psum in H1prop. destruct H1prop as [[a1 a2] bla].
  repeat unshelve esplit. exact a1. exact a2.
  - destruct dA as [dAmap dAz dAsmbl dApsum]. simpl in *. rewrite lt0r. apply /andP ; split.
    apply /negP. move=> absrd. apply bla. move: absrd=> /eqP absrd. rewrite absrd.
    rewrite GRing.mul0r //=.
    apply dAz.
  - destruct (FF1 (a1,a2)) as [FF1map FF1z FF1smbl FF1psum]. simpl in *.
    rewrite lt0r. apply /andP ; split.
    apply /negP. move=> absrd. apply bla. move: absrd=> /eqP absrd. rewrite absrd.
    rewrite GRing.mulr0 //=.
    apply FF1z.
Qed.

Lemma distr_get : forall {A : Type} {chA : Choice A} x y, 0 < SDistr_unit (Choice.Pack chA) x y -> x = y.
Proof.
  intuition. rewrite /SDistr_unit in H. rewrite dunit1E in H.
  case Hxy: (x==y).
    move: Hxy => /eqP Hxy //=.
  rewrite Hxy /= in H. rewrite (ltxx 0) in H. discriminate.
Qed.

Import OrderEnrichedRelativeMonadExamplesNotation.

Definition θ_morph : relativeLaxMonadMorphism
                                (* C  = choiceType × choiceType *)
                                (* D1 = OrdCat × OrdCat *)
                                (* D2 = OrdCat *)
                                (* J1 : C → D1, J1 = chDiscr × chDiscr *)
                                (* J2 : C → D2, J2 =  *)
                               Jprod (* J12 : D1 → D2 *)
                               ϕ (* : natIso J2 (J1; J12) *)
                               SDistr_squ (* ord_relativeMonad J1 *)
                               WRelProp (* ord_relativeMonad J2*).
Proof.
  exists θ.
  - move => [[C1 ch1] [C2 ch2]].
    simpl. rewrite /SubDistr.SDistr_obligation_1 /SDistr_unit.
    unfold "≤". rewrite /= /MonoCont_order /v_inv0 /=.
    move => [c1 c2] π π_x.
    simpl.
    exists (SDistr_unit (F_choice_prod ⟨ Choice.Pack ch1, Choice.Pack ch2 ⟩) (c1, c2)).
    split.
    + (* apply: Prop2SProp_truthMorphism_leftRight. *)
        by rewrite -coupling_vs_ret.
    + move => a1 a2 geq0.
      apply distr_get in geq0.
      by rewrite -geq0.
  - move => [[A1 chA1] [A2 chA2]] [[B1 chB1] [B2 chB2]] [f1 f2] [c1 c2] /=.
    unfold "≤". rewrite /= /MonoCont_order /v_inv0 /=.
    move => π  [dA [coupling_SProp integral]] /=.
    move: coupling_SProp => coupling_Prop.
   destruct (kd dA integral) as [FF1 FF2] eqn: FF.
    exists  (SDistr_bind (F_choice_prod(npair (Choice.Pack chA1) (Choice.Pack chA2)))
                    (F_choice_prod(npair (Choice.Pack chB1) (Choice.Pack chB2)))
                    (FF1) dA).
    split.
  - (* apply SProp2Prop_truthMorphism_rightLeft. *) (* rewrite PSP_retr. *) simpl.
    apply coupling_vs_bind; auto.
    intros x1 x2.
    apply FF2.
  - intros b1 b2 W. rewrite /SDistr_bind in W.
    assert (exists a1 a2, 0 < dA (a1, a2) /\ 0 < FF1 (a1, a2) (b1, b2)).
    apply extract_positive.
    assumption.
    simpl in W.
    destruct H as [a1 [a2 [HA HB]]].
    specialize (FF2 (a1, a2) HA) as RR.
    destruct RR.
    (* apply SProp2Prop_truthMorphism_rightLeft. *)
    apply H0.
    apply HB.
Defined.

Program Definition fromPrePost {A1 A2}
          (pre : Prop)
          (post : A1 -> A2 -> Prop)
    : WProp (A1 * A2)%type :=
    ⦑fun p =>  pre /\ forall a1 a2, post a1 a2 -> p (a1, a2)⦒.
Next Obligation.
  intros A1 A2 chA1 chA2. intros pre post.
  split; case: H0 => // HA HB.
  intros a1 a2 Hpost.
  apply H. apply HB.
  assumption.
Qed.

Definition semantic_judgement A1 A2 c1 c2 w :=
  (θ_morph ⟨A1,A2⟩) ∙1 ⟨c1,c2⟩ ≤ w.

Declare Scope semantic_scope.
Delimit Scope semantic_scope with sem.

Module SemanticNotation.

  Notation "⊨ c1 ≈ c2 [{ w }]" :=
    (semantic_judgement _ _ c1 c2 w) : semantic_scope.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ c1 c2 (fromPrePost pre post)) : semantic_scope.

End SemanticNotation.

Import SemanticNotation.
#[local] Open Scope semantic_scope.

Definition flip (r : R) : SDistr (bool).
  rewrite /SDistr_carrier.
  apply mkdistrd. intros b.
  destruct b.
  - exact r.
  - exact (1 - r).
Defined.

Lemma sample_rule : forall {A1 A2} {chA1 : Choice A1} {chA2 : Choice A2}
                      (pre : Prop) (post : A1 -> A2 -> Prop)
                      (d1 : SDistr (Choice.Pack chA1)) (d2 : SDistr (Choice.Pack chA2)) d
                      (Hd : coupling d d1 d2)
                      (Hpost : forall a1 a2, d (a1, a2) > 0 -> post a1 a2),
      ⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄.
Proof.
  intros. rewrite /semantic_judgement /θ_morph //= /θ0 //=.
  unfold "≤".  simpl.
  rewrite /MonoCont_order //=. intros pi [H1 H2].
  (* apply SProp2Prop_truthMorphism_leftRight in H1. *)
  (* rewrite PSP_retr in H1. *)
  exists d. split.
  - (* apply Prop2SProp_truthMorphism_leftRight. *)
    assumption.
  - intros a1 a2 Hdp. apply H2.
    (* apply Prop2SProp_truthMorphism_leftRight. *)
    apply Hpost.
    assumption.
Qed.


(* GENERIC MONADIC RULES *)

Theorem ret_rule  {A1 A2 : Type} {chA1 : Choice A1} {chA2 : Choice A2}
                  (a1 : A1) (a2 : A2) :

   ⊨ (ord_relmon_unit SDistr (Choice.Pack chA1) a1) ≈
     (ord_relmon_unit SDistr (Choice.Pack chA2) a2)
     [{ (ret (a1, a2)) }].
Proof.
  rewrite /semantic_judgement /θ_morph //= /θ0 //=.
  unfold "≤".  simpl.
  rewrite /MonoCont_order //=. move => π πa1a2.
  exists (SDistr_unit (F_choice_prod (npair (Choice.Pack chA1) (Choice.Pack chA2))) (a1,a2)).
  split.
  - rewrite /SubDistr.SDistr_obligation_1 /=.
    (* apply: Prop2SProp_truthMorphism_leftRight. *)
      by apply: SDistr_unit_F_choice_prod_coupling.
  - move => b1 b2 Hb1b2.
    by rewrite -(distr_get _ _ Hb1b2).
Qed.

Theorem weaken_rule  {A1 A2 : Type} {chA1 : Choice A1} {chA2 : Choice A2}
                     {d1 : SDistr (Choice.Pack chA1)}
                     {d2 : SDistr (Choice.Pack chA2)} :
  forall w w', (⊨ d1 ≈ d2 [{ w }]) -> w ≤ w' -> (⊨ d1 ≈ d2 [{ w' }] ).
Proof.
  move => w w' Hjudg Hleq.
  rewrite /semantic_judgement /θ_morph //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  move: (Hleq π H').
  by apply: Hjudg.
Qed.

(* Theorem bind_rule {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2} *)
(*                   {B1 B2 : Type} {chB1 : Choice.class_of B1} {chB2 : Choice.class_of B2} *)
(*                   {f1 : A1 -> SDistr (Choice.Pack chB1)} *)
(*                   {f2 : A2 -> SDistr (Choice.Pack chB2)} *)
(*                   (m1 : SDistr (Choice.Pack chA1)) *)
(*                   (m2 : SDistr (Choice.Pack chA2)) *)
(*                   (wm : WProp (A1 * A2)%type) *)
(*                   (judge_wm : ⊨ m1 ≈ m2 [{ wm }]) *)
(*                   (wf : (A1 * A2) -> WProp (B1 * B2)%type) *)
(*                   (a1 : A1) (a2 : A2) *)
(*                   (judge_wf : ⊨ (f1 a1) ≈ (f2 a2) [{ (wf (a1, a2)) }]) : *)
(*   ⊨ (ord_relmon_bind SDistr *)
(*                      (fun x : (Choice.Pack chA1) => f1 x) *)
(*                      m1) ≈ *)
(*     (ord_relmon_bind SDistr *)
(*                      (fun x : (Choice.Pack chA2) => f2 x) *)
(*                      m2) *)
(*     [{ bind wm wf }]. *)
(* Proof. *)
(*   rewrite /semantic_judgement /θ_morph //= /θ0 //=. *)
(*   unfold "≤". simpl. rewrite /MonoCont_order //=. *)
(*   move => π Hwm. *)
(*   rewrite /SubDistr.SDistr_obligation_2. *)
(*   Admitted. *)
