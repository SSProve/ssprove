From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Lists.List.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Rel GenericRulesComplex.


Set Universe Polymorphism.

Definition M01 := Exn unit.
Definition M02 := Identity.
Definition W01 := ExnSpec unit.
Definition W02 := MonoContSProp.

Definition M1 := monad_to_relmon M01.
Definition M2 := monad_to_relmon M02.
Definition W1 := ordmonad_to_relmon W01.
Definition W2 := ordmonad_to_relmon W02.

Import SPropNotations.
Import RelNotations.

Program Definition Wrel0 (A : TypeCatSq) : OrdCat :=
  dpair _ (MonoContSProp (option (nfst A) × (nsnd A))) ⦑@omon_rel _ _⦒.
Next Obligation. apply: MonoCont_order_preorder. Qed.

Notation " X --> Y " := (X -> dfst Y) (at level 99).

Program Definition retWrel0 (A : TypeCatSq) : OrdCat⦅ Jprod A; Wrel0 A⦆ :=
  let f : (typeCat_prod A --> Wrel0 A) :=
      fun a12 => ⦑fun p => p ⟨Some (nfst a12), nsnd a12⟩⦒
  in to_discr f.
Next Obligation. cbv ; intuition. Qed.

Program Definition actWrel0 A1 A2 B1 B2 :
  OrdCat ⦅ discr A1; W1 B1 ⦆ ->
  OrdCat ⦅ discr A2; W2 B2 ⦆ ->
  OrdCat ⦅ Jprod ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ ->
  OrdCat ⦅ Wrel0 ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ :=
  fun wf1 wf2 wfrel =>
    ⦑fun wm =>
       ⦑fun p =>
          let k a12 :=
              match nfst a12 with
              | Some a1 => (wfrel∙1 ⟨a1, nsnd a12⟩)∙1 p
              | None => (wf2∙1 (nsnd a12))∙1 (fun b2 => p ⟨None, b2⟩)
              end
          in wm∙1 k⦒⦒.
Next Obligation.
  move=> ? ? H; apply: wm∙2 => -[[?|] ?] /=;
    by [apply: (wfrel∙1 _)∙2| apply: (wf2∙1 _)∙2].
Qed.
Next Obligation. cbv;intuition. Qed.

Program Definition Wrc : rsm_components W1 W2 :=
  mkRSMComponents _ _ Wrel0 retWrel0 actWrel0 _ _ _ _.
Next Obligation.
  move=> ? ? H ? ? H1 ? ? H2 w ? /=.
  apply: w∙2=> -[[?|] ?] /=; [apply: H2| apply: H1].
Qed.
Next Obligation.
  apply Ssig_eq=> /=.
  extensionality wm. apply Ssig_eq. extensionality p=> /=.
  f_equal. extensionality a; move: a => [[?|] ?] //=.
Qed.

Definition Wrel : RelationalSpecMonad := mkRSM W1 W2 Wrc.




Program Definition θ01 : MonadMorphism M01 W01 :=
  @mkMorphism M01 W01 (fun A m => ⦑fun p pexc =>
                                  match m with
                                  | retFree _ a1 => p a1
                                  | opr _ => pexc tt
                                  end⦒) _ _.
Next Obligation.
  move=> ? ? H ? ? Hexc; move: m=> [?|? ?]; [apply: H| apply: Hexc].
Qed.
Next Obligation.
  apply Ssig_eq. extensionality p. extensionality pexc=> /=.
  move: m =>[?|? ?] //=.
Qed.


Program Definition θ02 : MonadMorphism M02 W02 :=
  @mkMorphism M02 W02 (fun A m => ret m) _ _.

Definition θ1 := mmorph_to_rmmorph θ01.
Definition θ2 := mmorph_to_rmmorph θ02.

Program Definition θrc : reo_components M1 M2 Wrc θ1 θ2:=
  mkREOComponents M1 M2 Wrc θ1 θ2
                  (fun A =>
                     let f : M1 (nfst A) × M2 (nsnd A) --> Wrc A :=
                         fun m12 => ⦑fun p => match nfst m12 with
                                        | retFree _ a1 => p ⟨Some a1, nsnd m12⟩
                                        | opr _ => p ⟨None, nsnd m12⟩
                                        end⦒
                     in to_discr f) _ _.
Next Obligation. move: m12 => [[?|? ?] ?] ? ?; apply. Qed.
Next Obligation.
  apply Ssig_eq; extensionality m12; move: m12 => [[?|??]?] //=.
Qed.

Definition θ : relationalEffectObservation M1 M2 Wrel :=
  mkREO _ _ Wrel θ1 θ2 θrc.
