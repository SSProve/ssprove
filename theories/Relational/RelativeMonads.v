From Coq Require Import ssreflect ssrfun.
From SSProve.Mon Require Export Base.
From Coq.Classes Require Import RelationClasses Morphisms.
From SSProve.Relational Require Import Category.

Set Primitive Projections.
Set Universe Polymorphism.

(*********************************************************)
(**     Monad relative to a functor, morphisms          **)
(**     underlying functor, monads as relative monads   **)
(*********************************************************)
Section RelativeMonad.
  Context {C D : category} {J : functor C D}.


  Cumulative Record relativeMonad :=
    mkRelativeMonad
      { relmonObj :> C -> D
      ; relmon_unit : forall A, D⦅J A; relmonObj A⦆
      ; relmon_bind : forall {A B}, D⦅J A; relmonObj B⦆ -> D⦅relmonObj A; relmonObj B⦆
      ; relmon_bind_proper : forall A B,
          Proper (@sim D (J A) (relmonObj B) ==> sim D) relmon_bind
      ; relmon_law1 : forall A, relmon_bind (relmon_unit A) ∼ Id _
      ; relmon_law2 : forall A B (f : D⦅J A; relmonObj B⦆),
          relmon_bind f ∙ relmon_unit A ∼ f
      ; relmon_law3 : forall A B C (f : D⦅J B; relmonObj C⦆) (g:D⦅J A; relmonObj B⦆),
          relmon_bind (relmon_bind f ∙ g) ∼ relmon_bind f ∙ relmon_bind g
      }.
  Global Existing Instance relmon_bind_proper.
End RelativeMonad.

Arguments relativeMonad {_ _} J.

Section RelativeMonadMorphism.
  Context {C D1 D2 : category} {J1 : functor C D1} (J12 : functor D1 D2) {J2 : functor C D2}
          (phi : natIso J2 (functor_comp J1 J12)) (psi := ni_inv phi)
          (M1 : relativeMonad J1) (M2: relativeMonad J2).

  Notation η := relmon_unit.
  Notation rbind := relmon_bind.

  Cumulative Record relativeMonadMorphism :=
    mkRelMonMorph
      { rmm_map :> forall {A}, D2⦅J12 (M1 A); M2 A⦆ 
      ; rmm_law1 : forall A, rmm_map ∙ fmap J12 (η M1 A) ∼ η M2 A ∙ psi _
      ; rmm_law2 : forall A B (f : D1⦅J1 A; M1 B⦆),
          rmm_map ∙ fmap J12 (rbind M1 f) ∼
                  rbind M2 (rmm_map ∙ fmap J12 f ∙ phi _) ∙ rmm_map
      }.
End RelativeMonadMorphism.

Section RelativeMonadToFunctor.
  Context {C D:category} {J:functor C D} (M : relativeMonad J).

  Program Definition rmon_to_functor : functor C D :=
    mkFunctor M (fun A B f => relmon_bind M (relmon_unit M _ ∙ fmap J f)) _ _ _.
  Next Obligation. cbv ; intuition. rewrite H ; reflexivity. Qed.
  Next Obligation. rewrite functor_law1 cat_law2 relmon_law1 ; reflexivity. Qed.
  Next Obligation.
    rewrite functor_law2 cat_law3.
    rewrite -relmon_law3 cat_law3 relmon_law2.
    reflexivity.
  Qed.
End RelativeMonadToFunctor.

Section RmonadUnit.
  Context {I C:category} {J:functor I C}
          (M0 : relativeMonad J) (M := rmon_to_functor M0).

  Program Definition rmon_unit : natTrans J M :=
    mkNatTrans _ _ (relmon_unit M0) _.
  Next Obligation. rewrite (relmon_law2 M0) ; reflexivity. Qed.
End RmonadUnit.

Section RMonadAsMonad.
  Context {C:category} (M0 : relativeMonad (functor_id C)) (M := rmon_to_functor M0).

  Program Definition rmon_id_mult : natTrans (functor_comp M M) M :=
    mkNatTrans _ _ (fun=> relmon_bind M0 (Id _)) _.
  Next Obligation.
    rewrite -!relmon_law3 cat_law3 (relmon_law2 M0) cat_law1 cat_law2.
    reflexivity.
  Qed.

  Notation η := (@rmon_unit C C (functor_id C) _ _).
  Notation μ := (rmon_id_mult _).

  Lemma rmon_id_law1 {A} : μ ∙ (fmap M η) ∼ Id (M A).
  Proof. cbv. rewrite -relmon_law3 cat_law3 (relmon_law2 M0) cat_law1 relmon_law1. reflexivity. Qed.

  Lemma rmon_id_law2 {A} : μ ∙ η ∼ Id (M A).
  Proof. cbv. rewrite (relmon_law2 M0). reflexivity. Qed.

  Lemma rmon_id_law3 {A} : μ ∙ μ ∼ μ ∙ fmap M (rmon_id_mult A).
  Proof.
    cbv. rewrite -!relmon_law3 !cat_law3 (relmon_law2 M0) cat_law2 cat_law1.
    reflexivity.
  Qed.
End RMonadAsMonad.

(* transport a J1-relative monad into a J2-relative monad along a natural isomorphism *)
Section RelativeMonadIso.
  Context {I C} {J1 J2 : functor I C} (M : relativeMonad J1)
          (phi : natIso J1 J2).

  Program Definition rmon_transp_natIso : relativeMonad J2 :=
    mkRelativeMonad M (fun A => relmon_unit M A ∙ ni_inv phi A)
                    (fun A B f => relmon_bind M (f ∙ phi A))
                    _ _ _ _.
  Next Obligation. cbv ; intuition ; rewrite H ; reflexivity. Qed.
  Next Obligation.
    rewrite -cat_law3 ni_leftinv cat_law2 relmon_law1 ; reflexivity.
  Qed.
  Next Obligation.
    rewrite cat_law3 relmon_law2 -cat_law3 ni_rightinv cat_law2 ; reflexivity.
  Qed.
  Next Obligation.
    rewrite -cat_law3 relmon_law3 ; reflexivity.
  Qed.
  (* Surprisingly, we never use naturality... *)
End RelativeMonadIso.

(* Given functors
     J1 : I1 -> C1
     J2 : I2 -> C2,
  J1-relative monad M1 and
  J2-relative monad M2
  builds a J1×J2-relative monad I1 × I2 -> C1 × C2
 *)
Section ProductRelativeMonad.
  Context {I1 I2 C1 C2} {J1 : functor I1 C1} {J2 : functor I2 C2}
          (M1 : relativeMonad J1) (M2 : relativeMonad J2).

  Program Definition product_rmon : relativeMonad (prod_functor J1 J2) :=
    mkRelativeMonad (fun A => ⟨M1 (nfst A), M2 (nsnd A)⟩)
                    (fun A => ⟨relmon_unit M1 (nfst A), relmon_unit M2 (nsnd A)⟩)
                    (fun _ _ f => ⟨relmon_bind M1 (nfst f), relmon_bind M2 (nsnd f)⟩) _ _ _ _.
  Next Obligation.
    cbv ; intuition ; [rewrite H0 | rewrite H1] ; reflexivity.
  Qed.
  Next Obligation. intuition; rewrite relmon_law1; reflexivity. Qed.
  Next Obligation. intuition; rewrite relmon_law2; reflexivity. Qed.
  Next Obligation. intuition; rewrite relmon_law3; reflexivity. Qed.

End ProductRelativeMonad.


(*********************************************************)
(** Precomposition is functorial on relative monads     **)
(*********************************************************)
Section RelativeMonadPrecomposition.
  Context {I I'} (J : functor I I').

  Section OnObjects.
    Context {C : category} {JC : functor I' C} (J' := functor_comp J JC)
            (M : relativeMonad JC).
    
    Program Definition relativeMonad_precomposition 
      : relativeMonad J' :=
      mkRelativeMonad (fun A => M (J A))
                      (fun A => relmon_unit M (J A))
                      (fun A B f => relmon_bind M f)
                      _ _ _ _.
    Next Obligation. cbv ; intuition. rewrite H; reflexivity. Qed.
    Next Obligation. rewrite relmon_law1 ; reflexivity. Qed.
    Next Obligation. rewrite relmon_law2 ; reflexivity. Qed.
    Next Obligation. rewrite relmon_law3 ; reflexivity. Qed.
  End OnObjects.


  Local Notation "J*" := relativeMonad_precomposition.

  Section OnMorphism.
    Context {C1 C2 : category} {JC1 : functor I' C1} {JC2 : functor I' C2}.
    Context {M1 : relativeMonad JC1} {M2 : relativeMonad JC2}
            {JC12 : functor C1 C2} (phi : natIso _ _)
            (θ : relativeMonadMorphism JC12 phi M1 M2).

    Program Definition relativeMonad_precomposition_morph
      : relativeMonadMorphism JC12
                              (natIso_comp (natIso_whisker_left phi J)
                                           (functor_assoc _ _ _))
                              (J* M1) (J* M2) :=
      mkRelMonMorph _ _ _ _ (fun A => θ (J A)) _ _.
    Next Obligation. rewrite rmm_law1 cat_law2 ; reflexivity. Qed.
    Next Obligation. rewrite rmm_law2 cat_law1 ; reflexivity. Qed.
  End OnMorphism.

  (* TODO : show the functorial laws *)
End RelativeMonadPrecomposition.

(*********************************************************)
(** Postcomposition by a *full and faithful* functor is **)
(** functorial on relative monads                       **)
(*********************************************************)

Section FullyFaithfulFunctor.
  Context {C D : category} (F : functor C D).

  Record ff_struct :=
    { ff_invmap :> forall {X Y}, D⦅F X;F Y⦆ -> C⦅X;Y⦆
    ; ff_inv_proper : forall {X Y}, Proper (sim D ==> sim C) (@ff_invmap X Y)
    ; ff_section : forall {X Y} (f : D⦅F X;F Y⦆), fmap F (ff_invmap f) ∼ f
    ; ff_retraction : forall {X Y} (f : C⦅X;Y⦆), ff_invmap (fmap F f) ∼ f
    }.

  Global Existing Instance ff_inv_proper.

  Lemma invert_comp (Fff : ff_struct) {X Y Z}
    (f:D⦅F Y;F Z⦆) (g:D⦅F X;F Y⦆): Fff _ _ (f ∙ g) ∼ Fff _ _ f ∙ Fff _ _ g. 
  Proof.
    rewrite -{1}(ff_section Fff f) -{1}(ff_section Fff g) -functor_law2 ff_retraction ; reflexivity.
  Qed.
End FullyFaithfulFunctor.

Section RelativeMonadPostcomposition.
  Context {I C D} {J: functor I C} (M:relativeMonad J)
          (F : functor C D) (Fff : ff_struct F).

  Let FJ := functor_comp J F.
  Program Definition relativeMonad_postcomposition : relativeMonad FJ :=
    mkRelativeMonad (fun A => F (M A))
                    (fun A => fmap F (relmon_unit M A))
                    (fun A B f => fmap F (relmon_bind M (Fff _ _ f)))
                    _ _ _ _.
  Next Obligation. cbv ; intuition ; rewrite H; reflexivity. Qed.
  Next Obligation.
    rewrite ff_retraction relmon_law1 functor_law1 ; reflexivity.
  Qed.
  Next Obligation.
    rewrite -functor_law2 relmon_law2 ff_section ; reflexivity.
  Qed.
  Next Obligation.
    rewrite invert_comp ff_retraction relmon_law3 functor_law2 ; reflexivity.
  Qed.
End RelativeMonadPostcomposition.

(*********************************************************)
(**        Right module on a relative monad             **)
(*********************************************************)
Section RightModule.
  Context {I C D : category} {J : functor I C} {M : relativeMonad J}
          {F0 : functor C D} (F := functor_comp J F0).

  Cumulative Record rightModuleStructure :=
    mkRightModule
      { rm_bind :> forall {X Y}, C⦅J X ; M Y⦆ -> D⦅F X ; F Y⦆
      ; rm_bind_proper : forall {X Y}, Proper (sim C ==> sim D) (@rm_bind X Y)
      ; rm_law1 : forall {X}, rm_bind (relmon_unit M X) ∼ Id (F X)
      ; rm_law2 : forall {X Y Z} (f : C⦅J X ; M Y⦆) (g:C⦅J Y; M Z⦆),
          rm_bind (relmon_bind M g ∙ f) ∼ rm_bind g ∙ rm_bind f
      ; rm_law3 : forall {X X' Y} (f : C⦅J X ; J X'⦆) (g : C⦅J X'; M Y⦆),
          rm_bind (g ∙ f) ∼ rm_bind g ∙ fmap F0 f
      }.

  Global Existing Instance rm_bind_proper.
End RightModule.

Arguments rightModuleStructure {_ _ _ _} M F0.

(* When the relative monad is actually a monad
   we recover the usual notion of right module *)
Section RightModuleId.
  Context {C D : category} (J := functor_id C) {M : relativeMonad J}
          {F0 : functor C D} (F := functor_comp J F0).

  Context (rmF : rightModuleStructure M F0).

  Lemma rm_law2_id {A B} (g : C⦅A ; M B⦆) :
    rm_bind rmF (relmon_bind M g) ∼ rm_bind rmF g ∙ rm_bind rmF (Id (M A)).
  Proof. rewrite -(cat_law2 _ _ _ (relmon_bind M g)) rm_law2 ; reflexivity. Qed.

  Let FM := (functor_comp (rmon_to_functor M) F).
  Program Definition right_module_nattrans : natTrans FM F :=
    mkNatTrans FM F (fun A => rm_bind rmF (Id (M A))) _.
  Next Obligation.
    rewrite -(rm_law3 rmF) cat_law1 rm_law2_id rm_law3 rm_law1 cat_law1 ; reflexivity.
  Qed.

  Notation η := (@rmon_unit C C (functor_id C) _ _).
  Notation μ := (rmon_id_mult M).
  Notation α := (right_module_nattrans _).

  Lemma right_module_law1 {A} : α ∙ fmap F η ∼ Id (F A).
  Proof. cbv. rewrite -(rm_law3 rmF) cat_law1 rm_law1. reflexivity. Qed.

  Lemma right_module_law2 {A} : α ∙ fmap F (μ A) ∼ α ∙ α.
  Proof. cbv. rewrite -(rm_law3 rmF) cat_law1 rm_law2_id; reflexivity. Qed.

End RightModuleId.

(* Monad morphisms yield right modules, generalizing the codomain
   to a relative monads *)
Section RelativeMonadMorphismToRightModule.
  Context {C D:category} {M0 : relativeMonad (functor_id C)}
          {J:functor C D} (W0 : relativeMonad J) {phi}
          (θ : relativeMonadMorphism J phi M0 W0).

  Let W := rmon_to_functor W0.

  Program Definition rmon_morph_right_module : rightModuleStructure M0 W :=
    mkRightModule (fun _ _ f => relmon_bind W0 (θ _ ∙ fmap J f∙ phi _)) _ _ _ _.
  Next Obligation. cbv ; intuition ; rewrite H; reflexivity. Qed.
  Next Obligation.  
    rewrite (rmm_law1 _ _ _ _ θ) ; cbv .
    rewrite -cat_law3 (ni_leftinv _ _ phi) -(functor_law1 _ _ J _).
    move: (functor_law1 _ _ W X) => /= -> ; reflexivity.
  Qed.
  Next Obligation.
    rewrite functor_law2 cat_law3 (rmm_law2 _ _ _ _ θ) ; cbv.
    rewrite -!cat_law3 relmon_law3 ; reflexivity.
  Qed.
  Next Obligation.
    rewrite -relmon_law3 functor_law2 !cat_law3 relmon_law2.
    rewrite -cat_law3 -(ni_natural _ _ phi) cat_law3 ; reflexivity.
  Qed.
End RelativeMonadMorphismToRightModule.

(* Taking phi = natIso_id _ would make the following go through *)
(* Another solution is to ask that J is full and faithful *)
(* Section RelativeMonadMorphismToRightModule. *)
(*   Context {I C D:category} {J:functor I C} {M0 : relativeMonad J} *)
(*           {J':functor C D} (W0 : relativeMonad J') *)
(*           phi *)
(*           (W1 := relativeMonad_precomposition J W0) *)
(*           (θ : relativeMonadMorphism J' phi M0 W1). *)

(*   Let W := rmon_to_functor W0. *)

(*   Program Definition rmon_morph_right_module : rightModuleStructure M0 W := *)
(*     mkRightModule (fun _ _ f => relmon_bind W0 (θ _ ∙ fmap J' f∙ phi _)) _ _ _ _. *)
(*   Next Obligation. cbv ; intuition ; rewrite H; reflexivity. Qed. *)
(*   Next Obligation.   *)
(*     rewrite (rmm_law1 _ _ _ _ θ) ; cbv . *)
(*     rewrite -cat_law3 (ni_leftinv _ _ phi) -(functor_law1 _ _ J' _). *)
(*     move: (functor_law1 _ _ W (J X)) => /= -> ; reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     rewrite functor_law2 cat_law3 (rmm_law2 _ _ _ _ θ) ; cbv. *)
(*     rewrite -!cat_law3 relmon_law3 ; reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     rewrite -relmon_law3 functor_law2 !cat_law3 relmon_law2. ; reflexivity. *)
(*   Qed. *)
(* End RelativeMonadMorphismToRightModule. *)


Section RightModuleHomomorphism.
  Context {I C D : category}
          {J : functor I C} {M : relativeMonad J}
          {F G : functor C D}
          (rmF : rightModuleStructure M F) (rmG : rightModuleStructure M G)
          (σ : natTrans F G).

  (* Notation αF := (right_module_nattrans rmF _). *)
  (* Notation αG := (right_module_nattrans rmG _). *)

  Class rightModuleHomomorphism : Prop :=
    rm_homo : forall {A B} (f:C⦅J A; M B⦆),
      σ _ ∙ rm_bind rmF f ∼ rm_bind rmG f ∙ σ _.

  (* Class rightModuleHomomorphism : Prop := rm_homo : forall {A}, σ A ∙ αF ∼ αG ∙ σ _.  *)
End RightModuleHomomorphism.

Section RightModulePostcomposition.
  Context {I C D1 D2 : category}
          {J : functor I C} (M : relativeMonad J)
          (F : functor C D1) (G : functor D1 D2)
          (rmF : rightModuleStructure M F).

  Let GF := functor_comp F G. 
  Program Definition rightModule_postcomp : rightModuleStructure M GF :=
    mkRightModule (fun _ _ f => fmap G (rm_bind rmF f)) _ _ _ _.
  Next Obligation. cbv ; intuition ; rewrite H ; reflexivity. Qed.
  Next Obligation. rewrite rm_law1 functor_law1 ; reflexivity. Qed.
  Next Obligation. rewrite rm_law2 functor_law2 ; reflexivity. Qed.
  Next Obligation. rewrite rm_law3 functor_law2 ; reflexivity. Qed.
End RightModulePostcomposition.

Section FreeRightModule.
  Context {C D : category} {M : relativeMonad (functor_id C)} (J : functor C D).

  Let JM := functor_comp (rmon_to_functor M) J.
  Program Definition free_right_module : rightModuleStructure M JM :=
    mkRightModule (fun _ _ f => fmap J (relmon_bind M f)) _ _ _ _.
  Next Obligation. cbv ; intuition. rewrite H. reflexivity. Qed.
  Next Obligation. rewrite relmon_law1 functor_law1 ; reflexivity. Qed.
  Next Obligation. rewrite relmon_law3 functor_law2 ; reflexivity. Qed.
  Next Obligation.
    rewrite -functor_law2 -relmon_law3 cat_law3 (relmon_law2 M) ; reflexivity.
  Qed.

  Context {F : functor C D} (rmF : rightModuleStructure M F).

  Notation "F ▷ ν" := (natTrans_whisker_left ν F) (at level 65).
  Notation "ν ◁ F" := (natTrans_whisker_right F ν) (at level 65).
  Notation "ν ⋅ θ" := (natTrans_comp ν θ) (at level 70).

  Section PointToHomomorphism.
    Context (η : natTrans J F).

    Definition point_to_homomorphism : natTrans JM F := 
      rmon_to_functor M ▷ (η ⋅ iso_to_natTrans_inv (functor_unit_left _))
                      ⋅ right_module_nattrans rmF
                      ⋅ iso_to_natTrans (functor_unit_left _).

      (* natTrans_comp (natTrans_whisker_left η (rmon_to_functor M)) *)
      (*               (). *)

    Global Instance : rightModuleHomomorphism free_right_module rmF point_to_homomorphism.
    Proof.
      move=> ? ? ? /= ; rewrite !cat_law1 -cat_law3 nt_natural !cat_law3 -(rm_law2 rmF).
     rewrite -(rm_law3 rmF) cat_law1 cat_law2 ; reflexivity. 
   Qed.
  End PointToHomomorphism.

  Section HomomorphismToPoint.
    Context (σ : natTrans JM F) `{!rightModuleHomomorphism free_right_module rmF σ}.

    Definition homomorphism_to_point : natTrans J F :=
      natTrans_comp (iso_to_natTrans_inv (functor_unit_left _)) (natTrans_comp (natTrans_whisker_right J (rmon_unit M)) σ).

  End HomomorphismToPoint.

  Lemma point_to_homomorphism_to_point η A :
    homomorphism_to_point (point_to_homomorphism η) A ∼ η A.
  Proof.
    cbv.
    rewrite !cat_law1 cat_law2 -cat_law3 nt_natural cat_law3
    -(rm_law3 rmF) cat_law1 rm_law1 cat_law1; reflexivity. Qed.

  Lemma homo_to_point_to_homo σ
        `{H:!rightModuleHomomorphism free_right_module rmF σ} A :
    point_to_homomorphism (homomorphism_to_point σ) A ∼ σ A.
  Proof.
    cbv.
    rewrite !cat_law3 cat_law1 !cat_law2.
    move: (@rm_homo _ _ _ _ _ _ _ _ _ σ H _ _ (Id (M A)))=> /= <-.
    rewrite -!cat_law3 -functor_law2 (relmon_law2 M).
    rewrite functor_law1 cat_law2 ; reflexivity.
  Qed.
End FreeRightModule.

Arguments free_right_module {_ _} _ _. 
