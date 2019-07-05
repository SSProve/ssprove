From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.

Set Primitive Projections.
Set Universe Polymorphism.

(*********************************************************)
(**       Category (using setoids on hom-sets)          **)
(*********************************************************)

Section Category.
  Reserved Notation "f ∼ g" (at level 65).
  Reserved Notation "f ∙ g" (at level 55).

  Cumulative Record category : Type :=
    mkCategory
      { Obj :> Type
      ; Hom : Obj -> Obj -> Type
      ; sim : forall {A B}, relation (Hom A B)
      where "f ∼ g" := (sim f g)
      ; sim_equiv : forall A B, Equivalence (@sim A B)
      ; Id : forall A, Hom A A
      ; Comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C
        where "f ∙ g" := (Comp f g)
      ; Comp_proper : forall {A B C},
          Proper (@sim B C ==> @sim A B ==> @sim A C) Comp
      ; cat_law1 : forall A B (f : Hom A B), Id _ ∙ f ∼ f
      ; cat_law2 : forall A B (f : Hom A B), f ∙ Id _ ∼ f
      ; cat_law3 : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
          h ∙ (g ∙ f) ∼ (h ∙ g) ∙ f
      }.

  Global Existing Instance sim_equiv.
  Global Existing Instance Comp_proper.
End Category.

Notation "C ⦅ A ; B ⦆" := (Hom C A B) (at level 60).
Notation "f ∙ g" := (Comp _ f g) (at level 55).
Notation "f ∼ g" := (sim _ f g) (at level 65).
Arguments Id {_} _.



(*********************************************************)
(**       Functor, identity, composition                **)
(*********************************************************)

Section Functor.
  Context (C D : category).

  Cumulative Record functor : Type :=
    mkFunctor
      { fmapObj :> C -> D
      ; fmap : forall {A B}, C⦅A;B⦆ -> D⦅fmapObj A;fmapObj B⦆
      ; fmap_proper : forall A B, Proper (@sim C A B ==> @sim D _ _) fmap
      ; functor_law1 : forall A, fmap (Id A) ∼ Id _
      ; functor_law2 : forall (X Y Z: C) (g : C⦅X;Y⦆) (f:C⦅Y;Z⦆),
          fmap (f ∙ g) ∼ (fmap f) ∙ (fmap g)
      }.

  Global Existing Instance fmap_proper.
End Functor.

Arguments mkFunctor {_ _} _ _ _ _ _.
Arguments fmap {_ _} _ {_ _} _.

Section FunctorId.
  Context (C:category).

  Program Definition functor_id : functor C C :=
    mkFunctor (fun A => A) (fun _ _ f => f) _ _ _.
  Next Obligation. solve_proper. Qed.
  Next Obligation. reflexivity. Qed.
  Next Obligation. reflexivity. Qed.
End FunctorId.

Section FunctorComposition.
  Context {C D E : category} (F : functor C D) (G : functor D E).
  Program Definition functor_comp : functor C E :=
    mkFunctor (fun A => G (F A)) (fun A B f=> fmap G (fmap F f)) _ _ _.
  Next Obligation. solve_proper. Qed.
  Next Obligation. do 2 setoid_rewrite functor_law1 ; reflexivity. Qed.
  Next Obligation. do 2 setoid_rewrite functor_law2 ; reflexivity. Qed.
End FunctorComposition.
(*********************************************************)
(**           Product of two categories,                **)
(**        diagonal and projection functors,            **)
(**        product of two functors                      **)
(*********************************************************)

Section ProductCat.
  Context (C D : category).
  Program Definition prod_cat : category :=
    mkCategory (C × D)
               (fun A B => C⦅nfst A ; nfst B⦆ × D⦅nsnd A ; nsnd B⦆)
               (fun _ _ f g => nfst f ∼ nfst g /\ nsnd f ∼ nsnd g)
               _
               (fun A => ⟨Id (nfst A), Id (nsnd A)⟩)
               (fun _ _ _ f g => ⟨nfst f ∙ nfst g, nsnd f ∙ nsnd g⟩)
               _ _ _ _.
  Next Obligation.
    constructor ; cbv ; intuition ; etransitivity ; eassumption.
  Qed.
  Next Obligation.
    cbv ; intuition.
    setoid_rewrite H0; setoid_rewrite H2; reflexivity.
    setoid_rewrite H1; setoid_rewrite H3; reflexivity.
  Qed.
  Next Obligation. split ; apply cat_law1. Qed.
  Next Obligation. split ; apply cat_law2. Qed.
  Next Obligation. split ; apply cat_law3. Qed.
End ProductCat.

Section FunctorToProdCat.
  Context {I C1 C2} (F1 : functor I C1) (F2 : functor I C2).

  Program Definition functor_to_prod_cat : functor I (prod_cat C1 C2) :=
    mkFunctor (fun A => ⟨F1 A, F2 A⟩) (fun _ _ f => ⟨fmap F1 f, fmap F2 f⟩) _ _ _.
  Next Obligation. cbv ; intuition ; rewrite H ; reflexivity. Qed.
  Next Obligation. split ; apply functor_law1. Qed.
  Next Obligation. split ; apply functor_law2. Qed.
End FunctorToProdCat.

Definition diagonal_functor (C:category) :=
  functor_to_prod_cat (functor_id C) (functor_id C).

Section ProjectionsFunctors.
  Context (C D : category).

  Program Definition left_proj_functor : functor (prod_cat C D) C :=
    mkFunctor nfst (fun _ _ => nfst) _ _ _.
  Solve All Obligations with cbv ; intuition.

  Program Definition right_proj_functor : functor (prod_cat C D) D :=
    mkFunctor nsnd (fun _ _ => nsnd) _ _ _.
  Solve All Obligations with cbv ; intuition.
End ProjectionsFunctors.

Section ProductFunctor.
  Context {C1 C2 D1 D2 : category} (F1 : functor C1 D1) (F2 : functor C2 D2).

  Program Definition prod_functor
    : functor (prod_cat C1 C2) (prod_cat D1 D2) :=
    mkFunctor (fun A => ⟨F1 (nfst A), F2 (nsnd A)⟩)
              (fun _ _ f => ⟨fmap F1 (nfst f), fmap F2 (nsnd f)⟩)
              _ _ _.
  Next Obligation. cbv ; intuition ; apply fmap_proper=> //. Qed.
  Next Obligation. split ; apply functor_law1. Qed.
  Next Obligation. split ; apply functor_law2. Qed.
End ProductFunctor.

(*********************************************************)
(**   Natural transformations, id, comp, whiskering     **)
(*********************************************************)
Section NaturalTrans.
  Context {C D : category} (F G : functor C D).

  Cumulative Record natTrans :=
    mkNatTrans
      { nt_map :> forall {A}, D⦅F A;G A⦆
      ; nt_natural : forall {A B} (f : C⦅A ; B⦆),
          nt_map ∙ fmap F f ∼ fmap G f ∙ nt_map
      }.

End NaturalTrans.

Section NaturalTransformationId.
  Context {C D : category} (F : functor C D).

  Program Definition natTrans_id : natTrans F F :=
    mkNatTrans _ _ (fun=> Id _) _.
  Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed.

End NaturalTransformationId.

Section NaturalTransformationComp.
  Context {C D : category} {F G H : functor C D}
          (phi : natTrans F G) (psi : natTrans G H).

  Program Definition natTrans_comp : natTrans F H :=
    mkNatTrans _ _ (fun A => psi A ∙ phi A) _.
  Next Obligation.
    rewrite -cat_law3 nt_natural cat_law3 nt_natural !cat_law3.
    reflexivity.
  Qed.
End NaturalTransformationComp.

Section NaturalTransformationRightWhiskering.
  Context {C D E: category} {F G : functor C D} (H : functor D E)
          (phi : natTrans F G).

  Program Definition natTrans_whisker_right : natTrans (functor_comp F H) (functor_comp G H) :=
    mkNatTrans _ _ (fun A => fmap H (phi A)) _.
  Next Obligation.
    rewrite -!functor_law2 !nt_natural ; reflexivity.
  Qed.
End NaturalTransformationRightWhiskering.

Section NaturalTransformationLeftWhiskering.
  Context {C D E: category} {F G : functor D E}
          (phi : natTrans F G) (H : functor C D).

  Program Definition natTrans_whisker_left : natTrans (functor_comp H F) (functor_comp H G) :=
    mkNatTrans _ _ (fun A => phi (H A)) _.
  Next Obligation. rewrite nt_natural. reflexivity. Qed.
End NaturalTransformationLeftWhiskering.

(*********************************************************)
(**   Natural isomorphisms, id, comp, whiskering        **)
(**   unitality and associativity laws for functors     **)
(*********************************************************)
Section NaturalIso.
  Context {C D : category} (F G : functor C D).

  Cumulative Record natIso :=
    mkNatIso
      { ni_map :> forall {A}, D⦅F A;G A⦆
      ; ni_inv : forall {A}, D⦅G A;F A⦆
      ; ni_natural : forall {A B} (f : C⦅A ; B⦆),
          ni_map ∙ fmap F f ∼ fmap G f ∙ ni_map
      ; ni_rightinv : forall {A}, ni_map ∙ ni_inv ∼ Id (G A)
      ; ni_leftinv : forall {A}, ni_inv ∙ ni_map ∼ Id (F A)
      }.

  Lemma natIso_inv_natural (phi:natIso) {A B} (f : C⦅A ; B⦆) :
    ni_inv phi ∙ fmap G f ∼ fmap F f ∙ ni_inv phi.
  Proof.
    symmetry.
    match goal with
    | [|- ?f ∙ _ ∼ _] => rewrite -(cat_law1 _ _ _ f)
    end.
    rewrite -(ni_leftinv phi) -(cat_law3 _ _ _ _ _ _ _ (ni_inv phi)).
    rewrite ni_natural -!cat_law3 ni_rightinv cat_law2.
    reflexivity.
  Qed.

End NaturalIso.

Arguments ni_inv {_ _ _ _} _ _.

Section NaturalIsoSym.
  Context {C D : category} {F G : functor C D}.

  Program Definition natIso_sym (phi : natIso F G) : natIso G F :=
    mkNatIso _ _ (ni_inv phi) phi _ _ _.
  Next Obligation. apply natIso_inv_natural. Qed.
  Next Obligation. apply ni_leftinv. Qed.
  Next Obligation. apply ni_rightinv. Qed.
End NaturalIsoSym.

Section NaturalIsoToNaturalTrans.
  Context {C D : category}.

  Definition iso_to_natTrans {F G : functor C D } (phi : natIso F G)
    : natTrans F G :=
    mkNatTrans _ _ phi (@ni_natural _ _ _ _ phi).

  Definition iso_to_natTrans_inv {F G : functor C D } (phi : natIso F G)
    : natTrans G F :=
    iso_to_natTrans (natIso_sym phi).
End NaturalIsoToNaturalTrans.

Section IdToNaturalIso.
  Context {C D : category} (F: functor C D).

  Program Definition natIso_id : natIso F F :=
    mkNatIso F F (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.
End IdToNaturalIso.

Section NaturalIsoComp.
  Context {C D : category} {F G H : functor C D}
          (phi : natIso F G) (psi : natIso G H).

  Program Definition natIso_comp : natIso F H :=
    mkNatIso _ _ (fun A => psi A ∙ phi A)
             (fun A => ni_inv phi A ∙ ni_inv psi A) _ _ _.
  Next Obligation.
    rewrite -cat_law3 ni_natural cat_law3 ni_natural !cat_law3.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite cat_law3 -(cat_law3 _ _ _ _ _ _ _ (psi _)).
    rewrite ni_rightinv cat_law2 ni_rightinv ; reflexivity.
  Qed.
  Next Obligation.
    rewrite -cat_law3 (cat_law3 _ _ _ _ _ (phi _)).
   rewrite ni_leftinv cat_law1 ni_leftinv ; reflexivity.
  Qed.

End NaturalIsoComp.

Section NaturalIsoLeftWhiskering.
  Context {C D E: category} {F G : functor D E}
          (phi : natIso F G) (H : functor C D).

  Program Definition natIso_whisker_left : natIso (functor_comp H F) (functor_comp H G) :=
    mkNatIso _ _ (fun A => phi (H A)) (fun A => ni_inv phi (H A)) _ _ _.
  Next Obligation. rewrite ni_natural; reflexivity. Qed.
  Next Obligation. rewrite ni_rightinv ; reflexivity. Qed.
  Next Obligation. rewrite ni_leftinv ; reflexivity. Qed.
End NaturalIsoLeftWhiskering.

Section NaturalIsoRightWhiskering.
  Context {C D E: category} {F G : functor C D} (H : functor D E)
          (phi : natIso F G) .

  Program Definition natIso_whisker_right : natIso (functor_comp F H) (functor_comp G H) :=
    mkNatIso _ _ (fun A => fmap H (phi A)) (fun A => fmap H (ni_inv phi A)) _ _ _.
  Next Obligation. rewrite -!functor_law2 ni_natural; reflexivity. Qed.
  Next Obligation. rewrite -functor_law2 ni_rightinv functor_law1 ; reflexivity. Qed.
  Next Obligation. rewrite -functor_law2 ni_leftinv functor_law1 ; reflexivity. Qed.
End NaturalIsoRightWhiskering.

Section FunctorCompId.
  Context {C D : category} (F : functor C D).

  Program Definition functor_unit_left
    : natIso (functor_comp (functor_id _) F) F
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.

  Program Definition functor_unit_right
    : natIso (functor_comp F (functor_id _)) F
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.

End FunctorCompId.

Section FunctorCompAssoc.
  Context {C1 C2 C3 C4} (F12 : functor C1 C2) (F23 : functor C2 C3) (F34 : functor C3 C4).

  Program Definition functor_assoc
    : natIso (functor_comp F12 (functor_comp F23 F34))
             (functor_comp (functor_comp F12 F23) F34)
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.

End FunctorCompAssoc.

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
