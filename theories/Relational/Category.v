From Coq Require Import ssreflect ssrfun.
From Mon Require Export Base.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.
From Mon.sprop Require Import SPropBase.

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
