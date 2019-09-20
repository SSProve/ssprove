From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Coq.Relations Require Import Relation_Definitions.
From Coq.Classes Require Import RelationClasses Morphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import Category RelativeMonads.

Set Primitive Projections.
Set Universe Polymorphism.

(* This file introduces a notion of relative monad enriched over a cartesian closed category *)
(* This development is not used yet in the POC framework *)

Section CartesianCategory.
  Reserved Notation "A ⨰ B" (at level 65).
  Reserved Notation "⟪ f | g ⟫" (at level 50).

  Program Definition functor_const {C D : category} (X : D) : functor C D :=
    mkFunctor (fun=> X) (fun _ _ f => Id X) _ _ _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. reflexivity. Qed.
  Next Obligation. rewrite cat_law1 ; reflexivity. Qed.

  Cumulative Record cartesian_category : Type :=
    mkCartesianCategory
      { cc_cat :> category
      ; cc_one : cc_cat
      ; cc_into_one : natTrans (functor_id cc_cat) (functor_const cc_one)
      ; cc_prod : functor (prod_cat cc_cat cc_cat) cc_cat
        where "A ⨰ B" := (cc_prod ⟨A,B⟩)
      ; cc_projl : natTrans cc_prod (left_proj_functor _ _)
      ; cc_projr : natTrans cc_prod (right_proj_functor _ _)
      ; cc_prod_into : forall {X A B},
          cc_cat⦅X;A⦆ -> cc_cat⦅X;B⦆ -> cc_cat⦅X; A⨰B⦆
        where "⟪ f | g ⟫" := (cc_prod_into f g)
      ; cc_prod_into_proper : forall {X A B},
          Proper (@sim cc_cat X A ==> @sim _ X B ==> @sim _ X (A ⨰ B)) cc_prod_into
      ; cc_law1 : forall {X} (f : cc_cat⦅X;cc_one⦆), f ∼ cc_into_one X
      ; cc_law2 : forall {X A B} (f :cc_cat⦅X;A⦆) (g:cc_cat⦅X;B⦆),
          cc_projl ⟨A,B⟩ ∙ ⟪f|g⟫ ∼ f
      ; cc_law3 : forall {X A B} (f :cc_cat⦅X;A⦆) (g:cc_cat⦅X;B⦆),
          cc_projr ⟨A,B⟩ ∙ ⟪f|g⟫ ∼ g
      ; cc_law4 : forall {X A B} (h : cc_cat⦅X;A⨰B⦆), h ∼ ⟪cc_projl _∙h|cc_projr _∙ h⟫
      }.

  Global Existing Instance cc_prod_into_proper.
End CartesianCategory.

Notation "A ⨰ B" := (cc_prod _ ⟨A, B⟩) (at level 65).
Notation "⟪ f | g ⟫" := (cc_prod_into _ f g) (at level 50).

Definition projl {C : cartesian_category} {A B : C} : C⦅A⨰B;A⦆ :=
  cc_projl C ⟨A,B⟩.
Definition projr {C : cartesian_category} {A B : C} : C⦅A⨰B;B⦆ :=
  cc_projr C ⟨A,B⟩.
Definition morphism_prod {C : cartesian_category} {A1 B1 A2 B2 : C}
           (f:C⦅A1;B1⦆) (g:C⦅A2;B2⦆) : C⦅A1⨰A2;B1⨰B2⦆ :=
  ⟪f∙projl|g∙projr⟫.

Notation "f ⨰r g" := (@morphism_prod _ _ _ _ _ f g) (at level 65).
Notation "!1" := (cc_into_one _ _).

Section EnrichedCat.
  Context {C : cartesian_category}.
  Reserved Notation "⟦ X ; Y ⟧".

  Definition assoc (X Y Z: C) : C⦅X ⨰ (Y ⨰ Z); (X ⨰ Y) ⨰ Z⦆ :=
    ⟪ ⟪projl|projl ∙ projr⟫ | projr ∙ projr ⟫.

  Record enriched_cat :=
    mkEnrichedCat
    { ec_Obj :> Type
    ; ec_Hom : ec_Obj -> ec_Obj -> C
      where "⟦ X ; Y ⟧" := (ec_Hom X Y)
    ; ec_id : forall A, C⦅cc_one _;⟦A;A⟧⦆
    ; ec_comp : forall {X Y Z}, C⦅⟦Y;Z⟧⨰⟦X;Y⟧;⟦X;Z⟧⦆
    ; ec_law1 : forall {A B}, ec_comp ∙ ⟪Id _|ec_id _ ∙ !1⟫ ∼ Id ⟦A;B⟧
    ; ec_law2 : forall {A B}, ec_comp ∙ ⟪ec_id _ ∙ !1|Id _⟫ ∼ Id ⟦A;B⟧
    ; ec_law3 : forall {X Y Z W},
        ec_comp ∙ (Id _ ⨰r ec_comp) ∼
                ec_comp ∙ (ec_comp ⨰r Id _) ∙ assoc ⟦Z;W⟧ ⟦Y;Z⟧ ⟦X;Y⟧
    }.

End EnrichedCat.

Arguments enriched_cat : clear implicits.
Notation "D ⟦ X ; Y ⟧" := (ec_Hom D X Y) (at level 50).

Section EnrichedFunctor.
  Context {C:cartesian_category} {D E : enriched_cat C}.

  Cumulative Record enriched_functor : Type :=
    mkEnrichedFunctor
      { ef_mapObj :> D -> E
      ; ef_map : forall {A B}, C⦅ D⟦A;B⟧ ; E⟦ef_mapObj A;ef_mapObj B⟧ ⦆
      ; functor_law1 : forall A, ef_map ∙ ec_id D A ∼ ec_id E _
      ; functor_law2 : forall {X Y Z},
          ef_map ∙ @ec_comp _ D X Y Z ∼ ec_comp E ∙ (ef_map ⨰r ef_map)
      }.
End EnrichedFunctor.

Arguments enriched_functor {_} _ _.

Section EnrichedRelativeMonad.
  Context {C} {D E:enriched_cat C} (J : enriched_functor D E).

  Cumulative Record enrichedRelativeMonad : Type :=
    mkEnrichedRMon
      { ermonObj :> D -> E
      ; ermon_ret : forall A, C⦅cc_one _;E⟦J A; ermonObj A⟧⦆
      ; ermon_bind : forall {A B}, C⦅E⟦J A; ermonObj B⟧ ; E⟦ermonObj A; ermonObj B⟧⦆
      ; ermon_law1 : forall {A},
          ermon_bind ∙ ermon_ret A ∼ ec_id E _
      ; ermon_law2 : forall {A B},
          ec_comp E ∙ ⟪ermon_bind|ermon_ret A ∙ !1⟫ ∼ Id (E⟦J A; ermonObj B⟧)
      ; ermon_law3 : forall {A B C},
          ec_comp E ∙ (@ermon_bind B C ⨰r @ermon_bind A B) ∼
                  ermon_bind ∙ ec_comp E ∙ (ermon_bind ⨰r Id _)
      }.
End EnrichedRelativeMonad.
