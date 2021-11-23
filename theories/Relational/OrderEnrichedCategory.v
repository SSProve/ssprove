From Coq Require Import ssreflect ssrfun.
From Mon Require Export Base.
From Mon Require Import SPropBase.
From Coq Require Import RelationClasses Morphisms Relation_Definitions.


Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(*********************************************************)
(**       Order-enriched Category                       **)
(*********************************************************)

Section Category.
  Reserved Notation "f ⪷ g" (at level 65).
  Reserved Notation "f ∙ g" (at level 55).

  Cumulative Record ord_category : Type :=
    mkOrdCategory
      { Obj :> Type
      ; Hom : Obj -> Obj -> Type
      ; ord_cat_le : forall {A B}, relation (Hom A B)
      where "f ⪷ g" := (ord_cat_le f g)
      ; ord_cat_le_preorder : forall A B, PreOrder (@ord_cat_le A B)
      ; Id : forall A, Hom A A
      ; Comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C
        where "f ∙ g" := (Comp f g)
      ; Comp_proper : forall {A B C},
          Proper (@ord_cat_le B C ==> @ord_cat_le A B ==> @ord_cat_le A C) Comp
      ; ord_cat_law1 : forall A B (f : Hom A B), Id _ ∙ f = f
      ; ord_cat_law2 : forall A B (f : Hom A B), f ∙ Id _ = f
      ; ord_cat_law3 : forall A B C D (f : Hom A B) (g : Hom B C) (h : Hom C D),
          h ∙ (g ∙ f) = (h ∙ g) ∙ f
      }.

  Global Existing Instance ord_cat_le_preorder.
  Global Existing Instance Comp_proper.
End Category.

Notation "C ⦅ A ; B ⦆" := (Hom C A B) (at level 60).
Notation "f ∙ g" := (Comp _ f g) (at level 55).
Notation "f ⪷ g" := (ord_cat_le _ f g) (at level 65).
Arguments Id {_} _.



(*********************************************************)
(**       Functor, identity, composition                **)
(*********************************************************)

Section Functor.
  Context (C D : ord_category).

  Cumulative Record ord_functor : Type :=
    mkOrdFunctor
      { ofmapObj :> C -> D
      ; ofmap : forall {A B}, C⦅A;B⦆ -> D⦅ofmapObj A;ofmapObj B⦆
      ; ofmap_proper : forall A B, Proper (@ord_cat_le C A B ==> @ord_cat_le D _ _) ofmap
      ; ord_functor_law1 : forall A, ofmap (Id A) = Id _
      ; ord_functor_law2 : forall (X Y Z: C) (g : C⦅X;Y⦆) (f:C⦅Y;Z⦆),
          ofmap (f ∙ g) = (ofmap f) ∙ (ofmap g)
      }.

  Global Existing Instance ofmap_proper.
End Functor.

Arguments mkOrdFunctor {_ _} _ _ _ _ _.
Arguments ofmap {_ _} _ {_ _} _.

Section FunctorId.
  Context (C:ord_category).

  Program Definition ord_functor_id : ord_functor C C :=
    mkOrdFunctor (fun A => A) (fun _ _ f => f) _ _ _.
  Next Obligation. cbv ; intuition. Qed.
End FunctorId.

Section FunctorComposition.
  Context {C D E : ord_category} (F : ord_functor C D) (G : ord_functor D E).
  Program Definition ord_functor_comp : ord_functor C E :=
    mkOrdFunctor (fun A => G (F A)) (fun A B f=> ofmap G (ofmap F f)) _ _ _.
  Next Obligation. cbv ; intuition; do 2 apply: ofmap_proper=> //. Qed.
  Next Obligation. do 2 rewrite ord_functor_law1=> //. Qed.
  Next Obligation. do 2 rewrite ord_functor_law2=> //. Qed.
End FunctorComposition.


(*********************************************************)
(**           Product of two categories,                **)
(**        diagonal and projection functors,            **)
(**        product of two functors                      **)
(*********************************************************)

Section ProductCat.
  Context (C D : ord_category).

  Import SPropNotations.
  Program Definition prod_cat : ord_category :=
    mkOrdCategory (C × D)
                  (fun A B => C⦅nfst A ; nfst B⦆ × D⦅nsnd A ; nsnd B⦆)
                  (fun _ _ f g => nfst f ⪷ nfst g /\ nsnd f ⪷ nsnd g)
                  _
                  (fun A => ⟨Id (nfst A), Id (nsnd A)⟩)
                  (fun _ _ _ f g => ⟨nfst f ∙ nfst g, nsnd f ∙ nsnd g⟩)
                  _ _ _ _.
  Next Obligation.
    constructor ; cbv ; intuition ; etransitivity ; eassumption.
  Qed.
  Next Obligation.
    cbv ; intuition; apply Comp_proper=> //.
  Qed.
  Next Obligation. rewrite 2!ord_cat_law1 //. Qed.
  Next Obligation. rewrite 2!ord_cat_law2 //. Qed.
  Next Obligation. rewrite 2!ord_cat_law3 //. Qed.
End ProductCat.

Section FunctorToProdCat.
  Context {I C1 C2} (F1 : ord_functor I C1) (F2 : ord_functor I C2).

  Program Definition functor_to_prod_cat : ord_functor I (prod_cat C1 C2) :=
    mkOrdFunctor (fun A => ⟨F1 A, F2 A⟩) (fun _ _ f => ⟨ofmap F1 f, ofmap F2 f⟩) _ _ _.
  Next Obligation. cbv ; intuition; apply ofmap_proper=> //. Qed.
  Next Obligation. rewrite 2!ord_functor_law1 //. Qed.
  Next Obligation. rewrite 2!ord_functor_law2 //. Qed.
End FunctorToProdCat.

Definition diagonal_functor (C:ord_category) :=
  functor_to_prod_cat (ord_functor_id C) (ord_functor_id C).

Section ProjectionsFunctors.
  Context (C D : ord_category).

  Program Definition left_proj_functor : ord_functor (prod_cat C D) C :=
    mkOrdFunctor nfst (fun _ _ => nfst) _ _ _.
  Solve All Obligations with cbv ; intuition.

  Program Definition right_proj_functor : ord_functor (prod_cat C D) D :=
    mkOrdFunctor nsnd (fun _ _ => nsnd) _ _ _.
  Solve All Obligations with cbv ; intuition.
End ProjectionsFunctors.

Section ProductFunctor.
  Context {C1 C2 D1 D2 : ord_category} (F1 : ord_functor C1 D1) (F2 : ord_functor C2 D2).

  Program Definition prod_functor
    : ord_functor (prod_cat C1 C2) (prod_cat D1 D2) :=
    mkOrdFunctor (fun A => ⟨F1 (nfst A), F2 (nsnd A)⟩)
                 (fun _ _ f => ⟨ofmap F1 (nfst f), ofmap F2 (nsnd f)⟩)
                 _ _ _.
  Next Obligation. cbv ; intuition ; apply ofmap_proper=> //. Qed.
  Next Obligation. rewrite 2!ord_functor_law1 //. Qed.
  Next Obligation. rewrite 2!ord_functor_law2 //. Qed.
End ProductFunctor.

(** Should I implement lax natural transformations ? *)
(* (*********************************************************) *)
(* (**   Natural transformations, id, comp, whiskering     **) *)
(* (*********************************************************) *)
(* Section NaturalTrans. *)
(*   Context {C D : ord_category} (F G : ord_functor C D). *)

(*   Cumulative Record natTrans := *)
(*     mkNatTrans *)
(*       { nt_map :> forall {A}, D⦅F A;G A⦆ *)
(*       ; nt_natural : forall {A B} (f : C⦅A ; B⦆), *)
(*           nt_map ∙ fmap F f ∼ fmap G f ∙ nt_map *)
(*       }. *)

(* End NaturalTrans. *)

(* Section NaturalTransformationId. *)
(*   Context {C D : category} (F : functor C D). *)

(*   Program Definition natTrans_id : natTrans F F := *)
(*     mkNatTrans _ _ (fun=> Id _) _. *)
(*   Next Obligation. rewrite cat_law1 cat_law2 ; reflexivity. Qed. *)

(* End NaturalTransformationId. *)

(* Section NaturalTransformationComp. *)
(*   Context {C D : category} {F G H : functor C D} *)
(*           (phi : natTrans F G) (psi : natTrans G H). *)

(*   Program Definition natTrans_comp : natTrans F H := *)
(*     mkNatTrans _ _ (fun A => psi A ∙ phi A) _. *)
(*   Next Obligation. *)
(*     rewrite -cat_law3 nt_natural cat_law3 nt_natural !cat_law3. *)
(*     reflexivity. *)
(*   Qed. *)
(* End NaturalTransformationComp. *)

(* Section NaturalTransformationRightWhiskering. *)
(*   Context {C D E: category} {F G : functor C D} (H : functor D E) *)
(*           (phi : natTrans F G). *)

(*   Program Definition natTrans_whisker_right : natTrans (functor_comp F H) (functor_comp G H) := *)
(*     mkNatTrans _ _ (fun A => fmap H (phi A)) _. *)
(*   Next Obligation. *)
(*     rewrite -!functor_law2 !nt_natural ; reflexivity. *)
(*   Qed. *)
(* End NaturalTransformationRightWhiskering. *)

(* Section NaturalTransformationLeftWhiskering. *)
(*   Context {C D E: category} {F G : functor D E}  *)
(*           (phi : natTrans F G) (H : functor C D). *)

(*   Program Definition natTrans_whisker_left : natTrans (functor_comp H F) (functor_comp H G) := *)
(*     mkNatTrans _ _ (fun A => phi (H A)) _. *)
(*   Next Obligation. rewrite nt_natural. reflexivity. Qed. *)
(* End NaturalTransformationLeftWhiskering. *)

(*********************************************************)
(**   Natural isomorphisms, id, comp, whiskering        **)
(**   unitality and associativity laws for functors     **)
(*********************************************************)
Section NaturalIso.
  Context {C D : ord_category} (F G : ord_functor C D).

  Cumulative Record natIso :=
    mkNatIso
      { ni_map :> forall {A}, D⦅F A;G A⦆
      ; ni_inv : forall {A}, D⦅G A;F A⦆
      ; ni_natural : forall {A B} (f : C⦅A ; B⦆),
          ni_map ∙ ofmap F f = ofmap G f ∙ ni_map
      ; ni_rightinv : forall {A}, ni_map ∙ ni_inv = Id (G A)
      ; ni_leftinv : forall {A}, ni_inv ∙ ni_map = Id (F A)
      }.

  Lemma natIso_inv_natural (phi:natIso) {A B} (f : C⦅A ; B⦆) :
    ni_inv phi ∙ ofmap G f = ofmap F f ∙ ni_inv phi.
  Proof.
    rewrite -[in RHS](ord_cat_law1 _ _ _ (ofmap _ _))
      -(ni_leftinv phi) -(ord_cat_law3 _ _ _ _ _ _ _ (ni_inv phi))
      ni_natural -!ord_cat_law3 ni_rightinv ord_cat_law2 //.
  Qed.

End NaturalIso.

Arguments ni_inv {_ _ _ _} _ _.

Section NaturalIsoSym.
  Context {C D : ord_category} {F G : ord_functor C D}.

  Program Definition natIso_sym (phi : natIso F G) : natIso G F :=
    mkNatIso _ _ (ni_inv phi) phi _ _ _.
  Next Obligation. apply natIso_inv_natural. Qed.
  Next Obligation. apply ni_leftinv. Qed.
  Next Obligation. apply ni_rightinv. Qed.
End NaturalIsoSym.

(* Section NaturalIsoToNaturalTrans. *)
(*   Context {C D : category}. *)

(*   Definition iso_to_natTrans {F G : functor C D } (phi : natIso F G) *)
(*     : natTrans F G := *)
(*     mkNatTrans _ _ phi (@ni_natural _ _ _ _ phi). *)

(*   Definition iso_to_natTrans_inv {F G : functor C D } (phi : natIso F G) *)
(*     : natTrans G F := *)
(*     iso_to_natTrans (natIso_sym phi). *)
(* End NaturalIsoToNaturalTrans. *)

Section IdToNaturalIso.
  Context {C D : ord_category} (F: ord_functor C D).

  Program Definition natIso_id : natIso F F :=
    mkNatIso F F (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite ord_cat_law1 ord_cat_law2 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.
End IdToNaturalIso.

Section NaturalIsoComp.
  Context {C D : ord_category} {F G H : ord_functor C D}
          (phi : natIso F G) (psi : natIso G H).

  Program Definition natIso_comp : natIso F H :=
    mkNatIso _ _ (fun A => psi A ∙ phi A)
             (fun A => ni_inv phi A ∙ ni_inv psi A) _ _ _.
  Next Obligation.
    rewrite -ord_cat_law3 ni_natural ord_cat_law3 ni_natural !ord_cat_law3 //.
  Qed.
  Next Obligation.
    rewrite ord_cat_law3 -(ord_cat_law3 _ _ _ _ _ _ _ (psi _)).
    rewrite ni_rightinv ord_cat_law2 ni_rightinv //.
  Qed.
  Next Obligation.
    rewrite -ord_cat_law3 (ord_cat_law3 _ _ _ _ _ (phi _)).
    rewrite ni_leftinv ord_cat_law1 ni_leftinv //.
  Qed.

End NaturalIsoComp.

Section NaturalIsoLeftWhiskering.
  Context {C D E: ord_category} {F G : ord_functor D E}
          (phi : natIso F G) (H : ord_functor C D).

  Program Definition natIso_whisker_left : natIso (ord_functor_comp H F) (ord_functor_comp H G) :=
    mkNatIso _ _ (fun A => phi (H A)) (fun A => ni_inv phi (H A)) _ _ _.
  Next Obligation. rewrite ni_natural; reflexivity. Qed.
  Next Obligation. rewrite ni_rightinv ; reflexivity. Qed.
  Next Obligation. rewrite ni_leftinv ; reflexivity. Qed.
End NaturalIsoLeftWhiskering.

Section NaturalIsoRightWhiskering.
  Context {C D E: ord_category} {F G : ord_functor C D} (H : ord_functor D E)
          (phi : natIso F G).

  Program Definition natIso_whisker_right : natIso (ord_functor_comp F H) (ord_functor_comp G H) :=
    mkNatIso _ _ (fun A => ofmap H (phi A)) (fun A => ofmap H (ni_inv phi A)) _ _ _.
  Next Obligation. rewrite -!ord_functor_law2 ni_natural //. Qed.
  Next Obligation. rewrite -ord_functor_law2 ni_rightinv ord_functor_law1 //. Qed.
  Next Obligation. rewrite -ord_functor_law2 ni_leftinv ord_functor_law1 //. Qed.
End NaturalIsoRightWhiskering.

Section FunctorCompId.
  Context {C D : ord_category} (F : ord_functor C D).

  Program Definition ord_functor_unit_left
    : natIso (ord_functor_comp (ord_functor_id _) F) F
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite ord_cat_law1 ord_cat_law2 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.

  Program Definition ord_functor_unit_right
    : natIso (ord_functor_comp F (ord_functor_id _)) F
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite ord_cat_law1 ord_cat_law2 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.

End FunctorCompId.

Section FunctorCompAssoc.
  Context {C1 C2 C3 C4} (F12 : ord_functor C1 C2) (F23 : ord_functor C2 C3) (F34 : ord_functor C3 C4).

  Program Definition ord_functor_assoc
    : natIso (ord_functor_comp F12 (ord_functor_comp F23 F34))
             (ord_functor_comp (ord_functor_comp F12 F23) F34)
    := mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  Next Obligation. rewrite ord_cat_law1 ord_cat_law2 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.
  Next Obligation. rewrite ord_cat_law1 //. Qed.

End FunctorCompAssoc.




(*********************************************************)
(**     Monad relative to a functor, morphisms          **)
(**     underlying functor, monads as relative monads   **)
(*********************************************************)
Section RelativeMonad.
  Context {C D : ord_category} {J : ord_functor C D}.


  Cumulative Record ord_relativeMonad :=
    mkOrdRelativeMonad
      { ord_relmonObj :> C -> D
      ; ord_relmon_unit : forall A, D⦅J A; ord_relmonObj A⦆
      ; ord_relmon_bind : forall {A B}, D⦅J A; ord_relmonObj B⦆ -> D⦅ord_relmonObj A; ord_relmonObj B⦆
      ; ord_relmon_bind_proper : forall A B,
          Proper (@ord_cat_le D (J A) (ord_relmonObj B) ==> ord_cat_le D) ord_relmon_bind
      ; ord_relmon_law1 : forall A, ord_relmon_bind (ord_relmon_unit A) = Id _
      ; ord_relmon_law2 : forall A B (f : D⦅J A; ord_relmonObj B⦆),
          ord_relmon_bind f ∙ ord_relmon_unit A = f
      ; ord_relmon_law3 : forall A B C (f : D⦅J B; ord_relmonObj C⦆) (g:D⦅J A; ord_relmonObj B⦆),
          ord_relmon_bind (ord_relmon_bind f ∙ g) = ord_relmon_bind f ∙ ord_relmon_bind g
      }.
  Global Existing Instance ord_relmon_bind_proper.
End RelativeMonad.

Arguments ord_relativeMonad {_ _} J.

Section RelativeLaxMonadMorphism.
  Context {C D1 D2 : ord_category} {J1 : ord_functor C D1} (J12 : ord_functor D1 D2) {J2 : ord_functor C D2}
          (phi : natIso J2 (ord_functor_comp J1 J12)) (psi := ni_inv phi)
          (M1 : ord_relativeMonad J1) (M2: ord_relativeMonad J2).

  Notation η := ord_relmon_unit.
  Notation rbind := ord_relmon_bind.

  Cumulative Record relativeMonadMorphism :=
    mkRelMonMorph
      { rmm_map :> forall {A}, D2⦅J12 (M1 A); M2 A⦆
      ; rmm_law1 : forall A, rmm_map ∙ ofmap J12 (η M1 A) = η M2 A ∙ psi _
      ; rmm_law2 : forall A B (f : D1⦅J1 A; M1 B⦆),
          rmm_map ∙ ofmap J12 (rbind M1 f) =
                  rbind M2 (rmm_map ∙ ofmap J12 f ∙ phi _) ∙ rmm_map
      }.

  Cumulative Record relativeLaxMonadMorphism :=
    mkRelLaxMonMorph
      { rlmm_map :> forall {A}, D2⦅J12 (M1 A); M2 A⦆
      ; rlmm_law1 : forall A, rlmm_map ∙ ofmap J12 (η M1 A) ⪷ η M2 A ∙ psi _
      ; rlmm_law2 : forall A B (f : D1⦅J1 A; M1 B⦆),
          rlmm_map ∙ ofmap J12 (rbind M1 f) ⪷
                  rbind M2 (rlmm_map ∙ ofmap J12 f ∙ phi _) ∙ rlmm_map
      }.

  Program Definition relativeMonadMorphism_to_lax
          (θ : relativeMonadMorphism) : relativeLaxMonadMorphism
    := mkRelLaxMonMorph θ _ _.
  Next Obligation. rewrite rmm_law1; reflexivity. Qed.
  Next Obligation. rewrite rmm_law2; reflexivity. Qed.
  Coercion relativeMonadMorphism_to_lax : relativeMonadMorphism >-> relativeLaxMonadMorphism.
End RelativeLaxMonadMorphism.

Section RelativeMonadToFunctor.
  Context {C D:ord_category} {J:ord_functor C D} (M : ord_relativeMonad J).

  Program Definition rmon_to_ord_functor : ord_functor C D :=
    mkOrdFunctor M (fun A B f => ord_relmon_bind M (ord_relmon_unit M _ ∙ ofmap J f)) _ _ _.
  Next Obligation.
    cbv ; intuition.
    apply ord_relmon_bind_proper, Comp_proper; [reflexivity| apply ofmap_proper; assumption].
  Qed.
  Next Obligation. rewrite ord_functor_law1 ord_cat_law2 ord_relmon_law1 //. Qed.
  Next Obligation.
    rewrite ord_functor_law2 ord_cat_law3
            -ord_relmon_law3 ord_cat_law3 ord_relmon_law2 //.
  Qed.
End RelativeMonadToFunctor.

(* Section RmonadUnit. *)
(*   Context {I C:ord_category} {J:ord_functor I C} *)
(*           (M0 : ord_relativeMonad J) (M := rmon_to_ord_functor M0). *)

(*   Program Definition rmon_unit : natTrans J M := *)
(*     mkNatTrans _ _ (relmon_unit M0) _. *)
(*   Next Obligation. rewrite (relmon_law2 M0) ; reflexivity. Qed. *)
(* End RmonadUnit. *)

(* Section RMonadAsMonad. *)
(*   Context {C:category} (M0 : relativeMonad (functor_id C)) (M := rmon_to_functor M0). *)

(*   Program Definition rmon_id_mult : natTrans (functor_comp M M) M := *)
(*     mkNatTrans _ _ (fun=> relmon_bind M0 (Id _)) _. *)
(*   Next Obligation. *)
(*     rewrite -!relmon_law3 cat_law3 (relmon_law2 M0) cat_law1 cat_law2. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Notation η := (@rmon_unit C C (functor_id C) _ _). *)
(*   Notation μ := (rmon_id_mult _). *)

(*   Lemma rmon_id_law1 {A} : μ ∙ (fmap M η) ∼ Id (M A). *)
(*   Proof. cbv. rewrite -relmon_law3 cat_law3 (relmon_law2 M0) cat_law1 relmon_law1. reflexivity. Qed. *)

(*   Lemma rmon_id_law2 {A} : μ ∙ η ∼ Id (M A). *)
(*   Proof. cbv. rewrite (relmon_law2 M0). reflexivity. Qed. *)

(*   Lemma rmon_id_law3 {A} : μ ∙ μ ∼ μ ∙ fmap M (rmon_id_mult A). *)
(*   Proof. *)
(*     cbv. rewrite -!relmon_law3 !cat_law3 (relmon_law2 M0) cat_law2 cat_law1. *)
(*     reflexivity. *)
(*   Qed. *)
(* End RMonadAsMonad. *)

(* transport a J1-relative monad into a J2-relative monad along a natural isomorphism *)
Section RelativeMonadIso.
  Context {I C} {J1 J2 : ord_functor I C} (M : ord_relativeMonad J1)
          (phi : natIso J1 J2).

  Program Definition rmon_transp_natIso : ord_relativeMonad J2 :=
    mkOrdRelativeMonad M (fun A => ord_relmon_unit M A ∙ ni_inv phi A)
                    (fun A B f => ord_relmon_bind M (f ∙ phi A))
                    _ _ _ _.
  Next Obligation.
    cbv ; intuition; apply: ord_relmon_bind_proper; apply: Comp_proper=> //; reflexivity. Qed.
  Next Obligation.
    rewrite -ord_cat_law3 ni_leftinv ord_cat_law2 ord_relmon_law1 //.
  Qed.
  Next Obligation.
    rewrite ord_cat_law3 ord_relmon_law2 -ord_cat_law3 ni_rightinv ord_cat_law2 //.
  Qed.
  Next Obligation.
    rewrite -ord_cat_law3 ord_relmon_law3 //.
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
  Context {I1 I2 C1 C2} {J1 : ord_functor I1 C1} {J2 : ord_functor I2 C2}
          (M1 : ord_relativeMonad J1) (M2 : ord_relativeMonad J2).

  Program Definition product_rmon : ord_relativeMonad (prod_functor J1 J2) :=
    mkOrdRelativeMonad (fun A => ⟨M1 (nfst A), M2 (nsnd A)⟩)
                    (fun A => ⟨ord_relmon_unit M1 (nfst A), ord_relmon_unit M2 (nsnd A)⟩)
                    (fun _ _ f => ⟨ord_relmon_bind M1 (nfst f), ord_relmon_bind M2 (nsnd f)⟩) _ _ _ _.
  Next Obligation.
    cbv ; intuition; apply: ord_relmon_bind_proper=> //.
  Qed.
  Next Obligation. intuition; rewrite !ord_relmon_law1 //. Qed.
  Next Obligation. intuition; rewrite !ord_relmon_law2 //. Qed.
  Next Obligation. intuition; rewrite !ord_relmon_law3 //. Qed.

End ProductRelativeMonad.


(*********************************************************)
(** Precomposition is functorial on relative monads     **)
(*********************************************************)
Section RelativeMonadPrecomposition.
  Context {I I'} (J : ord_functor I I').

  Section OnObjects.
    Context {C : ord_category} {JC : ord_functor I' C} (J' := ord_functor_comp J JC)
            (M : ord_relativeMonad JC).

    Program Definition relativeMonad_precomposition
      : ord_relativeMonad J' :=
      mkOrdRelativeMonad (fun A => M (J A))
                         (fun A => ord_relmon_unit M (J A))
                         (fun A B f => ord_relmon_bind M f)
                      _ _ _ _.
    Next Obligation. cbv ; intuition. apply: ord_relmon_bind_proper=> //. Qed.
    Next Obligation. rewrite !ord_relmon_law1 => //. Qed.
    Next Obligation. rewrite !ord_relmon_law2 => //. Qed.
    Next Obligation. rewrite !ord_relmon_law3 => //. Qed.
  End OnObjects.


  Local Notation "J*" := relativeMonad_precomposition.

  Section OnMorphism.
    Context {C1 C2 : ord_category} {JC1 : ord_functor I' C1} {JC2 : ord_functor I' C2}.
    Context {M1 : ord_relativeMonad JC1} {M2 : ord_relativeMonad JC2}
            {JC12 : ord_functor C1 C2} (phi : natIso _ _)
            (θ : relativeMonadMorphism JC12 phi M1 M2)
            (θl : relativeLaxMonadMorphism JC12 phi M1 M2).

    Program Definition relativeMonad_precomposition_morph
      : relativeMonadMorphism JC12
                              (natIso_comp (natIso_whisker_left phi J)
                                           (ord_functor_assoc _ _ _))
                              (J* M1) (J* M2) :=
      mkRelMonMorph _ _ _ _ (fun A => θ (J A)) _ _.
    Next Obligation. rewrite ord_cat_law2 ; apply: rmm_law1. Qed.
    Next Obligation. rewrite ord_cat_law1 ; apply: rmm_law2. Qed.


    Program Definition relativeMonad_precomposition_lax_morph
      : relativeLaxMonadMorphism JC12
                              (natIso_comp (natIso_whisker_left phi J)
                                           (ord_functor_assoc _ _ _))
                              (J* M1) (J* M2) :=
      mkRelLaxMonMorph _ _ _ _ (fun A => θl (J A)) _ _.
    Next Obligation. rewrite ord_cat_law2 ; apply: rlmm_law1. Qed.
    Next Obligation. rewrite ord_cat_law1 ; apply: rlmm_law2. Qed.
  End OnMorphism.


  (* TODO : show the functorial laws *)
End RelativeMonadPrecomposition.

(*********************************************************)
(** Postcomposition by a *full and faithful* functor is **)
(** functorial on relative monads                       **)
(*********************************************************)

Section FullyFaithfulFunctor.
  Context {C D : ord_category} (F : ord_functor C D).

  Record ff_struct :=
    { ff_invmap :> forall {X Y}, D⦅F X;F Y⦆ -> C⦅X;Y⦆
    ; ff_inv_proper : forall {X Y}, Proper (ord_cat_le D ==> ord_cat_le C) (@ff_invmap X Y)
    ; ff_section : forall {X Y} (f : D⦅F X;F Y⦆), ofmap F (ff_invmap f) = f
    ; ff_retraction : forall {X Y} (f : C⦅X;Y⦆), ff_invmap (ofmap F f) = f
    }.

  Global Existing Instance ff_inv_proper.

  Lemma invert_comp (Fff : ff_struct) {X Y Z}
    (f:D⦅F Y;F Z⦆) (g:D⦅F X;F Y⦆): Fff _ _ (f ∙ g) = Fff _ _ f ∙ Fff _ _ g.
  Proof.
    rewrite -{1}(ff_section Fff f) -{1}(ff_section Fff g) -ord_functor_law2 ff_retraction ; reflexivity.
  Qed.
End FullyFaithfulFunctor.

Section RelativeMonadPostcomposition.
  Context {I C D} {J: ord_functor I C} (M:ord_relativeMonad J)
          (F : ord_functor C D) (Fff : ff_struct F).

  Let FJ := ord_functor_comp J F.
  Program Definition relativeMonad_postcomposition : ord_relativeMonad FJ :=
    mkOrdRelativeMonad (fun A => F (M A))
                       (fun A => ofmap F (ord_relmon_unit M A))
                       (fun A B f => ofmap F (ord_relmon_bind M (Fff _ _ f)))
                    _ _ _ _.
  Next Obligation. cbv ; intuition; apply: ofmap_proper; apply: ord_relmon_bind_proper; apply: ff_inv_proper=> //. Qed.
  Next Obligation.
    rewrite ff_retraction ord_relmon_law1 ord_functor_law1 //.
  Qed.
  Next Obligation.
    rewrite -ord_functor_law2 ord_relmon_law2 ff_section //.
  Qed.
  Next Obligation.
    rewrite invert_comp ff_retraction ord_relmon_law3 ord_functor_law2 //.
  Qed.
End RelativeMonadPostcomposition.

(* From Equations Require Import Equations. *)

(* Section IdNatIso. *)
(*   Import EqNotations. *)

(*   Lemma rew_comp (C : ord_category) X Y Y' Z (f : C⦅X;Y⦆) (g : C⦅Y;Z⦆) (H : Y = Y') : *)
(*     g ∙ f = rew [fun y=> C⦅y;_⦆] H in g ∙ rew H in f. *)
(*   Proof. dependent elimination H=> //. Qed. *)

(*   Lemma rew_target (C : ord_category) X Y Z Z' (f : C⦅X;Y⦆) (g : C⦅Y;Z⦆) (H : Z = Z') : *)
(*     rew H in g ∙ f = rew H in (g ∙ f). *)
(*   Proof. dependent elimination H=> //. Qed. *)

(*   Context {I C D} {JC: ord_functor I C} {JD: ord_functor I D} *)
(*           (F : ord_functor C D) *)
(*           (JCF := ord_functor_comp JC F) *)
(*           (Hobj : forall x: I, JD x = JCF x) *)
(*           (Hmap : forall x y (f : I⦅x;y⦆), *)
(*               rew [fun x' => D⦅x'; _⦆](Hobj x) in *)
(*                 rew [fun y' => D⦅_; y'⦆] (Hobj y) in *)
(*                 ofmap JD f = ofmap JCF f). *)


(*   Goal natIso JD (ord_functor_comp JC F). *)
(*     unshelve econstructor. *)
(*     move=> A ; rewrite -(Hobj A); apply Id. *)
(*     move=> A ; rewrite -(Hobj A); apply Id. *)
(*     move=> A B f /=. *)
(*     rewrite [ofmap _ (ofmap _ _)]/(ofmap JCF f) -Hmap. *)
(*     set H1 := Hobj A. *)
(*     set H2 := Hobj B. *)
(*     move: H1 H2 => H2 H1. *)
(*     rewrite -rew_comp rew_target ord_cat_law2 ord_cat_law1 //. *)
(*     move=> ? /=. *)
(*     set H := (Hobj _). *)
(*     move: H => H. *)

(*     (* Rem.: This is totally getting out of hand !!!! *) *)

(* End IdNatIso. *)

Section RelativeMonadLifting.

  Section LiftingDatum.
    Context {I C D} {JC: ord_functor I C} {JD: ord_functor I D}
            (F : ord_functor C D)
            (JCF := ord_functor_comp JC F)
            (ϕ : natIso JD JCF)
            (MC:ord_relativeMonad JC)
            (MD:ord_relativeMonad JD).

    Let uMC := rmon_to_ord_functor MC.
    Let uMCF := ord_functor_comp uMC F.
    Let uMD := rmon_to_ord_functor MD.

    Definition lifts_object := natIso uMD uMCF.
    Definition lifts_ret (ψ : lifts_object):=
      forall (x:I), ofmap F (ord_relmon_unit MC x) ∙ ϕ _ = ψ _ ∙ ord_relmon_unit MD x.
    Definition lifts_bind (ψ : lifts_object):=
      forall (x y:I) (f: C⦅JC x; MC y⦆),
        ni_inv ψ _ ∙ ofmap F (ord_relmon_bind MC f) ∙ ψ _ =
        ord_relmon_bind MD (ni_inv ψ _ ∙ ofmap F f ∙ ϕ _).
  End LiftingDatum.

  Arguments lifts_ret {_ _ _ _ _ _} _ { _ _} _.
  Arguments lifts_bind {_ _ _ _ _ _} _ {_ _} _.

  Section LiftingOf.
    Context {I C D} (JC: ord_functor I C) {JD: ord_functor I D}
            (F : ord_functor C D)
            (JCF := ord_functor_comp JC F)
            (ϕ : natIso JD JCF)
            (MD:ord_relativeMonad JD).

    Record lifting_of :=
      mkLiftingOf {
          lifting_carrier :> ord_relativeMonad JC ;
          lifting_obj : lifts_object F lifting_carrier MD;
          lifting_ret : lifts_ret ϕ lifting_obj ;
          lifting_bind : lifts_bind ϕ lifting_obj ;
        }.

  End LiftingOf.
End RelativeMonadLifting.
