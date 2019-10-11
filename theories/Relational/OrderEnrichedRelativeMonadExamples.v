From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms SRelationPairs.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import OrderEnrichedCategory.

Set Primitive Projections.
Set Universe Polymorphism.


(** This files is an order-enriched alternative to RelativeMonadExamples.v *)

Section TypeCat.

  Import SPropNotations.
  Record strictSet :=
    mkStrictSet
      { sSet_carrier :> Type
      ; is_strict : forall (x y : sSet_carrier), x ≡ y -> x = y
      }.

  (* The category of types *)
  Program Definition TypeCat : ord_category :=
    mkOrdCategory Type (* strictSet *)
               (fun A B => A -> B)
               (fun _ _ f g => forall x, f x ≡ g x) _
               (fun A a => a)
               (fun _ _ _ f g x => f (g x))
               _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; estransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. induction (H0 x1). apply H. Qed.

  Import SPropNotations.
  (* TypeCat × TypeCat *)
  Definition TypeCatSq := prod_cat TypeCat TypeCat.

  (* Functor × : TypeCat × TypeCat → TypeCat *)
  Program Definition typeCat_prod : ord_functor TypeCatSq TypeCat :=
    mkOrdFunctor (fun A => nfst A × nsnd A)
              (fun _ _ f p => ⟨nfst f (nfst p), nsnd f (nsnd p)⟩)
              _ _ _.
  Next Obligation. cbv ; intuition; f_equiv; auto. Qed.

  (* Program Definition TypeCat_cc : cartesian_category := *)
  (*   mkCartesianCategory *)
  (*     TypeCat *)
  (*     unit *)
  (*     (mkNatTrans _ _ (fun _ _ => tt) _) *)
  (*     typeCat_prod *)
  (*     (mkNatTrans _ _ (fun=>nfst) _) *)
  (*     (mkNatTrans _ _ (fun=>nsnd) _) *)
  (*     (fun X A B f g x => ⟨f x, g x⟩) *)
  (*     _ _ _ _ _. *)
  (* Next Obligation. cbv ; intuition. rewrite H H0=> //. Qed. *)
  (* Next Obligation. destruct (f x)=> //. Qed. *)
End TypeCat.

Section OrdCat.
  Import SPropNotations.
  (* Category of preordered types *)
  Definition ordType := {A : Type ⫳ { R : srelation A ≫ PreOrder R } }.
  Definition extract_ord {A : ordType} := Spr1 (dsnd A).
  Definition extract_ord_preord A : PreOrder (@extract_ord A) := Spr2 (dsnd A).
  Global Existing Instance extract_ord_preord.
  Notation " x ≤ y " := (extract_ord x y).

  Program Definition OrdCat : ord_category :=
    mkOrdCategory
      ordType
      (fun A B => {f : dfst A -> dfst B ≫ SProper (extract_ord s==> extract_ord) f})
      (fun _ _ f g => forall x, f∙1 x ≤ g∙1 x) _
      (fun A => ⦑id⦒)
      (fun _ _ _ f g => ⦑f∙1 \o g∙1⦒)
      _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; estransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; intuition; apply f∙2; apply g∙2 => //. Qed.
  Next Obligation.
    cbv ; intuition; estransitivity; first (apply: x∙2; apply: H0).
    apply: H.
  Qed.

  Program Definition discr : ord_functor TypeCat OrdCat :=
    mkOrdFunctor (fun A => dpair _ A ⦑sEq⦒)
                 (fun _ _ f => ⦑ f ⦒)
              _ _ _.
  Next Obligation. intuition. Qed.
  Next Obligation. intuition. Qed.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition discr_ff : ff_struct discr :=
    {| ff_invmap _ _ f := Spr1 f |}.
  Next Obligation. cbv ; intuition. Qed.


  Program Definition OrdCat_cst {A B} (b:dfst B) : OrdCat⦅A; B⦆ := ⦑fun=> b⦒.
  Next Obligation. cbv; intuition. Qed.
End OrdCat.

Notation " x ≤ y " := (extract_ord x y).

(* Section OrdCatSelfEnrichment. *)
(*   Context {A B : OrdCat}. *)

(*   Definition ordcat_hom_ord : srelation (OrdCat⦅A;B⦆) := *)
(*     fun f1 f2 => forall a, Spr1 f1 a ≤ Spr1 f2 a. *)

(*   Global Instance ordcat_hom_ord_preord : PreOrder ordcat_hom_ord. *)
(*   Proof. constructor ; cbv ; intuition. estransitivity ; eauto. Qed. *)
(* End OrdCatSelfEnrichment. *)

(* Notation "f1 ≼ f2" := (ordcat_hom_ord f1 f2) (at level 65). *)


Section OrdProduct.
  Context {A B} (relA : srelation A) (relB : srelation B)
          `{!PreOrder relA, !PreOrder relB}.

  Definition prod_rel : srelation (A × B) :=
    srelation_conjunction (@SRelCompFun (A × B) A relA nfst)
                          (SRelCompFun relB nsnd).

  Global Instance : PreOrder prod_rel.
  Proof. constructor ; cbv ; intuition ; estransitivity ; eassumption. Qed.
End OrdProduct.

(** FunctionalExtensionality **)
Import SPropNotations.
Definition sfunext {A B} {f g : forall x : A, B x}: (forall x : A, f x ≡ g x) -> f ≡ g :=
  SPropAxioms.funext_sprop _ _ _ _.
From Coq Require Import FunctionalExtensionality.
Definition funext {A B} {f g : forall x : A, B x}: (forall x : A, f x = g x) -> f = g.
Proof. move=> h ; extensionality x ; apply h. Qed.

Section MonadAsRMonad.
  Context (M:Monad).
  Import FunctionalExtensionality.

  (* Transforming a standard monad to a relative monad on the identity functor *)
  Program Definition monad_to_relmon : ord_relativeMonad (ord_functor_id TypeCat) :=
    mkOrdRelativeMonad M (fun A => @ret M A) (fun A B f => bind^~ f) _ _ _ _.
  Next Obligation. cbv ; intuition. induction (sfunext H)=> //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law2 //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law1 //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law3 //. Qed.
End MonadAsRMonad.


Section RelationalSpecMonad.

  Definition Jprod := ord_functor_comp typeCat_prod discr.

  (* Simple relational specification  monad *)
  Definition RelationalSpecMonad0 : Type := ord_relativeMonad Jprod.


  Context (M1 M2 : Monad).
  Import SPropNotations.

  Let idxid := (prod_functor (ord_functor_id TypeCat) (ord_functor_id TypeCat)).
  Program Definition idxid_iso_id : natIso idxid (ord_functor_id TypeCatSq) :=
    mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.

  Definition compPair : ord_relativeMonad (ord_functor_id TypeCatSq) :=
    rmon_transp_natIso
      (product_rmon (monad_to_relmon M1) (monad_to_relmon M2))
      idxid_iso_id.

  Definition to_prod {A1 A2 B1 B2} (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2)
             : TypeCatSq⦅ ⟨A1,A2⟩ ; compPair ⟨B1, B2⟩⦆ := ⟨f1 , f2⟩.

  Definition RelationalEffectObservation0 (W:RelationalSpecMonad0) : Type :=
    relativeMonadMorphism Jprod (natIso_sym (ord_functor_unit_left _)) compPair W.

  Definition RelationalLaxEffectObservation0 (W:RelationalSpecMonad0) : Type :=
    relativeLaxMonadMorphism Jprod (natIso_sym (ord_functor_unit_left _)) compPair W.

  Definition mkREO0 (W:RelationalSpecMonad0) θ pf1 pf2
    : RelationalEffectObservation0 W
    := @mkRelMonMorph _ _ _ _ _ _ _ _ _ θ pf1 pf2.

  Definition mkRLEO0 (W:RelationalSpecMonad0) θ pf1 pf2
    : RelationalLaxEffectObservation0 W
    := @mkRelLaxMonMorph _ _ _ _ _ _ _ _ _ θ pf1 pf2.

  (* Changing this Let to Definition breaks RSM_from_RSM0 below... *)
  Definition OrdCatTr := prod_cat (prod_cat OrdCat OrdCat) OrdCat.

  (* Definition ordcattr_hom_ord {X Y} : (srelation (OrdCatTr⦅X;Y⦆)) := *)
  (*   prod_rel (prod_rel ordcat_hom_ord ordcat_hom_ord) ordcat_hom_ord. *)


  Program Definition J : ord_functor TypeCatSq OrdCatTr :=
    mkOrdFunctor (fun A => ⟨⟨discr (nfst A), discr (nsnd A)⟩, Jprod A⟩)
              (fun _ _ f => ⟨⟨ofmap discr (nfst f),
                           ofmap discr (nsnd f)⟩,
                          ofmap Jprod f⟩)
              _ _ _.
  Next Obligation. cbv ; intuition ; f_equiv ; auto. Qed.

  (* Full relational specification  monad *)
  (* With respect to the paper we take a slightly different encoding *)
  Definition RelationalSpecMonad : Type := ord_relativeMonad J.

  Definition RelationalEffectObservation (W:RelationalSpecMonad) : Type :=
    relativeLaxMonadMorphism J (natIso_sym (ord_functor_unit_left _)) compPair W.

  Program Definition πord1 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr A⦆ := ⦑ nfst ⦒.
  Next Obligation. intuition. Qed.

  Program Definition πord2 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr B⦆ := ⦑ nsnd ⦒.
  Next Obligation. intuition. Qed.


  Lemma Ssig_rew {A P} {x y : A} {Hx Hy}
    : x = y -> Sexists P x Hx = Sexists P y Hy.
  Proof. move=> ? ; apply Ssig_eq=> //. Qed.

  Import FunctionalExtensionality.
  (* Any simple relational specification monad yield a full relational specification monad *)
  Program Definition RSM_from_RSM0 (W : RelationalSpecMonad0) : RelationalSpecMonad :=
    mkOrdRelativeMonad
      (fun A => ⟨⟨W ⟨nfst A, unit⟩, W ⟨unit, nsnd A⟩⟩, W A⟩)
                    (fun A => ⟨⟨⦑fun a => Spr1 (ord_relmon_unit W ⟨nfst A, unit⟩) ⟨a,tt⟩⦒,
                             ⦑fun a => Spr1 (ord_relmon_unit W ⟨unit, nsnd A⟩) ⟨tt, a⟩⦒⟩,
                            ord_relmon_unit W A⟩)
                    (fun A B f =>
                       ⟨⟨ ord_relmon_bind W (nfst (nfst f) ∙ πord1),
                         ord_relmon_bind W (nsnd (nfst f) ∙ πord2)⟩,
                        ord_relmon_bind W (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed.
  Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed.
  Next Obligation.
    cbv ; intuition;
      apply (ord_relmon_bind_proper W ⟨_,_⟩ _ _ _)=> ?;
      [apply p0| apply q0| apply q].
  Qed.
  Next Obligation.
    intuition.
    f_equal;[f_equal|]; apply: Ssig_eq=> /=.
    1,2: set f := ⦑_⦒; have -> : f = ord_relmon_unit W ⟨_,_⟩.
    all: try by rewrite ord_relmon_law1.
    apply Ssig_eq; extensionality x; move: x=> [? []] //.
    apply Ssig_eq; extensionality x; move: x=> [[] ?] //.
  Qed.
  Next Obligation.
    intuition.
    f_equal;[f_equal|]; apply: Ssig_eq=> /=.
    - extensionality x; set f := ⦑_⦒.
      move: (ord_relmon_law2 W ⟨_,unit⟩ _ f)=> /(f_equal Spr1) /(equal_f ^~ ⟨_, _⟩)//=.
    - extensionality x; set f := ⦑_⦒.
      move: (ord_relmon_law2 W ⟨unit,_⟩ _ f)=> /(f_equal Spr1) /(equal_f ^~ ⟨_, _⟩)//=.
    - move: (ord_relmon_law2 W _ _ nsnd) => /(f_equal Spr1) //.
  Qed.
  Next Obligation.
    intuition ; cbv.
    f_equal;[f_equal|]; apply: Ssig_eq=> /=. (* ; extensionality x. *)
    - epose (ord_relmon_law3 W ⟨ _, unit⟩ ⟨_, unit⟩ _
                       ⦑fun x1 => Spr1 nfst1 (Base.nfst x1) ⦒
                       ⦑fun x0 => Spr1 nfst (Base.nfst x0)⦒) as s.
      extensionality x; move: s => /(f_equal Spr1) /(equal_f ^~ x) s; apply s.
    - epose (ord_relmon_law3 W ⟨unit, _⟩ ⟨unit, _⟩ _
                       ⦑fun x1 => Spr1 nsnd1 (Base.nsnd x1) ⦒
                       ⦑fun x0 => Spr1 nsnd2 (Base.nsnd x0)⦒) as s.
      extensionality x; move: s => /(f_equal Spr1) /(equal_f ^~ x) s; apply s.
    - rewrite ord_relmon_law3=> //.
  Qed.
End RelationalSpecMonad.

Arguments to_prod {_ _ _ _ _ _} _ _.

Section OrderedMonadAsRMonad.
  Context (M:OrderedMonad).

  Import SPropNotations.
  Import FunctionalExtensionality.
  (* Any unary specification monad in the sense of [Dijkstra monads for All] give raise to a relative monad *)
  Program Definition ordmonad_to_relmon : ord_relativeMonad discr :=
    mkOrdRelativeMonad (fun A => dpair _ (M A) ⦑@omon_rel M A⦒)
                       (fun A => ⦑@ret M A⦒)
                       (fun A B f => ⦑bind^~ (Spr1 f)⦒) _ _ _ _.
  Next Obligation. typeclasses eauto. Qed.
  Next Obligation. cbv ; intuition ; induction H ; sreflexivity. Qed.
  Next Obligation.
    cbv ; intuition. apply omon_bind=> //= ? ; apply (Spr2 f); sreflexivity.
  Qed.
  Next Obligation. cbv ; intuition. apply omon_bind=> //. sreflexivity. Qed.
  Next Obligation. apply Ssig_eq; extensionality x ; rewrite /= /bind monad_law2 //. Qed.
  Next Obligation. apply Ssig_eq; extensionality x ; rewrite /= /bind monad_law1 //. Qed.
  Next Obligation. apply Ssig_eq; extensionality x ; rewrite /= /bind monad_law3 //. Qed.

End OrderedMonadAsRMonad.

Section RelationalSpecMonadZeroFromOrderedMonad.
  Context (M:OrderedMonad).

  Definition ordmonad_to_relspecmon0 := relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon M).

End RelationalSpecMonadZeroFromOrderedMonad.

Section MonadMorphismAsRMonMorphism.
  Context {M0:Monad} {W0:OrderedMonad} (θ0:MonadMorphism M0 W0).
  Let M := monad_to_relmon M0.
  Let W := ordmonad_to_relmon W0.
  Let θ := from_discrete_monad_monotonic θ0.

  Import SPropNotations.
  Import FunctionalExtensionality.
  (* morphisms of monads also transfer to relativeMonad morphisms *)
  Program Definition mmorph_to_rmmorph :
    relativeMonadMorphism discr (natIso_sym (ord_functor_unit_left _)) M W :=
    mkRelMonMorph discr _ M W (fun (A:TypeCat) => ⦑θ A⦒) _ _.
  Next Obligation. cbv ; intros ; induction H ; sreflexivity. Qed.
  Next Obligation.
    apply Ssig_eq=> /=; extensionality a=> /=; rewrite mon_morph_ret //.
  Qed.
  Next Obligation.
    apply Ssig_eq ; extensionality a ; rewrite /= mon_morph_bind //.
  Qed.

End MonadMorphismAsRMonMorphism.
