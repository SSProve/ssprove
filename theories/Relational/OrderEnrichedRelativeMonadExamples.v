From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms SRelationPairs.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import OrderEnrichedCategory Rel.

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

  Notation " X --> Y " := (X -> dfst Y) (at level 99).

  Program Definition to_discr {X Y} (f : X --> Y) : OrdCat⦅discr X; Y⦆ := ⦑f⦒.
  Next Obligation. move=> ? ?; induction 1; sreflexivity. Qed.


  Program Definition OrdCat_cst {A B} (b:dfst B) : OrdCat⦅A; B⦆ := ⦑fun=> b⦒.
  Next Obligation. cbv; intuition. Qed.

  Lemma ordCat_helper {A B} (f g : OrdCat⦅A;B⦆) :
    f ⪷ g -> forall (x y:dfst A), x ≤ y -> f∙1 x ≤ g∙1 y.
  Proof.
    move=> Hfg x y Hxy; estransitivity;[apply: (f∙2); exact: Hxy| apply: Hfg].
  Qed.
End OrdCat.

(* Re-exporting the notation *)
Notation " x ≤ y " := (extract_ord x y).
Notation " X --> Y " := (X -> dfst Y) (at level 99).

Section OrdProduct.
  Context {A B} (relA : srelation A) (relB : srelation B)
          `{!PreOrder relA, !PreOrder relB}.

  Definition prod_rel : srelation (A × B) :=
    srelation_conjunction (@SRelCompFun (A × B) A relA nfst)
                          (SRelCompFun relB nsnd).

  Global Instance : PreOrder prod_rel.
  Proof. constructor ; cbv ; intuition ; estransitivity ; eassumption. Qed.
End OrdProduct.



(** Embedding of the monads from the unary setting into relative monads *)

Definition rMonad := ord_relativeMonad (ord_functor_id TypeCat).
Definition unarySpecMonad := ord_relativeMonad discr.
Definition unaryEffectObs M W := relativeMonadMorphism discr (natIso_sym (ord_functor_unit_left _)) M W.


Section UnarySpecMonadOps.
  Import SPropNotations.
  Definition retW {W : unarySpecMonad} {A} : A --> W A := (ord_relmon_unit W A)∙1.
  Definition bindWStr {W : unarySpecMonad} {Γ A B}
              (wm: Γ --> W A) (wf : Γ × A --> W B) : Γ --> W B :=
    fun γ => (ord_relmon_bind W (to_discr (fun a => wf⟨γ, a⟩)))∙1 (wm γ).
End UnarySpecMonadOps.


Section MonadAsRMonad.
  Context (M:Monad).
  Import FunctionalExtensionality.

  (* Transforming a standard monad to a relative monad on the identity functor *)
  Program Definition monad_to_relmon : rMonad :=
    mkOrdRelativeMonad M (fun A => @ret M A) (fun A B f => bind^~ f) _ _ _ _.
  Next Obligation. cbv ; intuition. induction (SPropAxioms.funext_sprop _ _ _ _ H)=> //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law2 //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law1 //. Qed.
  Next Obligation. extensionality c ; rewrite /bind monad_law3 //. Qed.
End MonadAsRMonad.

Section OrderedMonadAsRMonad.
  Context (M:OrderedMonad).

  Import SPropNotations.
  Import FunctionalExtensionality.
  (* Any unary specification monad in the sense of [Dijkstra monads for All] give raise to a relative monad *)
  Program Definition ordmonad_to_relmon : unarySpecMonad :=
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

Section MonadMorphismAsRMonMorphism.
  Context {M0:Monad} {W0:OrderedMonad} (θ0:MonadMorphism M0 W0).
  Let M := monad_to_relmon M0.
  Let W := ordmonad_to_relmon W0.
  Let θ := from_discrete_monad_monotonic θ0.

  Import SPropNotations.
  Import FunctionalExtensionality.
  (* morphisms of monads also transfer to relativeMonad morphisms *)

  Program Definition mmorph_to_rmmorph : unaryEffectObs M W :=
    mkRelMonMorph discr _ M W (fun (A:TypeCat) => ⦑θ A⦒) _ _.
  Next Obligation. cbv ; intros ; induction H ; sreflexivity. Qed.
  Next Obligation.
    apply Ssig_eq=> /=; extensionality a=> /=; rewrite mon_morph_ret //.
  Qed.
  Next Obligation.
    apply Ssig_eq ; extensionality a ; rewrite /= mon_morph_bind //.
  Qed.

End MonadMorphismAsRMonMorphism.







(** Specialization of relative monads for the simple setting *)


Section SimpleRelationalSpecMonad.

  Definition Jprod := ord_functor_comp typeCat_prod discr.

  (* Simple relational specification  monad *)
  Definition RelationalSpecMonad0 : Type := ord_relativeMonad Jprod.


  Import SPropNotations.

  Let idxid := (prod_functor (ord_functor_id TypeCat) (ord_functor_id TypeCat)).
  Program Definition idxid_iso_id : natIso idxid (ord_functor_id TypeCatSq) :=
    mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.

  Definition compPairRMonad (M1 M2 : rMonad): ord_relativeMonad (ord_functor_id TypeCatSq) :=
    rmon_transp_natIso (product_rmon M1 M2) idxid_iso_id.

  Context (M01 M02 : Monad).
  Let M1 := monad_to_relmon M01.
  Let M2 := monad_to_relmon M02.

  Definition compPair := compPairRMonad M1 M2.

  Definition to_prod {A1 A2 B1 B2} (f1 : A1 -> M01 B1) (f2 : A2 -> M02 B2)
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


End SimpleRelationalSpecMonad.

(* Any unary specification monad yield a simple relational spec monad
   when precomposing with the product functor *)
Section RelationalSpecMonadZeroFromOrderedMonad.
  Context (M:OrderedMonad).

  Definition ordmonad_to_relspecmon0 := relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon M).

End RelationalSpecMonadZeroFromOrderedMonad.


Notation "wm ≫= wf" := (Spr1 (ord_relmon_bind _ wf) wm) (at level 50).



(** Specialization of relative monads for the full setting *)
(* A direct definition using the lifting condition is difficult to use with
intensional equality, so we encode exactly the components we need *)


Section NaiveDefinition.
  Definition discr2 := prod_functor discr discr.
  Definition unarySpecPair (W1 W2 : unarySpecMonad)
    : ord_relativeMonad discr2 :=
      product_rmon W1 W2.

  (* Changing this Let to Definition breaks RSM_from_RSM0 below... *)
  Definition OrdCatSq := prod_cat OrdCat OrdCat.
  Definition OrdCatTr := prod_cat OrdCatSq OrdCat.

  Program Definition J : ord_functor TypeCatSq OrdCatTr :=
    mkOrdFunctor (fun A => ⟨⟨discr (nfst A), discr (nsnd A)⟩, Jprod A⟩)
                 (fun _ _ f => ⟨⟨ofmap discr (nfst f),
                              ofmap discr (nsnd f)⟩,
                             ofmap Jprod f⟩) _ _ _.
  Next Obligation. cbv ; intuition ; f_equiv ; auto. Qed.

  Definition ordcatTr2Sq : ord_functor OrdCatTr OrdCatSq :=
    left_proj_functor _ _.

  Program Definition discr2_iso_J_proj
    : natIso discr2 (ord_functor_comp J ordcatTr2Sq) :=
    mkNatIso _ _ (fun A => Id (discr2 A)) (fun A => Id (discr2 A)) _ _ _.


  Definition preRelationalSpecMonad : Type := ord_relativeMonad J.

  (* Relational specification monads are pre-relational specification monads
   satisfying a lifting condition ensuring that the first and second components
   define unary spec monads *)


  (* Record RelationalSpecMonad  := *)
  (*   mkRSM { *)
  (*       rsm_left : unarySpecMonad ; *)
  (*       rsm_right : unarySpecMonad ; *)
  (*       rsm_rel : lifting_of *)
  (*                   J ordcatTr2Sq discr2_iso_J_proj *)
  (*                   (unarySpecPair rsm_left rsm_right) *)
  (*     }. *)



  (* Context (M01 M02 : Monad). *)
  (* Notation compPair := (compPair M01 M02). *)

  (* Definition preRelationalEffectObservation (W:preRelationalSpecMonad) : Type := *)
  (*   relativeMonadMorphism J (natIso_sym (ord_functor_unit_left _)) compPair W. *)

  (* Definition preRelationalLaxEffectObservation (W:preRelationalSpecMonad) : Type := *)
  (*   relativeLaxMonadMorphism J (natIso_sym (ord_functor_unit_left _)) compPair W. *)

  (* Definition mkpreREO (W:preRelationalSpecMonad) θ pf1 pf2 *)
  (*   : preRelationalEffectObservation W *)
  (*   := @mkRelMonMorph _ _ _ _ _ _ _ _ _ θ pf1 pf2. *)

  (* Definition mkpreRLEO (W:preRelationalSpecMonad) θ pf1 pf2 *)
  (*   : preRelationalLaxEffectObservation W *)
  (*   := @mkRelLaxMonMorph _ _ _ _ _ _ _ _ _ θ pf1 pf2. *)

  (* Program Definition πord1 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr A⦆ := ⦑ nfst ⦒. *)
  (* Next Obligation. intuition. Qed. *)

  (* Program Definition πord2 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr B⦆ := ⦑ nsnd ⦒. *)
  (* Next Obligation. intuition. Qed. *)


  (* Lemma Ssig_rew {A P} {x y : A} {Hx Hy} *)
  (*   : x = y -> Sexists P x Hx = Sexists P y Hy. *)
  (* Proof. move=> ? ; apply Ssig_eq=> //. Qed. *)

  (* Import FunctionalExtensionality. *)
  (* (* Any simple relational specification monad yield a full relational specification monad *) *)
  (* Program Definition RSM_from_RSM0 (W : RelationalSpecMonad0) : preRelationalSpecMonad := *)
  (*   mkOrdRelativeMonad *)
  (*     (fun A => ⟨⟨W ⟨nfst A, unit⟩, W ⟨unit, nsnd A⟩⟩, W A⟩) *)
  (*                   (fun A => ⟨⟨⦑fun a => Spr1 (ord_relmon_unit W ⟨nfst A, unit⟩) ⟨a,tt⟩⦒, *)
  (*                            ⦑fun a => Spr1 (ord_relmon_unit W ⟨unit, nsnd A⟩) ⟨tt, a⟩⦒⟩, *)
  (*                           ord_relmon_unit W A⟩) *)
  (*                   (fun A B f => *)
  (*                      ⟨⟨ ord_relmon_bind W (nfst (nfst f) ∙ πord1), *)
  (*                        ord_relmon_bind W (nsnd (nfst f) ∙ πord2)⟩, *)
  (*                       ord_relmon_bind W (nsnd f)⟩) *)
  (*                   _ _ _ _. *)
  (* Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed. *)
  (* Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed. *)
  (* Next Obligation. *)
  (*   cbv ; intuition; *)
  (*     apply (ord_relmon_bind_proper W ⟨_,_⟩ _ _ _)=> ?; *)
  (*     [apply p0| apply q0| apply q]. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intuition. *)
  (*   f_equal;[f_equal|]; apply: Ssig_eq=> /=. *)
  (*   1,2: set f := ⦑_⦒; have -> : f = ord_relmon_unit W ⟨_,_⟩. *)
  (*   all: try by rewrite ord_relmon_law1. *)
  (*   apply Ssig_eq; extensionality x; move: x=> [? []] //. *)
  (*   apply Ssig_eq; extensionality x; move: x=> [[] ?] //. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intuition. *)
  (*   f_equal;[f_equal|]; apply: Ssig_eq=> /=. *)
  (*   - extensionality x; set f := ⦑_⦒. *)
  (*     move: (ord_relmon_law2 W ⟨_,unit⟩ _ f)=> /(f_equal Spr1) /(equal_f ^~ ⟨_, _⟩)//=. *)
  (*   - extensionality x; set f := ⦑_⦒. *)
  (*     move: (ord_relmon_law2 W ⟨unit,_⟩ _ f)=> /(f_equal Spr1) /(equal_f ^~ ⟨_, _⟩)//=. *)
  (*   - move: (ord_relmon_law2 W _ _ nsnd) => /(f_equal Spr1) //. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intuition ; cbv. *)
  (*   f_equal;[f_equal|]; apply: Ssig_eq=> /=. (* ; extensionality x. *) *)
  (*   - epose (ord_relmon_law3 W ⟨ _, unit⟩ ⟨_, unit⟩ _ *)
  (*                      ⦑fun x1 => Spr1 nfst1 (Base.nfst x1) ⦒ *)
  (*                      ⦑fun x0 => Spr1 nfst (Base.nfst x0)⦒) as s. *)
  (*     extensionality x; move: s => /(f_equal Spr1) /(equal_f ^~ x) s; apply s. *)
  (*   - epose (ord_relmon_law3 W ⟨unit, _⟩ ⟨unit, _⟩ _ *)
  (*                      ⦑fun x1 => Spr1 nsnd1 (Base.nsnd x1) ⦒ *)
  (*                      ⦑fun x0 => Spr1 nsnd2 (Base.nsnd x0)⦒) as s. *)
  (*     extensionality x; move: s => /(f_equal Spr1) /(equal_f ^~ x) s; apply s. *)
  (*   - rewrite ord_relmon_law3=> //. *)
  (* Qed. *)

End NaiveDefinition.


Section RelationalSpecMonad.


  Record rsm_components (W1 W2 : unarySpecMonad) :=
    mkRSMComponents
      { rsmc_carrier :> TypeCatSq -> OrdCat
      ; rsmc_return : forall A, OrdCat⦅Jprod A; rsmc_carrier A⦆
      ; rsmc_act: forall {A1 A2 B1 B2},
            OrdCat⦅discr A1;W1 B1⦆ -> OrdCat⦅discr A2;W2 B2⦆ ->
            OrdCat⦅Jprod ⟨A1,A2⟩; rsmc_carrier ⟨B1,B2⟩⦆ -> OrdCat⦅rsmc_carrier ⟨A1,A2⟩; rsmc_carrier ⟨B1,B2⟩⦆
      ; rsmc_act_proper :
          forall {A1 A2 B1 B2},
            SProper (ord_cat_le _ s==> ord_cat_le _ s==> ord_cat_le _ s==> ord_cat_le _) (@rsmc_act A1 A2 B1 B2)
      ; rsmc_law1 : forall A1 A2,
          rsmc_act (ord_relmon_unit W1 A1) (ord_relmon_unit W2 A2)
                   (rsmc_return ⟨A1,A2⟩) = Id _
      ; rsmc_law2 :
          forall A1 A2 B1 B2 f1 f2 (f: OrdCat⦅Jprod ⟨A1,A2⟩; rsmc_carrier ⟨B1,B2⟩⦆),
              rsmc_act f1 f2 f ∙ rsmc_return _ = f
      ; rsmc_law3 :
          forall A1 A2 B1 B2 C1 C2 f1 f2 f g1 g2 g,
            @rsmc_act A1 A2 C1 C2
                  (ord_relmon_bind W1 g1 ∙ f1)
                  (ord_relmon_bind W2 g2 ∙ f2)
                  (@rsmc_act B1 B2 C1 C2 g1 g2 g ∙ f)
            = (@rsmc_act B1 B2 C1 C2 g1 g2 g)
                 ∙ (@rsmc_act A1 A2 B1 B2 f1 f2 f)
      }.

  Record RelationalSpecMonad  :=
    mkRSM {
        rsm_left : unarySpecMonad ;
        rsm_right : unarySpecMonad ;
        rsm_rel : rsm_components rsm_left rsm_right
      }.


End RelationalSpecMonad.

Arguments rsmc_carrier {_ _} _ _.
Arguments rsmc_return {_ _} _ _.
Arguments rsmc_act {_ _} _ {_ _ _ _} _ _ _.

Arguments to_prod {_ _ _ _ _ _} _ _.


Section RelationalEffectObservation.


  Context (M1 M2 : rMonad) (M12 := compPairRMonad M1 M2).

  Section RelationalEffectObservationComponents.
    Context {W1 W2 : unarySpecMonad}.
    Context (Wrel : rsm_components W1 W2).
    Context (θ1 : unaryEffectObs M1 W1) (θ2 : unaryEffectObs M2 W2).
    Notation W := (rsmc_carrier Wrel).
    Notation η := (rsmc_return Wrel).
    Notation actW := (rsmc_act Wrel).


    Record reo_components
      :=
      mkREOComponents
        { reoc_carrier : forall {A}, OrdCat⦅Jprod (M12 A);W A⦆
        ; reoc_law1 : forall {A}, reoc_carrier ∙ ofmap Jprod (ord_relmon_unit M12 A) = η A
        ; reoc_law2 : forall {A B} (f:TypeCatSq⦅A;M12 B⦆),
            reoc_carrier ∙ ofmap Jprod (ord_relmon_bind M12 f)
            = actW (θ1 _ ∙ ofmap discr (nfst f))
                  (θ2 _ ∙ ofmap discr (nsnd f))
                  (reoc_carrier ∙ ofmap Jprod f) ∙ reoc_carrier
        }.
  End RelationalEffectObservationComponents.

  Context (W : RelationalSpecMonad).
  Record relationalEffectObservation :=
    mkREO
      { reo_left : unaryEffectObs M1 (rsm_left W)
      ; reo_right : unaryEffectObs M2 (rsm_right W)
      ; reo_rel : reo_components (rsm_rel W) reo_left reo_right
      }.

End RelationalEffectObservation.

Arguments reo_left {_ _ _} _.
Arguments reo_right {_ _ _} _.
Arguments reo_rel {_ _ _} _.

(** The definition that we use provides an instance of the naive def *)
Section ToNaiveDefinitions.
  Context (W : RelationalSpecMonad).

  Notation W1 := (rsm_left W).
  Notation W2 := (rsm_right W).

  Context {M1 M2 : rMonad}
          (θ : relationalEffectObservation M1 M2 W).

  Notation M12 := (compPair M1 M2).
  Notation θ1 := (reo_left θ).
  Notation θ2 := (reo_right θ).


  Notation Wrel := (rsm_rel W).
  Notation W0 := (rsmc_carrier Wrel).
  Notation η := (rsmc_return Wrel).
  Notation actW := (rsmc_act Wrel).

  Import SPropNotations.

  (* We show that we can define the sur-approximation of this coq-development from that data *)
  Local Ltac feq_npair := repeat (congr npair).

  Program Definition W' : preRelationalSpecMonad :=
    mkOrdRelativeMonad (fun A => ⟨⟨W1 (nfst A), W2 (nsnd A)⟩, W0 A⟩)
                    (fun A => ⟨⟨ord_relmon_unit W1 (nfst A), ord_relmon_unit W2 (nsnd A)⟩,
                           η A⟩)
                    (fun A B f =>
                       ⟨⟨ord_relmon_bind W1 (nfst (nfst f)),
                         ord_relmon_bind W2 (nsnd (nfst f))⟩,
                       actW(nfst (nfst f)) (nsnd (nfst f)) (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation.
    cbv ; intuition; last
        (apply: rsmc_act_proper=> ?; [apply p0| apply q0| apply q]) ;
      [apply: (ord_relmon_bind_proper W1)|
       apply: (ord_relmon_bind_proper W2)] ; cbv=> ? ; auto.
  Qed.
  Next Obligation.
    feq_npair ;[apply: (ord_relmon_law1 W1)| apply: (ord_relmon_law1 W2)|];
    rewrite /actW ?rsmc_law1 //.
  Qed.
  Next Obligation.
    move: f => [[f1 f2] frel].
    unshelve feq_npair.
    apply: (ord_relmon_law2 W1).
    apply: (ord_relmon_law2 W2).
    apply Ssig_eq, (f_equal Spr1), rsmc_law2.
  Qed.
  Next Obligation.
    unshelve feq_npair.
    apply: (ord_relmon_law3 W1).
    apply: (ord_relmon_law3 W2).
    apply Ssig_eq, (f_equal Spr1), rsmc_law3.
  Qed.


  (* Context (θrc : reo_components θ1 θ2 Wrel). *)
  (* Notation θW := (@reoc_carrier _ _ _ _ _ _ _ θrc ⟨_,_⟩). *)


  (* Program Definition θ : preRelationalEffectObservation M1 M2 W := *)
  (*   mkpreREO M1 M2 W (fun A => ⟨⟨θ1 (nfst A), θ2 (nsnd A)⟩, θW⟩) _ _. *)
  (* Next Obligation. *)
  (*   f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1). *)
  (*   apply (rmm_law1 _ _ _ _ θ1). *)
  (*   apply (rmm_law1 _ _ _ _ θ2). *)
  (*   apply: reoc_law1. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   f_equal ; [f_equal|]; apply Ssig_eq ; apply: (f_equal Spr1). *)
  (*   apply (rmm_law2 _ _ _ _ θ1). *)
  (*   apply (rmm_law2 _ _ _ _ θ2). *)
  (*   apply (reoc_law2 θ1 θ2). *)
  (* Qed. *)

End ToNaiveDefinitions.
