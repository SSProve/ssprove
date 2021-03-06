From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms SRelationPairs.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import Category RelativeMonads EnrichedSetting.

Set Primitive Projections.
Set Universe Polymorphism.


(** This files instantiates the categorical definitions of RelativeMonads.v *)
(** We first define the category of types and poset *)
(** Then we introduce the functors over which relative monads are taken
    to derive our notions of relational specification monads
    and relational effect observation *)

Section TypeCat.

  (* The category of types *)
  Program Definition TypeCat : category :=
    mkCategory Type
               (fun A B => A -> B)
               (fun _ _ f g => forall x, f x = g x) _
               (fun A a => a)
               (fun _ _ _ f g x => f (g x))
               _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; etransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. rewrite H0. apply H. Qed.

  Import SPropNotations.
  (* TypeCat × TypeCat *)
  Definition TypeCatSq := prod_cat TypeCat TypeCat.

  (* Functor × : TypeCat × TypeCat → TypeCat *)
  Program Definition typeCat_prod : functor TypeCatSq TypeCat :=
    mkFunctor (fun A => nfst A × nsnd A)
              (fun _ _ f p => ⟨nfst f (nfst p), nsnd f (nsnd p)⟩)
              _ _ _.
  Next Obligation. cbv ; intuition ; f_equal=> //. Qed.

  Program Definition TypeCat_cc : cartesian_category :=
    mkCartesianCategory
      TypeCat
      unit
      (mkNatTrans _ _ (fun _ _ => tt) _)
      typeCat_prod
      (mkNatTrans _ _ (fun=>nfst) _)
      (mkNatTrans _ _ (fun=>nsnd) _)
      (fun X A B f g x => ⟨f x, g x⟩)
      _ _ _ _ _.
  Next Obligation. cbv ; intuition. rewrite H H0=> //. Qed.
  Next Obligation. destruct (f x)=> //. Qed.
End TypeCat.

Section OrdCat.
  Import SPropNotations.
  (* Category of preordered types *)
  Program Definition OrdCat : category :=
    mkCategory {A : Type ⫳ { R : srelation A | PreOrder R } }
               (fun A B => {f : dfst A -> dfst B | SProper (proj1_sig (dsnd A) s==> proj1_sig (dsnd B)) f})
               (fun _ _ f g => forall x, proj1_sig f x = proj1_sig g x) _
               (fun A => ⦑id⦒)
               (fun _ _ _ f g => ⦑fun x => proj1_sig f (proj1_sig g x)⦒)
               _ _ _ _.
  Next Obligation. constructor ; cbv ; intuition ; etransitivity ; eauto. Qed.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; intuition; apply (proj2_sig f); apply (proj2_sig g)=> //. Qed.
  Next Obligation. cbv ; intuition. rewrite H0. apply H. Qed.

  Program Definition discr : functor TypeCat OrdCat :=
    mkFunctor (fun A => dpair _ A ⦑eq⦒)
              (fun _ _ f => ⦑ f ⦒)
              _ _ _.
  Next Obligation. intuition. Qed.
  Next Obligation. intuition. Qed.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition discr_ff : ff_struct discr :=
    {| ff_invmap _ _ f := proj1_sig f |}.
  Next Obligation. cbv ; intuition. Qed.

  Definition extract_ord {A : OrdCat} := proj1_sig (dsnd A).
  Definition extract_ord_preord A : PreOrder (@extract_ord A) := proj2_sig (dsnd A).
  Global Existing Instance extract_ord_preord.

  Program Definition OrdCat_cst {A B} (b:dfst B) : OrdCat⦅A; B⦆ := ⦑fun=> b⦒.
  Next Obligation. cbv; intuition. Qed.
End OrdCat.

Notation " x ≤ y " := (extract_ord x y).

Section OrdCatSelfEnrichment.
  Context {A B : OrdCat}.

  Definition ordcat_hom_ord : srelation (OrdCat⦅A;B⦆) :=
    fun f1 f2 => forall a, proj1_sig f1 a ≤ proj1_sig f2 a.

  Global Instance ordcat_hom_ord_preord : PreOrder ordcat_hom_ord.
  Proof. constructor ; cbv ; intuition. estransitivity ; eauto.
  apply H. apply H0.
  Qed.
End OrdCatSelfEnrichment.

Notation "f1 ≼ f2" := (ordcat_hom_ord f1 f2) (at level 65).


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

Import FunctionalExtensionality.

Lemma funext {A B} {f g : forall a:A, B a} : (forall a, f a = g a) -> f = g.
Proof. intros H ; extensionality a ; apply H. Qed.


Section MonadAsRMonad.
  Context (M:Monad).

  (* Transforming a standard monad to a relative monad on the identity functor *)
  Program Definition monad_to_relmon : relativeMonad (functor_id TypeCat) :=
    mkRelativeMonad M (fun A => @ret M A) (fun A B f => bind^~ f) _ _ _ _.
  Next Obligation. cbv ; intuition; rewrite (funext H) //. Qed.
  Next Obligation. rewrite /bind monad_law2 //. Qed.
  Next Obligation. rewrite /bind monad_law1 //. Qed.
  Next Obligation. rewrite /bind monad_law3 //. Qed.
End MonadAsRMonad.



Section RelationalSpecMonad.


  Definition Jprod := functor_comp typeCat_prod discr.

  (* Simple relational specification  monad *)
  Definition RelationalSpecMonad0 : Type := relativeMonad Jprod.

  Class BindMonotonicRelationalSpecMonad0 (W : RelationalSpecMonad0) : Prop :=
    rsm0_bind_monotonic :
      forall {A B}, SProper (ordcat_hom_ord s==> ordcat_hom_ord) (@relmon_bind _ _ _ W A B).
      (* forall {A B} (f1 f2 : OrdCat⦅Jprod A; W B⦆), *)
      (*   f1 ≼ f2 -> relmon_bind W f1 ≼ relmon_bind W f2. *)

  Context (M1 M2 : Monad).
  Import SPropNotations.

  Let idxid := (prod_functor (functor_id TypeCat) (functor_id TypeCat)).
  Program Definition idxid_iso_id : natIso idxid (functor_id TypeCatSq) :=
    mkNatIso _ _ (fun=> Id _) (fun=> Id _) _ _ _.
  
  Definition compPair : relativeMonad (functor_id TypeCatSq) :=
    rmon_transp_natIso
      (product_rmon (monad_to_relmon M1) (monad_to_relmon M2))
      idxid_iso_id.

  Definition to_prod {A1 A2 B1 B2} (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2)
             : TypeCatSq⦅ ⟨A1,A2⟩ ; compPair ⟨B1, B2⟩⦆ := ⟨f1 , f2⟩.

  Definition RelationalEffectObservation0 (W:RelationalSpecMonad0) : Type :=
    relativeMonadMorphism Jprod (natIso_sym (functor_unit_left _)) compPair W.

  Definition mkREO0 (W:RelationalSpecMonad0) θ pf1 pf2
    : RelationalEffectObservation0 W
    := @mkRelMonMorph _ _ _ _ _ _ _ _ _ θ pf1 pf2.

  (* Changing this Let to Definition breaks RSM_from_RSM0 below... *)
  Definition OrdCatTr := prod_cat (prod_cat OrdCat OrdCat) OrdCat.

  Definition ordcattr_hom_ord {X Y} : (srelation (OrdCatTr⦅X;Y⦆)) :=
    prod_rel (prod_rel ordcat_hom_ord ordcat_hom_ord) ordcat_hom_ord.


  Program Definition J : functor TypeCatSq OrdCatTr :=
    mkFunctor (fun A => ⟨⟨discr (nfst A), discr (nsnd A)⟩, Jprod A⟩)
              (fun _ _ f => ⟨⟨fmap discr (nfst f),
                           fmap discr (nsnd f)⟩,
                          fmap Jprod f⟩)
              _ _ _.
  Next Obligation. cbv ; intuition ; f_equal ; auto. Qed.

  (* Full relational specification  monad *)
  (* With respect to the paper we take a slightly different encoding *)
  Definition RelationalSpecMonad : Type := relativeMonad J.

  Class BindMonotonicRelationalSpecMonad (W : RelationalSpecMonad) : Prop :=
    rsm_bind_monotonic :
      forall {A B}, SProper (ordcattr_hom_ord s==> ordcattr_hom_ord) (@relmon_bind _ _ _ W A B).

  Definition RelationalEffectObservation (W:RelationalSpecMonad) : Type :=
    relativeMonadMorphism J (natIso_sym (functor_unit_left _)) compPair W.

  Program Definition πord1 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr A⦆ := ⦑ nfst ⦒.
  Next Obligation. intuition. Qed.

  Program Definition πord2 {A B} : OrdCat⦅Jprod ⟨A, B⟩ ; discr B⦆ := ⦑ nsnd ⦒.
  Next Obligation. intuition. Qed. 


  Lemma sig_rew {A P} {x y : A} {Hx Hy} : x = y -> exist P x Hx = exist P y Hy.
  Proof. move=> ? ; apply sig_eq=> //. Qed.

  (* Any simple relational specification monad yield a full relational specification monad *)
  Program Definition RSM_from_RSM0 (W : RelationalSpecMonad0) : RelationalSpecMonad :=
    mkRelativeMonad
      (fun A => ⟨⟨W ⟨nfst A, unit⟩, W ⟨unit, nsnd A⟩⟩, W A⟩)
                    (fun A => ⟨⟨⦑fun a => proj1_sig (relmon_unit W ⟨nfst A, unit⟩) ⟨a,tt⟩⦒,
                             ⦑fun a => proj1_sig (relmon_unit W ⟨unit, nsnd A⟩) ⟨tt, a⟩⦒⟩,
                            relmon_unit W A⟩)
                    (fun A B f =>
                       ⟨⟨ relmon_bind W (nfst (nfst f) ∙ πord1),
                         relmon_bind W (nsnd (nfst f) ∙ πord2)⟩,
                        relmon_bind W (nsnd f)⟩)
                    _ _ _ _.
  Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed.
  Next Obligation. cbv ; intuition. induction H. sreflexivity. Qed.
  Next Obligation.
    cbv ; intuition.
    (* Beware, tricky script ! f_equal, rewrite, apply behave strangely *)
    - apply funext in H.
      apply (f_equal (fun f (x:nfst × unit) => f (Base.nfst x))) in H.
      apply equal_f; apply (f_equal proj1_sig) ; f_equal.
      simple refine (sig_eq _ _ _ _)=> //. 
    
    - apply funext in H2.
      apply (f_equal (fun f (x:unit × nsnd) => f (Base.nsnd x))) in H2.
      apply equal_f; apply (f_equal proj1_sig) ; f_equal.
      simple refine (sig_eq _ _ _ _)=> //. 
    
    - enough (nsnd1 = Base.nsnd y) as -> ; move=> //.
      refine (sig_eq _ _ _ _) ; exact (funext H1).
  Qed.
  Next Obligation.
    intuition.
    - match goal with
      |[|- context c [⦑ ?t ⦒]] =>
       enough (⦑ t ⦒ = relmon_unit W ⟨nfst, unit ⟩) as ->
      end.
      rewrite relmon_law1 => //.
      refine (sig_eq _ _ _ _) ; extensionality x0 ; destruct x0 as [? []]=> //.

    - match goal with
      |[|- context c [⦑ ?t ⦒]] =>
       enough (⦑ t ⦒ = relmon_unit W ⟨unit,nsnd ⟩) as ->
      end.
      rewrite relmon_law1 => //.
      refine (sig_eq _ _ _ _) ; extensionality x0 ; destruct x0 as [[] ?]=> //.

    - rewrite relmon_law1=> //.
  Qed.
  Next Obligation.
    intuition; move: (relmon_law2 W) => /= -> //.
  Qed.
  Next Obligation.
    intuition ; cbv.
    
    - epose (relmon_law3 W ⟨ _, unit⟩ ⟨_, unit⟩ _
                       ⦑fun x1 => proj1_sig nfst1 (Base.nfst x1) ⦒
                       ⦑fun x0 => proj1_sig nfst (Base.nfst x0)⦒) as s.
      cbv in s ;  erewrite (s x) => //.

    - epose (relmon_law3 W ⟨unit, _⟩ ⟨unit, _⟩ _
                       ⦑fun x1 => proj1_sig nsnd1 (Base.nsnd x1) ⦒
                       ⦑fun x0 => proj1_sig nsnd2 (Base.nsnd x0)⦒) as s.
      cbv in s ;  erewrite (s x) => //.

    - rewrite relmon_law3=> //.
  Qed.
End RelationalSpecMonad.

Arguments to_prod {_ _ _ _ _ _} _ _. 

Section OrderedMonadAsRMonad.
  Context (M:OrderedMonad).

  Import SPropNotations.
  (* Any unary specification monad in the sense of [Dijkstra monads for All] give raise to a relative monad *)
  Program Definition ordmonad_to_relmon : relativeMonad discr :=
    mkRelativeMonad (fun A => dpair _ (M A) ⦑@omon_rel M A⦒)
                    (fun A => ⦑@ret M A⦒)
                    (fun A B f => ⦑bind^~ (proj1_sig f)⦒) _ _ _ _.
  Next Obligation. typeclasses eauto. Qed.
  Next Obligation. cbv ; intuition ; induction H ; sreflexivity. Qed.
  Next Obligation.
    cbv ; intuition. apply omon_bind=> //= ? ; apply (proj2_sig f); sreflexivity.
  Qed.
  Next Obligation. cbv ; intuition ; rewrite (funext H)=> //. Qed.
  Next Obligation. rewrite /bind monad_law2 //. Qed.
  Next Obligation. rewrite /bind monad_law1 //. Qed.
  Next Obligation. rewrite /bind monad_law3 //. Qed.

  (* We would like to derive such an instance but the types don't match exactly, the def of the typeclass should be generalized to some extent *)
  (* Global Instance : BindMonotonicRelationalSpecMonad0 ordmonad_to_relmon. *)
End OrderedMonadAsRMonad.

Section RelationalSpecMonadZeroFromOrderedMonad.
  Context (M:OrderedMonad).

  Definition ordmonad_to_relspecmon0 := relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon M).

  Global Instance : BindMonotonicRelationalSpecMonad0 ordmonad_to_relspecmon0.
  Proof. cbv. move=> ? ? ? ? ? ?  ; apply omon_bind=> //. sreflexivity. Qed.
End RelationalSpecMonadZeroFromOrderedMonad.

Section MonadMorphismAsRMonMorphism.
  Context {M0:Monad} {W0:OrderedMonad} (θ0:MonadMorphism M0 W0).
  Let M := monad_to_relmon M0.
  Let W := ordmonad_to_relmon W0.
  Let θ := from_discrete_monad_monotonic θ0.

  Import SPropNotations.
  (* morphisms of monads also transfer to relativeMonad morphisms *)
  Program Definition mmorph_to_rmmorph :
    relativeMonadMorphism discr (natIso_sym (functor_unit_left _)) M W :=
    mkRelMonMorph discr _ M W (fun (A:TypeCat) => ⦑θ A⦒) _ _.
  Next Obligation. cbv ; intros ; induction H ; sreflexivity. Qed.
  Next Obligation. apply mon_morph_ret. Qed.
  Next Obligation. apply mon_morph_bind. Qed.

End MonadMorphismAsRMonMorphism.
