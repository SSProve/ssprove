From Coq Require Import Relation_Definitions Morphisms.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Mon Require Import SPropBase.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect boolp.
Set Warnings "notation-overridden".

Import SPropNotations.

Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we define left relative adjunctions, the relative equivalent of adjunctions.
As standard adjunctions give rise to monads, left relative adjunctions give rise to
relative monads (and right relative adjunctions give rise to relative comonads).

We're using the definition in terms of natural isomorphism between hom sets.
*)



Section PreorderMorph.
  Context (A B : Type) (rA : relation A) (rB : relation B) .
  Context (pA : PreOrder rA) (pB : PreOrder rB).

  Definition is_preorder_morph (f : A -> B) := Proper (rA ==> rB) f.
End PreorderMorph.

Section PreorderIso.
  Context (A B: Type).

  Definition are_inv (f : A -> B) (g : B -> A) : Prop :=
    forall (a:A) (b:B), g(f(a)) = a /\ f(g(b)) = b.

  Context (rA : relation A) (rB : relation B).
  Context (pA : PreOrder rA) (pB : PreOrder rB).

  Definition are_preorder_inv (f : A -> B) (g : B -> A) :=
    (@is_preorder_morph A B rA rB f) /\
    (@is_preorder_morph B A rB rA g) /\
    (are_inv f g).

End PreorderIso.

(*opposite category*)
Section OpCat.
  Context (U : ord_category).


  Program Definition oppo : ord_category :=
    mkOrdCategory (Obj U) (fun B A => (Hom U A B)) _ _ _ _ _ _ _ _.
  Next Obligation.
    move=> A. apply (@Id U A).
  Defined.
  Next Obligation.
    move=> A B C. move=> f g. unshelve eapply Comp. exact B.
    exact g. exact f.
  Defined.
  Next Obligation.
    move=> A B f. rewrite /oppo_obligation_2. rewrite /oppo_obligation_1.
    pose (@ord_cat_law2 U B A f).
    apply e.
  Qed.
  Next Obligation.
    move=> A B f. rewrite /oppo_obligation_2. rewrite /oppo_obligation_1.
    pose (@ord_cat_law1 U B A f). apply e.
  Qed.
  Next Obligation.
    move=> A B C D f g h. rewrite /oppo_obligation_2.
    pose (ord_cat_law3 U D C B A h g f). symmetry. apply e.
  Qed.

End OpCat.

(*Opposite functor. the same functor but with opposite domain *and* codomain*)
Section OpFunc.
  Context (U V: ord_category).

  Program Definition oppoF (F : ord_functor U V) : ord_functor (oppo U) (oppo V) :=
    mkOrdFunctor (fun X => F X) _ _ _ _.
  Next Obligation.
    move=> F A B. move=> g. apply (ofmap F). assumption.
  Defined.
  Next Obligation.
    move=> F A. rewrite /oppoF_obligation_1 /oppo_obligation_1. rewrite ord_functor_law1.
    reflexivity.
  Qed.
  Next Obligation.
    move=> F X Y Z g f. rewrite /oppoF_obligation_1 /oppo_obligation_1 /oppo_obligation_2.
    rewrite ord_functor_law2. reflexivity.
  Qed.

End OpFunc.


Section HomFunctor.

  Program Definition PreorderInstHom (U : ord_category) (A B :U) : Obj OrdCat.
    unshelve econstructor. exact( U ⦅ A ; B ⦆).
    unshelve econstructor. apply ord_cat_le. apply ord_cat_le_preorder.
  Defined.

  Program Definition HomF U : ord_functor (prod_cat (oppo U) U) OrdCat :=
    mkOrdFunctor (fun AB => PreorderInstHom U (nfst AB) (nsnd AB)) _ _ _ _.
  Next Obligation.
    move=> U [A1 A2] [B1 B2] [/= pre post]. unshelve econstructor.
    move=> topp. exact (post ∙ topp ∙ pre).
    cbv. move=> f g Hfg. apply Comp_proper. apply Comp_proper.
    reflexivity. assumption. reflexivity.
  Defined.
  Next Obligation.
    move=> U [A1 A2] [B1 B2]. cbv.
    move=> [pre post] [pre' post']. move=> [Hpre Hpost].
    move=> topp. apply Comp_proper. apply Comp_proper.
    assumption. reflexivity. destruct Hpre. reflexivity.
  Qed.
  Next Obligation.
    move=> U [A1 A2]. rewrite /HomF_obligation_1 /oppo_obligation_1. simpl.
    apply sig_eq. simpl. apply funext. move=> topp.
    rewrite ord_cat_law2. rewrite ord_cat_law1. reflexivity.
  Qed.
  Next Obligation.
    move=> U [X1 X2] [Y1 Y2] [Z1 Z2] /=.
    move=> [g1 g2] [f1 f2].
    cbv. apply sig_eq. simpl. apply funext. move=> topp.
    repeat rewrite ord_cat_law3. reflexivity.
  Qed.

End HomFunctor.



Section LeftAdjDef.
  Context {I D C: ord_category}. (*I -> C meant to be the base. D = goal of the rel adj*)
  Context (J : ord_functor I C) (L : ord_functor I D) (R : ord_functor D C).

  (*below we define the functor where L appears : D⦅ LA ; B ⦆*)
  Definition leftHom : ord_functor ( prod_cat (oppo I) D ) OrdCat.
    eapply ord_functor_comp. all: revgoals. exact (HomF D).
    apply prod_functor. eapply oppoF. exact L.
    apply ord_functor_id.
  Defined.

  (*below we define the functor where R (and J appears): C⦅ JA ; RB⦆ *)
  Definition rightHom : ord_functor (prod_cat (oppo I) (D)) OrdCat.
    eapply ord_functor_comp. all: revgoals. exact (HomF C).
    apply prod_functor. eapply oppoF. exact J.
    exact R.
  Defined.

  (*a left relative adjunction is a natural isomorphism between hom sets (preorders for us!)*)
  Definition leftAdjunctionSituation := natIso leftHom rightHom.

End LeftAdjDef.


(*We can retrive a relative monad from a relative adjunction*)
Section RelativeMonadFromLeftRelAdjunction.
  Context {I D C: ord_category}. (*I -> C meant to be the base. D = goal of the rel adj*)
  Context (J : ord_functor I C) (L : ord_functor I D) (R : ord_functor D C).

  Hypothesis Chi : leftAdjunctionSituation J L R.

  Definition unit_fromLeftAdj : forall A : I, C ⦅ J A; R (L A) ⦆.
    move=> A. move: Chi => [Chi_map Chi_inv Chi_nat Chi_rightinv Chi_leftinv].
    pose (Chi_map_AA := (Chi_map ⟨A,L A⟩)∙1). apply Chi_map_AA.
    simpl. apply Id.
  Defined.

  Definition bind_fromLeftAdj : forall A B : I, C ⦅ J A; R (L B) ⦆ -> C ⦅ R (L A); R (L B) ⦆.
    move=> A B k. move: Chi => [Chi_map Chi_inv Chi_nat Chi_rightinv Chi_leftinv].
    apply (ofmap R).
    pose (Chi_map_ALB := (Chi_inv ⟨A,L B⟩)∙1). apply Chi_map_ALB. simpl.
    exact k.
  Defined.

  Program Definition relMon_fromLeftAdj : ord_relativeMonad J :=
    @mkOrdRelativeMonad I C J (ord_functor_comp L R) _ _ _ _ _ _.
  Next Obligation.
    exact unit_fromLeftAdj.
  Defined.
  Next Obligation.
    exact bind_fromLeftAdj.
  Defined.
  Next Obligation.
    move=> A B. rewrite /relMon_fromLeftAdj_obligation_2. cbv.
    move=> k1 k2. move=> H12. apply ofmap_proper.
    move: Chi => [Chi_map Chi_inv Chi_nat Chi_rightinv Chi_leftinv].
    eapply ((Chi_inv ⟨ A , L B ⟩)∙2). assumption.
  Qed.
  Next Obligation.
    rewrite /relMon_fromLeftAdj_obligation_2. rewrite /relMon_fromLeftAdj_obligation_1.
    move=> A. rewrite /bind_fromLeftAdj. rewrite /unit_fromLeftAdj.
    move: Chi => [Chi_map Chi_inv Chi_nat Chi_rightinv Chi_leftinv].
    cut ( forall (P : prod_cat (oppo I) D) (f : dfst (leftHom L P)) ,
        (Chi_inv P)∙1 ( (Chi_map P)∙1  f  )
        =
        (Chi_inv P ∙ Chi_map P)∙1 f
).
    move=> Hyp. rewrite (Hyp ⟨A, L A⟩ (Id (L A))). rewrite Chi_leftinv. simpl.
    rewrite ord_functor_law1. reflexivity.
    cbv. reflexivity.
  Qed.
  Next Obligation.
    move=> A B k. rewrite /relMon_fromLeftAdj_obligation_2 /relMon_fromLeftAdj_obligation_1.
    cbv.
    move: Chi => [Chi_map Chi_inv Chi_nat Chi_rightinv Chi_leftinv].
    unshelve epose (Chi_nat ⟨A,L A⟩ ⟨A , L B⟩ _).
    econstructor. cbv. apply Id. simpl. exact ((Chi_inv⟨A,L B⟩)∙1 k).
    cbv in e. apply (f_equal sval) in e. cbv in e. apply (f_equal (fun h => h (Id (L A)))) in e.
    rewrite !ord_functor_law1 in e. rewrite !ord_cat_law2 in e.
    rewrite -e.
    cut ( forall (P : prod_cat (oppo I) D) k ,
        (Chi_map P)∙1 ( (Chi_inv P)∙1  k  )
        =
        (Chi_map P ∙ Chi_inv P)∙1 k
).  move=> Hcut. specialize (Hcut ⟨A, L B⟩ k).
    move: Chi_rightinv => /(_ ⟨A, L B⟩) Chi_rightinv.
    eapply (f_equal sval) in Chi_rightinv. simpl in Chi_rightinv.
    eapply (f_equal (fun aFun => aFun k) )in Chi_rightinv.
    simpl in Chi_rightinv.
    cbv in Chi_rightinv. rewrite Chi_rightinv. reflexivity.
    intuition.
  Qed.
  Next Obligation.
    move=> X Y Z. move=> l k.
    rewrite /relMon_fromLeftAdj_obligation_2. cbv.
    unshelve epose (natIso_inv_natural _ _ Chi _).
      exact (⟨X, L Y⟩). exact (⟨X, L Z⟩).
      econstructor. simpl. apply Id. simpl. apply ((ni_inv Chi ⟨Y,L Z⟩)∙1). simpl. exact l.
    simpl in e. apply (f_equal sval) in e. simpl in e. apply (f_equal (fun h => h k)) in e.
    simpl in e. cbv in e. rewrite !ord_functor_law1 in e. rewrite !ord_cat_law2 in e.
    rewrite -ord_functor_law2. rewrite -e. reflexivity.
  Qed.

End RelativeMonadFromLeftRelAdjunction.


(*an arrow A --> B in the Kleisli of M is by definition an arrow JA → MB*)
Section RelativeKleisli.
  Context {I C:ord_category} {J : ord_functor I C} (M : ord_relativeMonad J).

  Program Definition relKleisli : ord_category :=
    mkOrdCategory (Obj I) (fun i j => C⦅ J i ; M j ⦆) (fun i j f1 f2=> (ord_cat_le C f1 f2))
_ _ _ _ _ _ _.
  Next Obligation.
    apply (ord_relmon_unit M).
  Defined.
  Next Obligation.
    move=> X Y Z g f. exact ((ord_relmon_bind M g) ∙ f).
  Defined.
  Next Obligation.
    move=> X Y Z. cbv. move=> g1 g2 Hg. move=> f1 f2 Hf.
    eapply Comp_proper.
    eapply ord_relmon_bind_proper. assumption. assumption.
  Qed.
  Next Obligation.
    move=> X Y. rewrite /relKleisli_obligation_2. move=> f.
    rewrite /relKleisli_obligation_1. rewrite (ord_relmon_law1 M Y).
    rewrite ord_cat_law1. reflexivity.
  Qed.
  Next Obligation.
    move=> X Y. rewrite /relKleisli_obligation_2 /relKleisli_obligation_1.
    move=> f. rewrite ord_relmon_law2. reflexivity.
  Qed.
  Next Obligation.
    move=> X Y Z T f g h. rewrite /relKleisli_obligation_2.
    rewrite ord_relmon_law3. rewrite ord_cat_law3. reflexivity.
  Qed.

End RelativeKleisli.


(*There is a relative adjunction between the base functor and the relative kleisli*)
Section RelativeKleisliAdjunction.
  Context {I C:ord_category} {J : ord_functor I C} (M : ord_relativeMonad J).


  Program Definition KleisliLeftAdjoint : ord_functor I (relKleisli M) := mkOrdFunctor
(fun (X:I) => (X:relKleisli M))
(fun X Y f => ord_relmon_unit M Y ∙ (ofmap J f)) _ _ _.
  Next Obligation.
    move=> X Y. cbv. move=> f1 f2 H12. apply Comp_proper. reflexivity.
    apply ofmap_proper. assumption.
  Qed.
  Next Obligation.
    move=> X. rewrite /relKleisli_obligation_1. rewrite ord_functor_law1.
    rewrite ord_cat_law2. reflexivity.
  Qed.
  Next Obligation.
    move=> X Y Z. move=> f g. rewrite /relKleisli_obligation_2.
    rewrite ord_cat_law3. rewrite ord_relmon_law2.
    rewrite ord_functor_law2. rewrite ord_cat_law3. reflexivity.
  Qed.


  Program Definition KleisliRightAdjoint : ord_functor (relKleisli M) C := mkOrdFunctor
(fun (X : relKleisli M) => M (X : I)) (fun X Y f => ord_relmon_bind M f) _ _ _.
  Next Obligation.
    move=> X. cbv. rewrite ord_relmon_law1. reflexivity.
  Qed.
  Next Obligation.
    move=> X Y Z f g. cbv. apply ord_relmon_law3.
  Qed.

  Definition ChiKleisli0 :   forall A : prod_cat (oppo I) (relKleisli M),
  OrdCat ⦅ leftHom KleisliLeftAdjoint A; rightHom J KleisliRightAdjoint A ⦆.
    move=> [X Y]. unshelve econstructor.
    simpl in *. move=> f. exact f.
    easy.
  Defined.

  Definition InvChiKleisli0 :   forall A : prod_cat (oppo I) (relKleisli M),
  OrdCat ⦅ rightHom J KleisliRightAdjoint A; leftHom KleisliLeftAdjoint A ⦆.
    move=> [X Y]. unshelve econstructor. simpl in *.
    move=> g. exact g. easy.
  Defined.

  Program Definition ChiKleisli : (leftAdjunctionSituation J KleisliLeftAdjoint KleisliRightAdjoint)
  := mkNatIso _ _ ChiKleisli0 InvChiKleisli0 _ _ _.
  Next Obligation.
    cbv. move=> [X1 X2] [Y1 Y2]. move=> [u v]. apply sig_eq. simpl.
    apply funext. move=> w.
    rewrite ord_cat_law3. rewrite ord_relmon_law2. reflexivity.
  Qed.
  Next Obligation.
    move=> [A1 A2]. apply sig_eq. cbv. reflexivity.
  Qed.
  Next Obligation.
    move=> [A1 A2]. apply sig_eq. cbv. reflexivity.
  Qed.

End RelativeKleisliAdjunction.


(*
Let M:I→ C be a J-relative monad.
Consider J♭ : I → I and R: C → C functors such that JL♭ ⊣ R
(the "transforming (left relative) adjunction")
M can be factored through its Kleisli: M = R^M ∘ L^M, with L^M ⊣ R^M
This section builds the "transformed" left relative adjunction:
L^M ∘ L♭ ⊣ R ∘ R^M .
as well as the associated monad of this new adjunction (see AdjTransform)
*)
Section TransformationViaRelativeAdjunction.
  Context {I C : ord_category} {J : ord_functor I C}.
  Context (M : ord_relativeMonad J).
  Context (Lflat : ord_functor I I) (R : ord_functor C C).
  Context (Chi_RJLflat : leftAdjunctionSituation J (ord_functor_comp Lflat J) R).


  Definition Chi_transformedAdjunction :   forall A : prod_cat (oppo I) (relKleisli M),
  OrdCat ⦅ leftHom (ord_functor_comp Lflat (KleisliLeftAdjoint M)) A;
  rightHom J (ord_functor_comp (KleisliRightAdjoint M) R) A ⦆.
    move=> [A B]. unshelve econstructor. simpl.
    move: Chi_RJLflat=> [Chi_RJLflat_map Chi_RJLflat_inv Chi_RJLflat_nat Chi_RJLflat_leftinv
                       Chi_RJLflat_rightinv].
    simpl in *. unshelve apply (Chi_RJLflat_map ⟨A, M B⟩)∙1 .
    cbv. move=> f1 f2 H12. apply (Chi_RJLflat ⟨A , M B⟩)∙2. assumption.
  Defined.


  Program Definition TransformedAdjunction : leftAdjunctionSituation J
  (ord_functor_comp Lflat (KleisliLeftAdjoint M)) (ord_functor_comp (KleisliRightAdjoint M) R):=
    mkNatIso _ _ (Chi_transformedAdjunction) _ _ _ _.
  Next Obligation.
    move=> [A B]. simpl. unshelve econstructor.
    move: Chi_RJLflat=> [Chi_RJLflat_map Chi_RJLflat_inv Chi_RJLflat_nat Chi_RJLflat_leftinv
                       Chi_RJLflat_rightinv].
    simpl in *. unshelve apply (Chi_RJLflat_inv ⟨A, M B⟩)∙1 .
    cbv. move=> f1 f2 H12. apply (natIso_sym (Chi_RJLflat) ⟨A, M B⟩)∙2. assumption.
  Defined.
  Next Obligation.
    move=> [A1 K1] [A2 K2] [fA fK] //=. simpl in fA. simpl in fK.
    apply sig_eq. simpl. apply funext. move=> topp. simpl.
    move: Chi_RJLflat =>
[Chi_RJLflat_map Chi_RJLflat_inv
Chi_RJLflat_nat Chi_RJLflat_leftinv Chi_RJLflat_rightinv].
    rewrite /relKleisli_obligation_2.
    move: Chi_RJLflat_nat. move=> /(_ ⟨A1, M K1⟩ ⟨A2, M K2⟩) Chi_RJLflat_nat.
    unfold leftHom in Chi_RJLflat_nat. unfold rightHom in Chi_RJLflat_nat.
    move: Chi_RJLflat_nat. move=> /(_ ⟨fA, (ord_relmon_bind M) fK⟩) Chi_RJLflat_nat.
    rewrite /oppoF_obligation_1. simpl. cbv in Chi_RJLflat_nat.
    apply (f_equal sval) in Chi_RJLflat_nat. simpl in Chi_RJLflat_nat.
    apply (f_equal (fun h => h topp)) in Chi_RJLflat_nat.
    cbv.
    rewrite -[RHS]Chi_RJLflat_nat. f_equal.
    (* move=> H. rewrite H. reflexivity. *)
    rewrite ord_relmon_law3. rewrite ord_cat_law3. f_equal.
    rewrite -ord_cat_law3. f_equal. rewrite ord_relmon_law2.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A K]. apply sig_eq. simpl.
    move: Chi_RJLflat =>
[Chi_RJLflat_map Chi_RJLflat_inv
Chi_RJLflat_nat Chi_RJLflat_leftinv Chi_RJLflat_rightinv].
    move: Chi_RJLflat_leftinv. move=> /(_ ⟨A, M K⟩) Chi_RJLflat_leftinv.
    apply (f_equal sval) in Chi_RJLflat_leftinv. cbv in Chi_RJLflat_leftinv.
    apply Chi_RJLflat_leftinv.
  Qed.
  Next Obligation.
    move=> [A K]. apply sig_eq. simpl.
    move: Chi_RJLflat =>
[Chi_RJLflat_map Chi_RJLflat_inv
Chi_RJLflat_nat Chi_RJLflat_leftinv Chi_RJLflat_rightinv].
    move: Chi_RJLflat_rightinv. move=> /(_ ⟨A, M K⟩) Chi_RJLflat_rightinv.
    apply (f_equal sval) in Chi_RJLflat_rightinv. cbv in Chi_RJLflat_rightinv.
    apply Chi_RJLflat_rightinv.
  Qed.



  Definition AdjTransform : ord_relativeMonad J := relMon_fromLeftAdj _ _ _ TransformedAdjunction.

End TransformationViaRelativeAdjunction.


(* A small lemma needed in the new section *)
Lemma equal_f : forall {A B : Type} {f g : A -> B},
  f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

(*Take a J relative adjunction between L and R. The structural iso Φ mapping left adjuncts
f : LA -> B to right adjuncts Φ f : JA -> RB can in fact be expressed in terms of
the right adjoint R, and the unit η of the adjunction.
Specifically Φ f = Rf ∘ η
This comes from the naturality of Φ ... *)
Section ExpressStrucIsoAsRightAdj.
  Context {I D C : ord_category}.
  Context {J : ord_functor I C} {L : ord_functor I D} {R : ord_functor D C}.

  Context (Phi : leftAdjunctionSituation J L R).
  Let myM :=  relMon_fromLeftAdj J L R Phi.

  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.


  Context {A : I} {B : D} (f : D⦅ L A ; B⦆).

  Lemma strucIso_rightAdj : (Phi ⟨A , B⟩)∙1 f = ofmap R f ∙ (η myM A).
  Proof.
    (*we have natuality of Phi *)
    unshelve epose (Phi_nat := (ni_natural _ _ Phi)).
      exact ⟨A, L A⟩. exact ⟨A , B⟩.
    specialize (Phi_nat ⟨Id _, f⟩). simpl in Phi_nat.
    apply (f_equal sval) in Phi_nat. simpl in Phi_nat.
    unshelve eapply equal_f in Phi_nat. exact (Id _).
    cbv in Phi_nat.
    (*cleaning*)
    move: Phi_nat. rewrite !ord_cat_law2. rewrite !ord_functor_law1. rewrite !ord_cat_law2.
    (*def of η*)
    move=> Phi_nat. assumption.
  Qed.

End ExpressStrucIsoAsRightAdj.
