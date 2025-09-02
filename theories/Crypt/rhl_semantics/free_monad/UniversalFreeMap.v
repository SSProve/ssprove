From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From SSProve.Mon Require Import SPropBase.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden".
From SSProve.Crypt Require Import FreeProbProg ChoiceAsOrd.

Import SPropNotations.


(*
in theory there is a free-forgetful adjunction between choiceType relative monads on one side,
and operations and arities on the other side (the involved category is the slice Ty / chTy).
Here we describe the object part of the forgetful functor U.
*)
Section ForgetFromRmonToOpar.
  Context (T : ord_relativeMonad choice_incl).

  Definition forgOps : Type := {A : choiceType & T A}.
  Definition forgAr : forgOps -> choiceType := fun op => match op with |existT A _ => A end.

End ForgetFromRmonToOpar.


Section UnivFreeMap.
  (*start with a morphism of signatures (given as operations and arities) σ → U(T) *)

  (*domain signature = arbitrary signature*)
  Context {sigma_ops : Type} {sigma_ar : sigma_ops -> choiceType}.

  (*codomain signature = coming from a relative monad*)
  Context {T : ord_relativeMonad choice_incl}.
  Let T_ops := forgOps T.
  Let T_ar := forgAr T.

  (*here is an arrow in the slice cat Ty / chTy *)
  (* Context (sigMap : sigma_ops -> T_ops). *)
  (* Hypothesis (slicemorph : forall op : sigma_ops, T_ar (sigMap (op)) = sigma_ar op). *)
  (*To avoid the need for equality transports we remark that to give such a morphism is
   the same as giving a section like this:*)
  Context  (sigMap : forall op : sigma_ops , T (sigma_ar op) ).

  Let Free_sigma := rFree sigma_ops sigma_ar. (*the domain relative monad*)

  Definition trivialChi :
  natIso choice_incl (ord_functor_comp choice_incl (ord_functor_id TypeCat)) :=
    natIso_sym( ord_functor_unit_right choice_incl ).

  Notation η := ord_relmon_unit.
  Notation dnib := ord_relmon_bind.

  Fixpoint outOfFree0 (A:choiceType) (tree : Free_sigma A) {struct tree} : T A.
  Proof.
  move: tree=>[|]. exact (η T A).
  move=> op opk.
  unshelve eapply (dnib T _).
    exact (sigma_ar op).
    simpl. move=> a0. apply outOfFree0. apply opk. exact a0.
    apply sigMap.
  Defined.


  Program Definition outOfFree : relativeMonadMorphism (ord_functor_id _) trivialChi Free_sigma T :=
    mkRelMonMorph (ord_functor_id _) trivialChi Free_sigma T outOfFree0 _ _.
  Next Obligation.
    move=> A B f.
    rewrite /outOfFree_obligation_1. rewrite /FreeProbProg.rFree_obligation_2.
    apply boolp.funext. move=> tree.
    elim: tree.
    (*ret case*)
    simpl. move=> a. pose (bind_vs_ret := ord_relmon_law2 T A B  (fun x : A => outOfFree0 B (f x))).
    simpl in bind_vs_ret.
    unshelve eapply FunctionalExtensionality.equal_f in bind_vs_ret. exact a.
    rewrite -bind_vs_ret. reflexivity.
    (*bind case*)
    move=> op opk Hind.
    simpl.
    epose (bind_bind := ord_relmon_law3 T _ _ _ _ _).
    eapply FunctionalExtensionality.equal_f in bind_bind.
      cbn in bind_bind.
      erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. move=> ans. apply Hind.
  Qed.

End UnivFreeMap.


Section ufmap_vs_callrFree.
  Context (sigma_ops : Type) (sigma_ar : sigma_ops -> choiceType)
          (T : ord_relativeMonad choice_incl).
  Context (sigMap : (forall op : sigma_ops , T ( sigma_ar op ))).

  Lemma outOfFree_vs_callrFree :
  forall op : sigma_ops, outOfFree sigMap _ (callrFree _ _ op) = sigMap op.
  Proof.
    move=> op.
    cbn. epose (T_bindRet := ord_relmon_law1 T _).
    eapply FunctionalExtensionality.equal_f in T_bindRet.
    cbn in T_bindRet. erewrite T_bindRet.
    reflexivity.
  Qed.

End ufmap_vs_callrFree.
