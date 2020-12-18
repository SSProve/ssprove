From Relational Require Import OrderEnrichedCategory.

(*In this file we devise a relative monad morphism Id -> M having the unit of M as carrier*)


Section InitialMonad.
  Notation η N := (ord_relmon_unit N).
  Notation dnib N := (ord_relmon_bind N).

(*First we remark that J is a J-relative monad*)
  Context {I C : ord_category}
          {J : ord_functor I C}.


  Program Definition initRmon : ord_relativeMonad J :=
    mkOrdRelativeMonad J _ _ _ _ _ _.
  Next Obligation.
    apply Id.
  Defined.
  Next Obligation.
    cbv. rewrite ord_cat_law2. reflexivity.
  Qed.

(*And J is in fact initial *)
  Context (M : ord_relativeMonad J).

  Definition trivialPhi :
  natIso J (ord_functor_comp J (ord_functor_id C)) :=
    natIso_sym (ord_functor_unit_right J).

  Program Definition etaAsRmm : 
  relativeMonadMorphism _ trivialPhi initRmon M :=
    mkRelMonMorph (ord_functor_id C) trivialPhi initRmon M _ _ _.
  Next Obligation.
    apply (η M).
  Defined.
  Next Obligation.
    cbv. rewrite ord_cat_law2. rewrite ord_relmon_law2.
    reflexivity.
  Qed.

End InitialMonad.
