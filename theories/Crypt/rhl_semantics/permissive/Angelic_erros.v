From Mon Require Import SpecificationMonads SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd Axioms FreeProbProg SubDistr Theta_exCP.
From mathcomp Require Import all_ssreflect.


Ltac my_unfolding :=
    rewrite /Morphisms.Proper /Morphisms.respectful ;
    rewrite /MonoCont_order /Morphisms.pointwise_relation ;
    rewrite /SPropMonadicStructures.SProp_op_order ;
    rewrite /Basics.flip ;
    rewrite /SPropMonadicStructures.SProp_order.

(* Section Error_rMonad. *)

(* (* *)
(*   Cumulative Record ord_relativeMonad := *)
(*     mkOrdRelativeMonad *)
(* *) *)

(* Inductive ERR_OP := *)
(* | err_op : ERR_OP. *)

(* Definition ERR_AR : ERR_OP -> choiceType := fun op => match op with *)
(*   | err_op => void_choiceType *)
(*   end. *)

(* Definition ErrM :=  rFree ERR_OP ERR_AR. *)

(* Definition ErrM_squ := product_rmon ErrM ErrM. *)


(* End Error_rMonad. *)


Section Error_rMonad.

  Inductive Err_M_carrier (A : choiceType) :=
  | just : A -> Err_M_carrier A
  | nope : Err_M_carrier A.

  Arguments just {_}.
  Arguments nope {_}.

  Program Definition Err_M : ord_relativeMonad choice_incl :=
  mkOrdRelativeMonad Err_M_carrier _ _ _ _ _ _.
  Next Obligation.
    move=> A a /=. exact (just a).
  Defined.
  Next Obligation.
    move=> A B f m. move: m => [a |].
    - exact (just (f a)).
    - exact nope.


Section Clean_base_morphism.

(*
About ϕ θ_morph
ϕ uses the v functions of Theta_exCP.v which destruct choiceTypes.
we redefine phi here so that it has a better behaviour
*)

Program Definition cleanϕ : natIso
    (ord_functor_comp F_choice_prod chDiscr)
    (ord_functor_comp (prod_functor choice_incl choice_incl) Jprod) :=
  mkNatIso _ _ _ _ _ _ _.
  Next Obligation.
    move=> [A0 A1] ; cbn. unshelve econstructor.
    move=> [a0 a1]. exact ⟨a0 , a1⟩.
    cbn. rewrite /Morphisms.Proper /Morphisms.respectful.
    move=> [a0 a1] [a0' a1']. move=> [H0 H1].
    rewrite H0 H1. reflexivity.
  Defined.
  Next Obligation.
    move=> [A0 A1]. cbn. unshelve econstructor.
    move=> [a0 a1]. exact (a0 , a1). cbn.
    move=> [a0 a1] [a0' a1']. move=> [H0 H1].
    rewrite H0 H1. reflexivity.
  Defined.
  Next Obligation.
    move=> [A0 A1] [B0 B1] /= [f0 f1].
    apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A0 A1]. apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.
  Next Obligation.
    move=> [A0 A1]. apply sig_eq ; cbn. apply boolp.funext ; move=> [a0 a1] ; cbn.
    reflexivity.
  Qed.


End Clean_base_morphism.

Section Angelic_theta.

  Program Definition θ_ang_carrier :
  forall A : choiceType × choiceType,
  {f
  : rFreeF ERR_OP ERR_AR (nfst A) × rFreeF ERR_OP ERR_AR (nsnd A) ->
    MonoContCarrier SPropMonadicStructures.SProp_op_order (nfst A * nsnd A)
  | Morphisms.Proper
      (Morphisms.respectful eq
         (MonoCont_order (Rrel:=SPropMonadicStructures.SProp_op_order) (A:=nfst A * nsnd A))) f} := fun A => exist _ _ _.
  Next Obligation.
    move=> [A0 A1]. cbn.


  Program Definition θ_ang: relativeLaxMonadMorphism Jprod cleanϕ ErrM_squ WRelProp :=
    mkRelLaxMonMorph _ _ _ _ _ _ _.
  Next Obligation.
    
