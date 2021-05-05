From Mon Require Import SpecificationMonads SPropBase.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
From Crypt Require Import ChoiceAsOrd SubDistr Theta_exCP Axioms Couplings.
From mathcomp Require Import all_ssreflect distr all_algebra reals.

Import SPropNotations.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(*
In this file we define a relational effect observation
SD² → BP  (where BP is the relational specification monad
of backward predicate transformer, ie
  BP( A0 , A1 ) := (A0 × A1 → Prop) → Prop

The defined semantics should be more permissive than
the one defined in ThetaDex.v in the sense that
null subdistributions will always be related to anything else
*)

Section Monotonic_spec.

  Context {A0 A1 : ord_choiceType}.
  Context ( w : Base.dfst (WRelProp ⟨ A0 , A1 ⟩) ).

  Goal True.
    cbn in w.
    unfold SPropMonadicStructures.SProp_op_order in w.
    unfold Basics.flip in w.
    unfold SPropMonadicStructures.SProp_order in w.
  Abort.

  Lemma monotonic_spec : forall (post post' : A0 * A1 -> Prop), 
  (forall a01 : A0 * A1, post' a01 -> post a01) ->
  w∙1 post' -> w∙1 post.
  Proof.
    move=> post post'. move=> Hpost.
    destruct w as [wmap wprop]. cbn.
    move: wprop.
    rewrite /Morphisms.Proper /Morphisms.respectful.
    rewrite /Morphisms.pointwise_relation. 
    rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip.
    rewrite /SPropMonadicStructures.SProp_order.    
    move=> wprop.
    apply wprop. assumption.
  Qed.

End Monotonic_spec.


Section Permissive_theta'.

(* Below our COMPUTATIONAL MONADs. Two subdistribution monads*)

(* About SDistr_squ. *)


(* Below our relational SPECIFICATION MONAD (backward predicates) *)

(* About WRelProp. *)

(*
the old, "demonic" (non permissive with respect to asserts) semantic
About θ_morph
relativeLaxMonadMorphism Jprod ϕ SDistr_squ WRelProp
*)

(*
I wanted to use the definition of the standard "harsh" semantics
but it behaves badly (definition destructs choiceTypes at hand for no reason,
and proofs based on it have to destruct those choiceTypes which creates confusion)
*)

(*   Program Definition θ_perm' : relativeLaxMonadMorphism Jprod ϕ SDistr_squ WRelProp := *)
(*     mkRelMonMorph _ _ _ _ _ _ _. *)
(*   Next Obligation. *)
(*     move=> [A0 A1]. cbn. *)
(*     unshelve econstructor. move=> [c0 c1]. *)
(*     unshelve econstructor. move=> post. *)
(*     exact ( ( c0 <> dnull  /\ c1 <> dnull  ) -> *)
(*             ( (θ_morph ⟨ A0 , A1 ⟩)∙1 ⟨c0,c1⟩)∙1 post ). *)
(*     1:{ *)
(*       cbn. move=> post post'. *)
(*       rewrite /Morphisms.pointwise_relation.  *)
(*       rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip. *)
(*       rewrite /SPropMonadicStructures.SProp_order. *)
(*       move=> Hpost thing. *)
(*       move=> Hzer. apply thing in Hzer. (* theta is monotonic *) *)
(*       unshelve eapply monotonic_spec. *)
(*         exact post'. assumption. assumption. } *)
(*     1:{ *)
(*       cbn. *)
(*       rewrite /Morphisms.Proper /Morphisms.respectful. *)
(*       rewrite /Morphisms.pointwise_relation.  *)
(*       rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip. *)
(*       rewrite /SPropMonadicStructures.SProp_order. *)
(*       move=> [c0 c1] [c0' c1']. move=> [H0 H1]. *)
(*       rewrite /MonoCont_order /Morphisms.pointwise_relation //. *)
(*       move=> post. cbn. rewrite H0 H1. by easy. } *)
(*   Defined. *)
(*   Next Obligation. *)
(*     move=> [[A0 chA0][A1 chA1]]. apply sig_eq. cbn. apply boolp.funext ; move=> a01 ; cbn. *)
(*     apply sig_eq ; cbn. apply boolp.funext ; move=> post ; cbn. *)
(*     rewrite /SubDistr.SDistr_obligation_1. *)
(*     assert ( truePrem : *)
(*    ( SDistr_unit (Choice.Pack chA0) (nfst a01) <> dnull /\ *)
(*    SDistr_unit (Choice.Pack chA1) (nsnd a01) <> dnull ) *)
(*                                                  = *)
(*     True). *)
(*     { admit. } *)
(*     { rewrite truePrem. *)
(*       assert ( TrueImpl : forall (Q : Prop), (True -> Q) = Q ). *)
(*       { move=> Q. apply boolp.propext. split. *)
(*         - move=> HTQ. apply HTQ. by easy. *)
(*         - move=> HQ. move=> _. assumption. } *)
(*       rewrite TrueImpl. *)
(*       unshelve etransitivity. *)
(*         exact *)
(* (( (θ_morph ⟨ (Choice.Pack chA0) , (Choice.Pack chA1) ⟩)∙1 *)
(* ⟨ SDistr_unit (Choice.Pack chA0) (nfst a01)  , SDistr_unit (Choice.Pack chA1) (nsnd a01)  ⟩ )∙1 *)
(* post ). *)
(*      { cbn. reflexivity. } *)
(*      { pose rlmm_unit :=  (rlmm_law1 _ _ _ _ θ_morph) *)
(*        ⟨ Choice.Pack chA0 , Choice.Pack chA1 ⟩ a01. *)
(*       cbn in rlmm_unit. *)
(*       move: rlmm_unit. *)
(*       rewrite /MonoCont_order. *)
(*       rewrite /Morphisms.pointwise_relation.  *)
(*       rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip. *)
(*       rewrite /SPropMonadicStructures.SProp_order. *)
(*       move=> rlmm_unit. specialize (rlmm_unit post). *)
(*   Abort. *)
        

End Permissive_theta'.

Section NonNullDistr.

  Context {A : choiceType}.


  Definition nonZer (d : SDistr A) : Prop :=
    exists (a:A), d a != 0.

  Lemma nonZer_dnull : forall d, nonZer d -> d <> dnull.
  Proof.
    move=> d Hd. move=> Heq. move: Hd. rewrite /nonZer.
    move=> [a0 prf]. move: prf => /eqP. move=> prf. apply prf.
    rewrite Heq. rewrite dnullE. reflexivity.
  Qed.

  Lemma dnull_nonZer : forall d, d <> dnull -> nonZer d.
  Proof.
    move=> d. move=> Hneq.
  Abort.

End NonNullDistr.


Section Permissive_theta.

  Program Definition θ_perm_carrier :
  forall (A0 A1 : choiceType),
  {f
  : SDistr_carrier A0 × SDistr_carrier A1 ->
    MonoContCarrier SPropMonadicStructures.SProp_op_order (A0 * A1)
  | Morphisms.Proper
      (Morphisms.respectful eq
         (MonoCont_order (Rrel:=SPropMonadicStructures.SProp_op_order) (A:=A0 * A1))) f} :=
    fun A0 A1 => exist _ _ _.
  Next Obligation.
    move=> A0 A1. move=> [c0 c1].
    rewrite /MonoContCarrier. unshelve econstructor.
    move=> post.
    exact (
      nonZer c0 /\ nonZer c1 -> 
      exists d, (coupling d c0 c1)  /\
      (forall (a0 : A0) (a1 : A1), (d (a0, a1)) > 0 -> post (a0, a1)) ).
    {
      rewrite /Morphisms.Proper /Morphisms.respectful.
      rewrite /Morphisms.pointwise_relation.
      rewrite /SPropMonadicStructures.SProp_op_order /Basics.flip.
      rewrite /SPropMonadicStructures.SProp_order.
      move=> post post'. move=> Hpost.
  Abort.
    

  Program Definition θ_perm: relativeLaxMonadMorphism Jprod ϕ SDistr_squ WRelProp :=
    mkRelMonMorph _ _ _ _ _ _ _.
  Next Obligation.
    move=> [A0 A1]. cbn.
    unshelve econstructor. move=> [c0 c1].
    unshelve econstructor. move=> post.
  Abort.
