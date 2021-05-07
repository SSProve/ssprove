From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase FiniteProbabilities.
From Coq Require Import RelationClasses Morphisms.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From Crypt Require Import Axioms ChoiceAsOrd only_prob.SubDistr Couplings.

Import SPropNotations.
Import Num.Theory.

Local Open Scope ring_scope.


Definition nonZer {A : choiceType} (d : SDistr A) : Prop :=
  exists (a:A), d a != 0.


Section Couplings_vs_bind.
  Context {A0 A1 B0 B1 : ord_choiceType}.

  Context (c0 : SDistr A0) (f0 : TypeCat ⦅ choice_incl A0 ; SDistr B0⦆ )
          (c1 : SDistr A1) (f1 : TypeCat ⦅ choice_incl A1 ; SDistr B1⦆).

  Context (dA : SDistr ( F_choice_prod (npair A0 A1) ) ) (dA_coup : coupling dA c0 c1).

  Context (kd : TypeCat ⦅ choice_incl (F_choice_prod (npair A0 A1)) ;
                          SDistr (F_choice_prod( npair B0 B1)) ⦆).
  Context (kd_pcoup : forall (x0 : A0) (x1 : A1),
      (dA (x0, x1) > 0) = true ->
      nonZer (f0 x0) /\ nonZer (f1 x1) ->
      coupling (kd (x0,x1)) (f0 x0) (f1 x1)  ).

  Lemma coupling_vs_bind :
  coupling (SDistr_bind (F_choice_prod(npair A0 A1)) (F_choice_prod(npair B0 B1)) kd dA)
           (SDistr_bind A0 B0 f0 c0) (SDistr_bind A1 B1 f1 c1).
  Proof.
    split.
    {
     rewrite /lmg /SDistr_bind. unfold dfst.
     move: dA_coup. rewrite /coupling /lmg. move=> [H0 H1].
     rewrite -H0. unfold dfst.
     apply distr_ext. move=> b0 ; cbn.
     rewrite (dlet_dlet kd (fun x => dunit x.1) dA). rewrite (dlet_dlet _ _ dA).
     apply (@eq_in_dlet _ _ _). move=> [x0 x1] Hsupp b1.
     rewrite dlet_unit /=. 
     specialize (kd_pcoup x0 x1).
     assert ( bla : (0 < dA (x0, x1)) = true ).
       { apply msupp. assumption. }
     apply kd_pcoup in bla. move: bla => [bla0 bla1].
     move: bla0. rewrite /lmg. unfold dfst.
     move=> bla0. rewrite bla0. reflexivity.
       {

(*   Proof. split. *)
(*          -  unfold lmg. *)
(*             unfold SDistr_bind. *)
(*             unfold dfst. *)
(*             move: dA_coup. *)
(*             rewrite /coupling /lmg. *)
(*             intros [H1 H2]. *)
(*             rewrite <- H1. *)
(*             unfold dfst. *)
(*             apply distr_ext. intro b. *)
(*             rewrite (dlet_dlet kd (fun x => dunit x.1) dA). *)
(*             rewrite (dlet_dlet _ _ dA). *)
(*             apply (@eq_in_dlet _ _ _). *)
(*             move => x12 Hsupp b2. *)
(*             destruct x12. *)
(*             simpl. rewrite (dlet_unit). *)
(*             assert (0 < dA (s, s0) = true). *)
(*             apply msupp. assumption. *)
(*             specialize (kd_pcoup s s0 H). *)
(*             unfold coupling in kd_pcoup. destruct kd_pcoup. *)
(*             unfold lmg in H0. unfold dfst in H0. *)
(*             rewrite H0. reflexivity. *)
(*             intro x. reflexivity. *)
(*          -  unfold rmg. *)
(*             unfold SDistr_bind. *)
(*             unfold dfst. *)
(*             move: dA_coup. *)
(*             rewrite /coupling /lmg. *)
(*             intros [H1 H2]. *)
(*             rewrite <- H2. *)
(*             unfold dfst. *)
(*             apply distr_ext. intro b. *)
(*             rewrite (dlet_dlet kd (fun x => dunit x.2) dA). *)
(*             rewrite (dlet_dlet _ _ dA). *)
(*             apply (@eq_in_dlet _ _ _). *)
(*             move => x12 Hsupp b2. *)
(*             destruct x12. *)
(*             simpl. rewrite (dlet_unit). *)
(*             assert (0 < dA (s, s0) = true). *)
(*             apply msupp. assumption. *)
(*             specialize (kd_pcoup s s0 H). *)
(*             unfold coupling in kd_pcoup. destruct kd_pcoup. *)
(*             unfold rmg in H3. unfold dfst in H3. *)
(*             rewrite H3. reflexivity. *)
(*             intro x. reflexivity. *)
(* Qed. *)
