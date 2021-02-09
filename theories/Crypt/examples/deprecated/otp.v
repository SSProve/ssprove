From Relational Require Import
     OrderEnrichedCategory
     GenericRulesSimple.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     RulesProb
     UniformDistrLemmas
     UniformDistr.

Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.

#[local] Axiom Words : finType.
#[local] Axiom w0 : Words.
#[local] Axiom xorW : Words -> Words -> Words.
#[local] Axiom xorWC : commutative xorW.
#[local] Axiom xorWA : associative xorW.
#[local] Axiom xorW0 : forall w, xorW w w0 = w.
#[local] Axiom xorWK : forall w, xorW w w = w0.

(*Rem. : when adding adversaries we might want also
       uniform distributions over booleans. In this
       case just change the Index to (≈ bool)

       Inductive Index :=
       | word_index : Index
       | bool_index : Index.

 *)

Inductive Index :=
| words_index : Index.

Module WordsParam <:  UniformParameters.

  Definition Index : Type := Index.
  Definition i0 : Index := words_index.
  Definition fin_family : Index -> finType := fun i => match i with words_index => Words end.
  Definition F_w0 : forall i : Index, (fin_family i).
  Proof.
    move => i.
    case: i.
    rewrite /fin_family.
    exact w0.
  Defined.

End WordsParam.

Inductive probEmpty : Type -> Type := .

(*Rem.: probably change this when adding adversaries
      (non necessarily uniform distributions over booleans!)
 *)
Module OtherParam <: ProbRulesParam.

  Definition probE : Type -> Type := probEmpty.

  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes -> choiceType.
  Proof.  move => contra. contradiction. Defined.

  Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
  Proof. move => contra. contradiction. Defined.

  Definition Hch : forall r : rel_choiceTypes, chEmb r.
  Proof. move => contra. contradiction. Defined.

End OtherParam.

Module MyRulesUniform := DerivedRulesUniform OtherParam WordsParam.
Export WordsParam.
Export MyRulesUniform.

Import RulesNotation.

#[local] Definition Dist X := MyRulesUniform.MyRulesU.MFreePr X.

Definition Plain : ord_choiceType := Words.
Definition Cipher : ord_choiceType := Words.
Definition Key : ord_choiceType := Words.

Definition KG  : Dist Key  := (@Uniform_F words_index).

Definition Enc (m : Plain) (k : Key) : Dist Cipher :=
  pure (xorW m k).

Definition Dec (c : Cipher) (k : Key) : Dist Plain :=
  pure (xorW c k).

(* KG; Enc *)
Definition Game (m : Plain) : Dist Cipher :=
  k <- KG ;;
  c <- Enc m k ;;
  pure c.

Definition RND : Dist Cipher := (@Uniform_F words_index).

Lemma xork_xork_eq (k : Words) :
 forall w1 w2, ((fun w => xorW (xorW w k) k) w1 = w2) -> (w1 = w2).
Proof.
  rewrite /= => w1 w2.
  by rewrite -xorWA xorWK xorW0.
Qed.

Lemma bijective_xor_xor (k : Words) : bijective (fun w => xorW (xorW w k) k).
Proof.
  exists (fun w => w); by move => w; rewrite -xorWA xorWK xorW0.
Qed.


Lemma bijective_xor (m : Words) : bijective (fun w => xorW m w).
Proof.
  exists (fun w => xorW m w);
  by move => w'; rewrite xorWA xorWK xorWC xorW0.
Qed.

Definition sampleWord_xor (m : Words) :=
  mkdistr (@bijective_isdistr Words w0 _ (bijective_xor m)).


Lemma id_bijective : bijective (fun w : Words => w).
Proof.
  by exists (fun w => w).
Qed.

Lemma dunit_gt0_eq {A : ord_choiceType} (x y : A) :
  (SDistr_unit _ x) y > 0 -> y = x.
Proof.
  rewrite /SDistr_unit dunit1E.
  case (x == y) eqn:Heq.
  - move: Heq. by move/eqP.
  - by rewrite (ltrr 0).
Qed.

Theorem secrecy (m : Plain) : ⊨ ⦃ True ⦄ (Game m) ≈ RND ⦃ eq ⦄.
Proof.
  rewrite /(Game m) /RND.
  eapply (seq_rule_ch KG RND True (fun a1 a2 => xorW m a1 == a2) eq).
  - by apply (@Uniform_bij_rule words_index _ (bijective_xor m)).
  - move => k c.
    apply: pre_hypothesis_rule_ch => Heq.
    move/eqP: Heq => Heq.
    rewrite -Heq.
    apply: MyRulesU.sample_rule_ch.
    by apply: SDistr_unit_F_choice_prod_coupling.
    move => c1 c2 Hpr.
    move: (dunit_gt0_eq _ _ Hpr).
    move => [H1 H2].
    by subst.
Qed.

