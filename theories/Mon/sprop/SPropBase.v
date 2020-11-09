(*From Coq Require Export Logic.StrictProp.*)
(*we try not using sprop this time*)
(*we redefine the logical connectives by replacing Prop with
Prop. The name are kept the same*)
From Coq Require PeanoNat.
From Mon Require Import Base.
From mathcomp Require Import ssreflect.
(* Conflicts with Coq.Utf8 and provides the same things *)

From Coq Require ClassicalFacts.

Axiom ax_proof_irrel : ClassicalFacts.proof_irrelevance.

Set Primitive Projections.

Module Redefined_sprop_constructs.
(*not all redefinitions Prop -> Prop are provided in this module
planning to put them all here
*)

Record Box (A:Prop) : Prop := box { unbox : A }.

End Redefined_sprop_constructs.
Export Redefined_sprop_constructs.

(** Conjunction *)
Definition sand := and.

Module SPropNotations.
  Notation "p s/\ q" := (and p q) (at level 80).

  Notation "⦑ t ⦒" := (exist _ t _).

  Notation " x ∙1" := (proj1_sig x) (at level 2).
  Notation " x ∙2" := (proj2_sig x) (at level 2).
End SPropNotations.

Section sigLemmas.

  Lemma sig_eq {A} (P : A -> Prop) :
    forall (mx my : sig P), proj1_sig mx = proj1_sig my -> mx = my.
  Proof.
    intros [cx ex] [cy ey]. simpl.
    induction 1.
    have hintUnif : ex = ey.
      by apply ax_proof_irrel.
    rewrite hintUnif. reflexivity.
  Defined.

  Lemma transport_sig :
    forall {A B} (F : B -> A -> Prop) {x y} h z,
      eq_rect x (fun x => sig (fun b => F b x)) z y h
      = exist _ (proj1_sig z) (@eq_ind A x (F (proj1_sig z)) (proj2_sig z) y h).
  Proof.
    intros.
    dependent inversion h. compute. destruct z. reflexivity.
  Qed.

  Lemma eq_above_sig {A B} (F : B -> A -> Prop)
        (G := fun x => sig (fun b => F b x)) {x1 x2 : A} {h : x1 = x2}
        {z1 : G x1} {z2 : G x2} :
    proj1_sig z1 = proj1_sig z2 -> z1 =⟨ h ⟩ z2.
  Proof.
    intro Hz.
    unfold eq_above.
    unfold G.
    rewrite (transport_sig F h z1).
    apply sig_eq.
    assumption.
  Qed.

End sigLemmas.

Module SPropAxioms.
  (** Propositional extensionality *)
  Import SPropNotations.

  Axiom sprop_ext : forall {p q : Prop}, p = q <-> Box (sand (p -> q) (q -> p)).
End SPropAxioms.

