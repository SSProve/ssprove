From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures SpecificationMonads.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.

Set Primitive Projections.
Set Universe Polymorphism.

Section RelatorOverAMonad.
  Context (M : Monad).
  Import SPropNotations.


  (* Definitions and notations to manipulate SProp valued
     heterogeneous relations *)
  Definition rel A B := A -> B -> SProp.
  Notation "A ⇸ B" := (rel A B) (at level 50).
  Definition IdRel A : srelation A := eq.
  Definition CompRel {A1 A2 A3} (R : A1 ⇸ A2) (S: A2 ⇸ A3) : A1 ⇸ A3 :=
    fun a1 a3 => exists a2, R a1 a2 /\ S a2 a3.
  Notation "R # S" := (CompRel R S) (at level 60).

  Definition subRel {A1 A2} (R S : A1 ⇸ A2) :=
    forall a1 a2, R a1 a2 -> S a1 a2.
  Definition rel_equiv {A1 A2} (R S : A1 ⇸ A2) := forall a1 a2, R a1 a2 <-> S a1 a2.
  Notation "R ≅ S" := (rel_equiv R S) (at level 60).
  Notation "R ⊂ S" := (subRel R S) (at level 65).

  Definition rel_pb {A1 A2 B1 B2} (f1 : A1 -> B1) (f2 : A2 -> B2) (R : B1 ⇸ B2)
    : A1 ⇸ A2
    := fun a1 a2 => R (f1 a1) (f2 a2).


  (* Definition of a relator over M
     Inspired from the definition in "Effectful
     Applicative Bisimilarity: Monads, Relators, and Howe’s Method" by Dal Lago, Gavazzo, Levy
     Wrt the paper we directly define a relator over a monad rather than
     over an endofunctor and we show below that the same law are satisified.
   *)
  Record relator :=
    mkRelator
      { relator_carrier : forall {A1 A2}, (A1 ⇸ A2) -> (M A1 ⇸ M A2)
      ; relator_ret : forall {A1 A2} (R: A1 ⇸ A2) a1 a2,
          (* R ⊂ rel_pb ret ret (relator_carrier R) *)
          R a1 a2 -> relator_carrier R (ret a1) (ret a2)
      ; relator_bind : forall {A1 A2 B1 B2} (R: A1 ⇸ A2) (S : B1 ⇸ B2)
                         m1 m2 f1 f2,
          (* (R ⊂ rel_pb f1 f2 (relator_carrier S)) -> *)
          (* relator_carrier R ⊂ rel_pb (bind^~ f1) (bind^~ f2) (relator_carrier S) *)
          relator_carrier R m1 m2 ->
          (forall a1 a2, R a1 a2 -> relator_carrier S (f1 a1) (f2 a2)) ->
          relator_carrier S (bind m1 f1) (bind m2 f2)
      ; relator_law1 : forall {A}, relator_carrier (IdRel A) ⊂ IdRel (M A)
      ; relator_law2 : forall {A1 A2 A3} (R : A1 ⇸ A2) (S : A2 ⇸ A3),
          relator_carrier R # relator_carrier S ⊂ relator_carrier (R # S)
      ; relator_law3 :
          forall {A1 A2 B1 B2} (f1 : A1 -> B1) (f2 : A2 -> B2) (R : B1 ⇸ B2),
            rel_pb (map f1) (map f2) (relator_carrier R) ⊂ relator_carrier (rel_pb f1 f2 R)
      }.

  Notation "Γ @ R" := (relator_carrier Γ R) (at level 10).

  Lemma relator_map (Γ : relator) {A1 A2 B1 B2}
        (R : A1 ⇸ A2) (S : B1 ⇸ B2) f1 f2 :
    (forall a1 a2, R a1 a2 -> S (f1 a1) (f2 a2)) ->
    forall m1 m2, Γ@R m1 m2 -> Γ@S (f1 <$> m1) (f2 <$> m2).
  Proof.
    move=> Hf m1 m2 Hm. apply (relator_bind _ _ _ _ _ _ _ Hm).
    move=> a1 a2 Ha ; apply relator_ret, Hf, Ha.
  Qed.

  Lemma relator_monotonic (Γ:relator) {A1 A2} (R S : A1 ⇸ A2) :
    R ⊂ S -> Γ@R ⊂ Γ@S.
  Proof.
    move=> H m1 m2; move: (relator_map Γ R S id id H m1 m2) ; rewrite !map_id //.
  Qed.

  Lemma relator_pb (Γ:relator)
        {A1 A2 B1 B2} (f1 : A1 -> B1) (f2 : A2 -> B2) (R : B1 ⇸ B2) :
    Γ@(rel_pb f1 f2 R) ≅ rel_pb (map f1) (map f2) (Γ@R).
  Proof.
    move=> m1 m2 ; split.
    apply relator_map=> //.
    apply relator_law3.
  Qed.
End RelatorOverAMonad.

Module RelatorNotations.
  Notation "A ⇸ B" := (rel A B) (at level 50).
  Notation "R # S" := (CompRel R S) (at level 60).
  Notation "R ≅ S" := (rel_equiv R S) (at level 60).
  Notation "R ⊂ S" := (subRel R S) (at level 65).
  Notation "Γ @ R" := (relator_carrier _ Γ R) (at level 10).
End RelatorNotations.

Section RelationalLaxEffectObservationFromRelator.
  Context (M : Monad) (Γ : relator M).

  Definition Wrel := Wrel MonoContSProp.

  Import SPropNotations.
  Import RelatorNotations.

  Program Let rleo_carrier (A:TypeCatSq) : M (nfst A) × M (nsnd A) --> Wrel A :=
    fun a => ⦑fun p => Γ@(fun a1 a2 => p ⟨a1, a2⟩) (nfst a) (nsnd a)⦒.
  Next Obligation.
    move=> ? ? H; apply: relator_monotonic=> ? ? ; apply: H.
  Qed.

  (* A relator Γ over M induces a lax relational effect observation
     from M,M to Wrel *)
  Program Definition rleo_from_relator :=
    mkRLEO0 M M Wrel (fun A => to_discr (rleo_carrier A)) _ _.
  Next Obligation.
    cbv=> p. apply: relator_ret.
  Qed.
  Next Obligation.
    move: x f=> [m1 m2] [f1 f2].
    cbv -[bind] => p H.
    apply: relator_bind; first apply: H.
    cbv=> //.
  Qed.

End RelationalLaxEffectObservationFromRelator.
