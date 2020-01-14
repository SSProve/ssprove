(*From Coq Require Export Logic.StrictProp.*)
(*we try not using sprop this time*)
(*we redefine the logical connectives by replacing SProp with
Prop. The name are kept the same*)
From Coq Require PeanoNat.
From Mon Require Import Base.
From mathcomp Require Import ssreflect.
(* Conflicts with Coq.Utf8 and provides the same things *)

Set Primitive Projections.

(********************************************************************)
(**                                                                 *)
(**           This file uses SProp crucially                        *)
(**                                                                 *)
(********************************************************************)
(*hopefully not*)

(* Create HintDb sprop discriminated. *)

(** SProp type formers and notations not present in the stdlib *)

(** Equality in SProp *)

About eq. Print eq.
Definition sEq {A} (x:A) : A -> Prop :=
  fun y => x = y.
(* old sprop equality type :
Inductive sEq {A} (x:A) : A -> SProp :=
  | sEq_refl : sEq x x.
Arguments sEq_refl {_} _.
*)


(** Existential quantification over SProp *)

Definition Ex {A} (P : A -> Prop)  : Prop :=
  ex P.
(* old sprop existential quantifier 
Inductive Ex {A} (P : A -> SProp)  : SProp :=
  | ExIntro : forall x, P x -> Ex P.

Arguments ExIntro {_} _ _.
*)

(** Universal quantifier over SProp *)
Definition All {A} (P : A -> Prop) : Prop := forall (x : A) , P x.

(* old sprop universal quantifier
Definition All {A} (P : A -> SProp) : SProp := forall (x:A), P x.
*)

(** Conjunction *)
Definition sand (P Q : Prop) : Prop := P /\ Q .

(*old sprop and connective 
Inductive sand (P Q : SProp) : SProp := | spair : P -> Q -> sand P Q.


Hint Constructors sand : core.
*)

(** Implication *)

Definition s_impl (P Q : Prop) := P -> Q.
(* old sprop implication connective 
Definition s_impl (P Q : SProp) := P -> Q.
*)

(** Disjunction *)

Definition sor (P Q : Prop) : Prop := P \/ Q.
(* old sprop disjunction connective 
Inductive sor (P Q : SProp) : SProp :=
| sor_introl : P -> sor P Q
| sor_intror : Q -> sor P Q.

Hint Constructors sor : core.
*)

(** If and only if *)

Definition siff (P Q : Prop) := P <-> Q.
(* old sprop iff connective 
Definition siff (P Q:SProp) := sand (P -> Q) (Q -> P).
*)

(** Negation *)

Definition snot (P : Prop) : Prop := ~ P.
(* old sprop negation
Definition snot (P:SProp) : SProp := P -> sEmpty.
*)

(** Well-founded order on natural number *)

About le. Print le.
(*the standard definition of le is a bit different from the sprop variant*)

Inductive Sle : nat -> nat -> Prop :=
| SleZ : forall n, Sle 0 n
| SleS : forall n m, Sle n m -> Sle (S n) (S m).

Lemma Sle_refl : forall m , Sle m m.
Proof.
elim.
  constructor.
move=> n H. constructor. assumption.
Qed.

Lemma Sle_rightmon : forall n m , Sle n m -> Sle n (S m).
Proof. 
move=> n m. elim.
  by move=> n0 ; constructor.
move=> n0 m0 H1 H2. constructor. assumption.
Qed.

Lemma Sle_iff_le : forall m n : nat, Sle m n <-> m <= n.
Proof.
intros m n ; split.
-  elim.
     by move=> n0 ; apply le_0_n.
   clear n m. move=> n m. move=> _ H. apply le_n_S. assumption.
-  elim.
     apply Sle_refl.
   move=> m0 LE SLE. apply Sle_rightmon. assumption.
Qed.

(* old sprop less or equal connective 
Inductive Sle : nat -> nat -> SProp :=
| SleZ : forall n, Sle 0 n
| SleS : forall n m, Sle n m -> Sle (S n) (S m).
*)

Module SPropNotations.
  Notation "x ≡ y" := (@sEq _ x y) (at level 70, no associativity).
  Notation "{ x : A ≫ P }" := (@Ssig A (fun x => P)) (x at level 99).
  Notation "s∃ x .. y , p" :=
    (Ex (fun x => .. (Ex (fun y => p )) .. ))
      (at level 200, x binder, y binder, right associativity).
  Notation "s∀ x .. y , p" :=
    (forall x, .. (forall y, p) ..)
      (at level 200, x binder, y binder, right associativity, only parsing).
  Notation "p s/\ q" := (sand p q) (at level 80).
  Notation "(s->)" := (s_impl) (only parsing).
  Notation "p s\/ q" := (sor p q) (at level 85).
  Notation "P s<-> Q" := (siff P Q) (at level 95).
  Notation "s~ P" := (snot P) (at level 75).

  Notation "n s<= m" := (Sle n m) (at level 70).
  Notation "n s< m" := (Sle (S n)  m) (at level 70).

  Notation "⦑ t ⦒" := (Sexists _ t _).
  Notation " x ∙1" := (Spr1 x) (at level 2).
  Notation " x ∙2" := (Spr2 x) (at level 2).
End SPropNotations.


Section sEqLemmas.
  Import SPropNotations.
  Definition sEq_sym {A} {x y : A} (H : x ≡ y) : y ≡ x.
    induction H. constructor.
  Defined.

  Definition sEq_trans {A} {x y z : A} (H1 : x ≡ y) (H2 : y ≡ z) : x ≡ z.
    induction H1 ; exact H2.
  Defined.

  Lemma eq_to_sEq {A} {x y: A} (H : x = y) : x ≡ y.
  Proof. induction H ; reflexivity. Qed.

  Definition f_sEqual {A B} (f : A -> B) {x y} (H : x ≡ y) : f x ≡ f y.
  Proof. induction H ; constructor. Qed.

  Definition f_sEqual2 {A B} (f1 f2 : A -> B) {x y} (Hf : f1 ≡ f2) (H : x ≡ y) : f1 x ≡ f2 y.
  Proof. induction Hf ; induction H ; constructor. Qed.

  Lemma sEq_to_eq_elim {A} {a a' : A} {p:SProp} :
    (a = a' -> p) -> a ≡ a' -> p.
  Proof.
    intros f H. revert f. induction H. intros f ; apply f ; reflexivity.
  Qed.

  Lemma sEq_to_eq_depelim A  (p:forall a a', a ≡ a' -> SProp) :
    (forall a a' (H : a = a'), p a a' (eq_to_sEq H)) ->
    forall (a a' : A) (H:a ≡ a'), p a a' H.
  Proof.
    intros f a a' H. generalize (f a a'). induction H.
    intros f' ; apply (f' eq_refl).
  Qed.
End sEqLemmas.

Ltac f_sEqual :=
    match goal with
    | [|- sEq (?f1 ?x1) (?f2 ?x2)] =>
      apply (@f_sEqual2 _ _ f1 f2 x1 x2) ; [f_sEqual|]
    | [|- sEq _ _] => try constructor
    end.

(* as a naive substitute to subst *)
Ltac subst_sEq :=
  try repeat match goal with
      | [ H : sEq _ _ |- _] => induction H ; clear H
      end.

Section SsigLemmas.

  Lemma Ssig_eq {A} (P : A -> SProp) :
    forall (mx my : Ssig P), Spr1 mx = Spr1 my -> mx = my.
  Proof.
    intros [cx ex] [cy ey]. simpl.
    induction 1. reflexivity.
  Defined.

  Lemma transport_Ssig :
    forall {A B} (F : B -> A -> SProp) {x y} h z,
      eq_rect x (fun x => Ssig (fun b => F b x)) z y h
      = Sexists _ (Spr1 z) (@eq_sind A x (F (Spr1 z)) (Spr2 z) y h).
  Proof.
    intros.
    dependent inversion h.
    reflexivity.
  Qed.

  Lemma eq_above_Ssig {A B} (F : B -> A -> SProp)
        (G := fun x => Ssig (fun b => F b x)) {x1 x2 : A} {h : x1 = x2}
        {z1 : G x1} {z2 : G x2} :
    Spr1 z1 = Spr1 z2 -> z1 =⟨ h ⟩ z2.
  Proof.
    intro Hz.
    unfold eq_above.
    unfold G.
    rewrite (transport_Ssig F h z1).
    apply Ssig_eq.
    assumption.
  Qed.

End SsigLemmas.

Section SleLemmas.
  Import SPropNotations.
  Import PeanoNat.Nat.
  Lemma sle_lower : forall n k, n s<= k + n.
  Proof.
    induction n. intros ; constructor.
    intros; rewrite add_succ_r ; constructor ; apply IHn.
  Qed.

  Lemma sle_refl : forall n, n s<= n.
  Proof. exact (fun n => sle_lower n 0). Qed.

  Lemma sle_addl : forall n1 n2 k, n1 s<= n2 -> n1 s<= k + n2.
  Proof.
    induction n1. intros ; constructor.
    intros ? ? H.
    inversion H.
    rewrite add_succ_r ; constructor ; apply IHn1 ; assumption.
  Qed.

  Lemma sle_trans : forall n1 n2 n3, n1 s<= n2 -> n2 s<= n3 -> n1 s<= n3.
  Proof.
    intros n1 n2 n3 H12 H23 ; revert n1 H12.
    induction H23.
    intros n1 H. inversion H. constructor.
    intros n1 H. inversion H. constructor.
    constructor. apply IHSle. assumption.
  Qed.
End SleLemmas.

Module SPropAxioms.
  (** Propositional extensionality *)
  Import SPropNotations.

  Axiom sprop_ext : forall {p q : SProp}, p = q <-> Box (sand (p -> q) (q -> p)).


  (** Functional Extensionality *)
  (* Taking the dependent variant as axiom,
    it should be provable from the non-dependent
    one as in the standard library *)
  Axiom funext_sprop : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x ≡ g x) -> f ≡ g.

  Tactic Notation "funext" simple_intropattern(x) :=
    match goal with
      [ |- ?X ≡ ?Y ] => apply (@funext_sprop _ _ X Y) ; intros x
    end.

  Axiom funext_sprop' : forall (A : SProp) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x ≡ g x) -> f ≡ g.

  Tactic Notation "funext_s" simple_intropattern(x) :=
    match goal with
      [ |- ?X ≡ ?Y ] => apply (@funext_sprop' _ _ X Y) ; intros x
    end.
End SPropAxioms.

(** A few surprises (actually makes sense, but still...) *)

Section SPropExamplesAndCounterExamples.

  (* As indicated in the ceps/37 there is no cumulativity *)
  Goal SProp -> Type.
  Proof.
    intro x ; exact x. Fail Qed. (* Universe inconsistency *)
    Restart.
    intro x ; exact (Box x). (* But it works if wrapped (as it should) *)
  Qed.

  (* A dependent pair of a type and a proof it's a subsingleton *)
  Record hprop := { ty : Type ; is_hprop : forall (x y : ty), x = y}.

  (* SProps should be subsingleton (definitionally) *)
  Definition sprop_to_hprop (P : SProp) : hprop.
  Proof.
    (* But trying directly, it fails (P is accepted in Type though...) *)
    exists P. intros. Fail reflexivity.
    Restart.
    (* However it works if we wrap the SProp (but that's quite unconvenient) *)
    exists (Box P); intros [?] [?];  reflexivity.
  Qed.

  (* Here the problem is more visible, P is in SProp, not in Type so the equality is not well formed *)
  Fail Check forall (P : SProp) (x y : P), x = y.

  (* The goal does not typecheck, but Coq still allows me to try to prove it ??? *)
  Goal forall (P : SProp) (x y : P), x = y. Proof. admit. Fail Admitted.
  Abort All.
  
End SPropExamplesAndCounterExamples.
