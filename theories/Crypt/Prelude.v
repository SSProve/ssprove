(* Global utility *)
(* Partly stolen from MetaCoq *)

From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden".
From mathcomp Require Import all_ssreflect word.
Set Warnings "notation-overridden".
From HB Require Import structures.
From extructures Require Import ord fset.
From Equations Require Import Equations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(* Simple products *)

(* Notation "x × y" := (prod x y) (at level 80, right associativity). *)


(* Dependent sums *)

(* Use \sum to input ∑ in Company Coq (it is not a sigma Σ). *)
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").


(* Handy rewrite on sig *)

Lemma sig_rewrite_aux :
  ∀ {T A} {P : A → Prop} {x y} (p : T → A) (h : P (p x)) (e : x = y),
    P (p y).
Proof.
  intros T A P x y p h e. subst. auto.
Defined.

Lemma sig_rewrite :
  ∀ {T A} {P : A → Prop} {x y} (p : T → A) (h : P (p x)) (e : x = y),
    exist _ (p x) h = exist _ (p y) (sig_rewrite_aux p h e).
Proof.
  intros T A P x y p h e. subst. reflexivity.
Qed.

Ltac sig_rewrite e :=
  lazymatch type of e with
  | ?x = _ =>
    match goal with
    | |- context [ exist ?P ?p ?h ] =>
      lazymatch p with
      | context [ x ] =>
        lazymatch eval pattern x in p with
        | (fun x => @?q x) ?y =>
          erewrite (sig_rewrite q _ e)
        end
      end
    end
  end.

(** Tactic sig rewrite

  Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
  a term of the form exist _ u v, specifically inside the term u.
  sig rewrite e will replace x by y in u and update v accordingly.

*)
Tactic Notation "sig" "rewrite" hyp(e) :=
  sig_rewrite e.


(** Tactic falso

  Usage: you have an hyothesis containing a use of [False_rect] at top-level.
  This tactic will take it to close the goal.

*)
Ltac falso :=
  lazymatch goal with
  | |- context [ False_rect _ ?x] => exact (False_rect _ x)
  | h : context [ False_rect _ ?x ] |- _ => exact (False_rect _ x)
  end.


(** mathcomp: derive EqDec for any ordType *)
#[export] Instance ordType_EqDec {A : ordType} : EqDec A.
Proof.
  intros x y. destruct (x == y) eqn:e.
  - move: e => /eqP. auto.
  - move: e => /eqP. auto.
Defined.

Ltac nat_reify :=
  repeat match goal with
  | h : is_true (_ < _) |- _ => move: h => /ltP h
  | h : is_true (_ <= _) |- _ => move: h => /leqP h
  | h : is_true (_ == _) |- _ => move: h => /eqP h
  end.


(** Lt class, for finite types  *)

Class Lt n m :=
  is_in_fin : n < m.

#[export] Hint Extern 1 (Lt ?n ?m) =>
  done : typeclass_instances.

#[export] Hint Extern 2 (Lt ?n ?m) =>
  unfold Lt ; apply/ltP ; lia : typeclass_instances.

#[export] Hint Extern 4 (Lt ?n) =>
  unfold Lt ; apply/ltP ; nat_reify ; lia : typeclass_instances.

#[export] Instance Lt_card_r {n m} : Lt n m → Lt n #|'I_m|.
Proof. by rewrite card_ord. Qed.

#[export] Instance Lt0_expn2 {n} : Lt 0 (2 ^ n).
Proof. by rewrite -prednK_modulus. Qed.

#[export] Instance Lt0_muln {n m} : Lt 0 n → Lt 0 m → Lt 0 (n * m).
Proof. move: n m => [|n] [|m] //. Qed.


(** Hints notation

  When dealing with typeclasses, sometimes automation will fail.
  The purpose of this is to be able to help the automation by providing
  hints without having to write the whole term.

  [hints h1 ; .. ; hn ] will try to solve the goal by having h1 to hn in the
  context. This can be useful to provide lemmata that are not usually picked
  up by the instance mechanism.
  This could also be used in combination with Programs or Equations'
  automation.

  [hints] is also provided for completeness, but is merely long for _.

*)

Declare Scope package_scope.
Delimit Scope package_scope with pack.

(* Hints notation *)
Notation "[ 'hints' ]" :=
  (_)
  (at level 0, only parsing)
  : package_scope.

Notation "[ 'hints' x1 ]" :=
  (let hint := x1 in _)
  (at level 0, only parsing)
  : package_scope.

Notation "[ 'hints' x ; .. ; z ]" :=
  (let hint := x in .. (let hint := z in _) ..)
  (at level 0, only parsing)
  : package_scope.

(* TODO Same as finmap.oextract but with a better name? *)
Definition getSome {A} (o : option A) :
  isSome o → A.
Proof.
  intro h.
  destruct o. 2: discriminate.
  assumption.
Defined.

Definition testSome {A} (P : A → bool) (o : option A) : bool :=
  match o with
  | Some a => P a
  | None => false
  end.
