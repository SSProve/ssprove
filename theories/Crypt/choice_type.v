(**
  This file defines an inductive type [choice_type] corresponding to codes for
  choice types.
  We give a total order on this type, which is then used to show that
  [choice_type] forms a [choiceType].
 *)


From Coq Require Import Utf8.

(* !!! Import before mathcomp, to avoid overriding instances !!! *)
(* specifically, importing after mathcomp results in conflicting instances for
   Z_choiceType. *)
From deriving Require Import deriving.

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ word.
(*From mathcomp Require Import word_ssrZ word.*)
(* From Jasmin Require Import utils word. *)
From SSProve.Crypt Require Import jasmin_word jasmin_util.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From HB Require Import structures.

From SSProve.Crypt Require Import Prelude Axioms Casts.
From extructures Require Import ord fset fmap.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.

Inductive choice_type :=
| chUnit
| chNat
| chInt
| chBool
| chProd (A B : choice_type)
| chMap (A B : choice_type)
| chOption (A : choice_type)
| chFin (n : positive)
| chWord (nbits : wsize)
| chList (A : choice_type)
| chSum (A B : choice_type).

Derive NoConfusion NoConfusionHom for choice_type.


(* Types T that may be represented by the interpretation of
   a choice_type A are given an instance of hasInterp.  *)
HB.mixin Record hasInterp (A : choice_type) T := { }.

HB.structure Definition Crypt (A : choice_type)
  := { T of Countable T & Ord.Ord T & hasInterp A T }.

HB.instance Definition _
  := hasInterp.Build chUnit unit.

HB.instance Definition _
  := hasInterp.Build chNat nat.

HB.instance Definition _
  := hasInterp.Build chInt BinInt.Z.

HB.instance Definition _
  := hasInterp.Build chBool bool.

HB.instance Definition _ (A B : choice_type)
  (T : Crypt.type A) (S : Crypt.type B)
  := hasInterp.Build (chProd A B) (T * S)%type.

HB.instance Definition _ (A B : choice_type)
  (T : Crypt.type A) (S : Crypt.type B) :=
  @CanIsCountable _ {fmap T → S} _ _ (@fmvalK T S).

HB.instance Definition _ (A B : choice_type)
  (T : Crypt.type A) (S : Crypt.type B)
  := hasInterp.Build (chMap A B) {fmap T → S}.

HB.instance Definition _ (A : choice_type) (T : Crypt.type A)
  := hasInterp.Build (chOption A) (option T).

HB.instance Definition _ n
  := hasInterp.Build (chFin n) (ordinal n.(pos)).

#[non_forgetful_inheritance]
HB.instance Definition _ nbits
  := hasInterp.Build (chWord nbits) (word nbits).

HB.instance Definition _ (A : choice_type) (T : Crypt.type A)
  := hasInterp.Build (chList A) (list T).

HB.instance Definition _ (A B : choice_type)
  (T : Crypt.type A) (S : Crypt.type B)
  := hasInterp.Build (chSum A B) (T + S)%type.

Fixpoint chInterp (U : choice_type) : Crypt.type U :=
  match U with
  | chUnit => unit
  | chNat => nat
  | chInt => BinInt.Z
  | chBool => bool
  | chProd u v => (chInterp u * chInterp v)%type
  | chMap u v => {fmap chInterp u → chInterp v}
  | chOption u => option (chInterp u)
  | chFin n => ordinal n.(pos)
  | chWord nbits => word nbits
  | chList u => list (chInterp u)
  | chSum u v => (chInterp u + chInterp v)%type
  end.

(* When a Crypt.type is found for an arbitrary type, the
   parameter U remembers how to construct a corresponding
   choice_type. This allows us to use this coercion in reverse. *)
#[reversible] Coercion chInterp : choice_type >-> Crypt.type.

(* Canonical element in a type of the choice_type *)
#[program] Fixpoint chCanonical (T : choice_type) : T :=
  match T with
  | chUnit => tt
  | chNat => 0
  | chInt => 0
  | chBool => false
  | chProd A B => (chCanonical A, chCanonical B)
  | chMap A B => emptym
  | chOption A => None
  | chFin n => Ordinal n.(cond_pos)
  | chWord nbits => word0
  | chList A => [::]
  | chSum A B => inl (chCanonical A)
  end.

Definition coerce {A B : choice_type} : A → B
  := λ x, odflt (chCanonical B) (unpickle (pickle x)).

Lemma coerceE {A : choice_type} (a : A) : coerce a = a.
Proof. rewrite /coerce pickleK //. Qed.
