(** Invariants on state

  These can be very useful when proving program equivalences.
*)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_lookup pkg_advantage.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, who knows why. *)
From Crypt Require Import FreeProbProg.

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(** Uniform distributions  *)

Definition uniform (i : nat) `{Positive i} : Op :=
  existT _ ('fin i) (Uni_W (mkpos i)).

(** Some bijections

  These are useful when working with uniform distributions that can only
  land in 'fin n.

  TODO: Move? In Prelude?

*)

Definition fto {F : finType} : F → 'I_#|F|.
Proof.
  intro x. eapply enum_rank. auto.
Defined.

Definition otf {F : finType} : 'I_#|F| → F.
Proof.
  intro x. eapply enum_val. exact x.
Defined.

Lemma fto_otf :
  ∀ {F} x, fto (F := F) (otf x) = x.
Proof.
  intros F x.
  unfold fto, otf.
  apply enum_valK.
Qed.

Lemma otf_fto :
  ∀ {F} x, otf (F := F) (fto x) = x.
Proof.
  intros F x.
  unfold fto, otf.
  apply enum_rankK.
Qed.

Lemma card_prod_iprod :
  ∀ i j,
    #|Datatypes_prod__canonical__fintype_Finite (fintype_ordinal__canonical__fintype_Finite i) (fintype_ordinal__canonical__fintype_Finite j)| = (i * j)%N.
Proof.
  intros i j.
  rewrite card_prod. simpl. rewrite !card_ord. reflexivity.
Qed.

Definition ch2prod {i j} `{Positive i} `{Positive j}
  (x : Arit (uniform (i * j))) :
  Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j)).
Proof.
  simpl in *.
  eapply otf. rewrite card_prod_iprod.
  auto.
Defined.

Definition prod2ch {i j} `{Positive i} `{Positive j}
  (x : Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j))) :
  Arit (uniform (i * j)).
Proof.
  simpl in *.
  rewrite -card_prod_iprod.
  eapply fto.
  auto.
Defined.

Definition ch2prod_prod2ch :
  ∀ {i j} `{Positive i} `{Positive j}
    (x : Datatypes_prod__canonical__fintype_Finite (Arit (uniform i)) (Arit (uniform j))),
    ch2prod (prod2ch x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite -[RHS]otf_fto. f_equal.
  rewrite rew_opp_l. reflexivity.
Qed.

Definition prod2ch_ch2prod :
  ∀ {i j} `{Positive i} `{Positive j} (x : Arit (uniform (i * j))),
    prod2ch (ch2prod x) = x.
Proof.
  intros i j hi hj x.
  unfold ch2prod, prod2ch.
  rewrite fto_otf.
  rewrite rew_opp_r. reflexivity.
Qed.

Lemma repr_Uniform :
  ∀ i `{Positive i},
    repr (x ← sample uniform i ;; ret x) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma repr_cmd_Uniform :
  ∀ i `{Positive i},
    repr_cmd (cmd_sample (uniform i)) = @Uniform_F (mkpos i) _.
Proof.
  intros i hi. reflexivity.
Qed.

Lemma ordinal_finType_inhabited :
  ∀ i `{Positive i}, fintype_ordinal__canonical__fintype_Finite i.
Proof.
  intros i hi.
  exists 0%N. auto.
Qed.

(** Fail and Assert *)

(* fail at any type in the choice_type *)
Definition fail {A : choice_type} : raw_code A :=
  x ← sample (A ; dnull) ;; ret x.

Definition assert b : raw_code 'unit :=
  if b then ret Datatypes.tt else @fail 'unit.

(* Dependent version of assert *)
Definition assertD {A : choice_type} b (k : b = true → raw_code A) : raw_code A :=
  (if b as b' return b = b' → raw_code A then k else λ _, fail) erefl.

Lemma valid_fail :
  ∀ A L I, valid_code L I (@fail A).
Proof.
  intros A L I. unfold fail. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I fail) =>
  eapply valid_fail
  : typeclass_instances ssprove_valid_db.

Lemma valid_assert :
  ∀ L I b, ValidCode L I (assert b).
Proof.
  intros L I b. unfold assert. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (assert ?b)) =>
  eapply valid_assert
  : typeclass_instances ssprove_valid_db.

Lemma valid_assertD :
  ∀ A L I b k,
    (∀ x, ValidCode L I (k x)) →
    ValidCode L I (@assertD A b k).
Proof.
  intros A L I b k h.
  destruct b.
  - simpl. eapply h.
  - simpl. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (@assertD ?A ?b ?k)) =>
  eapply (valid_assertD A _ _ b k) ;
  intro
  : typeclass_instances ssprove_valid_db.

Notation "'#assert' b 'as' id ;; k" :=
  (assertD b (λ id, k))
  (at level 100, id name, b at next level, right associativity,
  format "#assert  b  as  id  ;;  '//' k")
  : package_scope.

Notation "'#assert' b ;; k" :=
  (assertD b (λ _, k))
  (at level 100, b at next level, right associativity,
  format "#assert  b  ;;  '//' k")
  : package_scope.

(** Notion of losslessness for distributions *)

Class LosslessOp (op : Op) :=
  is_lossless_op : psum op.π2 = 1.

#[export] Instance LosslessOp_uniform i `{Positive i} : LosslessOp (uniform i).
Proof.
  unfold LosslessOp.
  simpl.
  unfold r. rewrite psumZ. 2: apply ler0n.
  simpl. rewrite GRing.mul1r.
  rewrite psum_fin. rewrite cardE. rewrite size_enum_ord. simpl.
  rewrite GRing.sumr_const. rewrite cardE. rewrite size_enum_ord.
  rewrite -normrMn.
  rewrite -GRing.Theory.mulr_natr.
  rewrite GRing.mulVf.
  2:{
    apply /negP => e.
    rewrite intr_eq0 in e.
    move: e => /eqP e.
    destruct i. all: discriminate.
  }
  rewrite normr1. reflexivity.
Qed.
