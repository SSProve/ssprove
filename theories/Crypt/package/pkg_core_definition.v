(*
  This file defines "packages" of stateful probabilistic computation.
  It should not be directly required but instead used via Package.v.

  * raw_package (computational part of a package without validity conditions)


 *)

From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd RulesStateProb StateTransformingLaxMorph
     chUniverse.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


(* General definitions *)

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.

Definition ident := nat.

(* Signature of an operation, including the identifier *)
Definition opsig := ident * (chUniverse * chUniverse).
(* Record opsig := mkop {
ident : nat ;
src : chUniverse ;
tgt : chUniverse
}. *)

Definition mkopsig id S T : opsig := (id, (S, T)).

Definition Location := ∑ (t : chUniverse), nat.

Definition loc_type (l : Location) := l.π1.

Coercion loc_type : Location >-> chUniverse.

Definition Value (t : chUniverse) := chElement t.

Definition Interface := {fset opsig}.

Definition ide (v : opsig) : ident :=
  let '(n, _) := v in n.

Definition chsrc (v : opsig) : chUniverse :=
  let '(n, (s, t)) := v in s.

Definition src (v : opsig) : choiceType :=
  chsrc v.

Definition chtgt (v : opsig) : chUniverse :=
  let '(n, (s, t)) := v in t.

Definition tgt (v : opsig) : choiceType :=
  chtgt v.

Section Translation.

  Definition Prob_ops_collection := FreeProbProg.P_OP.

  Definition Prob_arities : Prob_ops_collection → choiceType :=
    FreeProbProg.P_AR.

End Translation.

Definition Op := Prob_ops_collection.
Definition Arit := Prob_arities.

Section FreeModule.

  Context (Loc : {fset Location}).
  Context (import : Interface).

  Inductive raw_code (A : choiceType) : Type :=
  | ret (x : A)
  | opr (o : opsig) (x : src o) (k : tgt o → raw_code A)
  | getr (l : Location) (k : l → raw_code A)
  | putr (l : Location) (v : l) (k : raw_code A)
  | sampler (op : Op) (k : Arit op → raw_code A).

  Arguments ret [A] _.
  Arguments opr [A] _ _.
  Arguments getr [A] _.
  Arguments putr [A] _.
  Arguments sampler [A] _ _.

  Inductive valid_code {A} : raw_code A → Prop :=
  | valid_ret :
      ∀ x,
        valid_code (ret x)

  | valid_opr :
      ∀ o x k,
        o \in import →
        (∀ v, valid_code (k v)) →
        valid_code (opr o x k)

  | valid_getr :
      ∀ l k,
        l \in Loc →
        (∀ v, valid_code (k v)) →
        valid_code (getr l k)

  | valid_putr :
      ∀ l v k,
        l \in Loc →
        valid_code k →
        valid_code (putr l v k)

  | valid_sampler :
      ∀ op k,
        (∀ v, valid_code (k v)) →
        valid_code (sampler op k)
  .

  Derive NoConfusion NoConfusionHom for chUniverse.
  Derive NoConfusion NoConfusionHom EqDec for nat.
  Derive NoConfusion NoConfusionHom for raw_code.
  Derive Signature for valid_code.

  (* Inversion lemmata *)

  Lemma inversion_valid_opr :
    ∀ {A o x k},
      @valid_code A (opr o x k) →
      (o \in import) *
      (∀ v, valid_code (k v)).
  Proof.
    intros A o x k h.
    dependent destruction h.
    intuition auto.
  Qed.

  Lemma inversion_valid_getr :
    ∀ {A l k},
      @valid_code A (getr l k) →
      (l \in Loc) *
      (∀ v, valid_code (k v)).
  Proof.
    intros A l k h.
    dependent destruction h.
    intuition auto.
  Qed.

  Lemma inversion_valid_putr :
    ∀ {A l v k},
      @valid_code A (putr l v k) →
      (l \in Loc) *
      (valid_code k).
  Proof.
    intros A l v k h.
    dependent destruction h.
    intuition auto.
  Qed.

  Lemma inversion_valid_sampler :
    ∀ {A op k},
      @valid_code A (sampler op k) →
      ∀ v, valid_code (k v).
  Proof.
    intros A op k h.
    dependent destruction h.
    auto.
  Qed.

  Class ValidCode {A} (p : raw_code A) :=
    is_valid_code : valid_code p.

  Lemma valid_code_from_class :
    ∀ A (p : raw_code A),
      ValidCode p →
      valid_code p.
  Proof.
    intros A p h. auto.
  Defined.

  Record code A := mkprog {
    prog : raw_code A ;
    prog_valid : ValidCode prog
  }.

  Arguments mkprog {_} _.
  Arguments prog {_} _.
  Arguments prog_valid {_} _.

  Lemma code_ext :
    ∀ A (u v : code A),
      u.(prog) = v.(prog) →
      u = v.
  Proof.
    intros A u v h.
    destruct u as [u hu], v as [v hv].
    cbn in h. subst.
    f_equal. apply proof_irrelevance.
  Qed.

  Fixpoint bind {A B} (c : raw_code A) (k : A → raw_code B) :
    raw_code B :=
    match c with
    | ret a => k a
    | opr o x k'  => opr o x (λ p, bind (k' p) k)
    | getr l k' => getr l (λ v, bind (k' v) k)
    | putr l v k' => putr l v (bind k' k)
    | sampler op k' => sampler op (λ a, bind (k' a) k)
    end.

  Lemma valid_bind :
    ∀ A B c k,
      valid_code c →
      (∀ x, valid_code (k x)) →
      valid_code (@bind A B c k).
  Proof.
    intros A B c k hc hk.
    induction hc. all: simpl.
    all: solve [ try constructor ; eauto ].
  Qed.

  Lemma inversion_valid_bind :
    ∀ {A B} {c : raw_code A} {k : A → raw_code B},
      valid_code (bind c k) →
      valid_code c.
  Proof.
    intros A B c k h.
    induction c.
    - constructor.
    - simpl in h. apply inversion_valid_opr in h. destruct h as [h1 h2].
      constructor. all: eauto.
    - simpl in h. apply inversion_valid_getr in h.
      constructor. all: intuition eauto.
    - simpl in h. apply inversion_valid_putr in h.
      constructor. all: intuition eauto.
    - simpl in h.
      constructor. intro.
      eapply inversion_valid_sampler in h.
      eauto.
  Qed.

  (* Alternative to bind *)
  Inductive command : choiceType → Type :=
  | cmd_op o (x : src o) : command (tgt o)
  | cmd_get (ℓ : Location) : command (Value ℓ.π1)
  | cmd_put (ℓ : Location) (v : Value ℓ.π1) : command unit_choiceType
  | cmd_sample op : command (Arit op).

  Definition cmd_bind {A B} (c : command A) (k : A → raw_code B) :=
    match c in command A return (A → raw_code B) → raw_code B with
    | cmd_op o x => opr o x
    | cmd_get ℓ => getr ℓ
    | cmd_put ℓ v => λ k, putr ℓ v (k Datatypes.tt)
    | cmd_sample op => sampler op
    end k.

  Inductive valid_command : ∀ A, command A → Prop :=
  | valid_cmd_op :
      ∀ o x,
        o \in import →
        valid_command _ (cmd_op o x)

  | valid_cmd_get :
      ∀ ℓ,
        ℓ \in Loc →
        valid_command _ (cmd_get ℓ)

  | valid_cmd_put :
      ∀ ℓ v,
        ℓ \in Loc →
        valid_command _ (cmd_put ℓ v)

  | valid_cmd_sample :
      ∀ op,
        valid_command _ (cmd_sample op).

  Arguments valid_command [_] _.

  Class ValidCommand {A} (c : command A) :=
    is_valid_command : valid_command c.

  Lemma valid_command_from_class :
    ∀ A (c : command A),
      ValidCommand c →
      valid_command c.
  Proof.
    auto.
  Qed.

  Lemma valid_cmd_bind :
    ∀ {A B} (c : command A) (k : A → raw_code B),
      valid_command c →
      (∀ x, valid_code (k x)) →
      valid_code (cmd_bind c k).
  Proof.
    intros A B c k hc hk.
    induction hc.
    - cbn. constructor. all: auto.
    - cbn. constructor. all: auto.
    - cbn. constructor. all: auto.
    - cbn. constructor. auto.
  Qed.

  Lemma inversion_valid_cmd_bind :
    ∀ {A B} (c : command A) (k : A → raw_code B),
      valid_code (cmd_bind c k) →
      valid_command c ∧ (∀ x, valid_code (k x)).
  Proof.
    intros A B c k h.
    destruct c.
    - cbn. apply inversion_valid_opr in h. intuition auto.
      constructor. auto.
    - cbn. apply inversion_valid_getr in h. intuition auto.
      constructor. auto.
    - cbn. apply inversion_valid_putr in h. split.
      + constructor. intuition auto.
      + intros []. intuition auto.
    - cbn. split.
      + constructor.
      + intro. eapply inversion_valid_sampler in h. eauto.
  Qed.

  Lemma bind_assoc :
    ∀ {A B C : choiceType} (v : raw_code A)
      (k1 : A → raw_code B) (k2 : B → raw_code C),
      bind (bind v k1) k2 =
      bind v (λ x, bind (k1 x) k2).
  Proof.
    intros A B C v k1 k2.
    induction v in k1, k2 |- *.
    - cbn. reflexivity.
    - cbn. f_equal. apply functional_extensionality. auto.
    - cbn. f_equal. extensionality z. auto.
    - cbn. f_equal. auto.
    - cbn. f_equal. extensionality z. auto.
  Qed.

  Lemma bind_ret :
    ∀ A (v : raw_code A),
      bind v (λ x, ret x) = v.
  Proof.
    intros A v.
    induction v.
    all: cbn. 1: reflexivity.
    all: try solve [ f_equal ; apply functional_extensionality ; eauto ].
    f_equal. auto.
  Qed.

  Lemma bind_cmd_bind :
    ∀ {A B C : choiceType}
      (c : command A) (k1 : _ → raw_code B) (k2 : _ → raw_code C),
      bind (cmd_bind c k1) k2 =
      cmd_bind c (λ x, bind (k1 x) k2).
  Proof.
    intros A B C c k1 k2.
    destruct c. all: simpl. all: reflexivity.
  Qed.

  Lemma prove_code :
    ∀ {A} (P : code A → Type) p q,
      P p →
      p.(prog) = q.(prog) →
      P q.
  Proof.
    intros A P p q h e.
    apply code_ext in e. subst. auto.
  Defined.

  Open Scope package_scope.

  Import SPropAxioms. Import FunctionalExtensionality.

  (* TODO: NEEDED? *)
  (* Program Definition rFree : ord_relativeMonad choice_incl :=
    @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl code _ _ _ _ _ _.
  Next Obligation.
    simple refine {code ret _ }.
    auto.
  Defined.
  Next Obligation.
    eapply bind. all: eauto. Defined.
  Next Obligation.
    f_equal. apply functional_extensionality. auto.
  Qed.
  Next Obligation.
    apply functional_extensionality.
    intro c. apply code_ext.
    destruct c as [c h]. cbn.
    induction c.
    all: solve [
      simpl in * ; try reflexivity ;
      f_equal ; try apply functional_extensionality ; intuition auto
    ].
  Qed.
  Next Obligation.
    extensionality x. apply code_ext.
    cbn. reflexivity.
  Qed.
  Next Obligation.
    apply functional_extensionality. intros [c h].
    apply code_ext. cbn.
    induction c in h |- *.
    all: solve [
      simpl in * ; try reflexivity ;
      f_equal ; try apply functional_extensionality ; intuition auto
    ].
  Qed. *)

  Fixpoint mapFree {A B : choiceType} (f : A → B) (m : raw_code A) :
    raw_code B :=
    match m with
    | ret x => ret (f x)
    | opr o x k => opr o x (λ r, mapFree f (k r))
    | getr l k' => getr l (λ v, mapFree f (k' v))
    | putr l v k' => putr l v (mapFree f k')
    | sampler op k' => sampler op (λ a, mapFree f (k' a))
    end.

End FreeModule.

Arguments ret [A] _.
Arguments opr [A] _ _.
Arguments getr [A] _.
Arguments putr [A] _.
Arguments sampler [A] _ _.

Arguments mkprog [_ _ _] _.
Arguments prog [_ _ _] _.
Arguments prog_valid [_ _ _] _.

Notation "{ 'code' p }" :=
  (mkprog p _)
  (format "{ code  p  }") : package_scope.

Notation "{ 'code' p '#with' h }" :=
  (mkprog p h)
  (only parsing) : package_scope.


(* Having an instance here means that it will use ret when the code
  is unknown. Pretty bad.
  We will instead use Hint Extern.
*)
(* Instance ValidCode_ret (A : choiceType) (x : A) L I :
  ValidCode L I (ret x).
Proof.
  apply valid_ret.
Qed. *)

Create HintDb ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (ret ?x)) =>
  apply valid_ret
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (opr ?o ?x ?k)) =>
  eapply valid_opr ; [
    auto_in_fset
  | intro ; eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (getr ?o ?k)) =>
  eapply valid_getr ; [
    auto_in_fset
  | intro ; eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (putr ?o ?x ?k)) =>
  eapply valid_putr ; [
    auto_in_fset
  | eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (sampler ?op ?k)) =>
  eapply valid_sampler ;
  intro ; eapply valid_code_from_class
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (bind ?p ?k)) =>
  eapply valid_bind ; [
    eapply valid_code_from_class
  | intro ; eapply valid_code_from_class
  ]
  : typeclass_instances ssprove_valid_db.

Coercion prog : code >-> raw_code.

(* Only in typeclasses inference to avoid bad progress *)
#[export] Hint Extern 1 (ValidCode ?L ?I (?p.(prog))) =>
  eapply p.(prog_valid)
  : typeclass_instances.

Arguments valid_command _ _ [_] _.

#[export] Hint Extern 1 (ValidCommand ?L ?I (cmd_op ?o ?x)) =>
  eapply valid_cmd_op ;
  auto_in_fset
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCommand ?L ?I (cmd_get ?l)) =>
  eapply valid_cmd_get ;
  auto_in_fset
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_put ?l ?v)) =>
  eapply valid_cmd_put ;
  auto_in_fset
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_sample ?op)) =>
  eapply valid_cmd_sample
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_bind ?c ?k)) =>
  eapply valid_cmd_bind ; [
    eapply valid_command_from_class
  | intro ; eapply valid_code_from_class
  ]
  : typeclass_instances ssprove_valid_db.

Section FreeLocations.

  Context {import : Interface}.

  (* TODO Make this lemma more general? *)
  Lemma injectSubset :
    ∀ {locs1 locs2 : {fset Location}} {l : Location},
      fsubset locs1 locs2 →
      l \in locs1 →
      l \in locs2.
  Proof.
    intros locs1 locs2 l Hfsubset H.
    unfold fsubset in Hfsubset.
    move: Hfsubset.
    move /eqP => Q.
    rewrite -Q.
    rewrite in_fsetU.
    intuition.
  Defined.

  Let codeI locs := code locs import.

  Lemma valid_injectLocations :
    ∀ A L1 L2 (v : raw_code A),
      fsubset L1 L2 →
      valid_code L1 import v →
      valid_code L2 import v.
  Proof.
    intros A L1 L2 v h p.
    induction p.
    all: try solve [ constructor ; eauto ].
    - constructor. 2: eauto.
      eapply injectSubset. all: eauto.
    - constructor. 2: eauto.
      eapply injectSubset. all: eauto.
  Qed.

  Lemma valid_cmd_injectLocations :
    ∀ A L1 L2 (v : command A),
      fsubset L1 L2 →
      valid_command L1 import v →
      valid_command L2 import v.
  Proof.
    intros A L1 L2 v h p.
    destruct p.
    all: try solve [ constructor ; eauto ].
    - constructor.
      eapply injectSubset. all: eauto.
    - constructor.
      eapply injectSubset. all: eauto.
  Qed.

End FreeLocations.

Section FreeMap.

  Context {Locs : {fset Location}}.

  (* TODO Factorise with lemma above. *)
  Lemma in_fsubset :
    ∀ {e} {S1 S2 : Interface},
      fsubset S1 S2 →
      e \in S1 →
      e \in S2.
  Proof.
    intros e S1 S2 hs h.
    unfold fsubset in hs.
    move: hs. move /eqP => hs. rewrite -hs.
    rewrite in_fsetU.
    intuition.
  Defined.

  Let codeL I := code Locs I.

  Lemma valid_injectMap :
    ∀ {A I1 I2} (v : raw_code A),
      fsubset I1 I2 →
      valid_code Locs I1 v →
      valid_code Locs I2 v.
  Proof.
    intros A I1 I2 v h p.
    induction p.
    all: try solve [ constructor ; auto ].
    constructor. 2: eauto.
    eapply in_fsubset. all: eauto.
  Qed.

End FreeMap.

Definition typed_raw_function :=
  ∑ (S T : chUniverse), S → raw_code T.

Definition raw_package :=
  {fmap ident -> typed_raw_function}.

(* To avoid unification troubles, we wrap this definition in an inductive. *)
Definition valid_package_ext L I (E : Interface) (p : raw_package) :=
  ∀ o, o \in E →
    let '(id, (src, tgt)) := o in
    ∃ (f : src → raw_code tgt),
      p id = Some (src ; tgt ; f) ∧ ∀ x, valid_code L I (f x).

Inductive valid_package L I E p :=
| prove_valid_package : valid_package_ext L I E p → valid_package L I E p.

Lemma from_valid_package :
  ∀ L I E p,
    valid_package L I E p →
    valid_package_ext L I E p.
Proof.
  intros L I E p [h]. exact h.
Qed.

Class ValidPackage L I E p :=
  is_valid_package : valid_package L I E p.

(* Packages *)
Record package L I E := mkpackage {
  pack : raw_package ;
  pack_valid : ValidPackage L I E pack
}.

Arguments mkpackage [_ _ _] _ _.
Arguments pack [_ _ _] _.
Arguments pack_valid [_ _ _] _.

(* Packages coming with their set of locations *)
Record loc_package I E := mkloc_package {
  locs : {fset Location} ;
  locs_pack : package locs I E
}.

Arguments mkloc_package [_ _] _ _.
Arguments locs [_ _] _.
Arguments locs_pack [_ _] _.

Coercion locs_pack : loc_package >-> package.

Lemma loc_package_ext :
  ∀ {I E} (p1 p2 : loc_package I E),
    p1.(locs) = p2.(locs) →
    p1.(locs_pack).(pack) =1 p2.(locs_pack).(pack) →
    p1 = p2.
Proof.
  intros I E p1 p2 e1 e2.
  destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]].
  apply eq_fmap in e2.
  cbn in *. subst.
  f_equal. f_equal. apply proof_irrelevance.
Qed.

Notation "{ 'package' p }" :=
  (mkpackage p _)
  (format "{ package  p  }") : package_scope.

Notation "{ 'package' p '#with' h }" :=
  (mkpackage p h)
  (only parsing) : package_scope.

Coercion pack : package >-> raw_package.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (?p.(pack))) =>
  eapply p.(pack_valid)
  : typeclass_instances ssprove_valid_db.

Lemma valid_package_from_class :
  ∀ L I E (p : raw_package),
    ValidPackage L I E p →
    valid_package L I E p.
Proof.
  intros A p h. auto.
Defined.

Notation "{ 'locpackage' p }" :=
  (mkloc_package _ (mkpackage p _))
  (format "{ locpackage  p  }") : package_scope.

Notation "{ 'locpackage' p '#with' h }" :=
  (mkloc_package _ (mkpackage p h))
  (only parsing) : package_scope.

(* Some validity lemmata *)

Lemma valid_package_inject_locations :
  ∀ I E L1 L2 p,
    fsubset L1 L2 →
    valid_package L1 I E p →
    valid_package L2 I E p.
Proof.
  intros I E L1 L2 p hL h.
  apply prove_valid_package.
  eapply from_valid_package in h.
  intros [n [S T]] ho. specialize (h _ ho). cbn in h.
  destruct h as [f [ef hf]].
  exists f. intuition auto.
  eapply valid_injectLocations. all: eauto.
Qed.

Lemma valid_package_inject_export :
  ∀ L I E1 E2 p,
    fsubset E1 E2 →
    valid_package L I E2 p →
    valid_package L I E1 p.
Proof.
  intros L I E1 E2 p hE h.
  apply prove_valid_package.
  eapply from_valid_package in h.
  intros o ho. specialize (h o).
  destruct o as [o [So To]].
  forward h.
  { eapply in_fsubset. all: eauto. }
  destruct h as [f [ef hf]].
  exists f. intuition auto.
Qed.

Lemma valid_package_inject_import :
  ∀ L I1 I2 E p,
    fsubset I1 I2 →
    valid_package L I1 E p →
    valid_package L I2 E p.
Proof.
  intros L I1 I2 E p hE h.
  apply prove_valid_package.
  eapply from_valid_package in h.
  intros [n [S T]] ho. specialize (h _ ho). cbn in h.
  destruct h as [f [ef hf]].
  exists f. intuition auto.
  eapply valid_injectMap. all: eauto.
Qed.

Lemma package_ext :
  ∀ {L I E} (p1 p2 : package L I E),
    p1.(pack) =1 p2.(pack) →
    p1 = p2.
Proof.
  intros L I E p1 p2 e.
  destruct p1 as [p1 h1], p2 as [p2 h2].
  apply eq_fmap in e.
  cbn in *. subst.
  f_equal. apply proof_irrelevance.
Qed.

(* Rewriting in packages *)

Lemma mkpackage_rewrite :
  ∀ {L I E T} {x y} (p : T → _) h (e : x = y),
    @mkpackage L I E (p x) h = mkpackage (p y) (sig_rewrite_aux p h e).
Proof.
  intros L I E T x y p h e. subst. reflexivity.
Qed.

Ltac mkpackage_rewrite e :=
  lazymatch type of e with
  | ?x = _ =>
    match goal with
    | |- context [ mkpackage ?p ?h ] =>
      lazymatch p with
      | context [ x ] =>
        lazymatch eval pattern x in p with
        | (fun x => @?q x) ?y =>
          erewrite (mkpackage_rewrite q _ e)
        end
      end
    end
  end.

(** Tactic package rewrite

Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
a term of the form mkpackage u v, specifically inside the term u.
sig rewrite e will replace x by y in u and update v accordingly.

*)
Tactic Notation "package" "rewrite" constr(e) :=
  mkpackage_rewrite e.

(* Rewriting in codes *)

Lemma mkprog_rewrite :
  ∀ {L I A T} {x y} (p : T → _) h (e : x = y),
    @mkprog L I A (p x) h = mkprog (p y) (sig_rewrite_aux p h e).
Proof.
  intros L I A T x y p h e. subst. reflexivity.
Qed.

Ltac mkprog_rewrite e :=
  lazymatch type of e with
  | ?x = _ =>
    match goal with
    | |- context [ mkprog ?p ?h ] =>
      lazymatch p with
      | context [ x ] =>
        lazymatch eval pattern x in p with
        | (fun x => @?q x) ?y =>
          erewrite (mkprog_rewrite q _ e)
        end
      end
    end
  end.

(** Tactic code rewrite

Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
a term of the form mkcode u v, specifically inside the term u.
sig rewrite e will replace x by y in u and update v accordingly.

*)
Tactic Notation "code" "rewrite" constr(e) :=
  mkprog_rewrite e.
