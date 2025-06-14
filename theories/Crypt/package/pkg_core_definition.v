(*
  This file defines "packages" of stateful probabilistic computation.
  It should not be directly required but instead used via Package.v.

  * raw_package (computational part of a package without validity conditions)


 *)

From Stdlib Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd
  RulesStateProb StateTransformingLaxMorph choice_type Casts fmap_extra.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


(* General definitions *)

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.

Definition ident := nat.

(* Signature of an operation, including the identifier *)
Definition opsig := ident * (choice_type * choice_type).
(* Record opsig := mkop {
ident : nat ;
src : choice_type ;
tgt : choice_type
}. *)

Definition mkopsig id S T : opsig := (id, (S, T)).

Definition Location := nat * choice_type.

Definition Locations := {fmap nat → choice_type}.

Definition loc_type (l : Location) := l.2.

Coercion loc_type : Location >-> choice_type.

Definition Value (t : choice_type) := chElement t.

Definition Interface := {fmap ident → choice_type * choice_type}.

Definition ide (v : opsig) : ident :=
  let '(n, _) := v in n.

Definition chsrc (v : opsig) : choice_type :=
  let '(n, (s, t)) := v in s.

Definition src (v : opsig) : choiceType :=
  chsrc v.

Definition chtgt (v : opsig) : choice_type :=
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

  Context (Loc : Locations).
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
      ∀ (o : opsig) x k,
        fhas import o →
        (∀ v, valid_code (k v)) →
        valid_code (opr o x k)

  | valid_getr :
      ∀ l k,
        fhas Loc l →
        (∀ v, valid_code (k v)) →
        valid_code (getr l k)

  | valid_putr :
      ∀ l v k,
        fhas Loc l →
        valid_code k →
        valid_code (putr l v k)

  | valid_sampler :
      ∀ op k,
        (∀ v, valid_code (k v)) →
        valid_code (sampler op k)
  .

  Derive NoConfusion NoConfusionHom for choice_type.
  Derive NoConfusion NoConfusionHom EqDec for nat.
  Derive NoConfusion NoConfusionHom for raw_code.
  Derive Signature for valid_code.

  (* Inversion lemmata *)

  Lemma inversion_valid_opr :
    ∀ {A o x k},
      @valid_code A (opr o x k) →
      (fhas import o) *
      (∀ v, valid_code (k v)).
  Proof.
    intros A o x k h.
    dependent destruction h.
    intuition auto.
  Qed.

  Lemma inversion_valid_getr :
    ∀ {A l k},
      @valid_code A (getr l k) →
      (fhas Loc l) *
      (∀ v, valid_code (k v)).
  Proof.
    intros A l k h.
    dependent destruction h.
    intuition auto.
  Qed.

  Lemma inversion_valid_putr :
    ∀ {A l v k},
      @valid_code A (putr l v k) →
      (fhas Loc l) *
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
      ValidCode c →
      (∀ x, ValidCode (k x)) →
      ValidCode (@bind A B c k).
  Proof.
    intros A B c k hc hk.
    induction hc. all: simpl.
    all: solve [ try constructor ; eauto ].
  Qed.

  Lemma inversion_valid_bind :
    ∀ {A B} {c : raw_code A} {k : A → raw_code B},
      ValidCode (bind c k) →
      ValidCode c.
  Proof.
    intros A B c k h.
    unfold ValidCode in *.
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
  | cmd_get (ℓ : Location) : command (Value ℓ)
  | cmd_put (ℓ : Location) (v : Value ℓ) : command unit_choiceType
  | cmd_sample op : command (Arit op).

  Definition cmd_bind {A B} (c : command A) (k : A → raw_code B) :=
    match c in command A return (A → raw_code B) → raw_code B with
    | cmd_op o x => opr o x
    | cmd_get ℓ => getr ℓ
    | cmd_put ℓ v => λ k, putr ℓ v (k tt)
    | cmd_sample op => sampler op
    end k.

  Inductive valid_command : ∀ A, command A → Prop :=
  | valid_cmd_op :
      ∀ o x,
        fhas import o →
        valid_command _ (cmd_op o x)

  | valid_cmd_get :
      ∀ l,
        fhas Loc l →
        valid_command _ (cmd_get l)

  | valid_cmd_put :
      ∀ l v,
        fhas Loc l →
        valid_command _ (cmd_put l v)

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
      ValidCommand c →
      (∀ x, ValidCode (k x)) →
      ValidCode (cmd_bind c k).
  Proof.
    intros A B c k hc hk.
    unfold ValidCode in *.
    induction hc.
    - cbn. constructor. all: auto.
    - cbn. constructor. all: auto.
    - cbn. constructor. all: auto.
    - cbn. constructor. auto.
  Qed.

  Lemma inversion_valid_cmd_bind :
    ∀ {A B} (c : command A) (k : A → raw_code B),
      ValidCode (cmd_bind c k) →
      ValidCommand c ∧ (∀ x, ValidCode (k x)).
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
    solve [ fmap_solve ]
  | intro ; eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (getr ?o ?k)) =>
  eapply valid_getr ; [
    solve [ fmap_solve ]
  | intro ; eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (putr ?o ?x ?k)) =>
  eapply valid_putr ; [
    solve [ fmap_solve ]
  | eapply valid_code_from_class
  ] : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (sampler ?op ?k)) =>
  eapply valid_sampler ;
  intro ; eapply valid_code_from_class
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (bind ?p ?k)) =>
  eapply valid_bind ; [
    idtac
  | intro
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
  solve [ fmap_solve ]
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCommand ?L ?I (cmd_get ?l)) =>
  eapply valid_cmd_get ;
  solve [ fmap_solve ]
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_put ?l ?v)) =>
  eapply valid_cmd_put ;
  solve [ fmap_solve ]
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_sample ?op)) =>
  eapply valid_cmd_sample
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidCode ?L ?I (cmd_bind ?c ?k)) =>
  eapply valid_cmd_bind ; [
    idtac
  | intro
  ]
  : typeclass_instances ssprove_valid_db.

Section FreeLocations.

  Context {import : Interface}.

  Let codeI locs := code locs import.

  Lemma valid_injectLocations :
    ∀ A L1 L2 (v : raw_code A),
      fsubmap L1 L2 →
      ValidCode L1 import v →
      ValidCode L2 import v.
  Proof.
    move=> A L1 L2 v h p.
    induction p.
    all: try solve [ constructor ; eauto ].
    - constructor. 2: eauto.
      by apply (fsubmap_fhas L1).
    - constructor. 2: eauto.
      by apply (fsubmap_fhas L1).
  Qed.

  Lemma valid_cmd_injectLocations :
    ∀ A L1 L2 (v : command A),
      fsubmap L1 L2 →
      ValidCommand L1 import v →
      ValidCommand L2 import v.
  Proof.
    move=> A L1 L2 v h p.
    destruct p.
    all: try solve [ constructor ; eauto ].
    - constructor.
      by apply (fsubmap_fhas L1).
    - constructor.
      by apply (fsubmap_fhas L1).
  Qed.

End FreeLocations.

Section FreeMap.

  Context {Locs : Locations}.

  Let codeL I := code Locs I.

  Lemma valid_injectMap :
    ∀ {A I1 I2} (v : raw_code A),
      fsubmap I1 I2 →
      ValidCode Locs I1 v →
      ValidCode Locs I2 v.
  Proof.
    move=> A I1 I2 v h p.
    induction p.
    all: try solve [ constructor ; auto ].
    constructor. 2: eauto.
    by apply (fsubmap_fhas I1).
  Qed.

End FreeMap.

Definition typed_raw_function :=
  ∑ (S T : choice_type), S → raw_code T.

Definition raw_package :=
  {fmap ident -> typed_raw_function }.

Record valid_package L (I E : Interface) (p : raw_package) :=
  { valid_exports : ∀ o,
      fhas E o <-> (∃ f, fhas p (o.1, (chsrc o ; chtgt o ; f)))
  ; valid_imports : ∀ n (F : typed_raw_function) (x : F.π1),
      fhas p (n, F) → ValidCode L I (F.π2.π2 x)
  }.

Class ValidPackage (L : Locations) (I E : Interface) p :=
  is_valid_package : valid_package L I E p.

(* Packages *)
Record package I E := mkpackage {
  locs : Locations ;
  pack : raw_package ;
  pack_valid : ValidPackage locs I E pack
}.

Arguments mkpackage [_ _] _ _ _.
Arguments locs [_ _] _.
Arguments pack [_ _] _.
Arguments pack_valid [_ _] _.

Notation "{ 'package' p }" :=
  (mkpackage _ p _)
  (format "{ package  p  }") : package_scope.

Notation "{ 'package' p '#with' h }" :=
  (mkpackage p h)
  (only parsing) : package_scope.

Coercion pack : package >-> raw_package.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (?p.(pack))) =>
  eapply p.(pack_valid)
  : typeclass_instances ssprove_valid_db.

(* Some validity lemmata *)

Lemma valid_exports_eq {L I E p} :
  ValidPackage L I E p → E = mapm (λ '(So; To; f), (So, To)) p.
Proof.
  intros [he _].
  apply eq_fmap => n.
  rewrite mapmE.
  destruct (E n) as [[S T]|] eqn:e.
  - specialize (he (n, (S, T))).
    simpl in he.
    rewrite he in e.
    destruct e as [f e].
    rewrite e //.
  - destruct (p n) eqn:e'; rewrite e' //.
    destruct t as [S [T f]].
    assert (∃ f : S → raw_code T, p n = Some (S; T; f)) by by exists f.
    specialize (he (n, (S, T))).
    simpl in he.
    rewrite -he in H.
    by rewrite H in e.
Qed.

Lemma valid_package_inject_locations :
  ∀ I E L1 L2 p,
    fsubmap L1 L2 →
    ValidPackage L1 I E p →
    ValidPackage L2 I E p.
Proof.
  intros I E L1 L2 p hL [he hi].
  split; [ done |] => n F x h.
  eapply valid_injectLocations; [ eassumption |].
  eapply hi, h.
Qed.

Lemma valid_package_inject_export :
  ∀ L I E1 E2 p,
    fsubmap E2 E1 →
    fsubmap E1 E2 →
    ValidPackage L I E2 p →
    ValidPackage L I E1 p.
Proof.
  intros L I E1 E2 p h1 h2.
  by rewrite (fsubmap_eq _ _ h1 h2).
Qed.

Lemma valid_package_inject_import :
  ∀ L I1 I2 E p,
    fsubmap I1 I2 →
    ValidPackage L I1 E p →
    ValidPackage L I2 E p.
Proof.
  intros L I1 I2 E p hE [he hi].
  split; [ done |] => n F x h.
  eapply valid_injectMap; [ eassumption |].
  eapply hi, h.
Qed.

Lemma package_ext :
  ∀ {I E} (p1 p2 : package I E),
    p1.(locs) =1 p2.(locs) →
    p1.(pack) =1 p2.(pack) →
    p1 = p2.
Proof.
  intros I E p1 p2 e e'.
  destruct p1 as [p1 h1], p2 as [p2 h2].
  apply eq_fmap in e, e'.
  cbn in *. subst.
  f_equal. apply proof_irrelevance.
Qed.

(* Rewriting in packages *)

Lemma mkpackage_rewrite :
  ∀ {L I E T} {x y} (p : T → _) h (e : x = y),
    @mkpackage I E L (p x) h = mkpackage L (p y) (sig_rewrite_aux p h e).
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
