(** Package utility for lookup *)


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
  StateTransformingLaxMorph chUniverse pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics.
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

(* TODO Is it still needed? *)
Lemma opaque_me :
  ∀ {B L I E}
    (p : raw_package) (hp : valid_package L I E p)
    (o : opsig) (ho : o \in E) (arg : src o)
    (e : lookup_op p o = None),
    B.
Proof.
  intros B L I E p hp o ho arg e.
  exfalso.
  destruct o as [n [S T]].
  cbn - [lookup_op] in e.
  eapply from_valid_package in hp.
  specialize (hp _ ho). cbn in hp. destruct hp as [f [ef hf]].
  cbn in e. destruct (p n) as [[St [Tt g]]|] eqn:e2.
  2: discriminate.
  destruct chUniverse_eqP.
  2:{ noconf ef. congruence. }
  destruct chUniverse_eqP.
  2:{ noconf ef. congruence. }
  discriminate.
Qed.

Equations? get_raw_package_op {L} {I E : Interface} (p : raw_package)
  (hp : valid_package L I E p)
  (o : opsig) (ho : o \in E) (arg : src o) : code L I (tgt o) :=
  get_raw_package_op p hp o ho arg with inspect (lookup_op p o) := {
  | @exist (Some f) e1 := {code f arg } ;
  | @exist None e1 := False_rect _ _
  }.
Proof.
  - destruct o as [n [S T]].
    cbn - [lookup_op] in *.
    eapply lookup_op_valid in hp. 2: eauto.
    cbn - [lookup_op] in hp. destruct hp as [g [eg hg]].
    rewrite <- e1 in eg. noconf eg.
    eapply hg.
  - eapply opaque_me. all: eauto.
Defined.

Lemma get_raw_package_op_lookup :
  ∀ {L} {I E : Interface} (p : raw_package)
    (hp : valid_package L I E p)
    (o : opsig) (ho : o \in E) (arg : src o)
    (f : src o -> raw_code (tgt o))
    (H : lookup_op p o = Some f),
    (get_raw_package_op p hp o ho arg).(prog) = f arg.
Proof.
  intros L I E p hp o ho arg f e.
  funelim (get_raw_package_op p hp o ho arg).
  2:{ rewrite <- e in e0. discriminate. }
  rewrite <- Heqcall. cbn. rewrite <- e in e0.
  noconf e0. reflexivity.
Qed.

(* TODO Needed? MOVE? *)
Definition code_link_ext {E : Interface}
  (o : opsig) (ho : o \in E) (arg : src o) (p1 p2 : raw_package)
  (f : src o → raw_code (tgt o))
  (Hf : lookup_op p1 o = Some f)
  (g : src o → raw_code (tgt o))
  (Hg : lookup_op (link p1 p2) o = Some g)
  : g arg = code_link (f arg) p2.
Proof.
  unfold link in Hg.
  destruct o as [id [S T]].
  assert ((λ x, code_link (f x) p2) = g).
  { extensionality x.
    unfold raw_package in p1.
    unfold lookup_op in Hg.
    rewrite mapmE in Hg.
    unfold omap in Hg.
    unfold obind in Hg.
    unfold oapp in Hg.
    assert (p1 id = Some (S; T; f)).
    { unfold lookup_op in Hf.
      destruct (p1 id) eqn:Hp1id.
      2: { inversion Hf. }
      destruct t as [S' [T' f']].
      destruct chUniverse_eqP.
      2:{ noconf ef. congruence. }
      destruct chUniverse_eqP.
      2:{ noconf ef. congruence. }
      noconf e. noconf e0.
      repeat f_equal. inversion Hf.
      rewrite -H0. reflexivity. }
    rewrite H in Hg.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    noconf e. noconf e0.
    inversion Hg.
    reflexivity. }
  rewrite -H.
  reflexivity.
Qed.

Lemma get_raw_package_op_link {L} {I M E} {o : opsig}
  (hin : o \in E) (arg : src o) (p1 p2 : raw_package)
  (hp1 : valid_package L M E p1)
  (hpl : valid_package L I E (link p1 p2))
  : (get_raw_package_op (link p1 p2) hpl o hin arg).(prog) =
    code_link ((get_raw_package_op p1 hp1 o hin arg).(prog)) p2.
Proof.
  destruct (lookup_op (link p1 p2) o) as [f|] eqn:e.
  2:{
    eapply from_valid_package in hpl as H.
    specialize (H o hin).
    destruct o as [id [S T]].
    destruct H as [f [H1 H2]].
    unfold lookup_op in e.
    rewrite H1 in e.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    discriminate.
  }
  rewrite (get_raw_package_op_lookup (link p1 p2) _ o hin arg f e).
  destruct (lookup_op p1 o) as [fl|] eqn:el.
  2:{
    eapply from_valid_package in hp1 as H.
    specialize (H o hin).
    destruct o as [id [S T]].
    destruct H as [f' [H1 H2]].
    unfold lookup_op in el.
    rewrite H1 in el.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    discriminate.
  }
  rewrite (get_raw_package_op_lookup p1 _ o hin arg fl el).
  apply (code_link_ext o hin arg p1 p2 fl el f e).
Qed.

Lemma get_raw_package_op_trim {L} {I E} {o : opsig}
      (hin : o \in E) (arg : src o) (p : raw_package)
      (hp : valid_package L I E p)
      (hpt : valid_package L I E (trim E p))
  : get_raw_package_op (trim E p) hpt o hin arg =
    get_raw_package_op p hp o hin arg.
Proof.
  apply code_ext.
  destruct (lookup_op p o) as [f|] eqn:e.
  2:{
    eapply from_valid_package in hp as H.
    specialize (H o hin).
    destruct o as [id [S T]].
    destruct H as [f [H1 H2]].
    unfold lookup_op in e.
    rewrite H1 in e.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    discriminate.
  }
  rewrite (get_raw_package_op_lookup p _ o hin arg f e).
  assert (lookup_op (trim E p) o = Some f) as H.
  { rewrite (lookup_op_trim E o p).
    unfold obind, oapp. rewrite e. rewrite hin. reflexivity. }
  rewrite (get_raw_package_op_lookup (trim E p) _ o hin arg f H).
  reflexivity.
Qed.

Lemma get_raw_package_op_ext {L1 L2} {I E} {o : opsig}
      (hin : o \in E) (arg : src o) (p : raw_package)
      (hp1 : valid_package L1 I E p)
      (hp2 : valid_package L2 I E p)
  : (get_raw_package_op p hp1 o hin arg).(prog) =
    (get_raw_package_op p hp2 o hin arg).(prog).
Proof.
  destruct (lookup_op p o) as [f|] eqn:e.
  2:{
    eapply from_valid_package in hp1 as H.
    specialize (H o hin).
    destruct o as [id [S T]].
    destruct H as [f [H1 H2]].
    unfold lookup_op in e.
    rewrite H1 in e.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    discriminate.
  }
  rewrite (get_raw_package_op_lookup p _ o hin arg f e).
  rewrite (get_raw_package_op_lookup p _ o hin arg f e).
  reflexivity.
Qed.

Definition get_opackage_op {L} {I E : Interface} (P : package L I E)
  (op : opsig) (Hin : op \in E) (arg : src op) : code L I (tgt op).
Proof.
  exact (get_raw_package_op P.(pack) P.(pack_valid) op Hin arg).
Defined.

Definition get_package_op {I E : Interface} (P : loc_package I E)
            (op : opsig) (Hin : op \in E) (arg : src op)
  : code P.(locs) I (tgt op) :=
  let (L, PP) as s return (code s.(locs) I (tgt op)) := P in
  get_opackage_op PP op Hin arg.

(* Rather than the above, we use the version with default values *)
Definition get_op_default (p : raw_package) (o : opsig) :
  src o → raw_code (tgt o) :=
  match lookup_op p o with
  | Some f => f
  | None => λ x, ret (chCanonical (chtgt o))
  end.

Lemma valid_get_op_default :
  ∀ L I E p o x,
    valid_package L I E p →
    o \in E →
    valid_code L I (get_op_default p o x).
Proof.
  intros L I E p o x hp ho.
  unfold get_op_default.
  destruct lookup_op eqn:e.
  - eapply lookup_op_spec in e as h.
    eapply from_valid_package in hp.
    specialize (hp _ ho). destruct o as [id [S T]].
    destruct hp as [f [ef hf]].
    cbn in h. rewrite ef in h. noconf h.
    auto.
  - constructor.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (get_op_default ?p ?o ?x)) =>
  eapply valid_get_op_default ; [
    eapply valid_package_from_class
  | auto_in_fset
  ]
  : typeclass_instances ssprove_valid_db.

Lemma lookup_op_link :
  ∀ p q o,
    lookup_op (p ∘ q) o = omap (λ f x, code_link (f x) q) (lookup_op p o).
Proof.
  intros p q [id [S T]].
  unfold lookup_op. unfold link.
  rewrite mapmE.
  destruct (p id) as [[S' [T' g]]|] eqn:e. 2: reflexivity.
  simpl. destruct chUniverse_eqP. 2: reflexivity.
  destruct chUniverse_eqP. 2: reflexivity.
  subst. cbn. reflexivity.
Qed.

Lemma get_op_default_link :
  ∀ p q o x,
    get_op_default (p ∘ q) o x = code_link (get_op_default p o x) q.
Proof.
  intros p q o x.
  unfold get_op_default. rewrite lookup_op_link.
  destruct lookup_op as [f|] eqn:e. 2: reflexivity.
  simpl. reflexivity.
Qed.

(* TODO Still useful? *)
Definition get_op {I E : Interface} (p : loc_package I E)
  (o : opsig) (ho : o \in E) (arg : src o) :
  code p.(locs) I (tgt o).
Proof.
  (* TW: I transformed this definition so that it computes directly. *)
  destruct (lookup_op p o) as [f|] eqn:e.
  2:{
    (* Rem.: Done several times, I should make a lemma. *)
    exfalso.
    destruct p as [L [p hp]].
    destruct o as [n [S T]].
    cbn - [lookup_op] in e.
    eapply from_valid_package in hp.
    specialize (hp _ ho). cbn in hp. destruct hp as [f [ef hf]].
    cbn in e. destruct (p n) as [[St [Tt g]]|] eqn:e2.
    2: discriminate.
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    destruct chUniverse_eqP.
    2:{ noconf ef. congruence. }
    discriminate.
  }
  exists (f arg).
  destruct p as [L [p hp]].
  destruct o as [n [S T]].
  cbn - [lookup_op] in *.
  eapply lookup_op_valid in hp. 2: eauto.
  cbn - [lookup_op] in hp. destruct hp as [g [eg hg]].
  rewrite e in eg. noconf eg.
  eapply hg.
Defined.

Lemma lookup_op_spec_inv :
  ∀ (p : raw_package) id S T f,
    p id = Some (S ; T ; f) →
    lookup_op p (id, (S, T)) = Some f.
Proof.
  intros p id S T f e.
  unfold lookup_op.
  destruct (p id) as [[S' [T' g]]|] eqn:e1. 2: discriminate.
  destruct chUniverse_eqP.
  2:{ noconf e. contradiction. }
  destruct chUniverse_eqP.
  2:{ noconf e. contradiction. }
  subst.
  noconf e.
  reflexivity.
Qed.

Lemma get_op_default_spec :
  ∀ (p : raw_package) id S T f,
    p id = Some (S ; T ; f) →
    get_op_default p (id, (S, T)) = f.
Proof.
  intros p id S T f e.
  unfold get_op_default.
  eapply lookup_op_spec_inv in e. rewrite e.
  reflexivity.
Qed.