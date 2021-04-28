(**
  This file connects packages to the relational Hoare logic and provides
  basic crypto-style reasoning notions.
**)


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
  pkg_tactics pkg_composition.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, god knows why. *)
From Crypt Require Import FreeProbProg.

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

Definition Game_import : Interface := [interface].

Definition Game_Type (Game_export : Interface) : Type :=
  loc_package Game_import Game_export.

Definition RUN := (0, ('unit, 'bool)).

Definition A_export : Interface := fset1 RUN.

Lemma RUN_in_A_export : RUN \in A_export.
Proof.
  apply in_fset1.
Qed.

Definition Adversary4Game (Game_export : Interface) : Type :=
  loc_package Game_export A_export.

Definition Adversary4Game_weak (Game_export : Interface) : Type :=
  package fset0 Game_export A_export.

Local Open Scope fset.

(* Let iops_StP := @ops_StP probE chUniverse chElement. *)
(* Let iar_StP := @ar_StP probE chUniverse chElement. *)

Definition pointed_value := ∑ (t : chUniverse), t.

Definition raw_heap := {fmap Location -> pointed_value}.
Definition raw_heap_choiceType := [choiceType of raw_heap].

Definition check_loc_val (l : Location) (v : pointed_value) :=
  l.π1 == v.π1.

Definition valid_location (h : raw_heap) (l : Location) :=
  match h l with
  | None => false
  | Some v => check_loc_val l v
  end.

Definition valid_heap : pred raw_heap := λ h,
  domm h == fset_filter (fun l => valid_location h l) (domm h).

Definition heap_defaults := ∀ a : chUniverse, a.

Definition heap_init : heap_defaults.
Proof.
  intros a. induction a.
  - exact tt.
  - exact 0.
  - exact false.
  - exact (IHa1, IHa2).
  - exact emptym.
  - exact None.
  - exact (fintype.Ordinal n.(cond_pos)).
Defined.

Definition heap := { h : raw_heap | valid_heap h }.

Definition heap_choiceType := [choiceType of heap].

Definition Game_op_import_S : Type := {_ : ident & void}.

Definition Game_import_P : Game_op_import_S → choiceType :=
  λ v, let 'existT a b := v in match b with end.

Definition get_heap (map : heap) (l : Location) : Value l.π1.
Proof.
  destruct map as [rh valid_rh].
  destruct (getm rh l) eqn:Hgetm.
  - assert (exists v, rh l = Some v) as H0.
    { exists p. assumption. }
    move: H0. move /dommP => H0.
    unfold valid_heap in valid_rh.
    move: valid_rh. move /eqP => valid_rh.
    rewrite valid_rh in H0.
    rewrite in_fset_filter in H0.
    move: H0. move /andP => [H1 H2].
    unfold valid_location in H1.
    rewrite Hgetm in H1.
    unfold check_loc_val in H1.
    move: H1. move /eqP => H1.
    rewrite H1.
    unfold pointed_value in p.
    exact (p.π2).
  - destruct l as [l_ty l_idx]. exact (heap_init l_ty).
Defined.

Program Definition set_heap (map : heap) (l : Location) (v : Value l.π1)
: heap :=
  setm map l (l.π1 ; v).
Next Obligation.
  intros map l v.
  unfold valid_heap.
  destruct map as [rh valid_rh].
  cbn - ["_ == _"].
  apply /eqP.
  apply eq_fset.
  move => x.
  rewrite domm_set.
  rewrite in_fset_filter.
  destruct ((x \in l |: domm rh)) eqn:Heq.
  - rewrite andbC. cbn.
    symmetry. apply /idP.
    unfold valid_location.
    rewrite setmE.
    destruct (x == l) eqn:H.
    + cbn. move: H. move /eqP => H. subst. apply chUniverse_refl.
    + move: Heq. move /idP /fsetU1P => Heq.
      destruct Heq.
      * move: H. move /eqP => H. contradiction.
      * destruct x, l. rewrite mem_domm in H0.
        unfold isSome in H0.
        destruct (rh (x; s)) eqn:Hrhx.
        ** cbn. unfold valid_heap in valid_rh.
            move: valid_rh. move /eqP /eq_fset => valid_rh.
            specialize (valid_rh (x; s)).
            rewrite in_fset_filter in valid_rh.
            rewrite mem_domm in valid_rh.
            assert (valid_location rh (x;s)) as Hvl.
            { rewrite Hrhx in valid_rh. cbn in valid_rh.
              rewrite andbC in valid_rh. cbn in valid_rh.
              rewrite -valid_rh. auto. }
            unfold valid_location in Hvl.
            rewrite Hrhx in Hvl.
            cbn in Hvl.
            assumption.
        ** assumption.
  - rewrite andbC. auto.
Qed.

Ltac revert_last :=
  match goal with
  | h : _ |- _ => revert h
  end.

Ltac revert_all :=
  repeat revert_last.

Ltac abstract_goal :=
  (* revert_all ; *)
  let h := fresh "h" in
  match goal with
  | |- ?G => assert (G) as h ; [
      idtac
    | abstract (apply h)
    ]
  end.

Arguments retrFree {_ _ _} _.
Arguments bindrFree {_ _ _ _} _ _.
Arguments ropr {_ _ _} _ _.

(** Interpretation of raw codes into the semantic model

  Note that we don't require any validity proof to do so,
  instead we rely on the fact that types in the chUniverse are all
  inhabited.

*)
Fixpoint repr {A : choiceType} (p : raw_code A) :
  rFreeF (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) A :=
  match p with
  | ret x => retrFree x
  | opr o x k =>
      repr (k (chCanonical (chtgt o)))
  | getr l k =>
      bindrFree
        (ropr gett (λ s, retrFree (get_heap s l)))
        (λ v, repr (k v))
  | putr l v k =>
      bindrFree
        (ropr gett (λ s, ropr (putt (set_heap s l v)) (λ s, retrFree tt)))
        (λ _, repr k)

  | sampler op k =>
      bindrFree
        (ropr (op_iota op) (λ v, retrFree v))
        (λ s, repr (k s))
  end.

Lemma repr_bind :
  ∀ {A B : choiceType} (p : raw_code A) (f : A → raw_code B),
    repr (bind p f) = bindrFree (repr p) (λ a, repr (f a)).
Proof.
  intros A B p f.
  induction p in f |- *.
  - cbn. reflexivity.
  - simpl. auto.
  - simpl. f_equal. extensionality x. auto.
  - simpl. f_equal. extensionality x. f_equal. extensionality y. auto.
  - simpl. f_equal. extensionality x. auto.
Qed.

Definition repr_cmd {A} (c : command A) :
  rFreeF (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) A :=
  match c with
  | cmd_op o x => retrFree (chCanonical (chtgt o))
  | cmd_get ℓ =>
      bindrFree
        (ropr gett (λ s, retrFree (get_heap s ℓ)))
        (λ v, retrFree v)
  | cmd_put ℓ v =>
      bindrFree
        (ropr gett (λ s, ropr (putt (set_heap s ℓ v)) (λ s, retrFree tt)))
        (λ s', retrFree s')
  | cmd_sample op =>
      bindrFree
        (ropr (op_iota op) (λ v, retrFree v))
        (λ s, retrFree s)
  end.

Lemma repr_cmd_bind :
  ∀ {A B} (c : command A) (k : A → raw_code B),
    repr (cmd_bind c k) = bindrFree (repr_cmd c) (λ a, repr (k a)).
Proof.
  intros A B c k.
  destruct c. all: reflexivity.
Qed.

Notation " r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄ " :=
  (semantic_judgement _ _ (repr c1) (repr c2) (fromPrePost pre post))
  : package_scope.

Definition precond := heap * heap → Prop.
Definition postcond A B := (A * heap) → (B * heap) → Prop.

Theorem rbind_rule :
  ∀ {A1 A2 B1 B2 : ord_choiceType} {f1 f2} m1 m2
    (pre : precond) (mid : postcond A1 A2) (post : postcond B1 B2),
    r⊨ ⦃ pre ⦄ m1 ≈ m2 ⦃ mid ⦄ →
    (∀ a1 a2,
      r⊨ ⦃ λ '(s1, s2), mid (a1, s1) (a2, s2) ⦄ f1 a1 ≈ f2 a2 ⦃ post ⦄
    ) →
    r⊨ ⦃ pre ⦄ bind m1 f1 ≈ bind m2 f2 ⦃ post ⦄.
Proof.
  intros A1 A2 B1 B2 f1 f2 m1 m2 pre mid post hm hf.
  rewrite !repr_bind.
  apply (bind_rule_pp (repr m1) (repr m2) pre mid post hm hf).
Qed.

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
  : typeclass_instances packages.

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

Definition Pr_code {A} (p : raw_code A) :
  heap_choiceType → SDistr (F_choice_prod_obj ⟨ A , heap_choiceType ⟩) :=
  λ s, thetaFstd A (repr p) s.

(* TODO REMOVE? *)
Definition Pr_raw_func_code {A B} (p : A → raw_code B) :
  A → heap_choiceType → SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩) :=
  λ a s, Pr_code (p a) s.

Definition Pr_op (p : raw_package) (o : opsig) (x : src o) :
  heap_choiceType → SDistr (F_choice_prod_obj ⟨ tgt o , heap_choiceType ⟩) :=
  Pr_code (get_op_default p o x).

#[program] Definition empty_heap : heap := emptym.
Next Obligation.
  by rewrite /valid_heap domm0 /fset_filter -fset0E.
Qed.

Arguments SDistr_bind {_ _}.

Definition Pr (p : raw_package) :
  SDistr (bool_choiceType) :=
  SDistr_bind
    (λ '(b, _), SDistr_unit _ b)
    (Pr_op p RUN Datatypes.tt empty_heap).

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

Import Num.Theory.
Local Open Scope ring_scope.
Local Open Scope real_scope.

Definition loc_GamePair (Game_export : Interface) :=
  bool → Game_Type Game_export.

(* TODO Again, why not an actual pair? *)
Definition GamePair :=
    bool → raw_package.

Definition Advantage (G : GamePair) (A : raw_package) : R :=
  `| Pr (A ∘ (G false)) true - Pr (A ∘ (G true)) true |.

Definition AdvantageE (G₀ G₁ : raw_package) (A : raw_package) : R :=
  `| Pr (A ∘ G₀) true - Pr (A ∘ G₁) true |.

(* TODO We could have the following
  Not clear it would be an improvement. It would be shorter but maybe not
  as easy to work with.
*)

(* Record AdversaryFor {I} (G : loc_GamePair I) := mkAdversary {
  adv_pack : loc_package I A_export ;
  adv_disj_false : fdisjoint adv_pack.(locs) (G false).(locs) ;
  adv_disj_true : fdisjoint adv_pack.(locs) (G true).(locs)
}.

Coercion adv_pack : AdversaryFor >-> loc_package. *)

(* TODO Useful? *)
Definition state_pass_ {A} (p : raw_code A) :
  heap_choiceType → raw_code (prod_choiceType A heap_choiceType).
Proof.
  induction p; intros h.
  - constructor.
    exact (x, h).
  - apply (opr o).
    + exact x.
    + intros v. exact (X v h).
  - apply X.
    + exact (get_heap h l).
    + exact h.
  - apply IHp.
    apply (set_heap h l v).
  - apply (sampler op).
    intros v. exact (X v h).
Defined.

Definition state_pass__valid {A} {L} {I} (p : raw_code A)
  (h : valid_code L I p) :
  ∀ hp, valid_code fset0 I (state_pass_ p hp).
Proof.
  intro hp. induction h in hp |- *.
  - cbn. constructor.
  - simpl. constructor.
    + assumption.
    + intros t. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. constructor.
    intros v. eauto.
Qed.

Definition state_pass {A} (p : raw_code A) : raw_code A :=
  bind (state_pass_ p empty_heap) (λ '(r, _), ret r).

Definition state_pass_valid {A} {L} {I} (p : raw_code A)
  (h : valid_code L I p) :
  valid_code fset0 I (state_pass p).
Proof.
  apply valid_bind.
  - apply (state_pass__valid p h empty_heap).
  - intros x. destruct x. constructor.
Qed.

(* TODO Will have to be updated *)
(* Probably by having first an operation on raw_packages
  and then a validity proof.
*)
Definition turn_adversary_weak  {Game_export : Interface}
  (A : Adversary4Game Game_export) : Adversary4Game_weak Game_export.
Proof.
  unfold Adversary4Game_weak.
  pose (get_op A RUN RUN_in_A_export Datatypes.tt) as run.
  destruct run as [run valid_run].
  cbn in *.
  pose (state_pass run) as raw_run_st.
  pose (state_pass_valid run valid_run) as raw_run_st_valid.
  apply funmkpack.
  - unfold flat, A_export.
    intros n u1 u2.
    move /fset1P => h1.
    move /fset1P => h2.
    inversion h1. inversion h2.
    reflexivity.
  - intros o.
    move /fset1P => hin.
    subst. intros _.
    exists raw_run_st.
    assumption.
Defined.

(* TODO Update to the new setting *)
(* Lemma pr_weak {Game_export : Interface}
  (A : Adversary4Game Game_export) (G : loc_package _ _) :
  Pr {locpackage link (turn_adversary_weak A) G } true =
  Pr {locpackage link A G } true.
Proof.
Admitted. *)

(* TODO UPDATE, first figure out what its role is *)
(* Definition perf_ind {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
  ∀ A,
    fdisjoint A.(locs) G0.(locs) →
    fdisjoint A.(locs) G1.(locs) →
    AdvantageE G0 G1 A = 0. *)

(* TODO UPDATE *)
(* Definition perf_ind_weak {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
  ∀ A, AdvantageE_weak G0 G1 A = 0. *)

(* Definition perf_ind_weak_implies_perf_ind {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
  (h : perf_ind_weak G0 G1) : perf_ind G0 G1.
Proof.
  unfold perf_ind, perf_ind_weak, AdvantageE, AdvantageE_weak in *.
  intros A H1 H2.
  rewrite -(pr_weak A G0).
  rewrite -(pr_weak A G1).
  apply h.
Qed. *)

(* Notation "ε( GP )" :=
  (AdvantageE (GP false) (GP true))
  (at level 90)
  : package_scope. *)

Definition adv_equiv {L₀ L₁ E} (G₀ G₁ : raw_package)
  `{ValidPackage L₀ Game_import E G₀} `{ValidPackage L₁ Game_import E G₁} ε :=
  ∀ LA A,
    ValidPackage LA E A_export A →
    fdisjoint LA L₀ →
    fdisjoint LA L₁ →
    AdvantageE G₀ G₁ A = ε A.

Notation " G0 ≈[ R ] G1 " :=
  (adv_equiv G0 G1 R)
  (at level 50, format " G0  ≈[  R  ]  G1")
  : package_scope.

Notation " G0 ≈₀ G1 " :=
  (G0 ≈[ λ (_ : raw_package), 0 ] G1)
  (at level 50, format " G0  ≈₀  G1")
  : package_scope.

Lemma Advantage_equiv :
  ∀ I (G : loc_GamePair I),
    (G false) ≈[ Advantage G ] (G true).
Proof.
  intros I G. intros LA A vA hd₀ hd₁. reflexivity.
Qed.

Lemma AdvantageE_equiv :
  ∀ I (G₀ G₁ : Game_Type I),
    G₀ ≈[ AdvantageE G₀ G₁ ] G₁.
Proof.
  intros I G₀ G₁. intros LA A vA hd₀ hd₁. reflexivity.
Qed.

Lemma Advantage_E :
  ∀ (G : GamePair) A,
    Advantage G A = AdvantageE (G false) (G true) A.
Proof.
  intros G A.
  reflexivity.
Qed.

Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
Proof.
  intros G₀ G₁ A P.
  unfold AdvantageE. rewrite !link_assoc. reflexivity.
Qed.

Lemma Advantage_sym :
  ∀ P Q A,
    AdvantageE P Q A = AdvantageE Q P A.
Proof.
  intros P Q A.
  unfold AdvantageE.
  rewrite distrC. reflexivity.
Qed.

Lemma adv_equiv_sym :
  ∀ L₀ L₁ E G₀ G₁ h₀ h₁ ε,
    @adv_equiv L₀ L₁ E G₀ G₁ h₀ h₁ ε →
    adv_equiv G₁ G₀ ε.
Proof.
  intros L₀ L₁ E G₀ G₁ h₀ h₁ ε h.
  intros LA A hA hd₁ hd₀.
  rewrite Advantage_sym.
  eapply h. all: eauto.
Qed.

Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
Proof.
  intros P Q R A.
  unfold AdvantageE.
  apply ler_dist_add.
Qed.

Fixpoint advantage_sum P l Q A :=
  match l with
  | [::] => AdvantageE P Q A
  | R :: l => AdvantageE P R A + advantage_sum R l Q A
  end.

Lemma Advantage_triangle_chain :
  ∀ P (l : seq raw_package) Q A,
    AdvantageE P Q A <= advantage_sum P l Q A.
Proof.
  intros P l Q A.
  induction l as [| R l ih] in P, Q |- *.
  - simpl. auto.
  - simpl. eapply mc_1_10.Num.Theory.ler_trans.
    + eapply Advantage_triangle.
    + eapply ler_add.
      * auto.
      * eapply ih.
Qed.

Ltac advantage_sum_simpl_in h :=
  repeat
    change (advantage_sum ?P (?R :: ?l) ?Q ?A)
    with (AdvantageE P R A + advantage_sum R l Q A) in h ;
  change (advantage_sum ?P [::] ?Q ?A) with (AdvantageE P Q A) in h.

Tactic Notation "advantage_sum" "simpl" "in" hyp(h) :=
  advantage_sum_simpl_in h.

Lemma AdvantageE_le_0 :
  ∀ G₀ G₁ A,
    AdvantageE G₀ G₁ A <= 0 →
    AdvantageE G₀ G₁ A = 0.
Proof.
  intros G₀ G₁ A h.
  unfold AdvantageE in *.
  rewrite mc_1_10.Num.Theory.normr_le0 in h.
  apply/mc_1_10.Num.Theory.normr0P. auto.
Qed.

Lemma Advantage_le_0 :
  ∀ G A,
    Advantage G A <= 0 →
    Advantage G A = 0.
Proof.
  intros G A h.
  rewrite -> Advantage_E in *. apply AdvantageE_le_0. auto.
Qed.

Lemma TriangleInequality :
  ∀ {Game_export : Interface}
    {F G H : Game_Type Game_export}
    {ϵ1 ϵ2 ϵ3},
    F ≈[ ϵ1 ] G →
    G ≈[ ϵ2 ] H →
    F ≈[ ϵ3 ] H →
    ∀ LA A,
      ValidPackage LA Game_export A_export A →
      fdisjoint LA F.(locs) →
      fdisjoint LA G.(locs) →
      fdisjoint LA H.(locs) →
      ϵ3 A <= ϵ1 A + ϵ2 A.
Proof.
  intros Game_export F G H ε₁ ε₂ ε₃ h1 h2 h3 LA A vA hF hG hH.
  unfold adv_equiv in *.
  erewrite <- h1, <- h2, <- h3 by eassumption.
  apply ler_dist_add.
Qed.

Lemma Reduction :
  ∀ (M : raw_package) (G : GamePair) A b,
    `| Pr (A ∘ (M ∘ (G b))) true | =
    `| Pr ((A ∘ M) ∘ (G b)) true |.
Proof.
  intros M G A b.
  rewrite link_assoc. reflexivity.
Qed.

Lemma ReductionLem :
  ∀ L₀ L₁ E M (G : GamePair)
    `{ValidPackage L₀ Game_import E (M ∘ G false)}
    `{ValidPackage L₁ Game_import E (M ∘ G true)},
    (M ∘ (G false)) ≈[ λ A, Advantage G (A ∘ M) ] (M ∘ (G true)).
Proof.
  intros L₀ L₁ E M G v₀ v₁.
  unfold adv_equiv. intros LA A vA hd₀ hd₁. rewrite Advantage_E.
  unfold AdvantageE. rewrite !link_assoc. reflexivity.
Qed.

Definition INV (L : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, l \in L → get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, l \in L → I (set_heap s1 l v, set_heap s2 l v)).

Definition INV' (L1 L2 : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, l \notin L1 → l \notin L2 →
      get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, l \notin L1 → l \notin L2 →
      I (set_heap s1 l v, set_heap s2 l v)).

Lemma INV'_to_INV (L L1 L2 : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop)
  (HINV' : INV' L1 L2 I)
  (Hdisjoint1 : fdisjoint L L1) (Hdisjoint2 : fdisjoint L L2) :
  INV L I.
Proof.
  unfold INV.
  intros s1 s2. split.
  - intros hi l hin.
    apply HINV'.
    + assumption.
    + move: Hdisjoint1. move /fdisjointP => Hdisjoint1.
      apply Hdisjoint1. assumption.
    + move: Hdisjoint2. move /fdisjointP => Hdisjoint2.
      apply Hdisjoint2. assumption.
  - intros hi l v hin.
    apply HINV'.
    + assumption.
    + move: Hdisjoint1. move /fdisjointP => Hdisjoint1.
      apply Hdisjoint1. assumption.
    + move: Hdisjoint2. move /fdisjointP => Hdisjoint2.
      apply Hdisjoint2. assumption.
Qed.

Lemma get_case :
  ∀ LA (I : heap_choiceType * heap_choiceType → Prop) ℓ,
    INV LA I →
    ℓ \in LA →
    r⊨ ⦃ λ '(s₀, s₃), I (s₀, s₃) ⦄
      x ← get ℓ ;; ret x ≈ x ← get ℓ ;; ret x
      ⦃ λ '(b₁, s₁) '(b₂, s₂), b₁ = b₂ ∧ I (s₁, s₂) ⦄.
Proof.
  intros LA I ℓ hinv hin. intros [s₁ s₂]. simpl.
  rewrite /SpecificationMonads.MonoCont_bind /=.
  rewrite /SpecificationMonads.MonoCont_order
    /SPropMonadicStructures.SProp_op_order
    /Morphisms.pointwise_relation /Basics.flip
    /SPropMonadicStructures.SProp_order /=.
  intuition auto.
  assert (get_heap s₁ ℓ = get_heap s₂ ℓ) as Hv.
  { unfold INV in hinv.
    specialize (hinv s₁ s₂). destruct hinv as [hinv _].
    eapply hinv. all: auto.
  }
  pose v := (SDistr_unit _ (((get_heap s₁ ℓ), s₁),
                            ((get_heap s₂ ℓ), s₂))).
  exists v. split.
  - apply SDistr_unit_F_choice_prod_coupling.
    reflexivity.
  - intros [b₁ s₃] [b₂ s₄]. intro hd.
    apply H1. rewrite dunit1E in hd.
    assert (
      (get_heap s₁ ℓ, s₁, (get_heap s₂ ℓ, s₂)) = (b₁, s₃, (b₂, s₄))
    ) as e.
    { destruct ((get_heap s₁ ℓ, s₁, (get_heap s₂ ℓ, s₂)) == (b₁, s₃, (b₂, s₄))) eqn:e.
      - move: e => /eqP e. assumption.
      - rewrite e in hd. cbn in hd.
        rewrite mc_1_10.Num.Theory.ltrr in hd. discriminate.
    }
    inversion e. subst. intuition auto.
Qed.

Lemma put_case :
  ∀ {LA} (I : heap_choiceType * heap_choiceType → Prop) l v,
    INV LA I →
    l \in LA →
    r⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
        putr l v (ret tt) ≈ putr l v (ret tt)
        ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
Proof.
  intros LA I l v hinv hin.
  intros [s1 s2]. simpl.
  rewrite /SpecificationMonads.MonoCont_bind /=.
  rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
          /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order /=.
  intuition eauto.
  eexists (SDistr_unit _ _).
  split.
  + apply SDistr_unit_F_choice_prod_coupling.
    reflexivity.
  + intros [b1 s3] [b2 s4].
    intros Hd.
    apply H1.
    unfold SDistr_unit in Hd.
    rewrite dunit1E in Hd.
    assert ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) = (b1, s3, (b2, s4))) as Heqs.
    { destruct ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) == (b1, s3, (b2, s4))) eqn:Heqd.
      - move: Heqd. move /eqP => Heqd. assumption.
      - rewrite Heqd in Hd. simpl in Hd.
        rewrite mc_1_10.Num.Theory.ltrr in Hd. discriminate.
    }
    inversion Heqs.
    intuition eauto.
    eapply hinv. all: eauto.
Qed.

(* TODO MOVE? *)

Lemma destruct_pair_eq {R : ringType} {A B : eqType} {a b : A} {c d : B} :
  ((a, c) == (b, d))%:R = (a == b)%:R * (c == d)%:R :> R.
Proof.
  destruct (a == b) eqn:ab, (c == d) eqn:cd.
  all: cbn; rewrite ab cd /=; try rewrite GRing.mulr1; try rewrite GRing.mulr0; reflexivity.
Qed.

Lemma summable_eq {A : choiceType} {s : A} :
  realsum.summable (T:=A) (R:=R) (λ x, (x == s)%:R).
Proof.
  match goal with
  | |- realsum.summable ?f => eassert (f = _) as Hf end.
  { extensionality x. rewrite eq_sym.
    rewrite -dunit1E. reflexivity. }
  rewrite Hf. clear Hf.
  apply summable_mu.
Qed.

Lemma summable_pair_eq {A : choiceType} {B C : eqType} (f1 f3 : A -> B) (f2 f4 : A -> C)
      (h1 : realsum.summable (T:=A) (R:=R) (λ x, (f1 x == f3 x)%:R))
      (h2 : realsum.summable (T:=_) (R:=R) (λ x, (f2 x == f4 x)%:R))
  :
    realsum.summable (T:=_) (R:=R) (λ x, ((f1 x, f2 x) == (f3 x, f4 x))%:R).
Proof.
  match goal with
  | |- realsum.summable ?f => eassert (f = _) as Hf end.
  { extensionality x.
    apply (destruct_pair_eq (a:= f1 x) (b:=f3 x) (c:= f2 x) (d := f4 x)). }
  rewrite Hf.
  apply realsum.summableM. all: assumption.
Qed.

Lemma psum_exists {R : realType} {A : choiceType} {f : A -> R}
      (H : 0 < realsum.psum (T:=A) (R:=R) f) (Hpos : forall x, 0 <= f x) :
  exists x, 0 < f x.
Proof.
  assert (realsum.psum f ≠ 0) as Hneq.
  { intros Hgt.
    rewrite Hgt in H.
    rewrite mc_1_10.Num.Theory.ltrr in H.
    auto. }
  destruct (realsum.neq0_psum (R:=R) Hneq) as [x Hx].
  exists x. specialize (Hpos x).
  rewrite mc_1_10.Num.Theory.ler_eqVlt in Hpos.
  move: Hpos. move /orP => [H1 | H2].
  - move: H1. move /eqP => H1. rewrite -H1.
    rewrite mc_1_10.Num.Theory.ltrr. auto.
  - assumption.
Qed.

Lemma pmulr_me (x y : R) : 0 <= y -> (0 < y * x) -> (0 < x).
Proof.
  rewrite le0r => /orP[/eqP->|].
  - by rewrite GRing.mul0r mc_1_10.Num.Theory.ltrr.
  - intros. by rewrite -(pmulr_rgt0 x b).
Qed.

Lemma ge0_eq {R : realType} {A : eqType} {x y : A} (H : 0 < ((x == y)%:R) :> R) :
  x = y.
Proof.
  destruct (x == y) eqn:Heq.
  - move: Heq. by move /eqP.
  - by rewrite mc_1_10.Num.Theory.ltrr in H.
Qed.

Lemma ne0_eq {R : ringType} {A : eqType} {x y : A} (H : ((x == y)%:R) ≠ (0 : R)) :
  x = y.
Proof.
  destruct (x == y) eqn:Heq.
  - move: Heq. by move /eqP.
  - cbn in H. intuition.
Qed.

Lemma sampler_case :
  ∀ {LA} (I : heap_choiceType * heap_choiceType -> Prop) op,
    INV LA I →
    r⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
      sampler op [eta ret (A:=Arit op)] ≈ sampler op [eta ret (A:=Arit op)]
      ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
Proof.
  intros LA I op HINV.
  cbn - [thetaFstd θ]. intros [s1 s2].
  rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
          /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order.
  intuition eauto. unfold θ. cbn - [justInterpState stT_thetaDex].
  unfold justInterpState. unfold LaxComp.rlmm_comp.
  simpl (nfst _). simpl (nsnd _). unfold stT_thetaDex.
  simpl (TransformingLaxMorph.rlmm_from_lmla (stT_thetaDex_adj) ⟨ Arit op, Arit op ⟩).
  unfold stT_thetaDex_adj.
  cbn - [ThetaDex.thetaDex UniversalFreeMap.outOfFree_obligation_1].
  unfold TransformingLaxMorph.Kl_beta_obligation_1.
  simpl ((ThetaDex.thetaDex
  ⟨ F_choice_prod_obj ⟨ Arit op, heap_choiceType ⟩,
  F_choice_prod_obj ⟨ Arit op, heap_choiceType ⟩ ⟩) ∙1).
  unfold Theta_exCP.θ0.
  cbn - [Theta_dens.unary_theta_dens_obligation_1 ThetaDex.thetaDex UniversalFreeMap.outOfFree_obligation_1].
  pose foo := (sigMap (op_iota op) s1).
  cbn in foo.
  unfold probopStP in foo. cbn in foo.
  destruct op as [opA opB].
  pose foo2 := SDistr_bind (fun x => SDistr_unit _ ((x, s1), (x, s2))) (Theta_dens.unary_ThetaDens0 _ (ropr (opA; opB) (λ x : chElement opA, retrFree x))).
  exists foo2.
  split.
  - cbn. unfold coupling.
    split.
    + unfold lmg.
      unfold foo2. apply distr_ext.
      move => x0. unfold SDistr_bind, SDistr_unit.
      cbn.
      rewrite SDistr_rightneutral. cbn.
      rewrite dfstE. rewrite dletE. cbn.
      match goal with
      | |- realsum.psum ?f = _ => eassert (f = _) end.
      { extensionality y. rewrite dletE.
        match goal with
        | |- realsum.psum ?g = _ => eassert (g = _) end.
        { extensionality x. rewrite dunit1E. reflexivity. }
        rewrite H0. reflexivity. }
      rewrite H0. clear H0.
      rewrite realsum.psum_sum.
      * destruct x0. rewrite (realsum.sum_seq1 (s, s2)).
        ** f_equal.
            extensionality x. rewrite dunit1E. f_equal.
            rewrite destruct_pair_eq.
            destruct ((x, s1) == (s, h)) eqn:Heq1.
            2: by rewrite Heq1 GRing.mul0r.
            rewrite Heq1. rewrite GRing.mul1r.
            move: Heq1. move /eqP => Heq1. inversion Heq1. subst.
              by rewrite eq_refl.
        ** intros y.
            move /eqP => Hneq.
            apply realsum.neq0_psum in Hneq.
            destruct Hneq as [x C].
            unshelve eassert (((x, s1, (x, s2)) == (s, h, y))%:R ≠ 0).
            { exact R. }
            { unfold "_ ≠ _". intros Hne.
              rewrite Hne in C. rewrite GRing.mulr0 in C. contradiction. }
            apply ne0_eq in H0.
            inversion H0. subst. auto.
      * intros x. apply realsum.ge0_psum.
    + unfold rmg.
      unfold foo2. apply distr_ext.
      move => x0. unfold SDistr_bind, SDistr_unit.
      cbn.
      rewrite SDistr_rightneutral. cbn.
      rewrite dsndE. rewrite dletE. cbn.
      match goal with
      | |- realsum.psum ?f = _ => eassert (f = _) end.
      { extensionality y. rewrite dletE.
        match goal with
        | |- realsum.psum ?g = _ => eassert (g = _) end.
        { extensionality x. rewrite dunit1E. reflexivity. }
        rewrite H0. reflexivity. }
      rewrite H0. clear H0.
      rewrite realsum.psum_sum.
      * destruct x0. rewrite (realsum.sum_seq1 (s, s1)).
        ** f_equal.
            extensionality x. rewrite dunit1E. f_equal.
            rewrite destruct_pair_eq.
            destruct ((x, s2) == (s, h)) eqn:Heq1.
            2: by rewrite Heq1 GRing.mulr0.
            rewrite Heq1. rewrite GRing.mulr1.
            move: Heq1. move /eqP => Heq1. inversion Heq1. subst.
              by rewrite eq_refl.
        ** intros y.
            move /eqP => Hneq.
            apply realsum.neq0_psum in Hneq.
            destruct Hneq as [x C].
            unshelve eassert (((x, s1, (x, s2)) == (y, (s, h)))%:R ≠ 0).
            { exact R. }
            { unfold "_ ≠ _". intros Hne.
              rewrite Hne in C. rewrite GRing.mulr0 in C. contradiction. }
            apply ne0_eq in H0.
            inversion H0. subst. auto.
      * intros x. apply realsum.ge0_psum.
  - intros a1 a2.
    unfold foo2. cbn.
    intros Hd.
    cbn in H.
    destruct H as [HI H].
    apply H.
    destruct a1, a2.
    rewrite SDistr_rightneutral in Hd.
    cbn in Hd.
    rewrite /SDistr_bind /SDistr_unit in Hd.
    rewrite dletE in Hd.
    eassert ((λ x : chElement opA,
        opB x *
        dunit
                (x, s1, (x, s2)) (s, h, (s0, h0))) =
              _).
    { extensionality x. rewrite dunit1E. reflexivity. }
    rewrite H0 in Hd. clear H0.
    apply psum_exists in Hd.
    + destruct Hd as [x Hx].
      apply pmulr_me in Hx.
      * apply ge0_eq in Hx. inversion Hx. subst.
        intuition auto.
      * auto.
    + intros x. apply mulr_ge0.
      * auto.
      * apply ler0n.
Qed.

(** Syntactic judgment *)

(* It's the same as the semantic one, but we're abstracting it away. *)
Definition rel_jdg {A B : choiceType} (pre : precond) (post : postcond A B)
  (p : raw_code A) (q : raw_code B) :=
  locked (r⊨ ⦃ pre ⦄ p ≈ q ⦃ post ⦄).

Notation "⊢ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
  (rel_jdg pre post c1 c2)
  (format "⊢  ⦃  pre  ⦄ '/  '  '[' c1  ']' '/' ≈ '/  '  '[' c2  ']' '/' ⦃  post  ⦄")
  : package_scope.

Lemma rel_jdgE :
  ∀ {A B : choiceType} pre (post : postcond A B) p q,
    ⊢ ⦃ pre ⦄ p ≈ q ⦃ post ⦄ = r⊨ ⦃ pre ⦄ p ≈ q ⦃ post ⦄.
Proof.
  intros. unfold rel_jdg. rewrite -lock. reflexivity.
Qed.

(** Equivalence of packages in the program logic *)

Definition eq_up_to_inv (E : Interface) (I : precond) (p₀ p₁ : raw_package) :=
  ∀ (id : ident) (S T : chUniverse) (x : S),
    (id, (S, T)) \in E →
    ⊢ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
      get_op_default p₀ (id, (S, T)) x ≈ get_op_default p₁ (id, (S, T)) x
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄.

(* The version below works as well, but is weaker *)
(* Definition eq_up_to_inv (I : precond) (p₀ p₁ : raw_package) :=
  ∀ (id : ident) (S T : chUniverse) (x : S),
    r⊨ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
      get_op_default p₀ (id, (S, T)) x ≈ get_op_default p₁ (id, (S, T)) x
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄. *)

(* TODO MOVE *)
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

(* TODO MOVE *)

(* Slightly more expensive version that allows to change parameters *)
(* #[export] Hint Extern 3 (ValidCode ?L ?I ?p) =>
  match goal with
  | h : is_true (fsubset ?x ?y) |- _ =>
    eapply valid_injectLocations with (1 := h) ;
    eapply valid_code_from_class ; exact _
  end
  : typeclass_instances. *)

(* #[export] Hint Extern 3 (ValidCode ?L ?I ?p) =>
  match goal with
  | h : is_true (fsubset ?x ?y) |- _ =>
    eapply valid_injectMap with (1 := h) ;
    eapply valid_code_from_class ; exact _
  end
  : typeclass_instances. *)

(* #[export] Hint Extern 3 (ValidPackage ?L ?I ?E ?p) =>
  match goal with
  | h : is_true (fsubset ?x ?y) |- _ =>
    eapply valid_package_inject_locations with (1 := h) ;
    eapply valid_package_from_class ; exact _
  end
  : typeclass_instances. *)

(* #[export] Hint Extern 3 (ValidPackage ?L ?I ?E ?p) =>
  match goal with
  | h : is_true (fsubset ?x ?y) |- _ =>
    eapply valid_package_inject_export with (1 := h) ;
    eapply valid_package_from_class ; exact _
  end
  : typeclass_instances. *)

(* #[export] Hint Extern 3 (ValidPackage ?L ?I ?E ?p) =>
  match goal with
  | h : is_true (fsubset ?x ?y) |- _ =>
    eapply valid_package_inject_import with (1 := h) ;
    eapply valid_package_from_class ; exact _
  end
  : typeclass_instances. *)

Lemma Pr_eq_empty :
  ∀ {X Y : ord_choiceType}
    {A : pred (X * heap_choiceType)} {B : pred (Y * heap_choiceType)}
    Ψ ϕ
    (c1 : @FrStP heap_choiceType X) (c2 : @FrStP heap_choiceType Y),
    ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄ →
    Ψ (empty_heap, empty_heap) →
    (∀ x y, ϕ x y → (A x) ↔ (B y)) →
    \P_[ θ_dens (θ0 c1 empty_heap) ] A =
    \P_[ θ_dens (θ0 c2 empty_heap) ] B.
Proof.
  intros X Y A B Ψ Φ c1 c2 ? ? ?.
  apply (Pr_eq Ψ Φ). all: assumption.
Qed.

(* TODO Rename *)
Lemma some_lemma_for_prove_relational :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) {B} (A : raw_code B)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{@ValidCode LA E B A},
    INV LA I →
    eq_up_to_inv E I p₀ p₁ →
    r⊨ ⦃ I ⦄ code_link A p₀ ≈ code_link A p₁
      ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I B A vp₀ vp₁ vA hLA hp.
  induction A in vA |- *.
  - cbn - [semantic_judgement].
    eapply weaken_rule. 1: apply ret_rule.
    intros [h₀ h₁] post.
    cbn. unfold SPropMonadicStructures.SProp_op_order.
    unfold Basics.flip, SPropMonadicStructures.SProp_order.
    intros [HI Hp].
    apply Hp. intuition auto.
  - cbn - [semantic_judgement lookup_op].
    apply inversion_valid_opr in vA as hA. destruct hA as [hi vk].
    destruct o as [id [S T]].
    eapply from_valid_package in vp₀.
    specialize (vp₀ _ hi). simpl in vp₀.
    destruct vp₀ as [f₀ [e₀ h₀]].
    eapply from_valid_package in vp₁.
    specialize (vp₁ _ hi). simpl in vp₁.
    destruct vp₁ as [f₁ [e₁ h₁]].
    erewrite lookup_op_spec_inv. 2: eauto.
    erewrite lookup_op_spec_inv. 2: eauto.
    specialize (hp id S T x hi).
    erewrite get_op_default_spec in hp. 2: eauto.
    erewrite get_op_default_spec in hp. 2: eauto.
    rewrite !repr_bind.
    eapply bind_rule_pp. 1:{ rewrite -rel_jdgE. exact hp. }
    cbn - [semantic_judgement].
    intros a₀ a₁.
    apply pre_hypothesis_rule.
    intros s₀ s₁ [? ?]. subst.
    eapply pre_weaken_rule. 1: eapply H.
    + eapply vk.
    + cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_getr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (get_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply H.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    apply inversion_valid_putr in vA as hA. destruct hA as [hi vk].
    match goal with
    | |- ⊨ ⦃ ?pre_ ⦄ bindrFree ?m_ ?f1_ ≈ bindrFree _ ?f2_ ⦃ ?post_ ⦄ =>
      eapply (bind_rule_pp (f1 := f1_) (f2 := f2_) m_ m_ pre_ _ post_)
    end.
    + eapply (@put_case LA). all: auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply IHA.
      * eapply vk.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
  - cbn - [semantic_judgement bindrFree].
    eapply bind_rule_pp.
    + eapply (@sampler_case LA). auto.
    + intros a₀ a₁. cbn - [semantic_judgement].
      eapply pre_hypothesis_rule.
      intros s₀ s₁ [? ?]. subst a₁.
      eapply pre_weaken_rule. 1: eapply H.
      * eapply inversion_valid_sampler. eauto.
      * cbn. intros s₀' s₁' [? ?]. subst. auto.
Qed.

(* TODO RENAME *)
Lemma prove_relational :
  ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) (A : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁}
    `{ValidPackage LA E A_export A},
    INV' L₀ L₁ I →
    I (empty_heap, empty_heap) →
    fdisjoint LA L₀ →
    fdisjoint LA L₁ →
    eq_up_to_inv E I p₀ p₁ →
    AdvantageE p₀ p₁ A = 0.
Proof.
  intros L₀ L₁ LA E p₀ p₁ I A vp₀ vp₁ vA hI' hIe hd₀ hd₁ hp.
  unfold AdvantageE, Pr.
  pose r := get_op_default A RUN tt.
  assert (hI : INV LA I).
  { unfold INV. intros s₀ s₁. split.
    - intros hi l hin. apply hI'.
      + assumption.
      + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
      + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
    - intros hi l v hin. apply hI'.
      + assumption.
      + move: hd₀ => /fdisjointP hd₀. apply hd₀. assumption.
      + move: hd₁ => /fdisjointP hd₁. apply hd₁. assumption.
  }
  unshelve epose proof (some_lemma_for_prove_relational p₀ p₁ I r hI hp) as h.
  1:{
    eapply valid_get_op_default.
    - eauto.
    - auto_in_fset.
  }
  assert (
    ∀ x y : tgt RUN * heap_choiceType,
      (let '(b₀, s₀) := x in λ '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁)) y →
      (fst x == true) ↔ (fst y == true)
  ) as Ha.
  { intros [b₀ s₀] [b₁ s₁]. simpl.
    intros [e ?]. rewrite e. intuition auto.
  }
  unfold Pr_op.
  unshelve epose (rhs := thetaFstd _ (repr (code_link r p₀)) empty_heap).
  simpl in rhs.
  epose (lhs := Pr_op (A ∘ p₀) RUN tt empty_heap).
  assert (lhs = rhs) as he.
  { subst lhs rhs.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    rewrite get_op_default_link. reflexivity.
  }
  unfold lhs in he. unfold Pr_op in he.
  rewrite he.
  unshelve epose (rhs' := thetaFstd _ (repr (code_link r p₁)) empty_heap).
  simpl in rhs'.
  epose (lhs' := Pr_op (A ∘ p₁) RUN tt empty_heap).
  assert (lhs' = rhs') as e'.
  { subst lhs' rhs'.
    unfold Pr_op. unfold Pr_code.
    unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
    apply f_equal. apply f_equal.
    rewrite get_op_default_link. reflexivity.
  }
  unfold lhs' in e'. unfold Pr_op in e'.
  rewrite e'.
  unfold rhs', rhs.
  unfold SDistr_bind. unfold SDistr_unit.
  rewrite !dletE.
  assert (
    ∀ x : bool_choiceType * heap_choiceType,
      ((let '(b, _) := x in dunit (R:=R) (T:=bool_choiceType) b) true) ==
      (x.1 == true)%:R
  ) as h1.
  { intros [b s].
    simpl. rewrite dunit1E. apply/eqP. reflexivity.
  }
  assert (
    ∀ y,
      (λ x : prod_choiceType (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true) =
      (λ x : prod_choiceType (tgt RUN) heap_choiceType, (x.1 == true)%:R * (y x))
  ) as Hrew.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite !Hrew.
  unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
  unfold SubDistr.SDistr_obligation_2. simpl.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite !SDistr_rightneutral. simpl.
  pose proof (Pr_eq_empty _ _ _ _ h hIe Ha) as Heq.
  simpl in Heq.
  unfold θ_dens in Heq.
  simpl in Heq. unfold pr in Heq.
  simpl in Heq.
  rewrite Heq.
  rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
  assert (∀ (x : R), `|x - x| = 0) as Hzero.
  { intros x.
    assert (x - x = 0) as H3.
    { apply /eqP. rewrite GRing.subr_eq0. intuition. }
    rewrite H3. apply mc_1_10.Num.Theory.normr0.
  }
  apply Hzero.
Qed.

Lemma eq_rel_perf_ind :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package) (I : precond)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    INV' L₀ L₁ I →
    I (empty_heap, empty_heap) →
    eq_up_to_inv E I p₀ p₁ →
    p₀ ≈₀ p₁.
Proof.
  intros L₀ L₁ E p₀ p₁ I v₀ v₁ hI' hIe he.
  intros LA A vA hd₀ hd₁.
  eapply prove_relational. all: eauto.
Qed.

(* Special case where the invariant is equality of state. *)
Corollary eq_rel_perf_ind_eq :
  ∀ {L₀ L₁ E} (p₀ p₁ : raw_package)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    eq_up_to_inv E (λ '(h₀, h₁), h₀ = h₁) p₀ p₁ →
    p₀ ≈₀ p₁.
Proof.
  intros L₀ L₁ E p₀ p₁ v₀ v₁ h.
  eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁).
  - simpl. intros s₀ s₁. split.
    + intro e. rewrite e. auto.
    + intro e. rewrite e. auto.
  - reflexivity.
  - assumption.
Qed.

(* Rules for packages *)
(* same as in RulesStateprob.v with `r` at the beginning *)

(* Alternative to rbind_rule *)
Lemma r_bind :
  ∀ {A₀ A₁ B₀ B₁ : ord_choiceType} m₀ m₁ f₀ f₁
    (pre : precond) (mid : postcond A₀ A₁) (post : postcond B₀ B₁),
    ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ mid ⦄ →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₀, s₁), mid (a₀, s₀) (a₁, s₁) ⦄ f₀ a₀ ≈ f₁ a₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ bind m₀ f₀ ≈ bind m₁ f₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ B₀ B₁ m₀ m₁ f₀ f₁ pre mid post hm hf.
  rewrite rel_jdgE. eapply rbind_rule.
  - rewrite -rel_jdgE. exact hm.
  - intros a₀ a₁. rewrite -rel_jdgE. eapply hf.
Qed.

(* Pre-condition manipulating rules *)

Theorem rpre_weaken_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre pre' : precond) post,
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
    (∀ s₀ s₁, pre' (s₀, s₁) → pre (s₀, s₁)) →
    ⊢ ⦃ pre' ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre pre' post he hi.
  rewrite -> rel_jdgE in *.
  eapply pre_weaken_rule. all: eauto.
Qed.

Theorem rpre_hypothesis_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁,
      pre (s₀, s₁) → ⊢ ⦃ λ s, s.1 = s₀ ∧ s.2 = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
    ) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post h.
  rewrite rel_jdgE.
  eapply pre_hypothesis_rule.
  intros. rewrite -rel_jdgE.
  apply h. auto.
Qed.

Theorem rpre_strong_hypothesis_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁, pre (s₀, s₁)) →
    ⊢ ⦃ λ _, True ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post hs h.
  rewrite -> rel_jdgE in *.
  eapply pre_strong_hypothesis_rule.
  all: eauto.
Qed.

Theorem rpost_weaken_rule :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) (post1 post2 : postcond A₀ A₁),
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post1 ⦄ →
    (∀ a₀ a₁, post1 a₀ a₁ → post2 a₀ a₁) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post2 ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post1 post2 h hi.
  rewrite -> rel_jdgE in *.
  eapply post_weaken_rule. all: eauto.
Qed.

Local Open Scope package_scope.

Lemma rreflexivity_rule :
  ∀ {A : ord_choiceType} (c : raw_code A),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ eq ⦄.
Proof.
  intros A c.
  rewrite -> rel_jdgE.
  apply (reflexivity_rule (repr c)).
Qed.

(* TODO MOVE? *)
(* bindrFree_and_ret is too constrained *)
Lemma bindrFree_ret :
  ∀ S P A (m : rFreeF S P A),
    bindrFree m (λ x, retrFree x) = m.
Proof.
  intros S P A m.
  induction m.
  - reflexivity.
  - cbn. f_equal. extensionality x. auto.
Qed.

Theorem rpost_conclusion_rule :
  ∀ {A₀ A₁ B : ord_choiceType} {pre : precond}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁}
    (f₀ : A₀ → B) (f₁ : A₁ → B),
    ⊢ ⦃ pre ⦄
      x₀ ← c₀ ;; ret x₀ ≈ x₁ ← c₁ ;; ret x₁
    ⦃ λ '(a₀, s₀) '(a₁, s₁), s₀ = s₁ ∧ f₀ a₀ = f₁ a₁ ⦄ →
    ⊢ ⦃ pre ⦄ x₀ ← c₀ ;; ret (f₀ x₀) ≈ x₁ ← c₁ ;; ret (f₁ x₁) ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B pre c₀ c₁ f₀ f₁ h.
  rewrite rel_jdgE. rewrite rel_jdgE in h.
  rewrite !repr_bind in h. rewrite !repr_bind.
  eapply bind_rule_pp.
  - simpl (repr (ret _)) in h.
    rewrite !bindrFree_ret in h. exact h.
  - intros a₀ a₁. rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s s' [? e]. subst s'.
    rewrite e. eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

Theorem rpost_conclusion_rule_cmd :
  ∀ {A₀ A₁ B : ord_choiceType} {pre : precond}
    {c₀ : command A₀} {c₁ : command A₁}
    (f₀ : A₀ → B) (f₁ : A₁ → B),
    ⊢ ⦃ pre ⦄
      x₀ ← cmd c₀ ;; ret x₀ ≈
      x₁ ← cmd c₁ ;; ret x₁
    ⦃ λ '(a₀, s₀) '(a₁, s₁), s₀ = s₁ ∧ f₀ a₀ = f₁ a₁ ⦄ →
    ⊢ ⦃ pre ⦄ x₀ ← cmd c₀ ;; ret (f₀ x₀) ≈ x₁ ← cmd c₁ ;; ret (f₁ x₁) ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B pre c₀ c₁ f₀ f₁ h.
  rewrite rel_jdgE. rewrite rel_jdgE in h.
  rewrite !repr_cmd_bind in h.  rewrite !repr_cmd_bind.
  eapply bind_rule_pp.
  - simpl (repr (ret _)) in h.
    rewrite !bindrFree_ret in h. exact h.
  - intros a₀ a₁. rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s s' [? e]. subst s'.
    rewrite e. eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

Lemma r_ret :
  ∀ {A₀ A₁ : ord_choiceType} u₀ u₁ (pre : precond) (post : postcond A₀ A₁),
    (∀ s₀ s₁, pre (s₀, s₁) → post (u₀, s₀) (u₁, s₁)) →
    ⊢ ⦃ pre ⦄ ret u₀ ≈ ret u₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ u₀ u₁ pre post h.
  rewrite rel_jdgE. simpl.
  eapply weaken_rule. 1: eapply ret_rule.
  intros [s₀ s₁] P [hpre hpost]. simpl.
  eapply hpost. eapply h. apply hpre.
Qed.

Lemma repr_if :
  ∀ {A b} (c₀ c₁ : raw_code A),
    repr (if b then c₀ else c₁) = if b then repr c₀ else repr c₁.
Proof.
  intros A b c₀ c₁.
  destruct b. all: reflexivity.
Qed.

(* TW: The (∀ s, pre s → b₀ = b₁) hypothesis is really weird.
  The booleans do not depend on s, is that to say that they must be equal
  unless pre is empty?
*)
Theorem rif_rule :
  ∀ {A₀ A₁ : ord_choiceType}
    (c₀ c₀' : raw_code A₀) (c₁ c₁' : raw_code A₁)
    {b₀ b₁}
    {pre : precond} {post : postcond A₀ A₁},
    (∀ s, pre s → b₀ = b₁) →
    ⊢ ⦃ λ s, pre s ∧ b₀ = true ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ λ s, pre s ∧ b₀ = false ⦄ c₀' ≈ c₁' ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ if b₀ then c₀ else c₀' ≈ if b₁ then c₁ else c₁' ⦃ post ⦄.
Proof.
  intros A₀ A₁ c₀ c₀' c₁ c₁' b₀ b₁ pre post hb ht hf.
  rewrite -> rel_jdgE in *.
  rewrite !repr_if.
  eapply if_rule. all: eauto.
Qed.

(* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)

(* skipped for now:
Theorem bounded_do_while_rule *)

(*TODO: asymmetric variants of bounded_do_while --
  Rem.: low priority as not useful for our examples *)

Section For_loop_rule.

  (* for i = 0 to N : do c *)
  Fixpoint for_loop (c : nat → raw_code 'unit) (N : nat) : raw_code 'unit :=
    match N with
    | 0 => c 0%nat
    | S m => for_loop c m ;; c (S m)
    end.

  Context (I : nat → precond) (N : nat).

  Context (c₀ c₁ : nat → raw_code 'unit).

  (* hypothesis : *)
  (* body maintains the loop invariant I *)
  (* to ease the proof we forget about this condition (0 <= n <= N)%nat -> *)

  Lemma for_loop_rule :
    (∀ i, ⊢ ⦃ I i ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I i.+1 (s₀,s₁) ⦄) →
    ⊢ ⦃ I 0%nat ⦄
      for_loop c₀ N ≈ for_loop c₁ N
    ⦃ λ '(_,s₀) '(_,s₁), I N.+1 (s₀,s₁) ⦄.
  Proof.
    intros h.
    induction N as [| n ih].
    - simpl. apply h.
    - simpl. eapply r_bind.
      + eapply ih.
      + simpl. intros _ _. eapply h.
  Qed.

End For_loop_rule.

(* alternative, more imperative version (weaker)*)
(* Section For_loop_rule. *)
(* (*for i = 0 to N : do c*) *)
(*   Fixpoint for_loop (c : nat -> raw_code 'unit) *)
(*                     (N : nat) : raw_code 'unit := *)
(*   match N with *)
(*   | 0 => c 0%nat *)
(*   | S m => bind (for_loop c m) (λ _, c (S m)) *)
(*   end. *)

(*   Context (I : nat -> precond) *)
(*           (N : nat). *)

(*   Context (c0 c1 : raw_code 'unit). *)

(*   (* hypothesis : *) *)
(*   (*body maintains the loop invariant I*) *)
(*   (* to ease the proof we forget about this condition (0 <= n <= N)%nat -> *) *)

(*   Lemma for_loop_rule : *)
(*   (forall n : nat, *)
(*    ⊢ ⦃ I n ⦄ c0 ≈ c1 ⦃ λ '(_, s0) '(_, s1), I n.+1 (s0,s1) ⦄ ) -> *)
(*   ⊢ ⦃ I 0%nat ⦄ for_loop (λ _, c0) N ≈ for_loop (λ _, c1) N ⦃ λ '(_,s0) '(_,s1), I N.+1 (s0,s1) ⦄. *)
(*   Proof. *)
(*   move=> Hbody. *)
(*   elim: N. *)
(*   - rewrite /=. apply (Hbody 0%nat). *)
(*   - move=> /= n IH. *)
(*     rewrite rel_jdgE in IH. rewrite rel_jdgE. *)
(*     unshelve eapply (  @rbind_rule _ _ _ _ (λ _, c0) (λ _, c1) *)
(*           (for_loop (fun=> c0) n) (for_loop (fun=> c1) n) ). *)
(*     1:{ exact ( λ '(_, s0) '(_, s2), I n.+1 (s0, s2) ). } *)
(*     1:{ assumption. } *)
(*     move=> tt1 tt2. rewrite /=. *)
(*     pose (Hbody_suc := (Hbody n.+1)). rewrite -rel_jdgE. *)
(*     assumption. *)
(*   Qed. *)

(* End For_loop_rule. *)

Lemma valid_for_loop :
  ∀ L I c N,
    (∀ i, valid_code L I (c i)) →
    valid_code L I (for_loop c N).
Proof.
  intros L I c N h.
  induction N. all: simpl.
  - eapply h.
  - eapply valid_bind. all: eauto.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (for_loop ?c ?N)) =>
  eapply valid_for_loop ;
  intro ; eapply valid_code_from_class
  : typeclass_instances packages.

Lemma rcoupling_eq :
  ∀ {A : ord_choiceType} (K₀ K₁ : raw_code A) (ψ : precond),
    ⊢ ⦃ ψ ⦄ K₀ ≈ K₁ ⦃ eq ⦄ →
    ∀ s₀ s₁,
      ψ (s₀, s₁) →
      θ_dens (θ0 (repr K₀) s₀) = θ_dens (θ0 (repr K₁) s₁).
Proof.
  intros A K₀ K₁ ψ h s₀ s₁ hψ.
  rewrite -> rel_jdgE in h.
  eapply coupling_eq. all: eauto.
Qed.

Lemma rrewrite_eqDistrL :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ c₀' : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    (∀ s, θ_dens (θ0 (repr c₀) s) = θ_dens (θ0 (repr c₀') s)) →
    ⊢ ⦃ P ⦄ c₀' ≈ c₁ ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₀' c₁ h hθ.
  rewrite -> rel_jdgE in *.
  eapply rewrite_eqDistrL. all: eauto.
Qed.

Lemma rrewrite_eqDistrR :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ : raw_code A₀) (c₁ c₁' : raw_code A₁),
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    (∀ s, θ_dens (θ0 (repr c₁) s) = θ_dens (θ0 (repr c₁') s)) →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁' ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₁ c₁' h hθ.
  rewrite -> rel_jdgE in *.
  eapply rewrite_eqDistrR. all: eauto.
Qed.

Theorem rswap_rule :
  ∀ {A₀ A₁ : ord_choiceType} {I : precond} {post : postcond A₀ A₁}
    (c₀ : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ I ⦄ c₀ ≈ c₁
      ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
    ⊢ ⦃ I ⦄ c₁ ≈ c₀
      ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
    ⊢ ⦃ I ⦄ c₀ ;; c₁ ≈ c₁ ;; c₀
      ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄.
Proof.
  intros A₀ A₁ I post c₀ c₁ h1 h2.
  rewrite rel_jdgE in h1. rewrite rel_jdgE in h2.
  rewrite rel_jdgE.
  rewrite !repr_bind.
  eapply (swap_rule (repr c₀) (repr c₁)). all: auto.
Qed.

(** TW: I guess this to allow going under binders.
  We might be better off defining some morphisms on semantic judgments
  to use setoid_rewrite.
*)
Theorem rswap_ruleL :
  ∀ {A₀ A₁ B : ord_choiceType} {pre I : precond} {post : postcond A₁ A₀}
  (l : raw_code B) (c₀ : raw_code A₀) (c₁ : raw_code A₁),
  ⊢ ⦃ pre ⦄ l ≈ l ⦃ λ '(b₀, s₀) '(b₁, s₁), I (s₀, s₁) ⦄ →
  ⊢ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
  ⊢ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
  ⊢ ⦃ pre ⦄ l ;; c₀ ;; c₁ ≈ l ;; c₁ ;; c₀ ⦃ post ⦄.
Proof.
  intros A₀ A₁ B pre I post l c₀ c₁ hl h0 h1.
  rewrite rel_jdgE in h0. rewrite rel_jdgE in h1. rewrite rel_jdgE in hl.
  rewrite rel_jdgE.
  rewrite !repr_bind.
  eapply swap_ruleL. all: eauto.
Qed.

Theorem rswap_ruleR :
  ∀ {A₀ A₁ B : ord_choiceType} {post : postcond B B}
    (c₀ : raw_code A₀) (c₁ : raw_code A₁) (r : A₀ → A₁ → raw_code B),
    (∀ b b', b = b' → post b b') →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁) ≈
      a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈
      a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
      ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r postr hr h.
  rewrite rel_jdgE.
  repeat setoid_rewrite repr_bind. simpl.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr c₀) (repr c₁)).
  - intros. rewrite -rel_jdgE. apply hr.
  - apply postr.
  - intro s.
    unshelve eapply coupling_eq.
    + exact (λ '(h₀, h₁), h₀ = h₁).
    + rewrite rel_jdgE in h. repeat setoid_rewrite repr_bind in h.
      apply h.
    + reflexivity.
Qed.

Local Open Scope package_scope.

Lemma rsym_pre :
  ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁},
    (∀ h₀ h₁, pre (h₀, h₁) → pre (h₁, h₀)) →
    ⊢ ⦃ λ '(h₀, h₁), pre (h₁, h₀) ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post c₀ c₁ pre_sym h.
  unshelve eapply rpre_weaken_rule. 2: eassumption.
  assumption.
Qed.

Lemma rsymmetry :
  ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
    {c₀ : raw_code A₀} {c₁ : raw_code A₁},
    ⊢ ⦃ λ '(h₁, h₀), pre (h₀, h₁) ⦄ c₁ ≈ c₀
      ⦃ λ '(a₁, h₁) '(a₀, h₀), post (a₀, h₀) (a₁, h₁) ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post c₀ c₁ h.
  rewrite rel_jdgE.
  eapply symmetry_rule. rewrite -rel_jdgE. auto.
Qed.

Definition spl (o : Op) :=
  @callrFree (@ops_StP heap_choiceType) (@ar_StP heap_choiceType) (op_iota o).

Lemma rsamplerC :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r) ≈
      r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rrewrite_eqDistrL.
  - eapply rreflexivity_rule.
  - intro s.
    assert (
      repr_sample_c :
        repr (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r)) =
        bindrFree (spl o) (λ r, bindrFree (repr c) (λ a, retrFree (a,r)))
    ).
    { rewrite !repr_bind. f_equal. extensionality r.
      rewrite !repr_bind. reflexivity.
    }
    assert (
      repr_c_sample :
        repr (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r)) =
        bindrFree (repr c) (λ a, bindrFree (spl o) (λ r, retrFree (a,r)))
    ).
    { rewrite repr_bind. reflexivity. }
    rewrite repr_c_sample repr_sample_c.
    pose proof (sample_c_is_c_sample o (repr c) s) as hlp.
    unfold sample_c in hlp. unfold c_sample in hlp.
    apply hlp.
Qed.

Lemma rsamplerC_sym' :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← c ;; r ← (r ← sample o ;; ret r) ;;  (ret (r, a)) ≈
      r ← (r ← sample o ;; ret r) ;; a ← c ;;  (ret (r, a))
    ⦃ eq ⦄.
Proof.
  intros A o c.
  unshelve eapply rswap_ruleR.
  - auto.
  - intros a r. apply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - apply rsamplerC.
Qed.

Lemma rsamplerC' :
  ∀ {A : ord_choiceType} (o : Op) (c : raw_code A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (r, a) ≈
      a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (r, a)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - apply rsamplerC_sym'.
  - intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

(* TODO: generalize the corresponding rule in RulesStateProb.v  *)
Theorem rswap_rule_ctx :
∀ {A : ord_choiceType} {I pre} {post Q : postcond A A}
  (l r c₀ c₁ : raw_code A),
  ⊢ ⦃ pre ⦄ l ≈ l ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ⦄ →
  (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), Q (a₀,s₀) (a₁,s₁) ⦄ r ≈ r ⦃ post ⦄) →
  ⊢ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
  ⊢ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
  ⊢ ⦃ pre ⦄ l ;; c₀ ;; c₁ ;; r ≈ l ;; c₁ ;; c₀ ;; r ⦃ post ⦄.
Proof.
  intros A I pre post Q l r c₀ c₁ hl hr h₀ h₁.
  rewrite rel_jdgE.
  rewrite !repr_bind.
  eapply swap_rule_ctx.
  1:{ rewrite -rel_jdgE. exact hl. }
  2:{ rewrite -rel_jdgE. exact h₀. }
  2:{ rewrite -rel_jdgE. exact h₁. }
  intros a₀ a₁. rewrite -rel_jdgE. eapply hr.
Qed.

Theorem rsame_head :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
  (m : raw_code A) (post : postcond B B),
  (∀ a, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ bind m f₀ ≈ bind m f₁ ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m post h.
  eapply (r_bind m m).
  - eapply rreflexivity_rule.
  - intros a₀ a₁.
    eapply rpre_hypothesis_rule. intros s₀ s₁ e.
    noconf e.
    eapply rpre_weaken_rule. 1: eapply h.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

(* CA: not more useful than sampler_case *)
(* Lemma rsample_rule { B1 B2 : ord_choiceType} { L : {fset Location}}  { o } *)
(*       c1 c2  *)
(*       pre (post : B1 * heap -> B2 * heap -> Prop) *)
(*       (H : ⊢ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄) : *)
(*          ⊨ ⦃ pre ⦄ repr (locs := L ) (x <$ o ;; c1) ≈ repr (locs := L) (x <$ o ;; c2) ⦃ post ⦄. *)
(* Proof. Admitted.  *)

Lemma rf_preserves_eq :
  ∀ {A B : ord_choiceType} {c₀ c₁ : raw_code A}
    (f : A → B),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← c₀ ;; ret x ≈ x ← c₁ ;; ret x ⦃ eq ⦄ →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ x ← c₀ ;; ret (f x) ≈ x ← c₁ ;; ret (f x) ⦃ eq ⦄.
Proof.
  intros A B c₀ c₁ f h.
  eapply r_bind.
  - rewrite !bind_ret in h. exact h.
  - intros a₀ a₁.
    apply rpre_hypothesis_rule. intros s₀ s₁ e. noconf e.
    eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros ? ? [? ?]. subst. reflexivity.
Qed.

(* Rules I added *)

(* Similar to rrewrite_eqDistr but with program logic. *)
Lemma r_transL :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ c₀' : raw_code A₀) (c₁ : raw_code A₁),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c₀ ≈ c₀' ⦃ eq ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    ⊢ ⦃ P ⦄ c₀' ≈ c₁ ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₀' c₁ he h.
  eapply rrewrite_eqDistrL. 1: exact h.
  intro s. eapply rcoupling_eq. 1: exact he.
  cbn. reflexivity.
Qed.

Lemma r_transR :
  ∀ {A₀ A₁ : ord_choiceType} {P Q}
    (c₀ : raw_code A₀) (c₁ c₁' : raw_code A₁),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c₁ ≈ c₁' ⦃ eq ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
    ⊢ ⦃ P ⦄ c₀ ≈ c₁' ⦃ Q ⦄.
Proof.
  intros A₀ A₁ P Q c₀ c₁ c₁' he h.
  eapply rrewrite_eqDistrR. 1: exact h.
  intro s. eapply rcoupling_eq. 1: exact he.
  cbn. reflexivity.
Qed.

(* Rules using commands instead of bind *)

Theorem rsame_head_cmd :
  ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_code B}
  (m : command A) (post : postcond B B),
  (∀ a, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← cmd m ;; f₀ x ≈ x ← cmd m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B f₀ f₁ m post h.
  rewrite rel_jdgE. rewrite !repr_cmd_bind.
  eapply (bind_rule_pp (repr_cmd m) (repr_cmd m)).
  - apply (reflexivity_rule (repr_cmd m)).
  - intros a₀ a₁. rewrite -rel_jdgE.
    unshelve eapply rpre_weaken_rule.
    + exact (λ '(h₀, h₁), a₀ = a₁ ∧ h₀ = h₁).
    + specialize (h a₀).
      eapply rpre_hypothesis_rule. simpl. intros s₀ s₁ [ea es]. subst.
      eapply rpre_weaken_rule. 1: exact h.
      simpl. intros h₀ h₁ [? ?]. subst. reflexivity.
    + simpl. intros s₀ s₁ e. noconf e. intuition auto.
Qed.

Lemma rswap_cmd :
  ∀ (A₀ A₁ B : choiceType) (post : postcond B B)
    (c₀ : command A₀) (c₁ : command A₁)
    (r : A₀ → A₁ → raw_code B),
    (∀ b, post b b) →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
      ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r hpost hr h.
  rewrite rel_jdgE.
  repeat setoid_rewrite repr_cmd_bind.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr_cmd c₀) (repr_cmd c₁)).
  + intros a₀ a₁. rewrite -rel_jdgE. eapply hr.
  + intros ? ? []. eauto.
  + intro s. unshelve eapply coupling_eq.
    * exact: (λ '(h1, h2), h1 = h2).
    * rewrite rel_jdgE in h.
      repeat (setoid_rewrite repr_cmd_bind in h).
      auto.
    * reflexivity.
Qed.

(* Specialised version to use when post = eq *)
Lemma rswap_cmd_eq :
  ∀ (A₀ A₁ B : choiceType)
    (c₀ : command A₀) (c₁ : command A₁)
    (r : A₀ → A₁ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
      ⦃ eq ⦄.
Proof.
  intros A₀ A₁ B c₀ c₁ r h.
  eapply rswap_cmd.
  - intro. reflexivity.
  - intros a₀ a₁. eapply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - auto.
Qed.

Theorem rswap_ruleR_cmd :
  ∀ {A₀ A₁ B : ord_choiceType} {post : postcond B B}
    (c₀ : command A₀) (c₁ : command A₁) (r : A₀ → A₁ → raw_code B),
    (∀ b b', b = b' → post b b') →
    (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ≈
      a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
      ⦃ post ⦄.
Proof.
  intros A₀ A₁ B post c₀ c₁ r postr hr h.
  rewrite rel_jdgE.
  repeat setoid_rewrite repr_cmd_bind. simpl.
  eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr_cmd c₀) (repr_cmd c₁)).
  - intros. rewrite -rel_jdgE. apply hr.
  - apply postr.
  - intro s.
    unshelve eapply coupling_eq.
    + exact (λ '(h₀, h₁), h₀ = h₁).
    + rewrite rel_jdgE in h. repeat setoid_rewrite repr_cmd_bind in h.
      apply h.
    + reflexivity.
Qed.

Lemma rsamplerC_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a ← cmd c ;; r ← sample o ;; ret (a, r) ≈
      r ← sample o ;; a ← cmd c ;; ret (a, r)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rrewrite_eqDistrL.
  - eapply rreflexivity_rule.
  - intro s.
    assert (
      repr_sample_c :
        repr (r ← sample o ;; a ← cmd c ;; ret (a, r)) =
        bindrFree (spl o) (λ r, bindrFree (repr_cmd c) (λ a, retrFree (a,r)))
    ).
    { simpl. f_equal. extensionality r. rewrite repr_cmd_bind. reflexivity. }
    assert (
      repr_c_sample :
        repr (a ← cmd c ;; r ← sample o ;; ret (a, r)) =
        bindrFree (repr_cmd c) (λ a, bindrFree (spl o) (λ r, retrFree (a,r)))
    ).
    { rewrite repr_cmd_bind. reflexivity. }
    rewrite repr_c_sample repr_sample_c.
    pose proof (sample_c_is_c_sample o (repr_cmd c) s) as hlp.
    unfold sample_c in hlp. unfold c_sample in hlp.
    apply hlp.
Qed.

Lemma rsamplerC_sym'_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    a ← cmd c ;; r ← sample o ;; ret (r, a) ≈
    r ← sample o ;; a ← cmd c ;; ret (r, a)
    ⦃ eq ⦄.
Proof.
  intros A o c.
  unshelve eapply (rswap_ruleR_cmd _ (cmd_sample _)).
  - auto.
  - intros a r. apply rsym_pre. 1: auto.
    apply rreflexivity_rule.
  - apply rsamplerC_cmd.
Qed.

Lemma rsamplerC'_cmd :
  ∀ {A : ord_choiceType} (o : Op) (c : command A),
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    r ← sample o ;; a ← cmd c ;; ret (r, a) ≈
    a ← cmd c ;; r ← sample o ;; ret (r, a)
  ⦃ eq ⦄.
Proof.
  intros A o c.
  eapply rsymmetry. eapply rsym_pre. 1: auto.
  eapply rpost_weaken_rule.
  - apply rsamplerC_sym'_cmd.
  - intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

Theorem rdead_sampler_elimL :
  ∀ {A : ord_choiceType} {D}
    (c₀ c₁ : raw_code A) (pre : precond) (post : postcond A A),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ (x ← sample D ;; ret x) ;; c₀ ≈ c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ pre post h.
  eapply rrewrite_eqDistrL. 1: exact h.
  admit.
Admitted.

Theorem rdead_sampler_elimR :
  ∀ {A : ord_choiceType} {D}
    (c₀ c₁ : raw_code A) (pre : precond) (post : postcond A A),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ (x ← sample D ;; ret x) ;; c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ pre post h.
  eapply rrewrite_eqDistrR. 1: exact h.
  admit.
Admitted.

(* One-sided sampling rule. *)
(* Removes the need for intermediate games in some cases. *)
Lemma rconst_samplerL :
  ∀ {A : ord_choiceType} {D}
    (c₀ : Arit D -> raw_code A) (c₁ : raw_code A) (post : postcond A A),
    (∀ x, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← sample D ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof.
  intros A D c₀ c₁ post h.
  eapply r_transR with (x ← sample D ;; (λ _, c₁) x).
  - apply rdead_sampler_elimL.
    apply rreflexivity_rule.
  - apply (rsame_head_cmd (cmd_sample D)).
    apply h.
Qed.

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
    #|prod_finType (ordinal_finType i) (ordinal_finType j)| = (i * j)%N.
Proof.
  intros i j.
  rewrite card_prod. simpl. rewrite !card_ord. reflexivity.
Qed.

Definition ch2prod {i j} `{Positive i} `{Positive j}
  (x : Arit (uniform (i * j))) :
  prod_choiceType (Arit (uniform i)) (Arit (uniform j)).
Proof.
  simpl in *.
  eapply otf. rewrite card_prod_iprod.
  auto.
Defined.

Definition prod2ch {i j} `{Positive i} `{Positive j}
  (x : prod_choiceType (Arit (uniform i)) (Arit (uniform j))) :
  Arit (uniform (i * j)).
Proof.
  simpl in *.
  rewrite -card_prod_iprod.
  eapply fto.
  auto.
Defined.

Definition ch2prod_prod2ch :
  ∀ {i j} `{Positive i} `{Positive j} (x : prod_choiceType (Arit (uniform i)) (Arit (uniform j))),
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

(** Rules on uniform distributions  *)

Lemma r_uniform_bij :
  ∀ {A₀ A₁ : ord_choiceType} i j `{Positive i} `{Positive j} pre post f
    (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
    bijective f →
    (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄
      x ← sample uniform i ;; c₀ x ≈
      x ← sample uniform j ;; c₁ x
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ i j pi pj pre post f c₀ c₁ bijf h.
  rewrite rel_jdgE.
  change (repr (sampler (uniform ?i) ?k))
  with (bindrFree (@Uniform_F (mkpos i) heap_choiceType) (λ x, repr (k x))).
  eapply bind_rule_pp.
  - eapply Uniform_bij_rule. eauto.
  - intros a₀ a₁. simpl.
    rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
    move: e => /eqP e. subst.
    eapply rpre_weaken_rule. 1: eapply h.
    intros h₀ h₁. simpl. intros [? ?]. subst. auto.
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
  ∀ i `{Positive i}, ordinal_finType i.
Proof.
  intros i hi.
  exists 0%N. auto.
Qed.

Section Uniform_prod.

  Let SD_bind
      {A B : choiceType}
      (m : SDistr_carrier A)
      (k : A -> SDistr_carrier B) :=
    SDistr_bind k m.

  Let SD_ret {A : choiceType} (a : A) :=
    SDistr_unit A a.

  Arguments r _ _ : clear implicits.
  Arguments r [_] _.
  Arguments uniform_F _ _ : clear implicits.
  Arguments uniform_F [_] _.

  Lemma uniform_F_prod_bij :
    ∀ i j `{Positive i} `{Positive j} (x : 'I_i) (y : 'I_j),
      mkdistr
        (mu := λ _ : 'I_i * 'I_j, r (x, y))
        (@is_uniform _ (x,y))
      =
      SDistr_bind
        (λ z : 'I_(i * j),
          SDistr_unit _ (ch2prod z)
        )
        (mkdistr
          (mu := λ f : 'I_(i * j), r f)
          (@is_uniform _ (F_w0 (mkpos (i * j))))
        ).
  Proof.
    intros i j pi pj x y.
    apply distr_ext. simpl. intros [a b].
    unfold SDistr_bind. rewrite dletE. simpl.
    rewrite psumZ.
    2:{
      unshelve eapply @r_nonneg. eapply ordinal_finType_inhabited.
      exact _.
    }
    unfold r. rewrite card_prod. simpl.
    rewrite !card_ord.
    unfold SDistr_unit. unfold dunit. unlock. unfold drat. unlock. simpl.
    unfold mrat. simpl.
    erewrite eq_psum.
    2:{
      simpl. intro u. rewrite GRing.divr1. rewrite addn0. reflexivity.
    }
    erewrite psum_finseq with (r := [:: prod2ch (a, b)]).
    2: reflexivity.
    2:{
      simpl. intros u hu. rewrite inE in hu.
      destruct (ch2prod u == (a,b)) eqn:e.
      2:{
        exfalso.
        move: hu => /negP hu. apply hu. apply eqxx.
      }
      move: e => /eqP e. rewrite -e.
      rewrite inE. apply /eqP. symmetry. apply prod2ch_ch2prod.
    }
    rewrite bigop.big_cons bigop.big_nil.
    rewrite ch2prod_prod2ch. rewrite eqxx. simpl.
    rewrite GRing.addr0. rewrite normr1.
    rewrite GRing.mulr1. reflexivity.
  Qed.

  Lemma SDistr_bind_unit_unit :
    ∀ (A B C : ord_choiceType) (f : A → B) (g : B → C) u,
      SDistr_bind (λ y, SDistr_unit _ (g y)) (SDistr_bind (λ x, SDistr_unit _ (f x)) u) =
      SDistr_bind (λ x, SDistr_unit _ (g (f x))) u.
  Proof.
    intros A B C f g u.
    apply distr_ext. simpl. intro z.
    unfold SDistr_bind. unfold SDistr_unit.
    rewrite dlet_dlet.
    eapply eq_in_dlet. 2:{ intro. reflexivity. }
    intros x hx y.
    rewrite dlet_unit. reflexivity.
  Qed.

  Lemma UniformIprod_UniformUniform :
    ∀ (i j : nat) `{Positive i} `{Positive j},
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
        xy ← sample uniform (i * j) ;; ret (ch2prod xy) ≈
        x ← sample uniform i ;; y ← sample uniform j ;; ret (x, y)
      ⦃ eq ⦄.
  Proof.
    intros i j pi pj.
    change (
      ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
        xy ← cmd (cmd_sample (uniform (i * j))) ;;
        ret (ch2prod xy)
        ≈
        x ← cmd (cmd_sample (uniform i)) ;;
        y ← cmd (cmd_sample (uniform j)) ;;
        ret (x, y)
      ⦃ eq ⦄
    ).
    rewrite rel_jdgE.
    repeat setoid_rewrite repr_cmd_bind.
    change (repr_cmd (cmd_sample (uniform ?i)))
    with (@Uniform_F (mkpos i) heap_choiceType).
    cbn - [semantic_judgement Uniform_F].
    eapply rewrite_eqDistrR. 1: apply: reflexivity_rule.
    intro s. cbn.
    pose proof @prod_uniform as h.
    specialize (h [finType of 'I_i] [finType of 'I_j]). simpl in h.
    unfold Uni_W'. unfold Uni_W.
    specialize (h (F_w0 (mkpos _)) (F_w0 (mkpos _))).
    unfold uniform_F in h.
    rewrite uniform_F_prod_bij in h.
    eapply (f_equal (SDistr_bind (λ x, SDistr_unit _ (x, s)))) in h.
    simpl in h.
    rewrite SDistr_bind_unit_unit in h. simpl in h.
    unfold uniform_F. unfold F_choice_prod_obj.
    rewrite h. clear h.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.
    cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xi.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.  cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xj.
    epose (bind_ret := ord_relmon_law2 SDistr _ _ _).
    eapply equal_f in bind_ret.
    cbn in bind_ret.
    unfold SubDistr.SDistr_obligation_2 in bind_ret.
    unfold SubDistr.SDistr_obligation_1 in bind_ret.
    erewrite bind_ret. reflexivity.
  Qed.

End Uniform_prod.

Lemma r_uniform_prod :
  ∀ {A : ord_choiceType} i j `{Positive i} `{Positive j}
    (r : fin_family (mkpos i) → fin_family (mkpos j) → raw_code A),
    (∀ x y, ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ r x y ≈ r x y ⦃ eq ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      xy ← sample uniform (i * j) ;; let '(x,y) := ch2prod xy in r x y ≈
      x ← sample uniform i ;; y ← sample uniform j ;; r x y
    ⦃ eq ⦄.
Proof.
  intros A i j pi pj r h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      '(x,y) ← (z ← sample (uniform (i * j)) ;; ret (ch2prod z)) ;; r x y ≈
      '(x,y) ← (x ← sample uniform i ;; y ← sample uniform j ;; ret (x, y)) ;; r x y
    ⦃ eq ⦄
  ).
  eapply r_bind.
  - eapply UniformIprod_UniformUniform.
  - intros [? ?] [? ?].
    eapply rpre_hypothesis_rule. intros ? ? e. noconf e.
    eapply rpre_weaken_rule.
    1: eapply h.
    simpl. intros ? ? [? ?]. subst. reflexivity.
Qed.

(** Fail and Assert *)

Definition fail_unit : raw_code 'unit :=
  x ← sample ('unit ; dnull) ;; ret x.

Definition assert b : raw_code 'unit :=
  if b then ret Datatypes.tt else fail_unit.

(* fail at any type in the chUniverse *)
Definition fail {A : chUniverse} : raw_code A :=
  x ← sample (A ; dnull) ;; ret x.

(* Dependent version of assert *)
Definition assertD {A : chUniverse} b (k : b = true → raw_code A) : raw_code A :=
  (if b as b' return b = b' → raw_code A then k else λ _, fail) erefl.

Lemma valid_fail_unit :
  ∀ L I, valid_code L I fail_unit.
Proof.
  intros L I.
  unfold fail_unit. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I fail_unit) =>
  eapply valid_fail_unit
  : typeclass_instances packages.

Lemma valid_assert :
  ∀ L I b, valid_code L I (assert b).
Proof.
  intros L I b. unfold assert. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (assert ?b)) =>
  eapply valid_assert
  : typeclass_instances packages.

Lemma valid_fail :
  ∀ A L I, valid_code L I (@fail A).
Proof.
  intros A L I. unfold fail. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I fail) =>
  eapply valid_fail
  : typeclass_instances packages.

Lemma valid_assertD :
  ∀ A L I b k,
    (∀ x, valid_code L I (k x)) →
    valid_code L I (@assertD A b k).
Proof.
  intros A L I b k h.
  destruct b.
  - simpl. eapply h.
  - simpl. eapply valid_code_from_class. exact _.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (@assertD ?A ?b ?k)) =>
  eapply (valid_assertD A _ _ b k) ;
  intro ; eapply valid_code_from_class
  : typeclass_instances packages.

Notation "'#assert' b 'as' id ;; k" :=
  (assertD b (λ id, k))
  (at level 100, id name, b at next level, right associativity,
  format "#assert  b  as  id  ;;  '/' k")
  : package_scope.

Notation "'#assert' b ;; k" :=
  (assertD b (λ _, k))
  (at level 100, b at next level, right associativity,
  format "#assert  b  ;;  '/' k")
  : package_scope.

Lemma r_fail_unit :
  ∀ pre post,
    ⊢ ⦃ pre ⦄ fail_unit ≈ fail_unit ⦃ post ⦄.
Proof.
  intros pre post.
  rewrite rel_jdgE. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  exists dnull. split.
  - unfold coupling. split.
    + unfold lmg. apply distr_ext.
      intro. unfold dfst. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
    + unfold rmg. apply distr_ext.
      intro. unfold dsnd. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
  - intros [? ?] [? ?]. rewrite dnullE.
    rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Lemma r_assert' :
  ∀ b₀ b₁,
    ⊢ ⦃ λ _, b₀ = b₁ ⦄ assert b₀ ≈ assert b₁ ⦃ λ _ _, b₀ = true ∧ b₁ = true ⦄.
Proof.
  intros b₀ b₁.
  destruct b₀, b₁. all: simpl.
  - apply r_ret. auto.
  - eapply rpre_hypothesis_rule. intros ? ? e. discriminate e.
  - eapply rpre_hypothesis_rule. intros ? ? e. discriminate e.
  - apply r_fail_unit.
Qed.

Theorem r_assert :
  ∀ b₀ b₁ (pre : precond) (post : postcond _ _),
    (∀ s, pre s → b₀ = b₁) →
    (∀ s₀ s₁, b₀ = true ∧ b₁ = true → post s₀ s₁) →
    ⊢ ⦃ pre ⦄ assert b₀ ≈ assert b₁ ⦃ post ⦄.
Proof.
  intros b₀ b₁ pre post hpre hpost.
  eapply rpre_weaken_rule. 1: eapply rpost_weaken_rule.
  1: eapply r_assert'.
  - simpl. intros [? ?] [? ?]. eapply hpost.
  - simpl. intros ? ?. eapply hpre.
Qed.

Theorem r_assertL :
  ∀ b,
    ⊢ ⦃ λ _, b = true ⦄ assert b ≈ ret Datatypes.tt ⦃ λ _ _, b = true ⦄.
Proof.
  intros b.
  destruct b.
  - simpl. apply r_ret. auto.
  - simpl. apply rpre_hypothesis_rule. discriminate.
Qed.

Theorem r_assertR :
  ∀ b,
    ⊢ ⦃ λ _, b = true ⦄ ret Datatypes.tt ≈ assert b ⦃ λ _ _, b = true ⦄.
Proof.
  intros b.
  destruct b.
  - simpl. apply r_ret. auto.
  - simpl. apply rpre_hypothesis_rule. discriminate.
Qed.

Lemma r_fail :
  ∀ A₀ A₁ pre post,
    ⊢ ⦃ pre ⦄ @fail A₀ ≈ @fail A₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ pre post.
  rewrite rel_jdgE. intros [s₀ s₁]. hnf. intro P. hnf.
  intros [hpre hpost]. simpl.
  exists dnull. split.
  - unfold coupling. split.
    + unfold lmg. apply distr_ext.
      intro. unfold dfst. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
    + unfold rmg. apply distr_ext.
      intro. unfold dsnd. rewrite dlet_null.
      unfold SDistr_bind. rewrite dlet_null.
      reflexivity.
  - intros [? ?] [? ?]. rewrite dnullE.
    rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

Theorem r_assertD :
  ∀ {A₀ A₁ : chUniverse} b₀ b₁ (pre : precond) (post : postcond A₀ A₁) k₀ k₁,
    (∀ s, pre s → b₀ = b₁) →
    (∀ e₀ e₁, ⊢ ⦃ pre ⦄ k₀ e₀ ≈ k₁ e₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ #assert b₀ as x ;; k₀ x ≈ #assert b₁ as x ;; k₁ x ⦃ post ⦄.
Proof.
  intros A₀ A₁ b₀ b₁ pre post k₀ k₁ hpre h.
  destruct b₀, b₁. all: simpl.
  - eapply h.
  - eapply rpre_hypothesis_rule. intros ? ? hh.
    eapply hpre in hh. discriminate.
  - eapply rpre_hypothesis_rule. intros ? ? hh.
    eapply hpre in hh. discriminate.
  - eapply r_fail.
Qed.

(* Simpler version for same_head *)
Lemma r_assertD_same :
  ∀ (A : chUniverse) b (pre : precond) (post : postcond A A) k₀ k₁,
    (∀ e, ⊢ ⦃ pre ⦄ k₀ e ≈ k₁ e ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ #assert b as x ;; k₀ x ≈ #assert b as x ;; k₁ x ⦃ post ⦄.
Proof.
  intros A b pre post k₀ k₁ h.
  eapply r_assertD.
  - reflexivity.
  - intros e₀ e₁. assert (e₀ = e₁) by eapply eq_irrelevance. subst.
    eapply h.
Qed.

(* TODO Extract subgoals as lemmata *)
Lemma rswap_assertD_cmd_eq :
  ∀ A (B : chUniverse) b (c : command A) (r : _ → _ → raw_code B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      #assert b as e ;; x ← cmd c ;; r e x ≈
      x ← cmd c ;; #assert b as e ;; r e x
    ⦃ eq ⦄.
Proof.
  intros A B b c r.
  destruct b.
  - simpl. apply rreflexivity_rule.
  - simpl.
    eapply r_transR.
    + unfold fail.
      eapply rswap_cmd_eq with (c₀ := cmd_sample _) (c₁ := c).
      simpl.
      eapply rsamplerC'_cmd with (c0 := c).
    + simpl.
      unfold fail.
      rewrite rel_jdgE. intros [s₀ s₁]. hnf. intro P. hnf.
      intros [hpre hpost]. simpl.
      exists dnull. split.
      * unfold coupling. split.
        --- unfold lmg. apply distr_ext.
            intro. unfold dfst. rewrite dlet_null.
            unfold SDistr_bind. rewrite dlet_null.
            reflexivity.
        --- unfold rmg. apply distr_ext.
            intro. unfold dsnd. rewrite dlet_null.
            unfold SDistr_bind. rewrite dlet_null.
            reflexivity.
      * intros [? ?] [? ?]. rewrite dnullE.
        rewrite mc_1_10.Num.Theory.ltrr. discriminate.
Qed.

(* Symmetric of the above. *)
(* Lemma rswap_cmd_assertD_eq : *)