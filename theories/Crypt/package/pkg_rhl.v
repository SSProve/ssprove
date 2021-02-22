(**
  This file connects packages to the relational Hoare logic and provides
  basic crypto-style reasoning notions.
**)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings RulesStateProb
  StateTransfThetaDens StateTransformingLaxMorph
  pkg_chUniverse pkg_notation pkg_tactics.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, god knows why. *)
From Crypt Require Import FreeProbProg.


Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module PackageRHL (π : RulesParam).

  Import π.
  Include (PackageTactics π).

  Import PackageNotation.

  Local Open Scope fset.
  Local Open Scope fset_scope.
  Local Open Scope type_scope.
  Local Open Scope package_scope.

  Definition Game_import : Interface := fset0.

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

  (* Let iops_StP := @ops_StP probE rel_choiceTypes chEmb. *)
  (* Let iar_StP := @ar_StP probE rel_choiceTypes chEmb. *)

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
    - exact (fintype.Ordinal (cond_pos n)).
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

  (** Interpretation of raw programs into the semantic model

    Note that we don't require any validity proof to do so,
    instead we rely on the fact that types in the chUniverse are all
    inhabited.

  *)
  Fixpoint repr {A : choiceType} (p : raw_program A) :
    rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) A :=
    match p with
    | ret x => retrFree x
    | opr o x k =>
        repr (k (chCanonical (chtgt o)))
    | getr l k =>
        bindrFree
          (ropr (inl (inl (gett _))) (λ s, retrFree (get_heap s l)))
          (λ v, repr (k v))
    | putr l v k =>
        bindrFree
          (ropr
            (inl (inl (gett heap_choiceType)))
            (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s l v))))
            (λ s, retrFree tt)))
          (λ s', repr k)
    | sampler op k =>
        bindrFree
          (ropr (inr op) (λ v, retrFree v))
          (λ s, repr (k s))
    end.

  Lemma repr_bind :
    ∀ {A B : choiceType} (p : raw_program A) (f : A → raw_program B),
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
    rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) A :=
    match c with
    | cmd_op o x => retrFree (chCanonical (chtgt o))
    | cmd_get ℓ =>
        bindrFree
          (ropr (inl (inl (gett _))) (λ s, retrFree (get_heap s ℓ)))
          (λ v, retrFree v)
    | cmd_put ℓ v =>
        bindrFree
          (ropr
            (inl (inl (gett heap_choiceType)))
            (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s ℓ v))))
            (λ s, retrFree tt)))
          (λ s', retrFree s')
    | cmd_sample op =>
        bindrFree
          (ropr (inr op) (λ v, retrFree v))
          (λ s, retrFree s)
    end.

  Lemma repr_cmd_bind :
    ∀ {A B} (c : command A) (k : A → raw_program B),
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
    (o : opsig) (ho : o \in E) (arg : src o) : program L I (tgt o) :=
    get_raw_package_op p hp o ho arg with inspect (lookup_op p o) := {
    | @exist (Some f) e1 := {program f arg } ;
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
      (f : src o -> raw_program (tgt o))
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
  Definition program_link_ext {E : Interface}
    (o : opsig) (ho : o \in E) (arg : src o) (p1 p2 : raw_package)
    (f : src o → raw_program (tgt o))
    (Hf : lookup_op p1 o = Some f)
    (g : src o → raw_program (tgt o))
    (Hg : lookup_op (link p1 p2) o = Some g)
    : g arg = program_link (f arg) p2.
  Proof.
    unfold link in Hg.
    destruct o as [id [S T]].
    assert ((λ x, program_link (f x) p2) = g).
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
      program_link ((get_raw_package_op p1 hp1 o hin arg).(prog)) p2.
  Proof.
    destruct (lookup_op (link p1 p2) o) as [f|] eqn:e.
    2: { unfold valid_package in hpl.
          pose (hpl o hin) as H.
          destruct o as [id [S T]].
          destruct H as [f [H1 H2]].
          unfold lookup_op in e.
          rewrite H1 in e.
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          discriminate. }
    rewrite (get_raw_package_op_lookup (link p1 p2) _ o hin arg f e).
    destruct (lookup_op p1 o) as [fl|] eqn:el.
    2: { unfold valid_package in hp1.
          pose (hp1 o hin) as H.
          destruct o as [id [S T]].
          destruct H as [f' [H1 H2]].
          unfold lookup_op in el.
          rewrite H1 in el.
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          discriminate. }
    rewrite (get_raw_package_op_lookup p1 _ o hin arg fl el).
    apply (program_link_ext o hin arg p1 p2 fl el f e).
  Qed.

  Lemma get_raw_package_op_trim {L} {I E} {o : opsig}
        (hin : o \in E) (arg : src o) (p : raw_package)
        (hp : valid_package L I E p)
        (hpt : valid_package L I E (trim E p))
    : get_raw_package_op (trim E p) hpt o hin arg =
      get_raw_package_op p hp o hin arg.
  Proof.
    apply program_ext.
    destruct (lookup_op p o) as [f|] eqn:e.
    2: { unfold valid_package in hp.
          pose (hp o hin) as H.
          destruct o as [id [S T]].
          destruct H as [f [H1 H2]].
          unfold lookup_op in e.
          rewrite H1 in e.
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          discriminate. }
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
    2: { unfold valid_package in hp1.
          pose (hp1 o hin) as H.
          destruct o as [id [S T]].
          destruct H as [f [H1 H2]].
          unfold lookup_op in e.
          rewrite H1 in e.
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          destruct chUniverse_eqP.
          2:{ noconf ef. congruence. }
          discriminate. }
    rewrite (get_raw_package_op_lookup p _ o hin arg f e).
    rewrite (get_raw_package_op_lookup p _ o hin arg f e).
    reflexivity.
  Qed.

  Definition get_opackage_op {L} {I E : Interface} (P : package L I E)
    (op : opsig) (Hin : op \in E) (arg : src op) : program L I (tgt op).
  Proof.
    exact (get_raw_package_op P.(pack) P.(pack_valid) op Hin arg).
  Defined.

  Definition get_package_op {I E : Interface} (P : loc_package I E)
              (op : opsig) (Hin : op \in E) (arg : src op)
    : program P.(locs) I (tgt op) :=
    let (L, PP) as s return (program s.(locs) I (tgt op)) := P in
    get_opackage_op PP op Hin arg.

  (* Rather than the above, we use the version with default values *)
  Definition get_op_default (p : raw_package) (o : opsig) :
    src o → raw_program (tgt o) :=
    match lookup_op p o with
    | Some f => f
    | None => λ x, ret (chCanonical (chtgt o))
    end.

  Lemma valid_get_op_default :
    ∀ L I E p o x,
      valid_package L I E p →
      o \in E →
      valid_program L I (get_op_default p o x).
  Proof.
    intros L I E p o x hp ho.
    unfold get_op_default.
    destruct lookup_op eqn:e.
    - eapply lookup_op_spec in e as h.
      specialize (hp _ ho). destruct o as [id [S T]].
      destruct hp as [f [ef hf]].
      cbn in h. rewrite ef in h. noconf h.
      auto.
    - constructor.
  Qed.

  Hint Extern 1 (ValidProgram ?L ?I (get_op_default ?p ?o ?x)) =>
    eapply valid_get_op_default ; [
      apply valid_package_from_class
    | auto_in_fset
    ]
    : typeclass_instances.

  Definition Pr_program {A} (p : raw_program A) :
    heap_choiceType → SDistr (F_choice_prod_obj ⟨ A , heap_choiceType ⟩) :=
    λ s, thetaFstd (prob_handler := prob_handler) A (repr p) s.

  (* TODO REMOVE? *)
  Definition Pr_raw_func_program {A B} (p : A → raw_program B) :
    A → heap_choiceType → SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩) :=
    λ a s, Pr_program (p a) s.

  Definition Pr_op (p : raw_package) (o : opsig) (x : src o) :
    heap_choiceType → SDistr (F_choice_prod_obj ⟨ tgt o , heap_choiceType ⟩) :=
    Pr_program (get_op_default p o x).

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
    program p.(locs) I (tgt o).
  Proof.
    (* TW: I transformed this definition so that it computes directly. *)
    destruct (lookup_op p o) as [f|] eqn:e.
    2:{
      (* Rem.: Done several times, I should make a lemma. *)
      exfalso.
      destruct p as [L [p hp]].
      destruct o as [n [S T]].
      cbn - [lookup_op] in e.
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

  (* TODO Should it stay this way? Probably need to change the type Game_Type *)
  (* Definition GamePair (Game_export : Interface) :=
    bool → Game_Type Game_export. *)

  (* TODO Again, why not an actual pair? *)
  Definition GamePair :=
      bool → raw_package.

  (* TODO: Should the type of the adversary be raw_package?
    Probably, but should we give it a name anyway?
    I guess it'll just come up in theorems.

    NOTE: With this there is no longer a definition of weak advantage.
    We will still be able to talk about weak adversaries at another level.
  *)

  Definition Advantage (G : GamePair) (A : raw_package) : R :=
    `| Pr (A ∘ (G false)) true - Pr (A ∘ (G true)) true |.

  Definition AdvantageE (G₀ G₁ : raw_package) (A : raw_package) : R :=
    `| Pr (A ∘ G₀) true - Pr (A ∘ G₁) true |.

  (* TODO Useful? *)
  Definition state_pass_ {A} (p : raw_program A) :
    heap_choiceType → raw_program (prod_choiceType A heap_choiceType).
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

  Definition state_pass__valid {A} {L} {I} (p : raw_program A)
    (h : valid_program L I p) :
    ∀ hp, valid_program fset0 I (state_pass_ p hp).
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

  Definition state_pass {A} (p : raw_program A) : raw_program A :=
    bind (state_pass_ p empty_heap) (λ '(r, _), ret r).

  Definition state_pass_valid {A} {L} {I} (p : raw_program A)
    (h : valid_program L I p) :
    valid_program fset0 I (state_pass p).
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

  (* TODO Do I want to have a notion of equivalence on raw_packages?
    I could do it since I already have advantage on those.
    But then it would push disjointness requirements somewhere else.
    Maybe it's the ~[ ε ] which will imply ≈[ ε ]?
    I don't really see how because the quantification over the adversary
    is hidden here.

    Maybe for now I should try to just have it as before, without any
    restriction. And then we'll see where it comes up?
    I might have to redo some stuff, but it'll help tailoring things.
    The motivation for constraining it is we want to have perfect equivalence
    as ≈[ λ _, 0 ].
  *)

  Definition adv_equiv (G₀ G₁ : raw_package) ε :=
    ∀ A, AdvantageE G₀ G₁ A = ε A.

  (* Adversary for condition *)
  (* Definition adv_for {I} (A : Adversary4Game I) (G₀ G₁ : Game_Type I) :=
    fdisjoint A.(locs) G₀.(locs) && fdisjoint A.(locs) G₁.(locs).

  Definition adv_forp {I} (A : Adversary4Game I) (G : GamePair I) :=
    fdisjoint A.(locs) (G true).(locs) &&
    fdisjoint A.(locs) (G false).(locs).

  Definition adv_equiv {I} (G₀ G₁ : Game_Type I) ε :=
    ∀ A, adv_for A G₀ G₁ → AdvantageE G₀ G₁ A = ε A. *)

  (** The quantification over a disjoint adversary is now here.
    Also, the function equality is now pointwise.
  *)
  Notation " G0 ≈[ R ] G1 " :=
    (adv_equiv G0 G1 R)
    (at level 50, format " G0  ≈[  R  ]  G1")
    : package_scope.

  Notation " G0 ≈₀ G1 " :=
    (G0 ≈[ λ A, 0 ] G1)
    (at level 50, format " G0  ≈₀  G1")
    : package_scope.

  (* TODO Update *)
  (* Lemma Advantage_equiv :
    ∀ I (G : GamePair I),
      (G false) ≈[ Advantage G ] (G true).
  Proof.
    intros I G. intros A h. reflexivity.
  Qed.

  Lemma AdvantageE_equiv :
    ∀ I (G₀ G₁ : Game_Type I),
      G₀ ≈[ AdvantageE G₀ G₁ ] G₁.
  Proof.
    intros I G₀ G₁. intros A h. reflexivity.
  Qed. *)

  Lemma Advantage_E :
    ∀ (G : GamePair) A,
      Advantage G A = AdvantageE (G false) (G true) A.
  Proof.
    intros G A.
    reflexivity.
  Qed.

  Lemma TriangleInequality :
    ∀ {Game_export : Interface}
      {F G H : Game_Type Game_export}
      {ϵ1 ϵ2 ϵ3},
      F ≈[ ϵ1 ] G →
      G ≈[ ϵ2 ] H →
      F ≈[ ϵ3 ] H →
      ∀ A,
        (* adv_for A F G →
        adv_for A G H →
        adv_for A F H → *)
        ϵ3 A <= ϵ1 A + ϵ2 A.
  Proof.
    intros Game_export F G H ε₁ ε₂ ε₃ h1 h2 h3 A (* hA1 hA2 hA3 *).
    unfold adv_equiv in *.
    rewrite <- h1, <- h2, <- h3 by assumption.
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

  (* Lemma auxReduction :
    ∀ {Game_export M_export : Interface} {M : loc_package Game_export M_export}
      {G : Game_Type Game_export} {A : Adversary4Game M_export},
      fdisjoint M.(locs) G.(locs) →
      fdisjoint A.(locs) {locpackage link M G }.(locs) →
      fdisjoint {locpackage link A M }.(locs) G.(locs).
  Proof.
    intros Game_export M_export M G A Hdisjoint0 Hdisjoint1.
    simpl in *.
    rewrite fdisjointUl.
    apply /andP. split.
    - rewrite fdisjointUr in Hdisjoint1.
      move: Hdisjoint1. by move /andP => [_ Hdisjoint1].
    - apply Hdisjoint0.
  Qed. *)

  Lemma ReductionLem :
    ∀ M (G : GamePair),
      (M ∘ (G false)) ≈[ λ A, Advantage G (A ∘ M) ] (M ∘ (G true)).
  Proof.
    intros M G.
    unfold adv_equiv. intro A. rewrite Advantage_E.
    unfold AdvantageE. rewrite !link_assoc. reflexivity.
  Qed.

  (* Lemma rhl_repr_change_all {B1 B2 : choiceType} {L1 L2 L1' L2'}
    {pre : heap_choiceType * heap_choiceType -> Prop}
    {post : (B1 * heap_choiceType) → (B2 * heap_choiceType) → Prop}
    {r1 r1' : raw_program B1} {r2 r2' : raw_program B2}
    {hr11 : ValidProgram L1 Game_import r1}
    {hr12 : ValidProgram L2 Game_import r1'}
    {hr21 : ValidProgram L1' Game_import r2}
    {hr22 : ValidProgram L2' Game_import r2'}
    (Hr1 : r1 = r1') (Hr2 : r2 = r2')
    (H : ⊨ ⦃ pre ⦄ repr {program r1 } ≈ repr {program r2 } ⦃ post ⦄)
    : ⊨ ⦃ pre ⦄ repr {program r1' } ≈ repr {program r2' } ⦃ post ⦄.
  Proof.
    unfold repr in *.
    induction Hr1. induction Hr2.
    assert (repr' r1 hr11 = repr' r1 hr12) as Hr1.
    { apply repr'_ext. reflexivity. }
    assert (repr' r2 hr21 = repr' r2 hr22) as Hr2.
    { apply repr'_ext. reflexivity. }
    rewrite -Hr1 -Hr2. assumption.
  Qed. *)

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
    intuition.
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
      inversion e. subst. intuition.
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
    intuition.
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
      intuition.
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
    intuition. unfold θ. cbn - [justInterpState stT_thetaDex].
    unfold justInterpState. unfold LaxComp.rlmm_comp.
    simpl (nfst _). simpl (nsnd _). unfold stT_thetaDex.
    simpl (TransformingLaxMorph.rlmm_from_lmla (stT_thetaDex_adj prob_handler) ⟨ Arit op, Arit op ⟩).
    unfold stT_thetaDex_adj.
    cbn - [ThetaDex.thetaDex UniversalFreeMap.outOfFree_obligation_1].
    unfold TransformingLaxMorph.Kl_beta_obligation_1.
    simpl ((ThetaDex.thetaDex prob_handler
    ⟨ F_choice_prod_obj ⟨ Arit op, heap_choiceType ⟩,
    F_choice_prod_obj ⟨ Arit op, heap_choiceType ⟩ ⟩) ∙1).
    unfold Theta_exCP.θ0.
    cbn - [Theta_dens.unary_theta_dens_obligation_1 ThetaDex.thetaDex UniversalFreeMap.outOfFree_obligation_1].
    pose foo := (sigMap (inr op) s1).
    cbn in foo.
    unfold probopStP in foo. cbn in foo.
    destruct op as [opA opB].
    pose foo2 := SDistr_bind (fun x => SDistr_unit _ ((x, s1), (x, s2))) (Theta_dens.unary_ThetaDens0 prob_handler _ (ropr (opA; opB) (λ x : chEmb opA, retrFree x))).
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
      eassert ((λ x : chEmb opA,
          prob_handler (chEmb opA) opB x *
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

  (* TODO These guys type-check but they should be updated nonetheless
    I probably want to take the opportunity to remove the normal one and just
    use alt. It might be the only one that makes sense anyway.
    The problem is that at the moment equivalence is really weak so I shouldn't
    update the theorem now.

    For the final PRF theorem, we don't need the extra disjointness hypotheses.
    It's just we should use triangle inequality on advantage directly which
    doesn't have any requirements.
  *)

  Definition eq_up_to_inv (I : precond) (p₀ p₁ : raw_package) :=
    ∀ (id : ident) (S T : chUniverse) (x : S),
      r⊨ ⦃ λ '(s₀, s₁), I (s₀, s₁) ⦄
        get_op_default p₀ (id, (S, T)) x ≈ get_op_default p₁ (id, (S, T)) x
        ⦃ λ '(b₀, s₀) '(b₁, s₁), b₀ = b₁ ∧ I (s₀, s₁) ⦄.

  (* Definition eq_up_to_inv_alt {L₁ L₂} {E}
    (I : heap_choiceType * heap_choiceType → Prop)
    (p₁ : package L₁ Game_import E) (p₂ : package L₂ Game_import E) :=
    ∀ (id : ident) (S T : chUniverse) (h : (id, (S, T)) \in E) (x : S),
      r⊨ ⦃ λ '(s₀, s₃), I (s₀, s₃) ⦄
        (mkprog (get_op_default p₁ (id, (S, T)) x) _) ≈
        (mkprog (get_op_default p₂ (id, (S, T)) x) _)
        ⦃ λ '(b₁, s₀) '(b₂, s₃), b₁ = b₂ ∧ I (s₀, s₃) ⦄.

  Definition eq_up_to_inv {L1 L2} {E}
    (I : heap_choiceType * heap_choiceType → Prop)
    (P1 : package L1 Game_import E) (P2 : package L2 Game_import E) :=
    ∀ (id : ident) (S T : chUniverse)
      (hin : (id, (S, T)) \in E)
      (f : S → raw_program T) (g : S → raw_program T)
      (Hf : P1.(pack) id = Some (S; T; f)) (hpf : ∀ x, valid_program L1 Game_import (f x))
      (Hg : P2.(pack) id = Some (S; T; g)) (hpg : ∀ x, valid_program L2 Game_import (g x))
      (arg : S),
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄ repr (mkprog (f arg) (hpf arg)) ≈ repr (mkprog (g arg) (hpg arg)) ⦃ λ '(b1, s0) '(b2, s3), b1 = b2 ∧ I (s0, s3) ⦄. *)

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

  (* Lemma eq_up_to_inv_to_alt :
    ∀ L₁ L₂ E I p₁ p₂,
      @eq_up_to_inv L₁ L₂ E I p₁ p₂ →
      @eq_up_to_inv_alt L₁ L₂ E I p₁ p₂.
  Proof.
    intros L₁ L₂ E I p₁ p₂ h.
    intros id S T hin x.
    specialize (h id S T hin).
    destruct p₁ as [p₁ hp₁]. specialize (hp₁ _ hin) as h'.
    cbn in h'. destruct h' as [f₁ [e₁ h₁]].
    destruct p₂ as [p₂ hp₂]. specialize (hp₂ _ hin) as h'.
    cbn in h'. destruct h' as [f₂ [e₂ h₂]].
    specialize h with (1 := e₁) (2 := e₂).
    specialize (h h₁ h₂ x).
    lazymatch goal with
    | h : r⊨ ⦃ _ ⦄ ?x ≈ ?y ⦃ _ ⦄ |- r⊨ ⦃ _ ⦄ ?u ≈ ?v ⦃ _ ⦄ =>
      let e := fresh "e" in
      let e' := fresh "e" in
      assert (x = u) as e ; [
      | assert (y = v) as e' ; [
        | rewrite <- e ; rewrite <- e' ; auto
        ]
      ]
    end.
    - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
    - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
  Qed. *)

  (* Lemma eq_up_to_inv_from_alt :
    ∀ L₁ L₂ E I p₁ p₂,
      @eq_up_to_inv_alt L₁ L₂ E I p₁ p₂ →
      @eq_up_to_inv L₁ L₂ E I p₁ p₂.
  Proof.
    intros L₁ L₂ E I p₁ p₂ h.
    intros id S T hin f g ef hf eg hg x.
    specialize (h id S T hin x).
    lazymatch goal with
    | h : r⊨ ⦃ _ ⦄ ?x ≈ ?y ⦃ _ ⦄ |- r⊨ ⦃ _ ⦄ ?u ≈ ?v ⦃ _ ⦄ =>
      let e := fresh "e" in
      let e' := fresh "e" in
      assert (x = u) as e ; [
      | assert (y = v) as e' ; [
        | rewrite <- e ; rewrite <- e' ; auto
        ]
      ]
    end.
    - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
    - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
  Qed. *)

  (* TODO MOVE *)

  (* Slightly more expensive version that allows to change parameters *)
  Hint Extern 3 (ValidProgram ?L ?I ?p) =>
    match goal with
    | h : is_true (fsubset ?x ?y) |- _ =>
      eapply valid_injectLocations with (1 := h) ;
      eapply valid_program_from_class ; exact _
    end
    : typeclass_instances.

  Hint Extern 3 (ValidPackage ?L ?I ?E ?p) =>
    match goal with
    | h : is_true (fsubset ?x ?y) |- _ =>
      eapply valid_package_inject_locations with (1 := h) ;
      eapply valid_package_from_class ; exact _
    end
    : typeclass_instances.

  Lemma Pr_eq_empty :
    ∀ {X Y : ord_choiceType}
      {A : pred (X * heap_choiceType)} {B : pred (Y * heap_choiceType)}
      Ψ ϕ
      (c1 : FrStP heap_choiceType X) (c2 : FrStP heap_choiceType Y),
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
    ∀ {L₀ L₁ LA E} (p₀ p₁ : raw_package) (I : precond) {B} (A : raw_program B)
      `{ValidPackage L₀ Game_import E p₀}
      `{ValidPackage L₁ Game_import E p₁}
      `{@ValidProgram LA E B A},
      INV LA I →
      eq_up_to_inv I p₀ p₁ →
      r⊨ ⦃ I ⦄ program_link A p₀ ≈ program_link A p₁
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
      specialize (vp₀ _ hi). simpl in vp₀.
      destruct vp₀ as [f₀ [e₀ h₀]].
      specialize (vp₁ _ hi). simpl in vp₁.
      destruct vp₁ as [f₁ [e₁ h₁]].
      erewrite lookup_op_spec_inv. 2: eauto.
      erewrite lookup_op_spec_inv. 2: eauto.
      specialize (hp id S T x).
      erewrite get_op_default_spec in hp. 2: eauto.
      erewrite get_op_default_spec in hp. 2: eauto.
      rewrite !repr_bind.
      eapply bind_rule_pp. 1: exact hp.
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

  Lemma prove_relational :
    ∀ {L₀ L₁ E} (p₀ p₁ : raw_package) (I : precond)
      `{ValidPackage L₀ Game_import E p₀}
      `{ValidPackage L₁ Game_import E p₁},
      INV' L₀ L₁ I →
      eq_up_to_inv I p₀ p₁ →
      p₀ ≈[ λ A, 0 ] p₁.
  Proof.
    intros L₀ L₁ E p₀ p₁ I vp₀ vp₁ hI' hp.
    intros A. (* TODO More restrictions and rewrite happen here *)
    unfold AdvantageE, Pr.
    pose r := get_op_default A RUN tt.
    (* TODO We already start seeing contrainsts that A must satisfy. *)
    (* assert (hI : INV LA I). *)
    (* pose proof (some_lemma_for_prove_relational p₀ p₁ A hI hp). *)
    (* Maybe first it would be better not to use the ≈[] notation and
    directly talk about advantage and adversary?
    This way we don't have to decide what the definiton of ≈[] should be. *)
  Abort.

  (* Lemma prove_relational {L1 L2} {export}
    (P1 : package L1 Game_import export)
    (P2 : package L2 Game_import export)
    (I : heap_choiceType * heap_choiceType -> Prop)
    (HINV' : INV' L1 L2 I)
    (Hempty : I (empty_heap, empty_heap))
    (H : eq_up_to_inv I P1 P2) :
    (mkloc_package L1 P1) ≈[ λ A, 0 ] (mkloc_package L2 P2).
  Proof.
    intros A h. unfold adv_for in h. simpl in h. move: h => /andP [hd1 hd2].
    unfold Adversary4Game in A.
    unfold AdvantageE, Pr.
    pose r' := get_package_op A RUN RUN_in_A_export.
    pose r := r' tt.
    (* Rem.: from linking we should get the fact that A.π1 is disjoint from L1 and L2,
            and then from that conclude that we are invariant on A.π1 *)
    (* unshelve epose (fdisjoint_from_link A.π2 P1 _) as Hdisjoint1. *)
    (* { eexists. reflexivity. } *)
    (* unshelve epose (fdisjoint_from_link A.π2 P2 _) as Hdisjoint2. *)
    (* { eexists. reflexivity. } *)
    assert (INV A.(locs) I) as HINV.
    { destruct A. simpl in hd1, hd2.
      cbn.  unfold INV.
      intros s1 s2. split.
      - intros hi l hin.
        apply HINV'.
        + assumption.
        + move: hd1. move /fdisjointP => hd1.
          apply hd1. assumption.
        + move: hd2. move /fdisjointP => hd2.
          apply hd2. assumption.
      - intros hi l v hin.
        apply HINV'.
        + assumption.
        + move: hd1. move /fdisjointP => hd1.
          apply hd1. assumption.
        + move: hd2. move /fdisjointP => hd2.
          apply hd2. assumption.
    }
    pose Hlemma := (some_lemma_for_prove_relational _ _ _ HINV Hempty H r empty_heap empty_heap Hempty).
    assert (∀ x y : tgt RUN * heap_choiceType,
                (let '(b1, s1) := x in λ '(b2, s2), b1 = b2 s/\ I (s1, s2)) y → (fst x == true) ↔ (fst y == true)) as Ha.
    { intros [b1 s1] [b2 s2]. simpl.
      intros [H1 H2]. rewrite H1. intuition.
    }
    pose Heq := (Pr_eq_empty _ _ _ _ Hlemma Hempty Ha).
    simpl in Heq.
    simpl in Hlemma.
    unfold θ_dens in Heq.
    simpl in Heq. unfold pr in Heq.
    simpl in Heq.
    unfold Pr_op.
    (* Interestingly, ssreflect's pose here succeeds but leads to
      anomalies afterwards.
    *)
    unshelve epose (rhs := (
      thetaFstd _
        (repr {program
          program_link r P1
          #with [hints
            fsubsetUl A.(locs) (L1 :|: L2) ;
            fsubset_trans (y:=L1 :|: L2) (x:=L1)
              (z:= A.(locs) :|: (L1 :|: L2)) (fsubsetUl L1 L2)
              (fsubsetUr A.(locs) (L1 :|: L2))
          ]
        })
        empty_heap
    )).
    1: exact prob_handler.
    simpl in rhs.
    unshelve epose (lhs :=
      Pr_raw_package_op (link A P1) _ RUN RUN_in_A_export tt empty_heap
    ).
    2:{ eapply valid_package_from_class. exact _. }
    assert (lhs = rhs).
    { subst lhs rhs.
      unfold Pr_raw_package_op. unfold Pr_raw_program.
      unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
      apply f_equal. apply f_equal.
      destruct A as [LA [A A_valid]].
      apply repr'_ext.
      erewrite get_raw_package_op_link.
      apply f_equal2. 2: reflexivity.
      cbn - [get_raw_package_op].
      subst r. subst r'.
      unfold get_package_op. unfold get_opackage_op.
      simpl.
      cbn - [get_raw_package_op].
      epose (get_raw_package_op_ext RUN_in_A_export tt A) as e.
      specialize (e (valid_package_inject_locations export A_export LA (LA :|: L1) A
          (fsubsetUl LA L1) A_valid)).
      eapply e.
    }
    unfold lhs in H0.
    rewrite H0.
    unshelve epose (rhs' := (
      thetaFstd _
        (repr {program
          program_link r P2
          #with [hints
            fsubsetUl A.(locs) (L1 :|: L2) ;
            fsubset_trans (y:=L1 :|: L2) (x:=L2)
              (z:= A.(locs) :|: (L1 :|: L2)) (fsubsetUr L1 L2)
              (fsubsetUr A.(locs) (L1 :|: L2))
          ]
        })
        empty_heap
    )).
    1: exact prob_handler.
    simpl in rhs'.
    unshelve epose (lhs' :=
      Pr_raw_package_op (link A P2) _ RUN RUN_in_A_export tt empty_heap
    ).
    2:{ eapply valid_package_from_class. exact _. }
    assert (lhs' = rhs') as H0'.
    { subst lhs' rhs'.
      unfold Pr_raw_package_op. unfold Pr_raw_program.
      unfold thetaFstd. simpl. apply f_equal2. 2: reflexivity.
      apply f_equal. apply f_equal.
      destruct A as [LA [A A_valid]].
      apply repr'_ext.
      erewrite get_raw_package_op_link.
      apply f_equal2. 2: reflexivity.
      cbn - [get_raw_package_op]. subst r r'.
      unfold get_package_op. unfold get_opackage_op.
      cbn - [get_raw_package_op].
      epose (get_raw_package_op_ext RUN_in_A_export tt A) as e.
      specialize (e (valid_package_inject_locations export A_export LA (LA :|: L2) A
                                                    (fsubsetUl LA L2) A_valid)).
      eapply e.
    }
    unfold lhs' in H0'.
    rewrite H0'.
    unfold rhs', rhs.

    unfold SDistr_bind. unfold SDistr_unit.
    simpl.
    rewrite !dletE.
    assert (∀ x : bool_choiceType * heap_choiceType, ((let '(b, _) := x in dunit (R:=R) (T:=bool_choiceType) b) true) == (x.1 == true)%:R).
    { intros [b s].
      simpl. rewrite dunit1E. intuition.
    }
    assert (∀ y, (λ x : prod_choiceType (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true) = (λ x : prod_choiceType (tgt RUN) heap_choiceType, (x.1 == true)%:R * (y x))) as Hrew.
    { intros y. extensionality x.
      destruct x as [x1 x2].
      rewrite dunit1E.
      simpl. rewrite GRing.mulrC. reflexivity.
    }
    rewrite !Hrew.
    unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
    unfold SubDistr.SDistr_obligation_2. simpl.
    unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1. simpl.
    rewrite !SDistr_rightneutral. simpl.
    rewrite Heq.
    rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
    unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1, stT_thetaDens_adj.
    assert (∀ (x : R), `|x - x| = 0) as Hzero.
    { intros x.
      assert (x - x = 0) as H3.
      { apply /eqP. rewrite GRing.subr_eq0. intuition. }
      rewrite H3. apply mc_1_10.Num.Theory.normr0.
    }
    rewrite Hzero.
    reflexivity.
  Qed. *)

  (* Alternative version for packages *)
  (* Corollary prove_relational' :
    ∀ {export}
      (P1 : loc_package Game_import export)
      (P2 : loc_package Game_import export)
      (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV' : INV' P1.(locs) P2.(locs) I)
      (Hempty : I (empty_heap, empty_heap))
      (H : eq_up_to_inv I P1 P2),
      P1 ≈[ λ A, 0 ] P2.
  Proof.
    intros E [L₁ p₁] [L₂ p₂] I hI he h.
    eapply prove_relational. all: eauto.
  Qed. *)

  (* Rules for packages *)
  (* same as in RulesStateprob.v with `r` at the beginning *)

  (* Pre-condition manipulating rules *)

  Theorem rpre_weaken_rule :
    ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_program A₀} {p₁ : raw_program A₁}
      (pre pre' : precond) post,
      r⊨ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
      (∀ s₀ s₁, pre' (s₀, s₁) → pre (s₀, s₁)) →
      r⊨ ⦃ pre' ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre pre' post he hi.
    eapply pre_weaken_rule. all: eauto.
  Qed.

  Theorem rpre_hypothesis_rule :
    ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_program A₀} {p₁ : raw_program A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
        pre (s₀, s₁) → r⊨ ⦃ λ s, s.1 = s₀ ∧ s.2 = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      r⊨ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply pre_hypothesis_rule.
    exact h.
  Qed.

  Theorem rpre_strong_hypothesis_rule :
    ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_program A₀} {p₁ : raw_program A₁}
      (pre : precond) post,
      (∀ s₀ s₁, pre (s₀, s₁)) →
      r⊨ ⦃ λ _, True ⦄ p₀ ≈ p₁ ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post hs h.
    eapply pre_strong_hypothesis_rule.
    all: eauto.
  Qed.

  Theorem rpost_weaken_rule :
    ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_program A₀} {p₁ : raw_program A₁}
      (pre : precond) (post1 post2 : postcond A₀ A₁),
      r⊨ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post1 ⦄ →
      (∀ a₀ a₁, post1 a₀ a₁ → post2 a₀ a₁) →
      r⊨ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post2 ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post1 post2 h hi.
    eapply post_weaken_rule. all: eauto.
  Qed.

  (* Skipped for now *)
  (* Theorem comp_rule ... *)

  Lemma repr_if :
    ∀ {A b} (c₀ c₁ : raw_program A),
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
      (c₀ c₀' : raw_program A₀) (c₁ c₁' : raw_program A₁)
      {b₀ b₁}
      {pre : precond} {post : postcond A₀ A₁},
      (∀ s, pre s → b₀ = b₁) →
      r⊨ ⦃ λ s, pre s ∧ b₀ = true ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
      r⊨ ⦃ λ s, pre s ∧ b₀ = false ⦄ c₀' ≈ c₁' ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ if b₀ then c₀ else c₀' ≈ if b₁ then c₁ else c₁' ⦃ post ⦄.
  Proof.
    intros A₀ A₁ c₀ c₀' c₁ c₁' b₀ b₁ pre post hb ht hf.
    rewrite !repr_if.
    eapply if_rule. all: eauto.
  Qed.

  (* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)


  (* skipped for now:
  Theorem bounded_do_while_rule *)

  (*TODO: asymmetric variants of bounded_do_while --
    Rem.: low priority as not useful for our examples *)

  Lemma rcoupling_eq :
    ∀ {A : ord_choiceType} (K₀ K₁ : raw_program A) (ψ : precond),
      r⊨ ⦃ ψ ⦄ K₀ ≈ K₁ ⦃ eq ⦄ →
      ∀ s₀ s₁,
        ψ (s₀, s₁) →
        θ_dens (θ0 (repr K₀) s₀) = θ_dens (θ0 (repr K₁) s₁).
  Proof.
    intros A K₀ K₁ ψ h s₀ s₁ hψ.
    eapply coupling_eq. all: eauto.
  Qed.

  Lemma rrewrite_eqDistrL :
    ∀ {A₀ A₁ : ord_choiceType} {P Q}
      (c₀ c₀' : raw_program A₀) (c₁ : raw_program A₁),
      r⊨ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
      (∀ s, θ_dens (θ0 (repr c₀) s) = θ_dens (θ0 (repr c₀') s)) →
      r⊨ ⦃ P ⦄ c₀' ≈ c₁ ⦃ Q ⦄.
  Proof.
    intros A₀ A₁ P Q c₀ c₀' c₁ h hθ.
    eapply rewrite_eqDistrL. all: eauto.
  Qed.

  Lemma rrewrite_eqDistrR :
    ∀ {A₀ A₁ : ord_choiceType} {P Q}
      (c₀ : raw_program A₀) (c₁ c₁' : raw_program A₁),
      r⊨ ⦃ P ⦄ c₀ ≈ c₁ ⦃ Q ⦄ →
      (∀ s, θ_dens (θ0 (repr c₁) s) = θ_dens (θ0 (repr c₁') s)) →
      r⊨ ⦃ P ⦄ c₀ ≈ c₁' ⦃ Q ⦄.
  Proof.
    intros A₀ A₁ P Q c₀ c₁ c₁' h hθ.
    eapply rewrite_eqDistrR. all: eauto.
  Qed.

  Lemma rreflexivity_rule :
    ∀ {A : ord_choiceType} (c : raw_program A),
      r⊨ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ eq ⦄.
  Proof.
    intros A c.
    apply reflexivity_rule.
  Qed.

  Theorem rswap_rule :
    ∀ {A₀ A₁ : ord_choiceType} {I : precond} {post : postcond A₀ A₁}
      (c₀ : raw_program A₀) (c₁ : raw_program A₁),
      r⊨ ⦃ I ⦄ c₀ ≈ c₁
        ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
      r⊨ ⦃ I ⦄ c₁ ≈ c₀
        ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄ →
      r⊨ ⦃ I ⦄ c₀ ;; c₁ ≈ c₁ ;; c₀
        ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₀, s₀) (a₁, s₁) ⦄.
  Proof.
    intros A₀ A₁ I post c₀ c₁ h1 h2.
    rewrite !repr_bind.
    eapply swap_rule. all: auto.
  Qed.

  (** TW: I guess this to allow going under binders.
    We might be better off defining some morphisms on semantic judgments
    to use setoid_rewrite.
  *)
  Theorem rswap_ruleL :
    ∀ {A₀ A₁ B : ord_choiceType} {pre I : precond} {post : postcond A₁ A₀}
    (l : raw_program B) (c₀ : raw_program A₀) (c₁ : raw_program A₁),
    r⊨ ⦃ pre ⦄ l ≈ l ⦃ λ '(b₀, s₀) '(b₁, s₁), I (s₀, s₁) ⦄ →
    r⊨ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
    r⊨ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ post (a₁, s₁) (a₀, s₀) ⦄ →
    r⊨ ⦃ pre ⦄ l ;; c₀ ;; c₁ ≈ l ;; c₁ ;; c₀ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ B pre I post l c₀ c₁ hl h0 h1.
    rewrite !repr_bind.
    eapply swap_ruleL. all: eauto.
  Qed.

  Theorem rswap_ruleR :
    ∀ {A₀ A₁ B : ord_choiceType} {post : postcond B B}
      (c₀ : raw_program A₀) (c₁ : raw_program A₁) (r : A₀ → A₁ → raw_program B),
      (∀ b b', b = b' → post b b') →
      (∀ a₀ a₁, r⊨ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ≈ r a₀ a₁ ⦃ post ⦄) →
      r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁) ≈
        a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
        ⦃ eq ⦄ →
      r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈
        a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
        ⦃ post ⦄.
  Proof.
    intros A₀ A₁ B post c₀ c₁ r postr hr h.
    repeat setoid_rewrite repr_bind. simpl.
    eapply (swap_ruleR (λ a₀ a₁, repr (r a₀ a₁)) (repr c₀) (repr c₁) hr postr).
    intro s.
    unshelve eapply coupling_eq.
    - exact (λ '(h₀, h₁), h₀ = h₁).
    - repeat setoid_rewrite repr_bind in h.
      apply h.
    - reflexivity.
  Qed.

  Local Open Scope package_scope.

  Lemma rsym_pre :
    ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
      {c₀ : raw_program A₀} {c₁ : raw_program A₁},
      (∀ h₀ h₁, pre (h₀, h₁) → pre (h₁, h₀)) →
      r⊨ ⦃ λ '(h₀, h₁), pre (h₁, h₀) ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ pre post c₀ c₁ pre_sym h.
    unshelve eapply rpre_weaken_rule. 2: eassumption.
    assumption.
  Qed.

  Lemma rsymmetry :
    ∀ {A₀ A₁ : ord_choiceType} {pre : precond} {post}
      {c₀ : raw_program A₀} {c₁ : raw_program A₁},
      r⊨ ⦃ λ '(h₁, h₀), pre (h₀, h₁) ⦄ c₁ ≈ c₀
        ⦃ λ '(a₁, h₁) '(a₀, h₀), post (a₀, h₀) (a₁, h₁) ⦄ →
      r⊨ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ pre post c₀ c₁ h.
    eapply symmetry_rule. auto.
  Qed.

  Lemma rsamplerC :
    ∀ {A : ord_choiceType} (o : Op) (c : raw_program A),
      r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a ← c ;; r ← (r ← sample o ;; ret r) ;;  (ret (a, r)) ≈
        r ← (r ← sample o ;; ret r) ;; a ← c ;;  (ret (a, r))
      ⦃ eq ⦄.
  Proof.
    intros A o c.
  Admitted.

  Lemma rsamplerC' :
    ∀ {A : ord_choiceType} (o : Op) (c : raw_program A),
    r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (r, a) ≈
      a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (r, a)
    ⦃ eq ⦄.
  Proof.
  Admitted.

  (* TODO: generalize the corresponding rule in RulesStateProb.v  *)
  (* CA: not hight priority as never used yet! *)
  Theorem rswap_rule_ctx :
  ∀ {A : ord_choiceType} {I pre} {post Q : postcond A A}
    (l r c₀ c₁ : raw_program A),
    r⊨ ⦃ pre ⦄ l ≈ l ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ⦄ →
    (∀ a₀ a₁, r⊨ ⦃ λ '(s₁, s₀), Q (a₀,s₀) (a₁,s₁) ⦄ r ≈ r ⦃ post ⦄) →
    r⊨ ⦃ I ⦄ c₀ ≈ c₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
    r⊨ ⦃ I ⦄ c₁ ≈ c₀ ⦃ λ '(a₁, s₁) '(a₀, s₀), I (s₀, s₁) ∧ Q (a₀, s₀) (a₁, s₁) ⦄ →
    r⊨ ⦃ pre ⦄ l ;; c₀ ;; c₁ ;; r ≈ l ;; c₁ ;; c₀ ;; r ⦃ post ⦄.
  Proof.
    intros A I pre post Q l r c₀ c₁ hl hr h₀ h₁.
    rewrite !repr_bind.
    eapply swap_rule_ctx. 1: exact hl. 2: exact h₀. 2: exact h₁.
    intros a₀ a₁. eapply hr.
  Qed.

  Theorem rsame_head :
    ∀ {A B : ord_choiceType} {f₀ f₁ : A → raw_program B}
    (m : raw_program A) (post : postcond B B),
    (∀ a, r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
    r⊨ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ bind m f₀ ≈ bind m f₁ ⦃ post ⦄.
  Proof.
    intros A B f₀ f₁ m post h.
    eapply (rbind_rule m m).
    - eapply rreflexivity_rule.
    - intros a₀ a₁. unshelve eapply rpre_weaken_rule.
      + exact (λ '(h₀, h₁), a₀ = a₁ ∧ h₀ = h₁).
      + specialize (h a₀).
        eapply rpre_hypothesis_rule. simpl. intros s₀ s₁ [ea es]. subst.
        eapply rpre_weaken_rule. 1: exact h.
        simpl. intros h₀ h₁ [? ?]. subst. reflexivity.
      + simpl. intros s₀ s₁ e. noconf e. intuition auto.
  Qed.

  (* CA: not more useful than sampler_case *)
  (* Lemma rsample_rule { B1 B2 : ord_choiceType} { L : {fset Location}}  { o } *)
  (*       c1 c2  *)
  (*       pre (post : B1 * heap -> B2 * heap -> Prop) *)
  (*       (H : r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄) : *)
  (*          ⊨ ⦃ pre ⦄ repr (locs := L ) (x <$ o ;; c1) ≈ repr (locs := L) (x <$ o ;; c2) ⦃ post ⦄. *)
  (* Proof. Admitted.  *)

  Theorem rdead_sampler_elimL :
    ∀ {A : ord_choiceType} {D}
      (c₀ c₁ : raw_program A) (pre : precond) (post : postcond A A),
      r⊨ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ (x ← sample D ;; ret x) ;; c₀ ≈ c₁ ⦃ post ⦄.
  Proof.
    intros A D c₀ c₁ pre post h.
    eapply rrewrite_eqDistrL. 1: exact h.
    admit.
  Admitted.

  Theorem rdead_sampler_elimR :
    ∀ {A : ord_choiceType} {D}
      (c₀ c₁ : raw_program A) (pre : precond) (post : postcond A A),
      r⊨ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ c₀ ≈ (x ← sample D ;; ret x) ;; c₁ ⦃ post ⦄.
  Proof.
    intros A D c₀ c₁ pre post h.
    eapply rrewrite_eqDistrR. 1: exact h.
    admit.
  Admitted.

  (* TODO
    Instead of syntactic rules we should still find a way to make the judgment
    opaque, it takes so long to find it doesn't unify.
    Especially important when I will add commands in rules for which unification
    should be harder.
  *)

  (* TODO Find a proper place for it *)
  (** Rules on raw_program

    The idea is to define rules that don't care about validity. They will be the
    one manipulated by the user when showing perfect equivalence.
    A theorem will then say that when the programs are valid and in this relation
    then they are in the program relation from before.
    ⊢ ⦃ pre ⦄ u ~ v ⦃ post ⦄ →
    Valid u →
    Valid v →
    ⊨ ⦃ pre ⦄ u ~ v ⦃ post ⦄

    And with classes, the validity will be inferred automatically.
    Or even better when starting from packages, it will follow from the
    packages being valid themselves.

    Better: With context rules we could then use setoid rewrite.

  *)

  (** TODO Some rules will be missing, maybe best to wait after merge.

    Here is the list:
    - rpre_weaken_rule
    - rpre_hypothesis_rule
    - rpre_strong_hypothesis_rule
    - rpost_weaken_rule
    - rif_rule (should be provable without being assumed, otherwise we have a problem for user-defined types)
    - rsamplerC
    - rsamplerC'
    - rsame_head
    - rsym_pre
    - rsymmetry
    - rdead_sampler_elimL
    - rdead_sampler_elimR

    + context rules

    TODO Remove the rules above? It seems I will inline their proofs rather than
    use them.

  *)

  (* Definition ret_discr {A} (v : raw_program A) : Prop :=
    match v with
    | ret _ => False
    | _ => True
    end.

  Inductive ret_view {A} : raw_program A → Type :=
  | is_ret x : ret_view (ret x)
  | is_not_ret c : ret_discr c → ret_view c.

  Equations ret_viewc {A} (c : raw_program A) : ret_view c :=
    ret_viewc (ret x) := is_ret x ;
    ret_viewc c := is_not_ret c I.

  Lemma inversion_valid_bind2 :
        ∀ {L I} {A B} {c : raw_program A} {k : A → raw_program B},
          ret_discr c →
          valid_program L I (x ← c ;; k x) →
          ∀ x, valid_program L I (k x).
  Proof.
    intros L I A B c k nr h.
    induction c.
    - cbn in nr. contradiction.
    - simpl in h. apply inversion_valid_opr in h. destruct h as [? hk].
      intro a. remember (k a) as c eqn:e.
      destruct (ret_viewc c). 1: constructor.
      subst c. eapply H. eapply hk.
    - simpl in h1. apply inversion_valid_getr in h1. destruct h1 as [? hk].
      eapply H. eapply hk.
    - simpl in h1. apply inversion_valid_putr in h1. destruct h1 as [? hk].
      eapply IHc1. auto.
    - simpl in h1.
  Abort. *)

  (* Reserved Notation "⊢ ⦃ pre ⦄ c1 ~ c2 ⦃ post ⦄". *)

  (* TODO Complete *)

  (* Inductive raw_judgment :
    ∀ {A B : choiceType},
      precond → postcond A B → raw_program A → raw_program B → Prop :=

  | r_refl :
      ∀ A (c : raw_program A),
        ⊢ ⦃ λ '(s1, s2), s1 = s2 ⦄ c ~ c ⦃ eq ⦄

  (* r_seq *) (* Which one ist it? *)

  (* Legacy rule *)
  | r_swap :
      ∀ (A₀ A₁ : choiceType) (I : precond) (post : postcond A₀ A₁)
        (c₀ : raw_program A₀) (c₁ : raw_program A₁),
        ⊢ ⦃ I ⦄ c₀ ~ c₁ ⦃ λ b₀ b₁, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄ →
        ⊢ ⦃ I ⦄ c₁ ~ c₀ ⦃ λ b₁ b₀, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄ →
        ⊢ ⦃ I ⦄ c₀ ;; c₁ ~ c₁ ;; c₀ ⦃ λ b₁ b₀, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄

  (* Legacy rule, it requires extra validity assumptions *)
  (* Better use r_swap_cmd instead *)
  | r_swapR :
      ∀ L₀ L₁ Lr (A₀ A₁ B : choiceType) (post : postcond B B)
        (c₀ : raw_program A₀) (c₁ : raw_program A₁)
        (r : A₀ → A₁ → raw_program B),
        (∀ b, post b b) →
        (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ~ r a₀ a₁ ⦃ post ⦄) →
        (∀ x, ValidProgram L₁ Game_import (a₁ ← c₁ ;; r x a₁)) →
        (∀ x, ValidProgram L₀ Game_import (a₀ ← c₀ ;; r a₀ x)) →
        (∀ x y, ValidProgram Lr Game_import (r x y)) →
        ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
          a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁) ~
          a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
          ⦃ eq ⦄ →
        ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
          a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ~
          a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
          ⦃ post ⦄

  (* Not clear what the rule should be. *)
  (* Should we have rules for commands? That sounds cumbersome. *)
  (* | r_swap_cmd_seq :
      ∀ (A₀ A₁ B : choiceType) (I : precond) (post : postcond A₀ A₁)
        (c₀ : command A₀) (c₁ : command A₁) (k : raw_program B),
        ⊢ ⦃ I ⦄ c₀ ~ c₁ ⦃ λ b₀ b₁, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄ →
        ⊢ ⦃ I ⦄ c₁ ~ c₀ ⦃ λ b₁ b₀, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄ →
        ⊢ ⦃ I ⦄ c₀ ;' c₁ ;' k ~ c₁ ;' c₀ ;' k ⦃ λ b₁ b₀, I (b₀.2, b₁.2) ∧ post b₀ b₁ ⦄ *)

  | r_swap_cmd :
      ∀ (A₀ A₁ B : choiceType) (post : postcond B B)
        (c₀ : command A₀) (c₁ : command A₁)
        (r : A₀ → A₁ → raw_program B),
        (∀ b, post b b) →
        (∀ a₀ a₁, ⊢ ⦃ λ '(s₁, s₀), s₀ = s₁ ⦄ r a₀ a₁ ~ r a₀ a₁ ⦃ post ⦄) →
        ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
          a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; ret (a₀, a₁) ~
          a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; ret (a₀, a₁)
          ⦃ eq ⦄ →
        ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
          a₀ ← cmd c₀ ;; a₁ ← cmd c₁ ;; r a₀ a₁ ~
          a₁ ← cmd c₁ ;; a₀ ← cmd c₀ ;; r a₀ a₁
          ⦃ post ⦄

  where "⊢ ⦃ pre ⦄ c1 ~ c2 ⦃ post ⦄" := (raw_judgment pre post c1 c2) : package_scope.

  Lemma valid_judgment :
    ∀ (A₀ A₁ : choiceType) L₀ L₁ pre post c₀ c₁
      `{@ValidProgram L₀ _ A₀ c₀}
      `{@ValidProgram L₁ _ A₁ c₁},
      ⊢ ⦃ pre ⦄ c₀ ~ c₁ ⦃ post ⦄ →
      r⊨ ⦃ pre ⦄ mkprog c₀ _ ≈ mkprog c₁ _ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ L₀ L₁ pre post c₀ c₁ h₀ h₁ h.
    induction h in L₀, L₁, h₀, h₁ |- *.
    - pose proof (reflexivity_rule (repr {program c})) as h.
      erewrite repr_ext. 1: exact h.
      cbn. reflexivity.
    - apply inversion_valid_bind in h₀ as h₀'.
      apply inversion_valid_bind in h₁ as h₁'.
      specialize IHh1 with (h₀ := h₀') (h₁ := h₁').
      specialize IHh2 with (h₀ := h₁') (h₁ := h₀').
      pose proof @swap_rule as h.
      specialize h with (c1 := repr {program c₀ #with h₀' }).
      specialize h with (c2 := repr {program c₁ #with h₁' }).
      specialize h with (I := I) (post := post).
      eapply post_weaken_rule in IHh1.
      1: specialize h with (1 := IHh1).
      2:{
        cbn. intros [a₀ s₀] [a₁ s₁]. cbn. auto.
      }
      eapply post_weaken_rule in IHh2.
      1: specialize h with (1 := IHh2).
      2:{
        cbn. intros [a₀ s₀] [a₁ s₁]. cbn. auto.
      }
      cbn - [semantic_judgement repr].
      cbn - [semantic_judgement] in h.
      unshelve erewrite !repr_bind'. 3,4,7,8: eauto.
      eapply post_weaken_rule.
      1: exact h.
      cbn. intros [a₀ s₀] [a₁ s₁]. cbn. auto.
    - apply inversion_valid_bind in h₀ as h₀'.
      apply inversion_valid_bind in h₁ as h₁'.
      unshelve (repeat setoid_rewrite repr_bind'). 3,4,7,8,11,12,15,16:eauto.
      eapply (swap_ruleR (λ a₀ a₁, repr {program r a₀ a₁ }) (repr {program c₀ }) (repr {program c₁ })).
      + intros a₀ a₁. specialize (H1 a₀ a₁).
        specialize H1 with (h₀ := H4 _ _) (h₁ := H4 _ _).
        exact H1.
      + intros ? ? []. eauto.
      + intro s. unshelve eapply coupling_eq.
        * exact: (λ '(h1, h2), h1 = h2).
        * evar (L0 : {fset Location}).
          evar (L1 : {fset Location}).
          specialize (IHh L0 L1).
          subst L0 L1.
          match type of IHh with
          | ?A → _ =>
            assert (h0 : A)
          end.
          { eapply valid_bind.
            - eapply valid_injectLocations. 2: exact h₀'.
              eapply fsubsetUl.
            - intro. eapply valid_bind.
              + eapply valid_injectLocations. 2: eassumption.
                eapply fsubsetUr.
              + intro. constructor.
          }
          specialize (IHh h0).
          match type of IHh with
          | ?A → _ =>
            assert (h1 : A)
          end.
          { eapply valid_bind.
            - eapply valid_injectLocations. 2: exact h₁'.
              eapply fsubsetUl.
            - intro. eapply valid_bind.
              + eapply valid_injectLocations. 2: eassumption.
                eapply fsubsetUr.
              + intro. constructor.
          }
          specialize (IHh h1).
          revert IHh.
          unshelve (repeat (setoid_rewrite repr_bind')).
          3,7,11,15: eauto.
          6,8: intro ; constructor.
          2:{
            intro. eapply valid_bind. 1: eauto.
            intro. constructor.
          }
          2:{
            intro. eapply valid_bind. 1: eauto.
            intro. constructor.
          }
          1,2: exact fset0.
          auto.
        * cbn. reflexivity.
    - apply inversion_valid_cmd_bind in h₀ as hh.
      destruct hh as [hc₀ hk₀].
      apply inversion_valid_cmd_bind in h₁ as hh.
      destruct hh as [hc₁ hk₁].
      assert (hk : ∀ a₀ a₁, ValidProgram L₀ Game_import (r a₀ a₁)).
      { intros a₀ a₁. specialize (hk₀ a₀).
        apply inversion_valid_cmd_bind in hk₀ as [_ hk₀].
        eapply hk₀.
      }
      unshelve (repeat setoid_rewrite repr_cmd_bind).
      3,4,7,8,11,12,15,16: eauto.
      eapply (swap_ruleR (λ a₀ a₁, repr {program r a₀ a₁ }) (repr_cmd c₀ hc₀) (repr_cmd c₁ hc₁)).
      + intros a₀ a₁. specialize (H1 a₀ a₁).
        specialize H1 with (h₀ := hk _ _) (h₁ := hk _ _).
        exact H1.
      + intros ? ? []. eauto.
      + intro s. unshelve eapply coupling_eq.
        * exact: (λ '(h1, h2), h1 = h2).
        * evar (L0 : {fset Location}).
          evar (L1 : {fset Location}).
          specialize (IHh L0 L1).
          subst L0 L1.
          match type of IHh with
          | ?A → _ =>
            assert (h0 : A)
          end.
          { eapply valid_cmd_bind.
            - eapply valid_cmd_injectLocations. 2: exact hc₀.
              eapply fsubsetUl.
            - intro. eapply valid_cmd_bind.
              + eapply valid_cmd_injectLocations. 2: eassumption.
                eapply fsubsetUr.
              + intro. constructor.
          }
          specialize (IHh h0).
          match type of IHh with
          | ?A → _ =>
            assert (h1 : A)
          end.
          { eapply valid_cmd_bind.
            - eapply valid_cmd_injectLocations. 2: exact hc₁.
              eapply fsubsetUl.
            - intro. eapply valid_cmd_bind.
              + eapply valid_cmd_injectLocations. 2: eassumption.
                eapply fsubsetUr.
              + intro. constructor.
          }
          specialize (IHh h1).
          revert IHh.
          unshelve (repeat (setoid_rewrite repr_cmd_bind)).
          3,7,11,15: eauto.
          6,8: intro ; constructor.
          2:{
            intro. eapply valid_cmd_bind. 1: eauto.
            intro. constructor.
          }
          2:{
            intro. eapply valid_cmd_bind. 1: eauto.
            intro. constructor.
          }
          1,2: exact fset0.
          auto.
        * cbn. reflexivity.
  Qed. *)

  (* TODO Seems like repr only need no import, but doesn't care about
  locations. If so we could make a much simpler statement?
  Can probably define rep = repr' using noimport predicate
  Then the above would be simpler! No need for stupid Ls everywhere.
  *)

End PackageRHL.
