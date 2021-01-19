(*
  This file connects packages to the relational Hoare logic and provides basic crypto-style
  reasoning notions.
 *)


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
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

(* Must come after importing Equations.Equations, god knows why. *)
From Crypt Require Import FreeProbProg.


Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module PackageRHL (π : RulesParam).

  Import π.
  Include (PackageTactics π).

  Local Open Scope fset.
  Local Open Scope fset_scope.
  Local Open Scope type_scope.

  Section Games.
    Definition Game_import : Interface := fset0.
    Definition Game_Type (Game_export : Interface) : Type :=
      package Game_import Game_export.

    Definition RUN := (0, (chUnit, chBool)).
    Definition A_export : Interface := fset1 RUN.
    Lemma RUN_in_A_export : RUN \in A_export.
      apply in_fset1.
    Qed.

    Definition Adversary4Game (Game_export : Interface) : Type :=
      package Game_export A_export.
    Definition Adversary4Game_weak (Game_export : Interface) : Type :=
      opackage fset0 Game_export A_export.

    Open Scope fset.
    (* Let iops_StP := @ops_StP probE rel_choiceTypes chEmb. *)
    (* Let iar_StP := @ar_StP probE rel_choiceTypes chEmb. *)

    Definition pointed_value := ∑ (t : chUniverse), chElement t.

    Definition raw_heap := {fmap Location -> pointed_value}.
    Definition raw_heap_choiceType := [choiceType of raw_heap].

    Definition check_loc_val (l : Location) (v : pointed_value) := l.π1 == v.π1.
    Definition valid_location (h : raw_heap) (l : Location) :=
      match h l with
      | None => false
      | Some v => check_loc_val l v
      end.

    Definition valid_heap : pred raw_heap := fun h =>
      domm h == fset_filter (fun l => valid_location h l) (domm h).
    Definition heap := { h : raw_heap | valid_heap h }.
    Definition heap_choiceType := [choiceType of heap].

    Definition Game_op_import_S : Type := {_ : ident & void}.
    Definition Game_import_P : Game_op_import_S → choiceType :=
      fun v => match v with existT a b => match b with end end.

    Definition get_heap (map : heap) (l : Location) : option (Value l.π1).
    Proof.
      destruct map as [rh valid_rh].
      destruct (getm rh l) eqn:Hgetm.
      + assert (exists v, rh l = Some v) as H0.
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
        exact (Some p.π2).
      + exact None.
    Defined.

    Program Definition set_heap (map : heap) (l : Location)  (v : Value l.π1) : heap := setm map l (l.π1; v).
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

    Definition fromEmpty {B} {v : opsig} (H : v \in fset0) : B.
      rewrite in_fset0 in H.
      move: H. move /eqP. move /eqP => H.
      discriminate.
    Defined.

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
    Arguments ropr {_ _ _} _ _.

    Set Equations Transparent.

    Equations? repr' {B : choiceType} {L : {fset Location}}
      (p : raw_program B) (h : valid_program L Game_import p)
    : rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) B :=
      repr' p h with p := {
      | _ret x := retrFree _ ;
      | _opr o x k := False_rect _ _ ;
      | _getr l k := bindrFree _ _ (ropr (inl (inl (gett _))) (fun s => retrFree (get_heap s l))) (λ v, repr' (k v) _) ;
      | _putr l v k :=
        bindrFree _ _
        (ropr (inl (inl (gett heap_choiceType))) (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s l v)))) (fun s => retrFree tt))) (λ s', repr' k _) ;
      | _sampler op k := bindrFree _ _ (ropr (inr op) (fun v => retrFree v)) (λ s, repr' (k s) _)
      }.
    Proof.
      - destruct h as [hin _]. eapply fromEmpty. exact hin.
      - cbn in h. intuition auto.
      - cbn in h. destruct h as [ho h]. apply h.
    Defined.

    Definition repr {B locs} (p : program locs Game_import B) :=
      let '(exist p h) := p in
      repr' p h.

    Ltac fold_repr :=
      change (repr' ?p ?h) with (repr (exist _ p h)).

    Lemma repr'_ext {B L1 L2} (p1 p2 : raw_program B)
          (hp1 : valid_program L1 Game_import p1) (hp2 : valid_program L2 Game_import p2)
          (H : p1 = p2)
      : repr' p1 hp1 = repr' p2 hp2.
    Proof.
      destruct H.
      induction p1.
      - cbn. reflexivity.
      - pose f := hp1. destruct f as [hin _].
        eapply fromEmpty. exact hin.
      - cbn in hp1, hp2.
        cbn. f_equal. extensionality s.
        apply H.
      - cbn. f_equal. extensionality s.
        f_equal. extensionality s'.
        apply IHp1.
      - cbn. f_equal. extensionality s.
        apply H.
    Qed.

    Lemma repr_ext {B L1 L2} (p1 : program L1 Game_import B) (p2 : program L2 Game_import B)
          (H : p1.π1 = p2.π1)
      : repr p1 = repr p2.
    Proof.
      unfold repr.
      destruct p1. destruct p2.
      apply repr'_ext.
      exact H.
    Qed.

    Lemma repr_bind {B C} {L}
          (p : program L Game_import B) (f : B -> program L Game_import C) :
      repr (bind p f) =  bindrFree _ _ (repr p) (fun b => repr (f b)).
    Proof.
      destruct p as [p h].
      induction p.
      - cbn. fold_repr.
        f_equal.
        apply program_ext.
        simpl. reflexivity.
      - cbn in h. destruct h as [h1 h2]. eapply fromEmpty. exact h1.
      - cbn. f_equal. extensionality s.
        cbn in h. destruct h as [h1 h2].
        rewrite -(H (get_heap s l) (h2 (get_heap s l))).
        apply repr'_ext.
        repeat f_equal.
      - cbn. f_equal.
        extensionality s.
        f_equal.
        extensionality s'.
        destruct h as [h1 h2].
        rewrite -(IHp h2).
        apply repr'_ext.
        reflexivity.
      - cbn.
        f_equal.
        extensionality s.
        simpl in h.
        rewrite -(H s (h s)).
        apply repr'_ext.
        f_equal.
    Qed.


    Notation " r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄ " :=
        (semantic_judgement _ _ (repr c1) (repr c2) (fromPrePost pre post)).

    Theorem rbind_rule {A1 A2 B1 B2 : ord_choiceType}
            {L1 L2 : {fset Location}}
            {f1 : A1 -> program L1 Game_import B1}
            {f2 : A2 -> program L2 Game_import B2}
            (m1 : program L1 Game_import A1)
            (m2 : program L2 Game_import A2)
            (pre : heap * heap -> Prop)
            (middle : (A1 * heap) -> (A2 * heap) -> Prop)
            (post : (B1 * heap) -> (B2 * heap) -> Prop)
            (judge_wm : r⊨ ⦃ pre ⦄ m1 ≈ m2 ⦃ middle ⦄)
            (judge_wf : forall a1 a2,
                r⊨ ⦃ fun '(s1, s2) => middle (a1, s1) (a2, s2) ⦄
                  f1 a1 ≈ f2 a2
                  ⦃ post ⦄ ) :
      r⊨ ⦃ pre ⦄ (bind m1 f1 ) ≈ (bind m2 f2) ⦃ post ⦄.
    Proof.
      rewrite !repr_bind.
      apply (bind_rule_pp (repr m1) (repr m2) pre middle post judge_wm judge_wf).
    Qed.

    Let getLocations {I E} (P : package I E) : {fset Location} :=
      let '(locs; PP) := P in locs.

    Definition opaque_me {B} {L} {I E} (p : raw_package) (hp : valid_package L I E p)
               (o : opsig) (ho : o \in E) (arg : src o)
               (e : lookup_op p o = None) : B.
    Proof.
      (* TW: Done several times, I should make a lemma. *)
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

    Definition inspect {A : Type} (x : A) : { y : A | y = x } :=
      exist _ x erefl.

    Equations? get_raw_package_op {L} {I E : Interface} (p : raw_package)
      (hp : valid_package L I E p)
      (o : opsig) (ho : o \in E) (arg : src o) : program L I (tgt o) :=
      get_raw_package_op p hp o ho arg with inspect (lookup_op p o) := {
      | @exist (Some f) e1 := ⦑ f arg ⦒ ;
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
        (get_raw_package_op p hp o ho arg) ∙1 = f arg.
    Proof.
      intros L I E p hp o ho arg f e.
      funelim (get_raw_package_op p hp o ho arg).
      2:{ rewrite <- e in e0. discriminate. }
      rewrite <- Heqcall. cbn. rewrite <- e in e0.
      noconf e0. reflexivity.
    Qed.

    Definition raw_program_link_ext {E : Interface}
               (o : opsig) (ho : o \in E) (arg : src o) (p1 p2 : raw_package)
               (f : src o -> raw_program (tgt o))
               (Hf : lookup_op p1 o = Some f)
               (g : src o -> raw_program (tgt o))
               (Hg : lookup_op (raw_link p1 p2) o = Some g)
      : g arg = raw_program_link (f arg) p2.
    Proof.
      unfold raw_link in Hg.
      destruct o as [id [S T]].
      assert ((fun x => raw_program_link (f x) p2) = g).
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
          destruct p as [S' [T' f']].
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
          (hpl : valid_package L I E (raw_link p1 p2))
          : (get_raw_package_op (raw_link p1 p2) hpl o hin arg) ∙1 =
            raw_program_link ((get_raw_package_op p1 hp1 o hin arg) ∙1) p2.
    Proof.
      destruct (lookup_op (raw_link p1 p2) o) as [f|] eqn:e.
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
      rewrite (get_raw_package_op_lookup (raw_link p1 p2) _ o hin arg f e).
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
      apply (raw_program_link_ext o hin arg p1 p2 fl el f e).
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
      : (get_raw_package_op p hp1 o hin arg) ∙1 =
        (get_raw_package_op p hp2 o hin arg) ∙1.
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

    Definition get_opackage_op {L} {I E : Interface} (P : opackage L I E)
               (op : opsig) (Hin : op \in E) (arg : src op) : program L I (tgt op).
    Proof.
      exact (get_raw_package_op (projT1 P) (projT2 P) op Hin arg).
    Defined.

    Definition get_package_op {I E : Interface} (P : package I E)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : program (getLocations P) I (tgt op) :=
      let (L, PP) as s return (program (getLocations s) I (tgt op)) := P in
      get_opackage_op PP op Hin arg.

    Definition Pr_raw_program {L} {B}
               (p : raw_program B)
               (p_is_valid : valid_program L Game_import p)
      : heap_choiceType -> SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩).
    Proof.
      move => s0.
      pose STDIST := thetaFstd B (repr (exist _ p p_is_valid)) s0.
      exact (STDIST prob_handler).
    Defined.

    Definition Pr_raw_func_program {L} {A} {B}
               (p : A -> raw_program B)
               (p_is_valid : forall a, valid_program L Game_import (p a))
      : A -> heap_choiceType -> SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩).
    Proof.
      move => a s0.
      exact (Pr_raw_program (p a) (p_is_valid a) s0).
    Defined.

    Definition Pr_raw_package_op  {E : Interface} {L}
               (p : raw_package)
               (p_is_valid : valid_package L Game_import E p)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : heap_choiceType -> SDistr (F_choice_prod_obj ⟨ tgt op , heap_choiceType ⟩).
    Proof.
      move => s0.
      pose (get_raw_package_op p p_is_valid op Hin arg) as f.
      exact (Pr_raw_program (f∙1) (f∙2) s0).
    Defined.

    Definition Pr_op  {E : Interface} (P : package Game_import E)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : heap_choiceType -> SDistr (F_choice_prod_obj ⟨ tgt op , heap_choiceType ⟩).
    Proof.
      move => s0.
      destruct P as [L [PP PP_is_valid]].
      exact (Pr_raw_package_op PP PP_is_valid op Hin arg s0).
    Defined.

    Program Definition empty_heap : heap := emptym.
    Next Obligation.
      by rewrite /valid_heap domm0 /fset_filter -fset0E.
    Qed.

    Definition Pr (P : package Game_import A_export) : SDistr (bool_choiceType) :=
      SDistr_bind _ _ (fun '(b, _) => SDistr_unit _ b)
                      (Pr_op P RUN RUN_in_A_export Datatypes.tt empty_heap).

    Definition get_op {I E : Interface} (p : package I E)
      (o : opsig) (ho : o \in E) (arg : src o) :
      program (p.π1) I (tgt o).
    Proof.
      (* TW: I transformed this definition so that it computes directly. *)
      destruct (lookup_op (p.π2 ∙1) o) as [f|] eqn:e.
      2:{
        (* TW: Done several times, I should make a lemma. *)
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
    Open Scope ring_scope.
    Open Scope real_scope.

    Definition GamePair (Game_export : Interface) := bool -> Game_Type Game_export.

    Definition Advantage { Game_export : Interface } (G : GamePair Game_export)
               (A : Adversary4Game Game_export)
               {H1 : fdisjoint A.π1 (G false).π1} {H2 : fdisjoint A.π1 (G true).π1} : R :=
      `| (Pr (link A (G false)) true) - (Pr (link A (G true)) true)|.

    Definition AdvantageE { Game_export : Interface }
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
               (A : Adversary4Game Game_export)
               {H1 : fdisjoint A.π1 G0.π1} {H2 : fdisjoint A.π1 G1.π1} : R
      := `| (Pr (link A G0) true) - (Pr (link A G1) true)|.

    Definition AdvantageE_weak { Game_export : Interface }
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
               (A : Adversary4Game_weak Game_export) : R
      := `| (Pr (link (fset0; A) G0) true) - (Pr (link (fset0; A) G1) true)|.

    Definition state_pass_ {A} (p : raw_program A) : heap_choiceType -> raw_program (prod_choiceType A heap_choiceType).
    Proof.
      induction p; intros h.
      - constructor.
        exact (x, h).
      - apply (_opr o).
        + exact x.
        + intros v. exact (X v h).
      - apply X.
        + exact (get_heap h l).
        + exact h.
      - apply IHp.
        apply (set_heap h l v).
      - apply (_sampler op).
        intros v. exact (X v h).
    Defined.

    Definition state_pass__valid {A} {L} {I} (p : raw_program A) (h : valid_program L I p) :
      ∀ hp, valid_program fset0 I (state_pass_ p hp).
    Proof.
      induction p; intros hp.
      - auto.
      - destruct h as [h1 h2]. split.
        + assumption.
        + intros t.
          apply H.
          apply h2.
      - destruct h as [h1 h2].
        apply H.
        apply h2.
      - destruct h as [h1 h2].
        apply IHp.
        apply h2.
      - intros v.
        apply H.
        apply h.
    Qed.

    Definition state_pass {A} (p : raw_program A) : raw_program A :=
      bind_ (state_pass_ p empty_heap) (fun '(r, _) => _ret r).

    Definition state_pass_valid {A} {L} {I} (p : raw_program A) (h : valid_program L I p) :
      valid_program fset0 I (state_pass p).
    Proof.
      apply bind_valid.
      - apply (state_pass__valid p h empty_heap).
      - intros x. destruct x. cbn. auto.
    Qed.

    Definition turn_adversary_weak  { Game_export : Interface }
               (A : Adversary4Game Game_export) : Adversary4Game_weak Game_export.
    Proof.
      unfold Adversary4Game_weak, opackage.
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

    Definition pr_weak {Game_export : Interface} (A : Adversary4Game Game_export) G :
      Pr (link (fset0; turn_adversary_weak A) G) true = Pr (link A G) true.
    Proof.
    Admitted.

    Definition perf_ind {Game_export : Interface}
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
      forall A H1 H2, @AdvantageE _ G0 G1 A H1 H2 = 0.

    Definition perf_ind_weak {Game_export : Interface}
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
      forall A, @AdvantageE_weak _ G0 G1 A = 0.

    Definition perf_ind_weak_implies_perf_ind {Game_export : Interface}
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
               (h : perf_ind_weak G0 G1) : perf_ind G0 G1.
    Proof.
      unfold perf_ind, perf_ind_weak, AdvantageE, AdvantageE_weak in *.
      intros A H1 H2.
      rewrite -(pr_weak A G0).
      rewrite -(pr_weak A G1).
      apply h.
    Qed.

    Notation "ϵ( GP )" := (fun A => AdvantageE (GP false) (GP true) A) (at level 90).
    Notation " G0 ≈[ R ] G1 " := (AdvantageE G0 G1 = R) (at level 50).

    Lemma TriangleInequality  {Game_export : Interface} {F G H : Game_Type Game_export}
          {ϵ1 ϵ2 ϵ3}
          (ineq1 : F ≈[ ϵ1 ] G)
          (ineq2 : G ≈[ ϵ2 ] H)
          (ineq3 : F ≈[ ϵ3 ] H)
      : forall A H1 H2 H3 H4 H5 H6, ϵ3 A H1 H2 <= ϵ1 A H3 H4 + ϵ2 A H5 H6.
    Proof.
      move => A H1 H2 H3 H4 H5 H6.
      assert (@AdvantageE _ F G A H3 H4 = ϵ1 A H3 H4) as Ineq1.
      { rewrite ineq1. reflexivity. }
      assert (@AdvantageE _ G H A H5 H6 = ϵ2 A H5 H6) as Ineq2.
      { rewrite ineq2. reflexivity. }
      assert (@AdvantageE _ F H A H1 H2 = ϵ3 A H1 H2) as Ineq3.
      { rewrite ineq3. reflexivity. }
      unfold AdvantageE in Ineq1, Ineq2, Ineq3.
      rewrite -Ineq1 -Ineq2 -Ineq3.
      apply ler_dist_add.
    Qed.

    Lemma Reduction {Game_export M_export : Interface} {M : package Game_export M_export}
          (G : GamePair Game_export) (A : Adversary4Game M_export) (b : bool) :
      `| Pr (link A (link M (G b))) true | = `| Pr (link (link A M) (G b))  true |.
    Proof.
      rewrite link_assoc.
      reflexivity.
    Qed.

    Lemma rhl_repr_change_all {B1 B2 : choiceType} {L1 L2 L1' L2'}
          {pre : heap_choiceType * heap_choiceType -> Prop}
          {post : (B1 * heap_choiceType) -> (B2 * heap_choiceType) -> Prop}
          {r1 r1' : raw_program B1} {r2 r2' : raw_program B2}
          {hr11 : valid_program L1 Game_import r1}
          {hr12 : valid_program L2 Game_import r1'}
          {hr21 : valid_program L1' Game_import r2}
          {hr22 : valid_program L2' Game_import r2'}
          (Hr1 : r1 = r1') (Hr2 : r2 = r2')
          (H : ⊨ ⦃ pre ⦄ repr (exist _ r1 hr11) ≈ repr (exist _ r2 hr21) ⦃ post ⦄)
      : ⊨ ⦃ pre ⦄ repr (exist _ r1' hr12) ≈ repr (exist _ r2' hr22) ⦃ post ⦄.
    Proof.
      unfold repr in *.
      induction Hr1. induction Hr2.
      assert (repr' r1 hr11 = repr' r1 hr12) as Hr1.
      { apply repr'_ext. reflexivity. }
      assert (repr' r2 hr21 = repr' r2 hr22) as Hr2.
      { apply repr'_ext. reflexivity. }
      rewrite -Hr1 -Hr2. assumption.
    Qed.

    Definition INV (L : {fset Location}) (I : heap_choiceType * heap_choiceType -> Prop) :=
      forall s1 s2, (I (s1, s2) -> forall l, l \in L -> get_heap s1 l = get_heap s2 l) /\
               (I (s1, s2) -> forall l v, l \in L -> I (set_heap s1 l v, set_heap s2 l v)).

    Definition INV' (L1 L2 : {fset Location}) (I : heap_choiceType * heap_choiceType -> Prop) :=
      forall s1 s2, (I (s1, s2) -> forall l, l \notin L1 -> l \notin L2 -> get_heap s1 l = get_heap s2 l) /\
               (I (s1, s2) -> forall l v, l \notin L1 -> l \notin L2 -> I (set_heap s1 l v, set_heap s2 l v)).

    Lemma INV'_to_INV (L L1 L2 : {fset Location}) (I : heap_choiceType * heap_choiceType -> Prop)
          (HINV' : INV' L1 L2 I) (Hdisjoint1 : fdisjoint L L1) (Hdisjoint2 : fdisjoint L L2)
      : INV L I.
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

    Lemma get_case {L LA} (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) {l : Location} (Hin : l \in LA)
      (hp : [eta valid_program L Game_import] (_getr l (fun x => _ret x))):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (exist _ (_getr l (fun x => _ret x)) hp)
          ≈ repr (locs := L) (exist _ (_getr l (fun x => _ret x)) hp)
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
      cbn. intros [s1 s2].
      rewrite /SpecificationMonads.MonoCont_bind /=.
      rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
              /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order /=.
      intuition.
      assert (get_heap s1 l = get_heap s2 l) as Hv.
      { unfold INV in HINV.
        destruct hp as [hp _].
        specialize (HINV s1 s2). destruct HINV as [HINV _].
        specialize (HINV H0 _ Hin).
        assumption.
      }
      unfold repr'_obligation_1.
      pose v := (SDistr_unit _ (((get_heap s1 l), s1),
                                ((get_heap s2 l), s2))).
      exists v.
      split.
      + apply SDistr_unit_F_choice_prod_coupling.
        reflexivity.
      + intros [b1 s3] [b2 s4].
        intros Hd.
        apply H1.
        unfold SDistr_unit in Hd.
        rewrite dunit1E in Hd.
        unfold repr'_obligation_1 in Hd.
        assert (((get_heap s1 l, s1, (get_heap s2 l, s2)) = (b1, s3, (b2, s4)))) as Heqs.
        { destruct ((get_heap s1 l, s1, (get_heap s2 l, s2)) == (b1, s3, (b2, s4))) eqn:Heqd.
          + move: Heqd. move /eqP => Heqd. assumption.
          + rewrite Heqd in Hd. simpl in Hd.
            rewrite mc_1_10.Num.Theory.ltrr in Hd.
            move: Hd. move /eqP /eqP => Hd. discriminate. }
        inversion Heqs.
        all: rewrite -H3 -H5.
        intuition.
    Qed.

    Lemma put_case {L LA} (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) {l : Location} {v : Value l.π1} (Hin : l \in LA)
      (hp : [eta valid_program L Game_import] (_putr l v (_ret tt))):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (exist _ (_putr l v (_ret tt)) hp)
          ≈ repr (locs := L) (exist _ (_putr l v (_ret tt)) hp)
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
      cbn. intros [s1 s2].
      rewrite /SpecificationMonads.MonoCont_bind /=.
      rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
              /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order /=.
      intuition.
      exists (SDistr_unit _ ((repr'_obligation_1 unit_choiceType tt, set_heap s1 l v),
                        (repr'_obligation_1 unit_choiceType tt, set_heap s2 l v))).
      split.
      + apply SDistr_unit_F_choice_prod_coupling.
        reflexivity.
      + intros [b1 s3] [b2 s4].
        intros Hd.
        apply H1.
        unfold SDistr_unit in Hd.
        rewrite dunit1E in Hd.
        unfold repr'_obligation_1 in Hd.
        assert ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) = (b1, s3, (b2, s4))) as Heqs.
        { destruct ((tt, set_heap s1 l v, (tt, set_heap s2 l v)) == (b1, s3, (b2, s4))) eqn:Heqd.
          + move: Heqd. move /eqP => Heqd. assumption.
          + rewrite Heqd in Hd. simpl in Hd.
            rewrite mc_1_10.Num.Theory.ltrr in Hd.
            move: Hd. move /eqP /eqP => Hd. discriminate. }
        inversion Heqs.
        split.
        1: reflexivity.
        specialize (HINV s1 s2). destruct HINV as [_ HINV].
        specialize (HINV H0 l v Hin).
        assumption.
    Qed.

    Lemma destruct_pair_eq {R : ringType} {A B : eqType} {a b : A} {c d : B}
      : ((a, c) == (b, d))%:R = (a == b)%:R * (c == d)%:R :> R.
    Proof.
      destruct (a == b) eqn:ab, (c == d) eqn:cd.
      all: cbn; rewrite ab cd /=; try rewrite GRing.mulr1; try rewrite GRing.mulr0; reflexivity.
    Qed.
    Lemma summable_eq {A : choiceType} {s : A}
      : realsum.summable (T:=A) (R:=R) (λ x, (x == s)%:R).
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


    Lemma sampler_case {L LA} (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) {op}
      (hp : [eta valid_program L Game_import] (_sampler op [eta _ret (A:=Arit op)])):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (exist _ (_sampler op [eta _ret (A:=Arit op)]) hp)
          ≈ repr (locs := L) (exist _ (_sampler op [eta _ret (A:=Arit op)]) hp)
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
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
      Eval cbn in (ord_functor_comp
                    (OrderEnrichedRelativeAdjunctionsExamples.unaryTimesS1 heap_choiceType)
                    (OrderEnrichedRelativeAdjunctions.KleisliLeftAdjoint Frp)
                    (StateTransformingLaxMorph.ar_StP heap_choiceType (inr op))).
      pose foo := (sigMap (inr op) s1).
      cbn in foo.
      unfold probopStP in foo. cbn in foo.
      destruct op as [opA opB].
      pose foo2 :=  SDistr_bind _ _ (fun x => SDistr_unit _ ((x, s1), (x, s2))) (Theta_dens.unary_ThetaDens0 prob_handler _ (ropr (opA; opB) (λ x : chEmb opA, retrFree x))).
      exists foo2.
      split.
      - cbn. unfold coupling.
        split.
        + unfold lmg.
          unfold foo2. apply distr_ext.
          move => x0. unfold SDistr_bind, SDistr_unit.
          unfold repr'_obligation_1. cbn.
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
          unfold repr'_obligation_1. cbn.
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

    (* TODO MOVE *)
    (* (Safe) lookup in open packages *)
    Definition olookup_full {L I E} (p : opackage L I E)
      {id : ident} {S T : chUniverse} (h : (id, (S, T)) \in E) :
      ∑ f : S → program L I T,
        ∀ g, p.π1 id = Some (S ; T ; g) → ∀ (x : S), (f x) ∙1 = g x.
    Proof.
      destruct (p.π1 id) as [[S' [T' f]]|] eqn:e.
      2:{
        exfalso.
        destruct p as [p hp]. specialize (hp _ h) as h'.
        cbn in h'. cbn in e. rewrite e in h'.
        destruct h'. intuition discriminate.
      }
      unshelve eexists.
      - intro x.
        unshelve eexists.
        + simple refine (cast_fun _ _ f x).
          * destruct p as [p hp]. specialize (hp _ h) as h'.
            cbn in h'. cbn in e. rewrite e in h'.
            destruct h' as [g [he hv]].
            noconf he. reflexivity.
          * destruct p as [p hp]. specialize (hp _ h) as h'.
            cbn in h'. cbn in e. rewrite e in h'.
            destruct h' as [g [he hv]].
            noconf he. reflexivity.
        + destruct p as [p hp]. specialize (hp _ h) as h'.
          cbn in h'. cbn in e. rewrite e in h'.
          destruct h' as [g [he hv]].
          noconf he. cbn.
          rewrite cast_fun_K.
          apply hv.
      - intros g eg x. cbn. noconf eg.
        destruct p as [p hp]. specialize (hp _ h) as h'.
        cbn in h'. cbn in e. rewrite e in h'.
        destruct h' as [g [he hv]].
        noconf he. cbn.
        rewrite cast_fun_K.
        reflexivity.
    Defined.

    Definition olookup {L I E} (p : opackage L I E)
      {id : ident} {S T : chUniverse} (h : (id, (S, T)) \in E) :
      S → program L I T :=
      (olookup_full p h).π1.

    Lemma olookup_fst :
      ∀ L I E (p : opackage L I E) id S T (h : (id, (S, T)) \in E) f x,
        p.π1 id = Some (S ; T ; f) →
        (olookup p h x) ∙1 = f x.
    Proof.
      intros L I E p id S T h f x e.
      unfold olookup. destruct olookup_full as [g hg].
      cbn. specialize hg with (1 := e).
      apply hg.
    Qed.

    Definition cast_vfun {L I} {So To St Tt : chUniverse}
      (hS : St = So) (hT : Tt = To) (f : St → program L I Tt) :
      So → program L I To.
    Proof.
      subst. auto.
    Defined.

    Lemma cast_vfun_K :
      ∀ L I S T f e1 e2,
        @cast_vfun L I S T S T e1 e2 f = f.
    Proof.
      intros L I S T f e1 e2.
      rewrite (uip e1 erefl).
      rewrite (uip e2 erefl).
      reflexivity.
    Qed.

    Lemma cast_vfun_cong :
      ∀ L I S₁ S₂ T₁ T₂ f g u₁ v₁ u₂ v₂,
        f = g →
        @cast_vfun L I S₁ T₁ S₂ T₂ u₁ v₁ f =
        @cast_vfun L I S₁ T₁ S₂ T₂ u₂ v₂ g.
    Proof.
      intros L I S₁ S₂ T₁ T₂ f ? u₁ v₁ u₂ v₂ [].
      subst. cbn. rewrite cast_vfun_K. reflexivity.
    Qed.

    Equations? safe_list_lookup
      {L I id S T} (l : seq (nat * pointed_vprogram L I)) (h : (id, (S, T)) \in export_interface (mkfmap l)) :
      S → program L I T :=
      safe_list_lookup p h with (inspect (getm_def p id)) := {
      | @exist (Some (S' ; T'; f)) e := cast_vfun _ _ f ;
      | @exist None e := False_rect _ _
      }.
    Proof.
      - unfold export_interface in h. rewrite in_fset in h.
        move: h => /getmP h. rewrite mapmE in h.
        destruct (mkfmap p id) as [[SS [TT g]]|] eqn:e'.
        2:{ rewrite e' in h. discriminate. }
        rewrite e' in h. cbn in h. noconf h.
        rewrite mkfmapE in e'. rewrite e' in e. noconf e.
        reflexivity.
      - unfold export_interface in h. rewrite in_fset in h.
        move: h => /getmP h. rewrite mapmE in h.
        destruct (mkfmap p id) as [[SS [TT g]]|] eqn:e'.
        2:{ rewrite e' in h. discriminate. }
        rewrite e' in h. cbn in h. noconf h.
        rewrite mkfmapE in e'. rewrite e' in e. noconf e.
        reflexivity.
      - unfold export_interface in h. rewrite in_fset in h.
        move: h => /getmP h. rewrite mapmE in h.
        destruct (mkfmap p id) as [[SS [TT g]]|] eqn:e'.
        2:{ rewrite e' in h. discriminate. }
        rewrite e' in h. cbn in h. noconf h.
        rewrite mkfmapE in e'. rewrite e' in e. noconf e.
    Qed.

    (* Equations? safe_getm_def {A : eqType} n (x : A) (s : seq (nat * A))
      (h : (n,x) \in s) : A :=
      safe_getm_def n x s h with inspect (getm_def s n) := {
      | @exist (Some u) _ := u ;
      | @exist None e := False_rect _ _
      }.
    Proof.
      eapply in_getm_def_None. all: eauto.
    Qed. *)

    Lemma olookup_unfold :
      ∀ L I id S T l (h : (id, (S, T)) \in export_interface (mkfmap l)),
        olookup (L := L) (I := I) (mkpack (mkfmap l)) h =
        safe_list_lookup l h.
    Proof.
      intros L I id S T l h.
      funelim (safe_list_lookup l h). 2: falso.
      inversion H as [e1]. rewrite <- Heqcall.
      extensionality z. apply program_ext.
      unfold export_interface in h. pose proof h as h'.
      rewrite in_fset in h'. move: h' => /getmP h'.
      rewrite mapmE in h'.
      destruct (mkfmap l id) as [[SS [TT g]]|] eqn:e'.
      2:{ rewrite e' in h'. discriminate. }
      rewrite e' in h'. cbn in h'. noconf h'.
      (* rewrite mkfmapE in e'. rewrite e' in e. noconf e. *)
      erewrite olookup_fst.
      2:{
        unfold mkpack. cbn - [mapm]. rewrite mapmE.
        rewrite e'. cbn. reflexivity.
      }
      simpl.
      rewrite mkfmapE in e'. rewrite e' in e1. noconf e1.
      rewrite cast_vfun_K. reflexivity.
    Qed.

    Definition pdom (I : Interface) : {fset ident} :=
      (λ '(id, _), id) @: I.

    (* TODO MOVE *)
    (* (Safe) lookup (by id) in open packages *)
    Equations? olookup_id {L I E} (p : opackage L I E)
      {id : ident} (h : id \in pdom E) :
      pointed_vprogram L I :=
      olookup_id p h with inspect (p.π1 id) := {
      | @exist (Some (So ; To ; f)) e := (So ; To ; λ x, ⦑ f x ⦒) ;
      | @exist None e := False_rect _ _
      }.
    Proof.
      - destruct p as [p hp]. cbn in *.
        unfold pdom in h.
        move: h => /imfsetP h. cbn in h. destruct h as [[id' [S' T']] hin ?].
        subst id'.
        specialize (hp _ hin) as h'. cbn in h'.
        destruct h' as [g [eg hg]].
        rewrite -e in eg. noconf eg. cbn in hg.
        apply hg.
      - destruct p as [p hp]. cbn in *.
        unfold pdom in h.
        move: h => /imfsetP h. cbn in h. destruct h as [[id' [S' T']] hin ?].
        subst id'.
        specialize (hp _ hin) as h'. cbn in h'.
        destruct h' as [g [eg hg]].
        rewrite -e in eg. noconf eg.
    Qed.

    Definition pdefS {L I E} (p : opackage L I E) {id : ident}
      (h : id \in pdom E) : chUniverse :=
      (olookup_id p h).π1.

    Definition pdefT {L I E} (p : opackage L I E) {id : ident}
      (h : id \in pdom E) : chUniverse :=
      (olookup_id p h).π2.π1.

    Definition pdef {L I E} (p : opackage L I E) {id : ident}
      (h : id \in pdom E) : pdefS p h → program L I (pdefT p h) :=
      (olookup_id p h).π2.π2.

    Lemma pdefS_eq :
      ∀ {L₁ L₂ I E} (p₁ : opackage L₁ I E) (p₂ : opackage L₂ I E)
        {id : ident} (h : id \in pdom E),
        pdefS p₁ h = pdefS p₂ h.
    Proof.
      intros L₁ L₂ I E p₁ p₂ id h.
      unfold pdefS. funelim (olookup_id p₁ h). 2: falso.
      rewrite <- Heqcall. clear Heqcall. simpl.
      funelim (olookup_id p₂ h). 2: falso.
      rewrite <- Heqcall. clear Heqcall. simpl.
      destruct p as [p₁ h₁], p0 as [p₂ h₂]. cbn in *.
      unfold pdom in h.
      move: h => /imfsetP h. cbn in h. destruct h as [[id' [S' T']] hin ?].
      subst id'.
      specialize (h₁ _ hin). cbn in h₁.
      destruct h₁ as [f [ef hf]].
      rewrite -e in ef. noconf ef.
      specialize (h₂ _ hin). cbn in h₂.
      destruct h₂ as [g [eg hg]].
      rewrite -e0 in eg. noconf eg.
      reflexivity.
    Qed.

    Lemma pdefT_eq :
      ∀ {L₁ L₂ I E} (p₁ : opackage L₁ I E) (p₂ : opackage L₂ I E)
        {id : ident} (h : id \in pdom E),
        pdefT p₁ h = pdefT p₂ h.
    Proof.
      intros L₁ L₂ I E p₁ p₂ id h.
      unfold pdefT. funelim (olookup_id p₁ h). 2: falso.
      rewrite <- Heqcall. clear Heqcall. simpl.
      funelim (olookup_id p₂ h). 2: falso.
      rewrite <- Heqcall. clear Heqcall. simpl.
      destruct p as [p₁ h₁], p0 as [p₂ h₂]. cbn in *.
      unfold pdom in h.
      move: h => /imfsetP h. cbn in h. destruct h as [[id' [S' T']] hin ?].
      subst id'.
      specialize (h₁ _ hin). cbn in h₁.
      destruct h₁ as [f [ef hf]].
      rewrite -e in ef. noconf ef.
      specialize (h₂ _ hin). cbn in h₂.
      destruct h₂ as [g [eg hg]].
      rewrite -e0 in eg. noconf eg.
      reflexivity.
    Qed.

    Lemma pdefS_spec :
      ∀ {L I E} (p : opackage L I E) {id S T} (h : id \in pdom E) {f},
        p.π1 id = Some (S ; T ; f) →
        pdefS p h = S.
    Proof.
      intros L I E p id S T h f e.
      unfold pdefS. funelim (olookup_id p h). 2: falso.
      rewrite <- Heqcall. clear Heqcall.
      rewrite -e in e0. noconf e0.
      cbn. reflexivity.
    Qed.

    Lemma pdefT_spec :
      ∀ {L I E} (p : opackage L I E) {id S T} (h : id \in pdom E) {f},
        p.π1 id = Some (S ; T ; f) →
        pdefT p h = T.
    Proof.
      intros L I E p id S T h f e.
      unfold pdefT. funelim (olookup_id p h). 2: falso.
      rewrite <- Heqcall. clear Heqcall.
      rewrite -e in e0. noconf e0.
      cbn. reflexivity.
    Qed.

    Lemma pdef_fst :
      ∀ {L I E} (p : opackage L I E) {id S T} (h : id \in pdom E) {f}
        (e : p.π1 id = Some (S ; T ; f)) x,
        (cast_vfun (pdefS_spec p h e) (pdefT_spec p h e) (pdef p h) x) ∙1 = f x.
    Proof.
      intros L I E p id S T h f e x. cbn in f.
      unfold pdef. funelim (olookup_id p h). 2: falso.
      pose proof e0 as e'. rewrite -e in e'. noconf e'.
      cbn in e0. clear H.
      set (e1 := pdefS_spec _ _ _).
      set (e2 := pdefT_spec _ _ _).
      clearbody e1 e2. revert e1 e2.
      unfold pdefS. unfold pdefT.
      rewrite <- Heqcall. cbn.
      intros e1 e2.
      rewrite cast_vfun_K.
      cbn. reflexivity.
    Qed.

    Equations? safe_getm_def
      {L I id} (l : seq (nat * pointed_vprogram L I)) (h : id \in pdom (export_interface (mkfmap l))) :
      pointed_vprogram L I :=
      safe_getm_def p h with (inspect (getm_def p id)) := {
      | @exist (Some (S' ; T' ; f)) e := (S' ; T' ; f) ;
      | @exist None e := False_rect _ _
      }.
    Proof.
      unfold export_interface in h. unfold pdom in h.
      move: h => /imfsetP h. cbn - [mapm] in h.
      destruct h as [[id' [S' T']] h e']. subst id'.
      rewrite in_fset in h.
      move: h => /getmP h. rewrite mapmE in h.
      destruct (mkfmap p id) as [[SS [TT g]]|] eqn:e'.
      2:{ rewrite e' in h. discriminate. }
      rewrite e' in h. cbn in h. noconf h.
      rewrite mkfmapE in e'. rewrite e' in e. noconf e.
    Qed.

    Definition ldefS {L I id} l h : chUniverse :=
      (@safe_getm_def L I id l h).π1.

    Definition ldefT {L I id} l h : chUniverse :=
      (@safe_getm_def L I id l h).π2.π1.

    Definition ldef {L I id} l h : ldefS l h → program L I (ldefT l h) :=
      (@safe_getm_def L I id l h).π2.π2.

    Lemma ldefS_spec :
      ∀ {L I id l S T f} h,
        mkfmap (T:=nat_ordType) l id = Some (S ; T ; f) →
        @ldefS L I id l h = S.
    Proof.
      intros L I id l S T f h e.
      rewrite mkfmapE in e.
      unfold ldefS. funelim (safe_getm_def l h). 2: falso.
      rewrite <- Heqcall. clear Heqcall.
      cbn.
      rewrite -e in e0. noconf e0.
      reflexivity.
    Qed.

    Lemma ldefT_spec :
      ∀ {L I id l S T f} h,
        mkfmap (T:=nat_ordType) l id = Some (S ; T ; f) →
        @ldefT L I id l h = T.
    Proof.
      intros L I id l S T f h e.
      rewrite mkfmapE in e.
      unfold ldefT. funelim (safe_getm_def l h). 2: falso.
      rewrite <- Heqcall. clear Heqcall.
      cbn.
      rewrite -e in e0. noconf e0.
      reflexivity.
    Qed.

    Lemma ldefS_pdefS_eq :
      ∀ {L I id l} h,
        ldefS (id := id) l h = pdefS (L := L) (I := I) (mkpack (mkfmap l)) h.
    Proof.
      intros L I id l h.
      pose proof h as h'. unfold pdom in h'.
      move: h' => /imfsetP h'. cbn - [mkfmap] in h'.
      destruct h' as [[id' [S T]] h' e]. subst id'.
      unfold export_interface in h'.
      rewrite in_fset in h'.
      move: h' => /getmP h'. rewrite mapmE in h'.
      destruct (mkfmap l id) as [[S' [T' f]]|] eqn:e.
      2:{ rewrite e in h'. discriminate. }
      rewrite e in h'. cbn in h'. noconf h'.
      erewrite pdefS_spec.
      2:{
        unfold mkpack. cbn - [mapm mkfmap].
        rewrite mapmE. rewrite e. cbn. reflexivity.
      }
      eapply ldefS_spec. eassumption.
    Qed.

    Lemma ldefT_pdefT_eq :
      ∀ {L I id l} h,
        ldefT (id := id) l h = pdefT (L := L) (I := I) (mkpack (mkfmap l)) h.
    Proof.
      intros L I id l h.
      pose proof h as h'. unfold pdom in h'.
      move: h' => /imfsetP h'. cbn - [mkfmap] in h'.
      destruct h' as [[id' [S T]] h' e]. subst id'.
      unfold export_interface in h'.
      rewrite in_fset in h'.
      move: h' => /getmP h'. rewrite mapmE in h'.
      destruct (mkfmap l id) as [[S' [T' f]]|] eqn:e.
      2:{ rewrite e in h'. discriminate. }
      rewrite e in h'. cbn in h'. noconf h'.
      erewrite pdefT_spec.
      2:{
        unfold mkpack. cbn - [mapm mkfmap].
        rewrite mapmE. rewrite e. cbn. reflexivity.
      }
      eapply ldefT_spec. eassumption.
    Qed.

    Lemma pdef_unfold :
      ∀ L I id l (h : id \in pdom (export_interface (mkfmap l))),
        pdef (L := L) (I := I) (mkpack (mkfmap l)) h =
        cast_vfun (ldefS_pdefS_eq h) (ldefT_pdefT_eq h) (ldef l h).
    Proof.
      intros L I id l h.
      pose proof h as h'. unfold pdom in h'.
      move: h' => /imfsetP h'. cbn - [mkfmap] in h'.
      destruct h' as [[id' [S T]] h' e]. subst id'.
      unfold export_interface in h'.
      rewrite in_fset in h'.
      move: h' => /getmP h'. rewrite mapmE in h'.
      destruct (mkfmap l id) as [[S' [T' f]]|] eqn:e.
      2:{ rewrite e in h'. discriminate. }
      rewrite e in h'. cbn in h'. noconf h'.
      rewrite mkfmapE in e.
      unfold ldef. funelim (safe_getm_def l h). 2: falso.
      rewrite -e in e0. noconf e0.
      extensionality z. apply program_ext.
      clear H.
      pose proof (pdef_fst (mkpack (mkfmap l)) h (f := λ x, (p x) ∙1)) as e'.
      match type of e' with
      | ?A → _ =>
        assert (e'' : A)
      end.
      { simpl. rewrite mapmE.
        rewrite mkfmapE. rewrite <- e. cbn. reflexivity.
      }
      specialize (e' e'').
      set (e1 := ldefS_pdefS_eq _).
      set (e2 := ldefT_pdefT_eq _).
      clearbody e1 e2. revert e1 e2.
      unfold ldefS. unfold ldefT.
      rewrite <- Heqcall. simpl.
      intros e1 e2. subst. cbn.
      rewrite <- e'.
      rewrite cast_vfun_K.
      reflexivity.
    Qed.

    Definition eq_up_to_inv_alt2 {L₁ L₂} {E}
      (I : heap_choiceType * heap_choiceType → Prop)
      (p₁ : opackage L₁ Game_import E) (p₂ : opackage L₂ Game_import E) :=
      ∀ (id : ident) (h : id \in pdom E) x,
        r⊨ ⦃ λ '(s₀, s₃), I (s₀, s₃) ⦄
          pdef p₁ h x ≈
          cast_vfun (pdefS_eq p₂ p₁ h) (pdefT_eq p₂ p₁ h) (pdef p₂ h) x
          ⦃ λ '(b₁, s₀) '(b₂, s₃), b₁ = b₂ ∧ I (s₀, s₃) ⦄.

    Definition eq_up_to_inv_alt {L₁ L₂} {E}
      (I : heap_choiceType * heap_choiceType → Prop)
      (p₁ : opackage L₁ Game_import E) (p₂ : opackage L₂ Game_import E) :=
      ∀ (id : ident) (S T : chUniverse) (h : (id, (S, T)) \in E) (x : S),
        ⊨ ⦃ λ '(s₀, s₃), I (s₀, s₃) ⦄
          repr (olookup p₁ h x) ≈ repr (olookup p₂ h x)
          ⦃ λ '(b₁, s₀) '(b₂, s₃), b₁ = b₂ ∧ I (s₀, s₃) ⦄.

    Definition eq_up_to_inv {L1 L2} {E}
               (I : heap_choiceType * heap_choiceType → Prop)
               (P1 : opackage L1 Game_import E) (P2 : opackage L2 Game_import E) :=
      ∀ (id : ident) (S T : chUniverse)
        (hin : (id, (S, T)) \in E)
        (f : S → raw_program T) (g : S → raw_program T)
        (Hf : P1.π1 id = Some (S; T; f)) (hpf : ∀ x, valid_program L1 Game_import (f x))
        (Hg : P2.π1 id = Some (S; T; g)) (hpg : ∀ x, valid_program L2 Game_import (g x))
        (arg : S),
        ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄ repr (exist _ (f arg) (hpf arg)) ≈ repr (exist _ (g arg) (hpg arg)) ⦃ λ '(b1, s0) '(b2, s3), b1 = b2 ∧ I (s0, s3) ⦄.

    Lemma eq_up_to_inv_to_alt :
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
      (* Too slow *)
      (* match goal with
      | |- ?G =>
        let T := type of h in
        replace G with T ; [ auto | ]
      end.
      f_equal. *)
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
      - apply program_ext. cbn. erewrite olookup_fst. all: eauto.
      - apply program_ext. cbn. erewrite olookup_fst. all: eauto.
    Qed.

    Lemma eq_up_to_inv_from_alt :
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
      - apply program_ext. cbn. erewrite olookup_fst. all: eauto.
      - apply program_ext. cbn. erewrite olookup_fst. all: eauto.
    Qed.

    Lemma eq_up_to_inv_to_alt2 :
      ∀ L₁ L₂ E I p₁ p₂,
        @eq_up_to_inv L₁ L₂ E I p₁ p₂ →
        @eq_up_to_inv_alt2 L₁ L₂ E I p₁ p₂.
    Proof.
      intros L₁ L₂ E I p₁ p₂ h.
      intros id hin x.
      specialize (h id).
      pose proof hin as hin'. unfold pdom in hin'.
      move: hin' => /imfsetP hin'. cbn in hin'.
      destruct hin' as [[id' [S' T']] hin' ?]. subst id'.
      specialize h with (1 := hin').
      destruct p₁ as [p₁ hp₁]. specialize (hp₁ _ hin') as h'.
      cbn in h'. destruct h' as [f₁ [e₁ h₁]].
      destruct p₂ as [p₂ hp₂]. specialize (hp₂ _ hin') as h'.
      cbn in h'. destruct h' as [f₂ [e₂ h₂]].
      specialize h with (1 := e₁) (2 := e₂).
      specialize (h h₁ h₂).
      pose proof (pdefS_spec (exist _ p₁ hp₁) hin e₁) as e. subst S'.
      specialize (h x).
      pose proof (pdefT_spec (exist _ p₁ hp₁) hin e₁) as e. subst T'.
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
      - apply program_ext. cbn.
        pose proof (pdef_fst (exist _ p₁ hp₁) hin e₁) as e.
        rewrite <- e.
        rewrite cast_vfun_K. reflexivity.
      - apply program_ext. cbn.
        pose proof (pdef_fst (exist _ p₂ hp₂) hin e₂) as e'.
        rewrite <- e'.
        apply (f_equal (λ f, (f x) ∙1)).
        apply cast_vfun_cong. reflexivity.
    Qed.
    (* TODO Also \in domp can be replaced by \in domm p when proving useful
      lemma with mkpack mkfmap *)

    Lemma eq_up_to_inv_from_alt2 :
      ∀ L₁ L₂ E I p₁ p₂,
        @eq_up_to_inv_alt2 L₁ L₂ E I p₁ p₂ →
        @eq_up_to_inv L₁ L₂ E I p₁ p₂.
    Proof.
      intros L₁ L₂ E I p₁ p₂ h.
      intros id S T hin f g ef hf eg hg x.
      specialize (h id).
      eapply mem_imfset in hin as hin'.
      specialize (h hin').
      eapply pdefS_spec with (h0 := hin') in ef as e'.
      cbn in hin'. subst S.
      specialize (h x).
      eapply pdefT_spec with (h0 := hin') in ef as e'. subst T.
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
      - apply program_ext. cbn.
        pose proof (pdef_fst p₁ hin' ef) as e.
        rewrite <- e.
        rewrite cast_vfun_K. reflexivity.
      - apply program_ext. cbn.
        pose proof (pdef_fst p₂ hin' eg) as e'.
        rewrite <- e'.
        apply (f_equal (λ f, (f x) ∙1)).
        apply cast_vfun_cong. reflexivity.
    Qed.

    Lemma some_lemma_for_prove_relational {export : Interface} {B} {L1 L2 LA}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (HINV : INV LA I) (Hempty : I (empty_heap, empty_heap))
               (H : eq_up_to_inv I P1 P2)
               (A : program LA export B)
               (s1 : heap_choiceType) (s2 : heap_choiceType) (Hs1s2 : I (s1, s2))
      :
        ⊨ ⦃ fun '(s1, s2) => I (s1, s2)  ⦄
          repr (program_link (injectLocations (fsubsetUl LA (L1 :|: L2)) A) (opackage_inject_locations (fsubset_trans (fsubsetUl L1 L2) (fsubsetUr LA (L1 :|: L2))) P1))
          ≈
          repr (program_link (injectLocations (fsubsetUl LA (L1 :|: L2)) A) (opackage_inject_locations (fsubset_trans (fsubsetUr L1 L2) (fsubsetUr LA (L1 :|: L2))) P2))
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
      destruct P1 as [P1a P1b] eqn:HP1.
      destruct P2 as [P2a P2b] eqn:HP2.
      destruct A as [A hA].
      induction A; intros.
      - cbn - [semantic_judgement].
        unfold repr'_obligation_1.
        eapply weaken_rule.
        + apply ret_rule.
        + cbn. intros [h1 h2] post.
          cbn. unfold SPropMonadicStructures.SProp_op_order.
          unfold Basics.flip, SPropMonadicStructures.SProp_order.
          intros [HI Hp].
          apply Hp. split.
          * reflexivity.
          * assumption.
      - cbn in hA. destruct hA as [hA1 hA2].
        pose foo := (P1b o hA1).
        destruct o as [id [S T]].
        destruct foo as [f [K1 K2]].
        cbn - [semantic_judgement lookup_op].
        fold_repr.
        assert (lookup_op P1a (id, (S, T)) = Some f).
        { cbn. rewrite K1.
          destruct (chUniverse_eqP S S), (chUniverse_eqP T T).
          all: try contradiction.
          noconf e. noconf e0. reflexivity.
        }
        sig rewrite H1.
        unshelve erewrite fold_bind.
        { intro. eapply raw_program_link_valid.
          - eapply valid_injectLocations.
            2: eapply hA2.
            apply fsubsetUl.
          - eapply valid_package_inject_locations.
            2: eauto.
            eapply fsubset_trans.
            + eapply fsubsetUl.
            + eapply fsubsetUr.
        }
        (* Would need funext rewrite *)
        (* unshelve erewrite fold_program_link. *)
        pose foo2 := (P2b (id, (S, T)) hA1).
        destruct foo2 as [f2 [K12 K22]].
        cbn - [semantic_judgement lookup_op bind].
        assert (lookup_op P2a (id, (S, T)) = Some f2) as H2.
        { cbn. rewrite K12.
          destruct (chUniverse_eqP S S), (chUniverse_eqP T T). all: try contradiction.
          noconf e. noconf e0. reflexivity. }
        fold_repr.
        sig rewrite H2.
        unshelve erewrite fold_bind.
        { intro. eapply raw_program_link_valid.
          - eapply valid_injectLocations.
            2: eapply hA2.
            apply fsubsetUl.
          - eapply valid_package_inject_locations.
            2: eauto.
            eapply fsubset_trans.
            + eapply fsubsetUr.
            + eapply fsubsetUr.
        }
        rewrite !repr_bind.
        eapply bind_rule_pp.
        + unfold eq_up_to_inv in H.
          specialize (H id S T hA1 f f2 K1 K2 K12 K22 x).
          unfold repr in H. unfold repr.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity.
          exact H.
        + intros a1 a2.
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          specialize (H0 a1 (hA2 a1)).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (exist _ p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity.
          exact H0.
      - unfold program_link. unfold injectLocations.
        unfold opackage_inject_locations.
        cbn - [semantic_judgement bindrFree].
        destruct hA as [hA1 hA2].
        unfold repr'_obligation_4.
        cbn - [semantic_judgement bindrFree].
        match goal with
        | |- ⊨ ⦃ ?pre_ ⦄ bindrFree _ _ ?m_ ?f1_ ≈ bindrFree _ _ _ ?f2_ ⦃ ?post_ ⦄ =>
          pose (m := m_); pose (f1 := f1_); pose (f2 := f2_); pose (pre := pre_); pose (post := post_)
        end.
        eapply (bind_rule_pp (f1 := f1) (f2 := f2) m m pre _ post).
        + eapply (@get_case _ LA).
          ++ assumption.
          ++ exact hA1.
             Unshelve.
          * exact LA.
          * cbn. auto.
        + intros a1 a2.
          simpl (λ '(s0, s3), (λ '(b1, s4) '(b2, s5), b1 = b2 s/\ I (s4, s5)) (a1, s0) (a2, s3)).
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          specialize (H0 a1 (hA2 a1)).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (exist _ p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact H0.
      - unfold program_link. unfold injectLocations. unfold opackage_inject_locations.
        cbn - [semantic_judgement bindrFree].
        destruct hA as [hA1 hA2].
        match goal with
        | |- ⊨ ⦃ ?pre_ ⦄ bindrFree _ _ ?m_ ?f1_ ≈ bindrFree _ _ _ ?f2_ ⦃ ?post_ ⦄ =>
          pose (m := m_); pose (f1 := f1_); pose (f2 := f2_); pose (pre := pre_); pose (post := post_)
        end.
        eapply (bind_rule_pp (f1 := f1) (f2 := f2) m m pre _ post).
        + eapply (@put_case _ LA).
          ++ assumption.
          ++ exact hA1.
          Unshelve.
          * exact LA.
          * cbn. auto.
        + intros a1 a2.
          simpl (λ '(s0, s3), (λ '(b1, s4) '(b2, s5), b1 = b2 s/\ I (s4, s5)) (a1, s0) (a2, s3)).
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          specialize (IHA hA2).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in IHA.
          change (repr' ?p ?h) with (repr (exist _ p h)) in IHA.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact IHA.
      - unfold program_link. unfold injectLocations. unfold opackage_inject_locations.
        cbn - [bindrFree semantic_judgement].
        eapply bind_rule_pp.
        + eapply (@sampler_case LA LA).
          ++ assumption.
             Unshelve.
             1: { cbn. auto. }
        + intros a1 a2.
          simpl (λ '(s0, s3), (λ '(b1, s4) '(b2, s5), b1 = b2 s/\ I (s4, s5)) (a1, s0) (a2, s3)).
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          cbn in hA. pose (hA a1) as hAa1.
          specialize (H0 a1 hAa1).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (exist _ p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact H0.
    Qed.

    (* ER: How do we connect the package theory with the RHL?
           Something along the following lines should hold? *)
    Lemma prove_relational {L1 L2} {export}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (HINV' : INV' L1 L2 I)
               (Hempty : I (empty_heap, empty_heap))
               (H : eq_up_to_inv I P1 P2)
      : (L1; P1) ≈[ fun A {H1} {H2} => 0 ] (L2; P2).
    Proof.
      extensionality A.
      unfold Adversary4Game in A.
      unfold AdvantageE, Pr.
      extensionality Hdisjoint1. extensionality Hdisjoint2.
      pose r' := get_package_op A RUN RUN_in_A_export.
      pose r := r' tt.
      (* ER: from linking we should get the fact that A.π1 is disjoint from L1 and L2,
             and then from that conclude that we are invariant on A.π1 *)
      (* unshelve epose (fdisjoint_from_link A.π2 P1 _) as Hdisjoint1. *)
      (* { eexists. reflexivity. } *)
      (* unshelve epose (fdisjoint_from_link A.π2 P2 _) as Hdisjoint2. *)
      (* { eexists. reflexivity. } *)
      assert (INV A.π1 I) as HINV.
      { destruct A. simpl in Hdisjoint1, Hdisjoint2.
        cbn.  unfold INV.
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
      }
      pose Hlemma := (some_lemma_for_prove_relational _ _ _ HINV Hempty H r empty_heap empty_heap Hempty).
      assert (∀ x y : tgt RUN * heap_choiceType,
                 (let '(b1, s1) := x in λ '(b2, s2), b1 = b2 s/\ I (s1, s2)) y → (fst x == true) ↔ (fst y == true)) as Ha.
      { intros [b1 s1] [b2 s2]. simpl.
        intros [H1 H2]. rewrite H1. intuition. }
      pose Heq := (Pr_eq _ _ _ _ Hlemma Hempty Ha).
      simpl in Heq.
      simpl in Hlemma.
      unfold θ_dens in Heq.
      simpl in Heq. unfold pr in Heq.
      simpl in Heq.
      unfold Pr_op.
      pose _rhs := (thetaFstd _ (repr (program_link
            (injectLocations (fsubsetUl (getLocations A) (L1 :|: L2)) r)
            (opackage_inject_locations
               (fsubset_trans (y:=L1 :|: L2) (x:=L1)
                  (z:=getLocations A :|: (L1 :|: L2)) (fsubsetUl L1 L2)
                  (fsubsetUr (getLocations A) (L1 :|: L2))) P1))) empty_heap).
      pose rhs := _rhs prob_handler.
      simpl in _rhs, rhs.
      pose lhs := (let (L, o) := link A (L1; P1) in
                   let (PP, PP_is_valid) := o in
                   Pr_raw_package_op PP PP_is_valid RUN RUN_in_A_export tt empty_heap).
      assert (lhs = rhs).
      { unfold lhs, rhs, _rhs. simpl.
        unfold Pr_raw_package_op. unfold Pr_raw_program.
        unfold thetaFstd. simpl. apply f_equal2. 2: { reflexivity. }
        apply f_equal. apply f_equal.
        unfold getLocations. unfold ".π1".
        destruct A as [LA [A A_valid]].
        apply repr'_ext.
        erewrite (get_raw_package_op_link RUN_in_A_export tt (trim A_export ((LA; ⦑ A ⦒).π2) ∙1) (P1 ∙1) _ _).
        apply f_equal2. 2: { reflexivity. }
        cbn - [get_raw_package_op].
        unfold get_opackage_op. cbn - [get_raw_package_op].
        unshelve erewrite get_raw_package_op_trim.
        { apply (valid_package_inject_locations _ _ LA (LA :|: L1)).
          - apply fsubsetUl.
          - exact A_valid.
        }
        epose (get_raw_package_op_ext RUN_in_A_export tt A) as e.
        specialize (e (valid_package_inject_locations export A_export LA (LA :|: L1) A
                                                      (fsubsetUl LA L1) A_valid)).
        eapply e.
      }
      unfold lhs in H0.
      rewrite H0.
      pose _rhs' := (thetaFstd _ (repr (program_link
            (injectLocations (fsubsetUl (getLocations A) (L1 :|: L2)) r)
            (opackage_inject_locations
               (fsubset_trans (y:=L1 :|: L2) (x:=L2)
                  (z:=getLocations A :|: (L1 :|: L2)) (fsubsetUr L1 L2)
                  (fsubsetUr (getLocations A) (L1 :|: L2))) P2))) empty_heap).
      pose rhs' := _rhs' prob_handler.
      simpl in _rhs', rhs'.
      pose lhs' := (let (L, o) := link A (L2; P2) in
                   let (PP, PP_is_valid) := o in
                   Pr_raw_package_op PP PP_is_valid RUN RUN_in_A_export tt empty_heap).
      assert (lhs' = rhs') as H0'.
      { unfold lhs', rhs', _rhs'. simpl.
        unfold Pr_raw_package_op. unfold Pr_raw_program.
        unfold thetaFstd. simpl. apply f_equal2. 2: { reflexivity. }
        apply f_equal. apply f_equal.
        unfold getLocations. unfold ".π1".
        destruct A as [LA [A A_valid]].
        apply repr'_ext.
        erewrite (get_raw_package_op_link RUN_in_A_export tt (trim A_export ((LA; ⦑ A ⦒).π2) ∙1) (P2 ∙1) _ _).
        apply f_equal2. 2: { reflexivity. }
        cbn - [get_raw_package_op].
        unfold get_opackage_op. cbn - [get_raw_package_op].
        unshelve erewrite get_raw_package_op_trim.
        { apply (valid_package_inject_locations _ _ LA (LA :|: L2)).
          - apply fsubsetUl.
          - exact A_valid.
        }
        epose (get_raw_package_op_ext RUN_in_A_export tt A) as e.
        specialize (e (valid_package_inject_locations export A_export LA (LA :|: L2) A
                                                      (fsubsetUl LA L2) A_valid)).
        eapply e.
      }
      unfold lhs' in H0'.
      rewrite H0'.
      unfold rhs', _rhs', rhs, _rhs.

      unfold SDistr_bind. unfold SDistr_unit.
      simpl.
      rewrite !dletE.
      assert (forall x : bool_choiceType * heap_choiceType, ((let '(b, _) := x in dunit (R:=R) (T:=bool_choiceType) b) true) == (x.1 == true)%:R).
      { intros [b s].
        simpl. rewrite dunit1E. intuition. }
      assert (forall y, (λ x : prod_choiceType (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) true) = (λ x : prod_choiceType (tgt RUN) heap_choiceType, (x.1 == true)%:R * (y x))) as Hrew.
      { intros y. extensionality x.
        destruct x as [x1 x2].
        rewrite dunit1E.
        simpl. rewrite GRing.mulrC. reflexivity. }
      rewrite !Hrew.
      unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
      unfold SubDistr.SDistr_obligation_2. simpl.
      unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1. simpl.
      rewrite !SDistr_rightneutral. simpl.
      rewrite Heq.
      rewrite /StateTransfThetaDens.unaryStateBeta'_obligation_1.
      unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1, stT_thetaDens_adj.
      assert (forall (x : R), `|x - x| = 0) as Hzero.
      { intros x.
        assert (x - x = 0) as H3.
        { apply /eqP. rewrite GRing.subr_eq0. intuition.  }
        rewrite H3. apply mc_1_10.Num.Theory.normr0.
        }
      rewrite Hzero.
      reflexivity.
      Unshelve.
      - apply valid_trim.
        cbn.
        apply (valid_package_inject_locations _ _ LA (LA :|: L1)).
            + apply fsubsetUl.
            + exact A_valid.
      - apply valid_trim.
        cbn.
        apply (valid_package_inject_locations _ _ LA (LA :|: L2)).
            + apply fsubsetUl.
            + exact A_valid.
    Qed.

    (* Alternative version for packages *)
    Corollary prove_relational' :
      ∀ {export}
        (P1 : package Game_import export)
        (P2 : package Game_import export)
        (I : heap_choiceType * heap_choiceType -> Prop)
        (HINV' : INV' P1.π1 P2.π1 I)
        (Hempty : I (empty_heap, empty_heap))
        (H : eq_up_to_inv I P1.π2 P2.π2),
        P1 ≈[ fun A {H1} {H2} => 0 ] P2.
    Proof.
      intros E [L₁ p₁] [L₂ p₂] I hI he h.
      eapply prove_relational. all: eauto.
    Qed.


  (* Rules for packages *)
  (* same as in RulesStateprob.v with `r` at the beginning *)

  (* Pre-condition manipulating rules *)
  Theorem rpre_weaken_rule {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
          {p1 : program L1 Game_import A1}
          {p2 : program L2 Game_import A2} :
    forall (pre pre' : heap * heap -> Prop) post, ( r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄) ->
                                         (forall st1 st2, pre' (st1, st2) -> pre (st1, st2) ) ->
                                          ( r⊨ ⦃ pre' ⦄ p1 ≈ p2 ⦃ post ⦄ ) .
  Proof. by apply: pre_weaken_rule. Qed.

  Theorem rpre_hypothesis_rule  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
          {p1 : program L1 Game_import A1}
          {p2 : program L2 Game_import A2} :
    forall (pre : heap * heap -> Prop) post,
      (forall st1 st2, pre (st1, st2) -> r⊨ ⦃ (fun st => st.1 = st1 /\ st.2 = st2 ) ⦄ p1 ≈ p2 ⦃ post ⦄) ->
      (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄).
  Proof. by apply: pre_hypothesis_rule. Qed.


Theorem rpre_strong_hypothesis_rule  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
                             {p1 : program L1 Game_import A1}
                             {p2 : program L1 Game_import A2} :
  forall (pre : heap * heap -> Prop) post, (forall st1 st2, pre (st1, st2)) -> (r⊨ ⦃ (fun st => True ) ⦄ p1 ≈ p2 ⦃ post ⦄) ->
                              (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄).
Proof. by apply: pre_strong_hypothesis_rule. Qed.

Theorem rpost_weaken_rule  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
                          {p1 : program L1 Game_import A1}
                          {p2 : program L2 Game_import A2} :
    forall (pre : heap * heap -> Prop) (post1 post2 : A1 * heap -> A2 * heap -> Prop),
    (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post1 ⦄) ->
    (forall as1 as2, post1 as1 as2 -> post2 as1 as2) -> (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post2 ⦄).
Proof. by apply: post_weaken_rule. Qed.


(* Skipped for now *)
(* Theorem comp_rule ... *)

Print repr_bind.

Lemma repr_if {A} {L} {b : bool} (c1 c2 : program L Game_import A):
      repr (if b then c1 else c2) =  if b then (repr c1) else (repr c2).
Proof. by destruct b. Qed.


Theorem rif_rule  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
                 (c1 c2 : program L1 Game_import A1)
                 (c1' c2' : program L2 Game_import A2)
                 {b1 b2 : bool}
                 {pre : heap * heap -> Prop} {post : A1 * heap -> A2 * heap -> Prop}
                 {pre_b1b2 : forall st, pre st -> b1 = b2}
                 { H1 : r⊨ ⦃ fun st => pre st /\ b1 = true ⦄ c1 ≈ c1' ⦃ post ⦄ }
                 { H2 : r⊨ ⦃ fun st => pre st /\ b1 = false ⦄ c2 ≈ c2' ⦃ post ⦄ } :
  r⊨ ⦃ pre ⦄
      (if b1 then c1 else c2) ≈
      (if b2 then c1' else c2')
     ⦃ post ⦄.
Proof. rewrite !repr_if. by apply: if_rule. Qed.

(* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)


(* skipped for now:
Theorem bounded_do_while_rule *)

(*TODO: asymmetric variants of bounded_do_while -- CA: low priority as not useful for our examples *)

Lemma rcoupling_eq { A : ord_choiceType } { L : {fset Location} }
                  (K1 K2 : program L Game_import A )
                  (ψ : heap * heap -> Prop)
                  (H : r⊨ ⦃ ψ ⦄ K1 ≈ K2 ⦃ eq ⦄):
  forall s1 s2, ψ (s1, s2) -> θ_dens (θ0 (repr K1) s1) = θ_dens (θ0 (repr K2) s2).
Proof. by apply: coupling_eq (repr K1) (repr K2) ψ H. Qed.


Lemma rrewrite_eqDistrL { A1 A2 : ord_choiceType } {L1 L2 : {fset Location} } { P } { Q }
      (c1 c1' : program L1 Game_import A1) (c2 : program L2 Game_import A2)
      (H : r⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
      (θeq : forall s, θ_dens (θ0 (repr c1) s) = θ_dens (θ0 (repr c1') s )) :

 r⊨ ⦃ P ⦄ c1'  ≈ c2 ⦃ Q ⦄.
Proof. by apply: rewrite_eqDistrL (repr c1) (repr c1') (repr c2) H θeq. Qed.

Lemma rrewrite_eqDistrR { A1 A2 : ord_choiceType } {L1 L2 : {fset Location} } { P } { Q }
                       (c1  : program L1 Game_import A1) (c2 c2': program L2 Game_import A2)
                       (H : r⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
                       (θeq : forall s, θ_dens (θ0 (repr c2) s) = θ_dens (θ0 (repr c2') s)) :

  r⊨ ⦃ P ⦄ c1  ≈ c2' ⦃ Q ⦄.
Proof. by apply: rewrite_eqDistrR (repr c1) (repr c2) (repr c2') H θeq. Qed.

Lemma rreflexivity_rule { A : ord_choiceType } { L : {fset Location} }
      (c : program L Game_import A):
  r⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ c ≈ c ⦃ eq ⦄.
Proof. by apply: reflexivity_rule (repr c). Qed.

Theorem rswap_rule { A : ord_choiceType } { L : {fset Location} } { I Q }
                  (c1 c2 : program L Game_import A)
                  (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ )
                  (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ ):
  r⊨ ⦃ I ⦄ (bind c1 (fun _ => c2)) ≈ (bind c2 (fun _ => c1)) ⦃ Q ⦄.
Proof. rewrite !repr_bind. by apply: swap_rule (repr c1) (repr c2) Hinv1 Hinv2. Qed.

Theorem rswap_ruleL { A : ord_choiceType } { L : {fset Location} }
                   { pre I } { Left  post : A * heap -> A * heap -> Prop }
                   (l c1 c2 : program L Game_import A)
                   (HL    : r⊨ ⦃ pre ⦄ l ≈ l ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) ⦄)
                   (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Left (a1, s1) (a2, s2) ⦄ )
                   (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Left (a1, s1) (a2, s2) ⦄ )
                   (LQ : forall a1 s1 a2 s2, Left (a1, s1) (a2, s2) -> post (a1, s1) (a2, s2)):
  r⊨ ⦃ pre ⦄
   (bind l (fun _ => (bind c1 (fun _ => c2)))) ≈
   (bind l (fun _ => (bind c2 (fun _ => c1))))
   ⦃ post ⦄ .
Proof. rewrite !repr_bind. by apply: swap_ruleL (repr l) (repr c1) (repr c2) HL Hinv1 Hinv2 LQ. Qed.

Theorem rswap_ruleR { A : ord_choiceType } { L : {fset Location} }
                   { I } { post Q : A * heap -> A * heap -> Prop }
                   (r c1 c2 : program L Game_import A)
                   (HR    : forall a1 a2, r⊨ ⦃ fun '(s1, s2) => Q (a1,s1) (a2,s2) ⦄ r ≈ r ⦃ post ⦄)
                   (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ )
                   (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ ):
  r⊨ ⦃ I ⦄
   (bind c1 (fun _ => bind c2 (fun _ => r))) ≈
   (bind c2 (fun _ => bind c1 (fun _ => r)))
   ⦃ post ⦄.
Proof. rewrite !repr_bind. by apply: swap_ruleR (repr r) (repr c1) (repr c2) HR Hinv1 Hinv2. Qed.

Theorem rswap_rule_ctx { A : ord_choiceType } { L : {fset Location} }
                       { I pre } { post Q : A * heap -> A * heap -> Prop }
                       (l r c1 c2 : program L Game_import A)
                      (HL    : r⊨ ⦃ pre ⦄ l ≈ l ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) ⦄)
                      (HR    : forall a1 a2, r⊨ ⦃ fun '(s1, s2) => Q (a1,s1) (a2,s2) ⦄ r ≈ r ⦃ post ⦄)
                      (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ )
                      (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ ):
  r⊨ ⦃ pre ⦄
   (bind l (fun _ => bind c1  (fun _ => bind c2 (fun _ => r)))) ≈
   (bind l (fun _ => bind c2  (fun _ => bind c1 (fun _ => r))))
    ⦃ post ⦄.
Proof. rewrite !repr_bind. by apply: swap_rule_ctx (repr l) (repr r) (repr c1) (repr c2) HL HR Hinv1 Hinv2. Qed.

Check rbind_rule.

Theorem rsame_head {A B : ord_choiceType}
            {L : {fset Location}}
            {f1 : A -> program L Game_import B}
            {f2 : A -> program L Game_import B}
            (m : program L Game_import A)
            (post : (B * heap) -> (B * heap) -> Prop)
            (judge_wf : forall a,
                r⊨ ⦃ fun '(h1,h2) => h1 = h2 ⦄ f1 a ≈ f2 a ⦃ post ⦄ ) :
      r⊨ ⦃  fun '(h1,h2) => h1 = h2 ⦄ (bind m f1 ) ≈ (bind m f2) ⦃ post ⦄.
Proof.
  eapply (rbind_rule m m).
  - exact: rreflexivity_rule.
  - move => a1 a2. apply: rpre_weaken_rule.
    -- Unshelve. 2:{ exact: (fun '(h1,h2) => a1 = a2 /\ h1 = h2). }
       1: { specialize (judge_wf a1).
            apply: rpre_hypothesis_rule. rewrite /= => st1 st2 [Heq1 Heq2].
            subst. apply: rpre_weaken_rule.
            + exact: judge_wf.
            + rewrite /= => h1 h2 [Heq1 Heq2]. by subst. }
         rewrite /= => h1 h2 [Heq1 Heq2]. by subst.
Qed.





Local Open Scope package_scope.

(* CA: not more useful than sampler_case *)
(* Lemma rsample_rule { B1 B2 : ord_choiceType} { L : {fset Location}}  { o } *)
(*       c1 c2  *)
(*       pre (post : B1 * heap -> B2 * heap -> Prop) *)
(*       (H : r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄) : *)
(*          ⊨ ⦃ pre ⦄ repr (locs := L ) (x <$ o ;; c1) ≈ repr (locs := L) (x <$ o ;; c2) ⦃ post ⦄. *)
(* Proof. Admitted.  *)

(*CA: probably not sound *)
Theorem rdead_sampler_eliminationL { A : ord_choiceType } { L : {fset Location} } { D }
        (c1 c2 : program L Game_import A)
        (pre : heap * heap -> Prop) (post : (A * heap) -> (A * heap) -> Prop)
        (H : r⊨ ⦃ pre ⦄ c1 ≈ c2  ⦃ post ⦄) :
  r⊨ ⦃ pre ⦄ c1 ≈ (x <$ D ;; c2)  ⦃ post ⦄.
Proof.
  eapply rrewrite_eqDistrR.
  - exact: H.
  - admit.
Admitted.


End Games.

End PackageRHL.
