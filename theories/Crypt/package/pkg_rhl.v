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

  Section Games.

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

    Open Scope fset.

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
    Arguments ropr {_ _ _} _ _.

    Set Equations Transparent.

    Equations? repr' {B : choiceType} {L : {fset Location}}
      (p : raw_program B) (h : valid_program L Game_import p)
    : rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) B :=
      repr' p h with p := {

      | ret x := retrFree x ;

      | opr o x k := False_rect _ _ ;

      | getr l k :=
        bindrFree _ _
          (ropr (inl (inl (gett _))) (λ s, retrFree (get_heap s l)))
          (λ v, repr' (k v) _) ;

      | putr l v k :=
        bindrFree _ _
          (ropr
            (inl (inl (gett heap_choiceType)))
            (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s l v))))
            (λ s, retrFree tt)))
          (λ s', repr' k _) ;

      | sampler op k :=
        bindrFree _ _
          (ropr (inr op) (λ v, retrFree v))
          (λ s, repr' (k s) _)
      }.
    Proof.
      - apply inversion_valid_opr in h. destruct h as [? ?].
        eapply fromEmpty. eauto.
      - apply inversion_valid_getr in h. destruct h as [? ?].
        auto.
      - apply inversion_valid_putr in h. destruct h as [? ?]. auto.
      - eapply inversion_valid_sampler in h. eauto.
    Defined.

    Definition repr {B locs} (p : program locs Game_import B) :=
      let '(mkprog p h) := p in
      repr' p h.

    Ltac fold_repr :=
      change (repr' ?p ?h) with (repr (mkprog p h)).

    Lemma repr'_ext :
      ∀ {B L1 L2} (p1 p2 : raw_program B)
        (hp1 : valid_program L1 Game_import p1)
        (hp2 : valid_program L2 Game_import p2)
        (H : p1 = p2),
        repr' p1 hp1 = repr' p2 hp2.
    Proof.
      intros B L1 L2 p1 p2 hp1 hp2 H.
      subst p2.
      induction p1.
      - cbn. reflexivity.
      - apply inversion_valid_opr in hp1 as h'.
        destruct h' as [? ?].
        eapply fromEmpty. eauto.
      - cbn. f_equal. extensionality s.
        apply H.
      - cbn. f_equal. extensionality s.
        f_equal. extensionality s'.
        apply IHp1.
      - cbn. f_equal. extensionality s.
        apply H.
    Qed.

    Lemma repr_ext :
      ∀ {B L1 L2}
        (p1 : program L1 Game_import B) (p2 : program L2 Game_import B),
        p1.(prog) = p2.(prog) →
        repr p1 = repr p2.
    Proof.
      intros B L1 L2 p1 p2 e.
      unfold repr.
      destruct p1. destruct p2.
      apply repr'_ext.
      auto.
    Qed.

    Lemma repr_bind :
      ∀ {B C} {L} p f
        {hp : @ValidProgram L Game_import B p}
        {hf : ∀ b, @ValidProgram L Game_import C (f b)}
        {h : ValidProgram L Game_import _},
        repr {program bind p f #with h } =
        bindrFree _ _ (repr {program p}) (λ b, repr {program f b}).
    Proof.
      intros B C L p f hp hf h.
      induction p in hp, h, f, hf |- *.
      - cbn. fold_repr.
        f_equal. apply program_ext.
        simpl. reflexivity.
      - apply inversion_valid_opr in hp as h'. destruct h' as [h1 h2].
        eapply fromEmpty. exact h1.
      - cbn. f_equal. extensionality s.
        fold_repr. apply H.
      - cbn. f_equal.
        extensionality s.
        f_equal.
        extensionality s'.
        fold_repr. apply IHp.
      - cbn.
        f_equal.
        extensionality s.
        fold_repr. apply H.
    Qed.

    Lemma repr_bind' :
      ∀ {B C} {L1 L2 L3} p f
        {hp : @ValidProgram L1 Game_import B p}
        {hf : ∀ b, @ValidProgram L2 Game_import C (f b)}
        {h : ValidProgram L3 Game_import _},
        repr {program bind p f #with h } =
        bindrFree _ _ (repr {program p}) (λ b, repr {program f b}).
    Proof.
      intros B C L1 L2 L3 p f hp hf h.
      induction p in hp, h, f, hf |- *.
      - cbn. fold_repr. eapply repr_ext.
        simpl. reflexivity.
      - apply inversion_valid_opr in hp as h'. destruct h' as [h1 h2].
        eapply fromEmpty. exact h1.
      - cbn. f_equal. extensionality s.
        fold_repr. apply H.
      - cbn. f_equal.
        extensionality s.
        f_equal.
        extensionality s'.
        fold_repr. apply IHp.
      - cbn.
        f_equal.
        extensionality s.
        fold_repr. apply H.
    Qed.

    Equations? repr_cmd {L} {A} (c : command A)
      (hc : valid_command L Game_import c) :
      rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) A :=

      repr_cmd (cmd_op o x) hc := False_rect _ _ ;

      repr_cmd (cmd_get ℓ) hc :=
        bindrFree _ _
          (ropr (inl (inl (gett _))) (λ s, retrFree (get_heap s ℓ)))
          (λ v, retrFree v) ;

      repr_cmd (cmd_put ℓ v) hc :=
        bindrFree _ _
          (ropr
            (inl (inl (gett heap_choiceType)))
            (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s ℓ v))))
            (λ s, retrFree tt)))
          (λ s', retrFree s') ;

      repr_cmd (cmd_sample op) hc :=
        bindrFree _ _
          (ropr (inr op) (λ v, retrFree v))
          (λ s, retrFree s).
    Proof.
      inversion hc. eapply fromEmpty. eassumption.
    Qed.

    Lemma repr_cmd_bind :
      ∀ {B C} {L1 L2 L3} p f
        {hp : @ValidCommand L1 Game_import B p}
        {hf : ∀ b, @ValidProgram L2 Game_import C (f b)}
        {h : ValidProgram L3 Game_import _},
        repr {program cmd_bind p f #with h } =
        bindrFree _ _ (repr_cmd p hp) (λ b, repr {program f b}).
    Proof.
      intros B C L1 L2 L3 p f hp hf h.
      destruct p.
      - cbn. falso.
      - cbn. f_equal. extensionality s.
        fold_repr. apply repr_ext. cbn. reflexivity.
      - cbn. f_equal. extensionality s.
        f_equal. extensionality s'.
        fold_repr. apply repr_ext. reflexivity.
      - cbn. f_equal. extensionality s.
        fold_repr. apply repr_ext. reflexivity.
    Qed.

    Notation " r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄ " :=
      (semantic_judgement _ _ (repr c1) (repr c2) (fromPrePost pre post)).

    Theorem rbind_rule :
      ∀ {A1 A2 B1 B2 : ord_choiceType}
        {L1 L2 : {fset Location}}
        {f1}
        {hf1 : ∀ (x : A1), @ValidProgram L1 Game_import B1 (f1 x)}
        {f2}
        {hf2 : ∀ (x : A2), @ValidProgram L2 Game_import B2 (f2 x)}
        m1
        {hm1 : @ValidProgram L1 Game_import A1 m1}
        m2
        {hm2 : @ValidProgram L2 Game_import A2 m2}
        (pre : heap * heap → Prop)
        (middle : (A1 * heap) → (A2 * heap) → Prop)
        (post : (B1 * heap) → (B2 * heap) → Prop)
        (judge_wm : r⊨ ⦃ pre ⦄ (mkprog m1 hm1) ≈ (mkprog m2 hm2) ⦃ middle ⦄)
        (judge_wf : ∀ a1 a2,
          r⊨ ⦃ λ '(s1, s2), middle (a1, s1) (a2, s2) ⦄
            (mkprog (f1 a1) _) ≈ (mkprog (f2 a2) _)
            ⦃ post ⦄
        )
        {h1 : ValidProgram L1 _ _}
        {h2 : ValidProgram L2 _ _},
        r⊨ ⦃ pre ⦄ mkprog (bind m1 f1) h1 ≈ mkprog (bind m2 f2) h2 ⦃ post ⦄.
    Proof.
      intros A1 A2 B1 B2 L1 l2 f1 hf1 f2 hf2 m1 hm1 m2 hm2 pre middle post
        judge_wm judge_wf h1 h2.
      rewrite !repr_bind.
      apply (bind_rule_pp (repr {program m1}) (repr {program m2}) pre middle post judge_wm judge_wf).
    Qed.

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

    Definition Pr_raw_program {L} {B}
      (p : raw_program B)
      (p_is_valid : ValidProgram L Game_import p)
      : heap_choiceType → SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩).
    Proof.
      move => s0.
      pose STDIST := thetaFstd B (repr {program p}) s0.
      specialize (STDIST prob_handler).
      eapply STDIST. exact _.
    Defined.

    Definition Pr_program {L} {B}
               (p : program L Game_import B)
      : heap_choiceType -> SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩) :=
      Pr_raw_program p _.

    Definition Pr_raw_func_program {L} {A} {B}
      (p : A → raw_program B)
      (p_is_valid : ∀ a, valid_program L Game_import (p a))
      : A → heap_choiceType → SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩).
    Proof.
      move => a s0.
      exact (Pr_raw_program (p a) (p_is_valid a) s0).
    Defined.

    Definition Pr_raw_package_op  {E : Interface} {L}
      (p : raw_package)
      (p_is_valid : valid_package L Game_import E p)
      (op : opsig) (Hin : op \in E) (arg : src op)
      : heap_choiceType → SDistr (F_choice_prod_obj ⟨ tgt op , heap_choiceType ⟩).
    Proof.
      move => s0.
      pose (get_raw_package_op p p_is_valid op Hin arg) as f.
      exact (Pr_raw_program f _ s0).
    Defined.

    Definition Pr_op  {E : Interface} (P : loc_package Game_import E)
      (op : opsig) (Hin : op \in E) (arg : src op)
      : heap_choiceType → SDistr (F_choice_prod_obj ⟨ tgt op , heap_choiceType ⟩).
    Proof.
      move => s0.
      destruct P as [L [PP PP_is_valid]].
      exact (Pr_raw_package_op PP PP_is_valid op Hin arg s0).
    Defined.

    Program Definition empty_heap : heap := emptym.
    Next Obligation.
      by rewrite /valid_heap domm0 /fset_filter -fset0E.
    Qed.

    Definition Pr (P : loc_package Game_import A_export) :
      SDistr (bool_choiceType) :=
      SDistr_bind _ _ (λ '(b, _), SDistr_unit _ b)
                      (Pr_op P RUN RUN_in_A_export Datatypes.tt empty_heap).

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
    Open Scope ring_scope.
    Open Scope real_scope.

    Definition GamePair (Game_export : Interface) :=
      bool → Game_Type Game_export.

    Definition Advantage { Game_export : Interface }
      (G : GamePair Game_export)
      (A : Adversary4Game Game_export)
      {H1 : fdisjoint A.(locs) (G false).(locs)}
      {H2 : fdisjoint A.(locs) (G true).(locs)} : R :=
      `| (Pr {locpackage link A (G false) } true) -
         (Pr {locpackage link A (G true) } true) |.

    Definition AdvantageE { Game_export : Interface }
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
               (A : Adversary4Game Game_export)
               {H1 : fdisjoint A.(locs) G0.(locs)}
               {H2 : fdisjoint A.(locs) G1.(locs)} : R
      := `| (Pr {locpackage link A G0 } true) -
            (Pr {locpackage link A G1 } true)|.

    Definition AdvantageE_weak { Game_export : Interface }
               (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
               (A : Adversary4Game_weak Game_export) : R
      := `| (Pr {locpackage link A G0 } true) -
            (Pr {locpackage link A G1 } true)|.

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

    Lemma pr_weak {Game_export : Interface}
      (A : Adversary4Game Game_export) (G : loc_package _ _) :
      Pr {locpackage link (turn_adversary_weak A) G } true =
      Pr {locpackage link A G } true.
    Proof.
    Admitted.

    Definition perf_ind {Game_export : Interface}
      (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
      ∀ A H1 H2, @AdvantageE _ G0 G1 A H1 H2 = 0.

    Definition perf_ind_weak {Game_export : Interface}
      (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
      ∀ A, @AdvantageE_weak _ G0 G1 A = 0.

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

    Notation "ϵ( GP )" :=
      (λ A, AdvantageE (GP false) (GP true) A) (at level 90).

    Notation " G0 ≈[ R ] G1 " :=
      (AdvantageE G0 G1 = R) (at level 50).

    Lemma TriangleInequality {Game_export : Interface}
      {F G H : Game_Type Game_export}
      {ϵ1 ϵ2 ϵ3}
      (ineq1 : F ≈[ ϵ1 ] G)
      (ineq2 : G ≈[ ϵ2 ] H)
      (ineq3 : F ≈[ ϵ3 ] H)
      : ∀ A H1 H2 H3 H4 H5 H6, ϵ3 A H1 H2 <= ϵ1 A H3 H4 + ϵ2 A H5 H6.
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

    Lemma Reduction {Game_export M_export : Interface}
      {M : loc_package Game_export M_export}
      (G : GamePair Game_export) (A : Adversary4Game M_export) (b : bool) :
      `| Pr {locpackage link A (link M (G b)) } true | =
      `| Pr {locpackage link (link A M) (G b) } true |.
    Proof.
      (* @Assia:
        What I wanted to do was to directly use rewrite link_assoc here.
        But I cannot do it because Pr expects a package and not a
        raw_package. These are defined in pkg_core_definition.
        Record package L I E := mkpackage {
          pack : raw_package ;
          pack_valid : ValidPackage L I E pack
        }.

        Notation "{ 'package' p }" :=
          (mkpackage p _)
          (format "{ package  p  }") : package_scope.

        {locpackage} is just a layer above, but it doesn't add complexity.
      *)
      package_before_rewrite.
      rewrite link_assoc.
      package_after_rewrite.
      f_equal. f_equal. f_equal. apply loc_package_ext.
      - cbn. rewrite fsetUA. reflexivity.
      - cbn. intro. reflexivity.
    Qed.

    Lemma auxReduction :
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
    Qed.

    Lemma ReductionLem :
      ∀ {Game_export M_export : Interface}
        {M : loc_package Game_export M_export}
        (G : GamePair Game_export)
        (Hdisjoint0 : fdisjoint M.(locs) (G false).(locs))
        (Hdisjoint1 : fdisjoint M.(locs) (G true).(locs)),
        {locpackage link M (G false)}
        ≈[ λ A H1 H2, @AdvantageE Game_export (G false) (G true) {locpackage link A M} (auxReduction Hdisjoint0 H1) (auxReduction Hdisjoint1 H2) ]
        {locpackage link M (G true)}.
    Proof.
      intros Game_export M_export M G Hdisjoint0 Hdisjoint1.
      unfold AdvantageE. extensionality A.
      extensionality H1. extensionality H2.
      simpl.
      (* TODO FIX *)
      (* This means that the Reduction lemma should be stated better *)
      (* rewrite Reduction. rewrite Reduction.
      reflexivity.
    Qed. *)
    Admitted.

    Lemma rhl_repr_change_all {B1 B2 : choiceType} {L1 L2 L1' L2'}
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

    Lemma get_case {L LA} (I : heap_choiceType * heap_choiceType → Prop)
      (HINV : INV LA I) {l : Location} (Hin : l \in LA)
      (hp : [eta valid_program L Game_import] (getr l (λ x, ret x))) :
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (mkprog (getr l (λ x, ret x)) hp)
          ≈ repr (locs := L) (mkprog (getr l (λ x, ret x)) hp)
          ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
    Proof.
      cbn. intros [s1 s2].
      rewrite /SpecificationMonads.MonoCont_bind /=.
      rewrite /SpecificationMonads.MonoCont_order /SPropMonadicStructures.SProp_op_order
              /Morphisms.pointwise_relation /Basics.flip /SPropMonadicStructures.SProp_order /=.
      intuition.
      assert (get_heap s1 l = get_heap s2 l) as Hv.
      { unfold INV in HINV.
        apply inversion_valid_getr in hp as [hp _].
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

    Lemma put_case {L LA} (I : heap_choiceType * heap_choiceType → Prop)
      (HINV : INV LA I) {l : Location} {v : Value l.π1} (Hin : l \in LA)
      (hp : [eta valid_program L Game_import] (putr l v (ret tt))):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (mkprog (putr l v (ret tt)) hp)
          ≈ repr (locs := L) (mkprog (putr l v (ret tt)) hp)
          ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
    Proof.
      cbn. intros [s1 s2].
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
      (hp : [eta valid_program L Game_import] (sampler op [eta ret (A:=Arit op)])):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (mkprog (sampler op [eta ret (A:=Arit op)]) hp)
          ≈ repr (locs := L) (mkprog (sampler op [eta ret (A:=Arit op)]) hp)
          ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
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

    Definition eq_up_to_inv_alt {L₁ L₂} {E}
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
        ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄ repr (mkprog (f arg) (hpf arg)) ≈ repr (mkprog (g arg) (hpg arg)) ⦃ λ '(b1, s0) '(b2, s3), b1 = b2 ∧ I (s0, s3) ⦄.

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
      - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
      - apply program_ext. cbn. erewrite get_op_default_spec. all: eauto.
    Qed.

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

    Lemma Pr_eq_empty {X Y : ord_choiceType} {A : pred (X * heap_choiceType)} {B : pred (Y * heap_choiceType)}
            Ψ ϕ
            (c1 : FrStP heap_choiceType X) (c2 : FrStP heap_choiceType Y)
            (H : ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄)
            (HPsi : Ψ (empty_heap, empty_heap) )
            (Hpost : forall x y,  ϕ x y -> (A x) <-> (B y)) :
      \P_[ θ_dens (θ0 c1 empty_heap) ] A =
      \P_[ θ_dens (θ0 c2 empty_heap) ] B.
    Proof.
      apply (Pr_eq Ψ ϕ); assumption.
    Qed.

    Lemma some_lemma_for_prove_relational {export : Interface} {B} {L1 L2 LA}
      (P1 : package L1 Game_import export)
      (P2 : package L2 Game_import export)
      (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) (Hempty : I (empty_heap, empty_heap))
      (H : eq_up_to_inv I P1 P2)
      (A : program LA export B)
      (s1 : heap_choiceType) (s2 : heap_choiceType) (Hs1s2 : I (s1, s2)) :
      ⊨ ⦃ λ '(s1, s2), I (s1, s2)  ⦄
        repr (mkprog (program_link A P1) [hints (fsubsetUl LA (L1 :|: L2)) ; (fsubset_trans (fsubsetUl L1 L2) (fsubsetUr LA (L1 :|: L2))) ])
        ≈
        repr (mkprog (program_link A P2) [hints (fsubsetUl LA (L1 :|: L2)) ; (fsubset_trans (fsubsetUr L1 L2) (fsubsetUr LA (L1 :|: L2))) ])
        ⦃ λ '(b1, s1) '(b2, s2), b1 = b2 ∧ I (s1, s2) ⦄.
    Proof.
      destruct P1 as [P1a P1b] eqn:HP1.
      destruct P2 as [P2a P2b] eqn:HP2.
      destruct A as [A hA]. simpl.
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
      - apply inversion_valid_opr in hA as hA'. destruct hA' as [hA1 hA2].
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
        program_before_rewrite.
        rewrite H1.
        program_after_rewrite.
        pose foo2 := (P2b (id, (S, T)) hA1).
        destruct foo2 as [f2 [K12 K22]].
        cbn - [semantic_judgement lookup_op bind].
        assert (lookup_op P2a (id, (S, T)) = Some f2) as H2.
        { cbn. rewrite K12.
          destruct (chUniverse_eqP S S), (chUniverse_eqP T T). all: try contradiction.
          noconf e. noconf e0. reflexivity.
        }
        fold_repr.
        program_before_rewrite.
        rewrite H2.
        program_after_rewrite.
        (* TODO: Is there a way to avoid these side conditions? *)
        unshelve erewrite repr_bind.
        1:{
          eapply valid_injectLocations. 2: eauto.
          exact (fsubset_trans (fsubsetUl L1 L2) (fsubsetUr LA (L1 :|: L2))).
        }
        1:{
          intro. eapply valid_program_link.
          - eapply valid_injectLocations. 2: eauto.
            eapply fsubsetUl.
          - eapply valid_package_inject_locations. 2: eauto.
            exact (fsubset_trans (fsubsetUl L1 L2) (fsubsetUr LA (L1 :|: L2))).
        }
        unshelve erewrite repr_bind.
        1:{
          eapply valid_injectLocations. 2: eauto.
          exact (fsubset_trans (fsubsetUr L1 L2) (fsubsetUr LA (L1 :|: L2))).
        }
        1:{
          intro. eapply valid_program_link.
          - eapply valid_injectLocations. 2: eauto.
            eapply fsubsetUl.
          - eapply valid_package_inject_locations. 2: eauto.
            exact (fsubset_trans (fsubsetUr L1 L2) (fsubsetUr LA (L1 :|: L2))).
        }
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
          2:{
            intros st0 st3.
            cbn. intros [Heqst0 Heqst3].
            rewrite Heqst0 Heqst3. assumption.
          }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (mkprog p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity.
          exact H0.
      - cbn - [semantic_judgement bindrFree].
        apply inversion_valid_getr in hA as h'.
        destruct h' as [hA1 hA2].
        unfold repr'_obligation_4.
        cbn - [semantic_judgement bindrFree].
        match goal with
        | |- ⊨ ⦃ ?pre_ ⦄ bindrFree _ _ ?m_ ?f1_ ≈ bindrFree _ _ _ ?f2_ ⦃ ?post_ ⦄ =>
          pose (m := m_); pose (f1 := f1_); pose (f2 := f2_); pose (pre := pre_); pose (post := post_)
        end.
        eapply (bind_rule_pp (f1 := f1) (f2 := f2) m m pre _ post).
        + unshelve eapply (@get_case _ LA).
          3: assumption.
          3: exact hA1.
          * exact LA.
          * eapply valid_program_from_class. exact _.
        + intros a1 a2.
          simpl.
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          specialize (H0 a1 (hA2 a1)).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (mkprog p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact H0.
      - cbn - [semantic_judgement bindrFree].
        apply inversion_valid_putr in hA as h'.
        destruct h' as [hA1 hA2].
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
          * eapply valid_program_from_class. exact _.
        + intros a1 a2.
          simpl.
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          specialize (IHA hA2).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2: { intros st0 st3.
               cbn. intros [Heqst0 Heqst3].
               rewrite Heqst0 Heqst3. assumption. }
          cbn -[semantic_judgement] in IHA.
          change (repr' ?p ?h) with (repr (mkprog p h)) in IHA.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact IHA.
      - cbn - [bindrFree semantic_judgement].
        eapply bind_rule_pp.
        + eapply (@sampler_case LA LA).
          ++ assumption.
             Unshelve.
             eapply valid_program_from_class. exact _.
        + intros a1 a2.
          simpl.
          apply pre_hypothesis_rule.
          intros st1 st2 [Heqa Ist1st2].
          induction Heqa.
          unshelve eapply inversion_valid_sampler in hA as hAa1.
          1: exact a1.
          specialize (H0 a1 hAa1).
          apply (pre_weaken_rule  (λ '(s1, s2), I (s1, s2))).
          2:{
            intros st0 st3.
            cbn. intros [Heqst0 Heqst3].
            rewrite Heqst0 Heqst3. assumption.
          }
          cbn -[semantic_judgement] in H0.
          change (repr' ?p ?h) with (repr (mkprog p h)) in H0.
          eapply rhl_repr_change_all.
          1: reflexivity. 1: reflexivity. exact H0.
    Qed.

    (* Rem.: How do we connect the package theory with the RHL?
           Something along the following lines should hold? *)
    Lemma prove_relational {L1 L2} {export}
      (P1 : package L1 Game_import export)
      (P2 : package L2 Game_import export)
      (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV' : INV' L1 L2 I)
      (Hempty : I (empty_heap, empty_heap))
      (H : eq_up_to_inv I P1 P2)
      : (mkloc_package L1 P1) ≈[ λ A H1 H2, 0 ] (mkloc_package L2 P2).
    Proof.
      extensionality A.
      unfold Adversary4Game in A.
      unfold AdvantageE, Pr.
      extensionality Hdisjoint1. extensionality Hdisjoint2.
      pose r' := get_package_op A RUN RUN_in_A_export.
      pose r := r' tt.
      (* Rem.: from linking we should get the fact that A.π1 is disjoint from L1 and L2,
             and then from that conclude that we are invariant on A.π1 *)
      (* unshelve epose (fdisjoint_from_link A.π2 P1 _) as Hdisjoint1. *)
      (* { eexists. reflexivity. } *)
      (* unshelve epose (fdisjoint_from_link A.π2 P2 _) as Hdisjoint2. *)
      (* { eexists. reflexivity. } *)
      assert (INV A.(locs) I) as HINV.
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
    Qed.

    (* Alternative version for packages *)
    Corollary prove_relational' :
      ∀ {export}
        (P1 : loc_package Game_import export)
        (P2 : loc_package Game_import export)
        (I : heap_choiceType * heap_choiceType -> Prop)
        (HINV' : INV' P1.(locs) P2.(locs) I)
        (Hempty : I (empty_heap, empty_heap))
        (H : eq_up_to_inv I P1 P2),
        P1 ≈[ λ A H1 H2, 0 ] P2.
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
    ∀ (pre pre' : heap * heap -> Prop) post,
      (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄) →
      (∀ st1 st2, pre' (st1, st2) → pre (st1, st2)) →
      (r⊨ ⦃ pre' ⦄ p1 ≈ p2 ⦃ post ⦄).
  Proof.
    by apply: pre_weaken_rule.
  Qed.

  Theorem rpre_hypothesis_rule
    {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
    {p1 : program L1 Game_import A1}
    {p2 : program L2 Game_import A2} :
    ∀ (pre : heap * heap → Prop) post,
      (∀ st1 st2, pre (st1, st2) →
        r⊨ ⦃ λ st, st.1 = st1 ∧ st.2 = st2 ⦄ p1 ≈ p2 ⦃ post ⦄) →
      (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄).
  Proof.
    by apply: pre_hypothesis_rule.
  Qed.

Theorem rpre_strong_hypothesis_rule
  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
  {p1 : program L1 Game_import A1}
  {p2 : program L1 Game_import A2} :
  ∀ (pre : heap * heap → Prop) post,
    (∀ st1 st2, pre (st1, st2)) → (r⊨ ⦃ (λ st, True ) ⦄ p1 ≈ p2 ⦃ post ⦄) →
    (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post ⦄).
Proof.
  by apply: pre_strong_hypothesis_rule.
Qed.

Theorem rpost_weaken_rule
  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
  {p1 : program L1 Game_import A1}
  {p2 : program L2 Game_import A2} :
  ∀ (pre : heap * heap → Prop)
    (post1 post2 : A1 * heap → A2 * heap → Prop),
    (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post1 ⦄) →
    (∀ as1 as2, post1 as1 as2 → post2 as1 as2) →
    (r⊨ ⦃ pre ⦄ p1 ≈ p2 ⦃ post2 ⦄).
Proof.
  by apply: post_weaken_rule.
Qed.

(* Skipped for now *)
(* Theorem comp_rule ... *)

Lemma repr_if {A} {L} {b : bool} (c1 c2 : program L Game_import A) :
  repr (if b then c1 else c2) = if b then (repr c1) else (repr c2).
Proof.
  by destruct b.
Qed.

Theorem rif_rule {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}}
  (c1 c2 : program L1 Game_import A1)
  (c1' c2' : program L2 Game_import A2)
  {b1 b2 : bool}
  {pre : heap * heap → Prop} {post : A1 * heap → A2 * heap → Prop}
  {pre_b1b2 : ∀ st, pre st → b1 = b2}
  { H1 : r⊨ ⦃ λ st, pre st ∧ b1 = true ⦄ c1 ≈ c1' ⦃ post ⦄ }
  { H2 : r⊨ ⦃ λ st, pre st ∧ b1 = false ⦄ c2 ≈ c2' ⦃ post ⦄ } :
  r⊨ ⦃ pre ⦄
      (if b1 then c1 else c2) ≈
      (if b2 then c1' else c2')
     ⦃ post ⦄.
Proof.
  rewrite !repr_if.
  by apply: if_rule.
Qed.

(* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)


(* skipped for now:
Theorem bounded_do_while_rule *)

(*TODO: asymmetric variants of bounded_do_while -- Rem.: low priority as not useful for our examples *)

Lemma rcoupling_eq {A : ord_choiceType} {L : {fset Location}}
  (K1 K2 : program L Game_import A)
  (ψ : heap * heap → Prop)
  (H : r⊨ ⦃ ψ ⦄ K1 ≈ K2 ⦃ eq ⦄) :
  ∀ s1 s2,
    ψ (s1, s2) →
    θ_dens (θ0 (repr K1) s1) = θ_dens (θ0 (repr K2) s2).
Proof.
  by apply: coupling_eq (repr K1) (repr K2) ψ H.
Qed.

Lemma rrewrite_eqDistrL
  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location}} {P} {Q}
  (c1 c1' : program L1 Game_import A1) (c2 : program L2 Game_import A2)
  (H : r⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
  (θeq : ∀ s, θ_dens (θ0 (repr c1) s) = θ_dens (θ0 (repr c1') s )) :
  r⊨ ⦃ P ⦄ c1'  ≈ c2 ⦃ Q ⦄.
Proof.
  by apply: rewrite_eqDistrL (repr c1) (repr c1') (repr c2) H θeq.
Qed.

Lemma rrewrite_eqDistrR
  {A1 A2 : ord_choiceType} {L1 L2 : {fset Location} } {P Q}
  (c1  : program L1 Game_import A1) (c2 c2': program L2 Game_import A2)
  (H : r⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
  (θeq : ∀ s, θ_dens (θ0 (repr c2) s) = θ_dens (θ0 (repr c2') s)) :
  r⊨ ⦃ P ⦄ c1  ≈ c2' ⦃ Q ⦄.
Proof.
  by apply: rewrite_eqDistrR (repr c1) (repr c2) (repr c2') H θeq.
Qed.

Lemma rreflexivity_rule
  {A : ord_choiceType} {L : {fset Location}}
  (c : program L Game_import A):
  r⊨ ⦃ λ '(s1, s2), s1 = s2 ⦄ c ≈ c ⦃ eq ⦄.
Proof.
  by apply: reflexivity_rule (repr c).
Qed.

Theorem rswap_rule {A1 A2 : ord_choiceType} {L : {fset Location}}
  {I : heap * heap → Prop}
  {post : A1 * heap → A2 * heap → Prop}
  (c1 : raw_program A1) (c2 : raw_program A2)
  (hc1 : valid_program L Game_import c1) (hc2 : valid_program L Game_import c2)
  (Hinv1 : r⊨ ⦃ I ⦄ mkprog c1 hc1 ≈ mkprog c2 hc2 ⦃ λ '(a1, s1) '(a2, s2), I (s1, s2) ∧ post (a1, s1) (a2, s2) ⦄)
  (Hinv2 : r⊨ ⦃ I ⦄ mkprog c2 hc2 ≈ mkprog c1 hc1 ⦃ λ '(a2, s2) '(a1, s1), I (s1, s2) ∧ post (a1, s1) (a2, s2) ⦄)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ I ⦄
    mkprog (c1 ;; c2) h1 ≈ mkprog (c2 ;; c1) h2
    ⦃ λ '(a2,s2) '(a1,s1), I (s1, s2) ∧ post (a1,s1) (a2, s2) ⦄.
Proof.
  erewrite !repr_bind.
  by apply: swap_rule (repr {program c1}) (repr {program c2}) Hinv1 Hinv2.
Qed.

(** TW: I guess this to allow going under binders.
  We might be better off defining some morphisms on semantic judgments
  to use setoid_rewrite.
*)
Theorem rswap_ruleL
  {A1 A2 B : ord_choiceType} {L : {fset Location}}
  {pre I : heap * heap → Prop}
  {post :  A2 * heap → A1 * heap → Prop}
  (l : program L Game_import B)
  (c1 : program L Game_import A1)
  (c2 : program L Game_import A2)
  (HL : r⊨ ⦃ pre ⦄ l ≈ l ⦃ λ '(b1, s1) '(b2, s2), I (s1, s2) ⦄)
  (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ λ '(a1, s1) '(a2, s2), I (s1, s2) ∧ post (a2, s2) (a1, s1) ⦄)
  (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ λ '(a2, s2) '(a1, s1), I (s1, s2) ∧ post (a2, s2) (a1, s1) ⦄)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ pre ⦄ mkprog (l ;; c1 ;; c2) h1 ≈ mkprog (l ;; c2 ;; c1) h2 ⦃ post ⦄ .
Proof.
  erewrite !repr_bind.
  by apply: swap_ruleL (repr l) (repr c1) (repr c2) HL Hinv1 Hinv2.
Qed.

Theorem rswap_ruleR
  {A1 A2 B : ord_choiceType} {L : {fset Location}}
  {post : B * heap → B * heap → Prop}
  {post_refl : ∀ bs bs', bs = bs' → post bs bs'}
  (c1 : program L Game_import A1)
  (c2 : program L Game_import A2)
  (r : A1 → A2 → program L Game_import B)
  (HR : ∀ a1 a2, r⊨ ⦃ λ '(s2, s1), s1 = s2 ⦄ (r a1 a2) ≈ (r a1 a2) ⦃ post ⦄)
  (Hcomm : r⊨ ⦃ λ '(h1, h2), h1 = h2 ⦄
              mkprog (a1 ← c1 ;; a2 ← c2 ;; ret (a1, a2)) _ ≈
              mkprog (a2 ← c2 ;; a1 ← c1 ;; ret (a1 , a2)) _
            ⦃ eq ⦄ )
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ λ '(h1,h2), h1 = h2 ⦄
      mkprog (a1 ← c1 ;; a2 ← c2 ;; r a1 a2) h1 ≈
      mkprog (a2 ← c2 ;; a1 ← c1 ;; r a1 a2) h2
   ⦃ post ⦄.
Proof.
  repeat setoid_rewrite repr_bind.  simpl.
  eapply (swap_ruleR (fun a1 a2 => repr (r a1 a2)) (repr c1) (repr c2) HR post_refl).
  move => s.
  unshelve eapply coupling_eq.
  - exact: (λ '(h1, h2), h1 = h2).
  - repeat setoid_rewrite repr_bind in Hcomm. 1: apply: Hcomm.
    all: intro. all: exact _.
  - by [].
  Unshelve.
  all: intro. all: exact _.
Qed.

Local Open Scope package_scope.

Lemma rsym_pre  { A1 A2 : ord_choiceType } { L : {fset Location} } { pre : heap * heap -> Prop } { post }
                     { c1 : program L Game_import A1 } { c2 : program L Game_import A2 }
                     (pre_sym : forall h1 h2, pre (h1, h2) -> pre (h2, h1))
                     (H : r⊨ ⦃ fun '(h1, h2) => pre (h2, h1) ⦄ c1 ≈ c2 ⦃ post ⦄) :
                     r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄.
Proof.
  unshelve eapply rpre_weaken_rule.
  { exact: (fun '(h1, h2) => pre (h2, h1)). }
  - assumption. - assumption.
Qed.


Lemma rsymmetry  { A1 A2 : ord_choiceType } { L : {fset Location} } { pre : heap * heap -> Prop } { post }
                 { c1 : program L Game_import A1 } { c2 : program L Game_import A2 }
                 (H : r⊨ ⦃ fun '(h2, h1) => pre (h1, h2) ⦄ c2 ≈ c1 ⦃ fun '(a2,h2) '(a1,h1) => post (a1,h1) (a2, h2) ⦄ ):
   r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄.
Proof. by apply: symmetry_rule. Qed.

Lemma rsamplerC
  {A : ord_choiceType} {L : {fset Location}} (o : Op)
  (c : program L Game_import A)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ λ '(h1,h2), h1 = h2 ⦄
       mkprog (a ← c ;; r ← (r ← sample o ;; ret r) ;;  (ret (a, r))) h1 ≈
       mkprog (r ← (r ← sample o ;; ret r) ;; a ← c ;;  (ret (a, r))) h2
   ⦃ eq ⦄.
Proof.
  apply: rrewrite_eqDistrL.
  - apply: rreflexivity_rule.
  - move => s. f_equal.
    (*Rem.: we should be able to rewrite smMonequ1/2 ? and have the equality? *)

Admitted.

Lemma rsamplerC' {A : ord_choiceType} {L : {fset Location}} (o : Op)
  (c : program L Game_import A)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ λ '(h1,h2), h1 = h2 ⦄
      mkprog (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (r, a)) h1 ≈
      mkprog (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (r, a)) h2
   ⦃ eq ⦄.
Proof.
Admitted.


(* TODO: generalize the corresponding rule in RulesStateProb.v  *)
(* CA: not hight priority as never used yet! *)
Theorem rswap_rule_ctx
  {A : ord_choiceType} {L : {fset Location}}
  {I pre} {post Q : A * heap → A * heap → Prop}
  (l r c1 c2 : program L Game_import A)
  (HL : r⊨ ⦃ pre ⦄ l ≈ l ⦃ λ '(a1, s1) '(a2, s2), I (s1, s2) ⦄)
  (HR : ∀ a1 a2, r⊨ ⦃ λ '(s1, s2), Q (a1,s1) (a2,s2) ⦄ r ≈ r ⦃ post ⦄)
  (Hinv1 : r⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ λ '(a1, s1) '(a2, s2), I (s1, s2) ∧ Q (a1, s1) (a2, s2) ⦄)
  (Hinv2 : r⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ λ '(a2, s2) '(a1, s1), I (s1, s2) ∧ Q (a1, s1) (a2, s2) ⦄)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ pre ⦄
    mkprog (l ;; c1 ;; c2 ;; r) h1 ≈
    mkprog (l ;; c2 ;; c1 ;; r) h2
    ⦃ post ⦄.
Proof.
  erewrite !repr_bind.
  (* by apply (swap_rule_ctx (repr l) (repr r) (repr c1) (repr c2) HL HR Hinv1 Hinv2). Qed. *)
Admitted.

Theorem rsame_head
  {A B : ord_choiceType}
  {L : {fset Location}}
  {f1 : A → program L Game_import B}
  {f2 : A → program L Game_import B}
  (m : program L Game_import A)
  (post : (B * heap) → (B * heap) → Prop)
  (judge_wf : ∀ a, r⊨ ⦃ λ '(h1,h2), h1 = h2 ⦄ f1 a ≈ f2 a ⦃ post ⦄)
  {h1 : ValidProgram L _ _} {h2 : ValidProgram L _ _} :
  r⊨ ⦃ λ '(h1,h2), h1 = h2 ⦄
    mkprog (bind m f1) h1 ≈ mkprog (bind m f2) h2
    ⦃ post ⦄.
Proof.
  eapply (rbind_rule m m).
  - exact: rreflexivity_rule.
  - move => a1 a2. unshelve apply: rpre_weaken_rule.
    + exact: (λ '(h1,h2), a1 = a2 ∧ h1 = h2).
    + specialize (judge_wf a1).
      apply: rpre_hypothesis_rule. rewrite /= => st1 st2 [Heq1 Heq2].
      subst. apply: rpre_weaken_rule.
      * exact: judge_wf.
      * rewrite /= => h1' h2' [Heq1 Heq2]. by subst.
    + rewrite /= => h1' h2' [Heq1 Heq2]. by subst.
Qed.

(* TODO Decompose prgram? *)
(* Lemma rsym_pre
  {A1 A2 : ord_choiceType} {L : {fset Location}}
  {pre : heap * heap → Prop} {post}
  {c1 : program L Game_import A1}
  {c2 : program L Game_import A2}
  (pre_sym : ∀ h1 h2, pre (h1, h2) → pre (h2, h1))
  (H : r⊨ ⦃ λ '(h1, h2), pre (h2, h1) ⦄ c1 ≈ c2 ⦃ post ⦄) :
  r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄.
Proof.
  unshelve eapply rpre_weaken_rule.
  - exact: (λ '(h1, h2), pre (h2, h1)).
  - assumption.
  - assumption.
Qed. *)

(* TODO Decompose prgram? *)
(* Lemma rsymmetry
  {A1 A2 : ord_choiceType} {L : {fset Location}}
  {pre : heap * heap → Prop} {post}
  {c1 : program L Game_import A1}
  {c2 : program L Game_import A2}
  (H : r⊨ ⦃ λ '(h1, h2), pre (h2, h1) ⦄ c2 ≈ c1 ⦃ λ '(a2,h2) '(a1,h1), post (a1,h1) (a2, h2) ⦄) :
  r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄.
Proof.
Admitted. *)

(* CA: not more useful than sampler_case *)
(* Lemma rsample_rule { B1 B2 : ord_choiceType} { L : {fset Location}}  { o } *)
(*       c1 c2  *)
(*       pre (post : B1 * heap -> B2 * heap -> Prop) *)
(*       (H : r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄) : *)
(*          ⊨ ⦃ pre ⦄ repr (locs := L ) (x <$ o ;; c1) ≈ repr (locs := L) (x <$ o ;; c2) ⦃ post ⦄. *)
(* Proof. Admitted.  *)

Theorem rdead_sampler_elimL
  {A : ord_choiceType} {L : {fset Location}} {D}
  (c1 c2 : program L Game_import A)
  (pre : heap * heap → Prop)
  (post : (A * heap) → (A * heap) → Prop)
  (H : r⊨ ⦃ pre ⦄ c1 ≈ c2  ⦃ post ⦄)
  {h1 : ValidProgram L _ _} :
  r⊨ ⦃ pre ⦄ mkprog ((x ← sample D ;; ret x) ;; c1) h1 ≈ c2  ⦃ post ⦄.
Proof.
  eapply rrewrite_eqDistrL.
  - exact: H.
  - admit.
Admitted.

Theorem rdead_sampler_elimR
  {A : ord_choiceType} {L : {fset Location}} {D}
  (c1 c2 : program L Game_import A)
  (pre : heap * heap → Prop) (post : (A * heap) → (A * heap) → Prop)
  (H : r⊨ ⦃ pre ⦄ c1 ≈ c2  ⦃ post ⦄)
  {h2 : ValidProgram L _ _} :
  r⊨ ⦃ pre ⦄ c1 ≈ mkprog ((x ← sample D ;; ret x) ;; c2) h2 ⦃ post ⦄.
Proof.
  eapply rrewrite_eqDistrR.
  - exact: H.
  - admit.
Admitted.

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

Definition precond := heap * heap → Prop.
Definition postcond A B := (A * heap) → (B * heap) → Prop.

Reserved Notation "⊢ ⦃ pre ⦄ c1 ~ c2 ⦃ post ⦄".

(* TODO Complete *)

Inductive raw_judgment :
  ∀ {A B : choiceType},
    precond → postcond A B → raw_program A → raw_program B → Prop :=

| r_refl :
    ∀ A (c : raw_program A),
      ⊢ ⦃ λ '(s1, s2), s1 = s2 ⦄ c ~ c ⦃ eq ⦄

(* r_seq *) (* Which one ist it? *)

(* Legacy rule *)
| r_swap :
    ∀ (A₀ A₁ : choiceType) (I : precond) (post : postcond A₀ A₁) (c₀ : raw_program A₀) (c₁ : raw_program A₁),
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

(* | r_swap_cmd_seq *)

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

where "⊢ ⦃ pre ⦄ c1 ~ c2 ⦃ post ⦄" := (raw_judgment pre post c1 c2).

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
Qed.

(* TODO Seems like repr only need no import, but doesn't care about
locations. If so we could make a much simpler statement?
Can probably define rep = repr' using noimport predicate
Then the above would be simpler! No need for stupid Ls everywhere.
*)

End Games.

End PackageRHL.
