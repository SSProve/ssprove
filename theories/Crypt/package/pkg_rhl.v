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
Require Equations.Prop.DepElim.
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
  Include (PackageNotation π).
  Include (DerivedRules π).

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

    Open Scope fset.
    (* Let iops_StP := @ops_StP probE rel_choiceTypes chEmb. *)
    (* Let iar_StP := @ar_StP probE rel_choiceTypes chEmb. *)

    Definition heap := {fmap Location -> Value}.
    Definition heap_choiceType := [choiceType of heap].

    Definition Game_op_import_S : Type := {_ : ident & void}.
    Definition Game_import_P : Game_op_import_S → choiceType :=
      fun v => match v with existT a b => match b with end end.

    Definition get_heap (map : heap) (l : Location) : Value.
    Proof.
      destruct (getm map l).
      + exact s.
      + exact 0.
    Defined.

    Definition set_heap (map : heap) (l : Location)  (v : Value) : heap := setm map l v.

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
      repr (bind _ _ p f) =  bindrFree _ _ (repr p) (fun b => repr (f b)).
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

    Notation "r⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
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
      r⊨ ⦃ pre ⦄ (bind _ _ m1 f1 ) ≈ (bind _ _ m2 f2) ⦃ post ⦄.
    Proof.
      rewrite !repr_bind.
      apply (bind_rule_pp (repr m1) (repr m2) pre middle post judge_wm judge_wf).
    Qed.

    Let getLocations {I E} (P : package I E) : {fset Location} :=
      let '(locs; PP) := P in locs.

    Definition get_raw_package_op {L} {I E : Interface} (p : raw_package)
               (hp : valid_package L I E p)
               (o : opsig) (ho : o \in E) (arg : src o) : program L I (tgt o).
    Proof.
      (* ER: updated using the same order as TW below *)
      destruct (lookup_op p o) as [f|] eqn:e.
      2:{
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
      }
      exists (f arg).
      destruct o as [n [S T]].
      cbn - [lookup_op] in *.
      eapply lookup_op_valid in hp. 2: eauto.
      cbn - [lookup_op] in hp. destruct hp as [g [eg hg]].
      rewrite e in eg. noconf eg.
      eapply hg.
    Defined.

    Lemma get_raw_package_op_link {L} {I E} {o : opsig}
          (hin : o \in E) (arg : src o) (p1 p2 : raw_package)
          (hp1 : valid_package L I E p1)
          (hpl : valid_package L I E (raw_link p1 p2))
          : (get_raw_package_op (raw_link p1 p2) hpl o hin arg) ∙1 =
            raw_program_link ((get_raw_package_op p1 hp1 o hin arg) ∙1) p2.
    Proof.
      admit.
    Admitted.

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

    Definition Pr (P : package Game_import A_export) : SDistr (bool_choiceType) :=
      SDistr_bind _ _ (fun '(b, _) => SDistr_unit _ b)
                      (Pr_op P RUN RUN_in_A_export Datatypes.tt emptym).

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
               (A : Adversary4Game Game_export) : R :=
      `| (Pr (link A (G false)) true) - (Pr (link A (G true)) true)|.

    Definition AdvantageE { Game_export : Interface }
      : Game_Type Game_export -> Game_Type Game_export -> Adversary4Game Game_export -> R
      := fun G0 G1 A => `| (Pr (link A G0) true) - (Pr (link A G1) true)|.

    Notation "ϵ( GP )" := (fun A => AdvantageE (GP false) (GP true) A) (at level 90).
    Notation " G0 ≈[ R ] G1 " := (AdvantageE G0 G1 = R) (at level 50).

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

    Lemma get_case {L LA} (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) {l : Location} (Hin : l \in LA)
      (hp : [eta valid_program L Game_import] (_getr l [eta _ret (A:=Value)])):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (exist _ (_getr l [eta _ret (A:=Value)]) hp)
          ≈ repr (locs := L) (exist _ (_getr l [eta _ret (A:=Value)]) hp)
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
      simpl (repr'_obligation_1 Value (get_heap s1 l), s1).
      exists (SDistr_unit _ ((repr'_obligation_1 Value (get_heap s1 l), s1),
                        (repr'_obligation_1 Value (get_heap s2 l), s2))).
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
      (HINV : INV LA I) {l : Location} {v : Value} (Hin : l \in LA)
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

    Lemma sampler_case {L LA} (I : heap_choiceType * heap_choiceType -> Prop)
      (HINV : INV LA I) {op}
      (hp : [eta valid_program L Game_import] (_sampler op [eta _ret (A:=Arit op)])):
      ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄
            repr (locs := L) (exist _ (_sampler op [eta _ret (A:=Arit op)]) hp)
          ≈ repr (locs := L) (exist _ (_sampler op [eta _ret (A:=Arit op)]) hp)
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
      cbn - [semantic_judgement].
    Admitted.

    Definition eq_up_to_inv {L1 L2} {E}
               (I : heap_choiceType * heap_choiceType → Prop)
               (P1 : opackage L1 Game_import E) (P2 : opackage L2 Game_import E) :=
      forall  (id : ident) (S T : chUniverse)
         (hin : (id, (S, T)) \in E)
         (f : S → raw_program T) (g : S → raw_program T)
         (Hf : P1.π1 id = Some (S; T; f)) (hpf : forall x, valid_program L1 Game_import (f x))
         (Hg : P2.π1 id = Some (S; T; g)) (hpg : forall x, valid_program L2 Game_import (g x))
         (arg : S),
         ⊨ ⦃ λ '(s0, s3), I (s0, s3) ⦄ repr (exist _ (f arg) (hpf arg)) ≈ repr (exist _ (g arg) (hpg arg)) ⦃ λ '(b1, s0) '(b2, s3), b1 = b2 /\ I (s0, s3) ⦄.

    Lemma valid_bind_1 :
      ∀ {A B L I} {v : raw_program A} {k : A → raw_program B},
        valid_program L I (bind_ v k) →
        valid_program L I v.
    Proof.
      intros A B L I v k h.
      induction v in k, h |- *.
      - cbn. auto.
      - cbn. cbn in h. intuition eauto.
      - cbn. cbn in h. intuition eauto.
      - cbn. cbn in h. intuition eauto.
      - cbn. cbn in h. intuition eauto.
    Qed.

    Lemma fold_bind :
      ∀ A B L I
        (v : raw_program A) (k : A → raw_program B)
        (h : valid_program L I (bind_ v k))
        (h' : ∀ x, valid_program L I (k x)),
        exist _ (bind_ v k) h =
        bind L I (exist _ v (valid_bind_1 h)) (λ x, exist _ (k x) (h' x)).
    Proof.
      intros A B L I v k h h'.
      apply program_ext. cbn. reflexivity.
    Qed.

    Lemma fold_program_link :
      ∀ A L Im Ir (v : raw_program A) (p : raw_package)
        (hv : valid_program L Im v)
        (hp : valid_package L Ir Im p)
        (h : valid_program L Ir (raw_program_link v p)),
          exist _ (raw_program_link v p) h =
          program_link (exist _ v hv) (exist _ p hp).
    Proof.
      intros A L Im Ir v p hv hp h.
      apply program_ext. cbn.
      reflexivity.
    Qed.

    Lemma some_lemma_for_prove_relational {export : Interface} {B} {L1 L2 LA}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (HINV : INV LA I) (Hempty : I (emptym, emptym))
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
        + cbv. intuition.
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
        eapply bind_rule_pp.
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
        eapply bind_rule_pp.
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
    Definition prove_relational {export : Interface} {L1 L2}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (Hempty : I (emptym, emptym))
               (H : eq_up_to_inv I P1 P2)
      : (L1; P1) ≈[ fun A => 0 ] (L2; P2).
    Proof.
      extensionality A.
      unfold Adversary4Game in A.
      unfold AdvantageE, Pr.
      pose r' := get_package_op A RUN RUN_in_A_export.
      pose r := r' tt.
      (* ER: from linking we should get the fact that A.π1 is disjoint from L1 and L2,
             and then from that conclude that we are invariant on A.π1 *)
      assert (INV A.π1 I) as HINV.
      { destruct A.
        cbn.  unfold INV.
        intros s1 s2. admit. }
      pose Hlemma := (some_lemma_for_prove_relational _ _ _ HINV Hempty H r emptym emptym Hempty).
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
            (injectLocations (fsubsetUl (T:=nat_ordType) (getLocations A) (L1 :|: L2)) r)
            (opackage_inject_locations
               (fsubset_trans (T:=nat_ordType) (y:=L1 :|: L2) (x:=L1)
                  (z:=getLocations A :|: (L1 :|: L2)) (fsubsetUl (T:=nat_ordType) L1 L2)
                  (fsubsetUr (T:=nat_ordType) (getLocations A) (L1 :|: L2))) P1))) emptym).
      pose rhs := _rhs prob_handler.
      simpl in _rhs, rhs.
      pose lhs := (let (L, o) := link A (L1; P1) in
                   let (PP, PP_is_valid) := o in
                   Pr_raw_package_op PP PP_is_valid RUN RUN_in_A_export tt emptym).
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
        admit.
      }
      unfold lhs in H0.
      rewrite H0.
      pose _rhs' := (thetaFstd _ (repr (program_link
            (injectLocations (fsubsetUl (T:=nat_ordType) (getLocations A) (L1 :|: L2)) r)
            (opackage_inject_locations
               (fsubset_trans (T:=nat_ordType) (y:=L1 :|: L2) (x:=L2)
                  (z:=getLocations A :|: (L1 :|: L2)) (fsubsetUr (T:=nat_ordType) L1 L2)
                  (fsubsetUr (T:=nat_ordType) (getLocations A) (L1 :|: L2))) P2))) emptym).
      pose rhs' := _rhs' prob_handler.
      simpl in _rhs', rhs'.
      pose lhs' := (let (L, o) := link A (L2; P2) in
                   let (PP, PP_is_valid) := o in
                   Pr_raw_package_op PP PP_is_valid RUN RUN_in_A_export tt emptym).
      assert (lhs' = rhs') as H0'.
      { unfold lhs', rhs', _rhs'. simpl.
        unfold Pr_raw_package_op. unfold Pr_raw_program.
        unfold thetaFstd. simpl. apply f_equal2. 2: { reflexivity. }
        apply f_equal. apply f_equal.
        apply repr'_ext. cbn. admit. }
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
      - admit.
    Admitted.
  End Games.

End PackageRHL.
