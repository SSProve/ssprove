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
  pkg_chUniverse pkg_notation.
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
      | _getr l k := ropr (inl (inl (gett _))) (λ s, let v := get_heap s l in repr' (k v) _) ;
      | _putr l v k :=
        ropr (inl (inl (gett heap_choiceType))) (λ s, ropr (inl (inr (putt heap_choiceType (set_heap s l v)))) (λ s', repr' k _)) ;
      | _sampler op k := ropr (inr op) (λ s, repr' (k s) _)
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

   
    Lemma some_lemma_for_prove_relational {export : Interface} {B} {L1 L2 LA}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (Hempty : I (emptym, emptym))
               (H : forall (op : opsig) (Hin : op \in export) (arg : src op),
                   ⊨ ⦃ fun '(s1, s2) => I (s1, s2) ⦄
                     (repr (get_opackage_op P1 op Hin arg))
                     ≈
                     (repr (get_opackage_op P2 op Hin arg))
                     ⦃ fun '(b1, s1) '(b2, s2) => I (s1, s2) /\ b1 = b2 ⦄)
               (A : program LA export B)
               (s1 : heap_choiceType) (s2 : heap_choiceType) (Hs1s2 : I (s1, s2))
      :
        ⊨ ⦃ fun '(s1, s2) => I (s1, s2)  ⦄
          repr (program_link (injectLocations (fsubsetUl LA (L1 :|: L2)) A) (opackage_inject_locations (fsubset_trans (fsubsetUl L1 L2) (fsubsetUr LA (L1 :|: L2))) P1))
          ≈
          repr (program_link (injectLocations (fsubsetUl LA (L1 :|: L2)) A) (opackage_inject_locations (fsubset_trans (fsubsetUr L1 L2) (fsubsetUr LA (L1 :|: L2))) P2))
          ⦃ fun '(b1, s1) '(b2, s2) => b1 = b2 /\ I (s1, s2) ⦄.
    Proof.
      destruct P1 as [P1a P1b].
      destruct P2 as [P2a P2b].
      destruct A as [A hA].
      induction A; intros.
      - cbn - [semantic_judgement].
        unfold repr'_obligation_1.
        eapply weaken_rule.
        + apply ret_rule.
        + cbv. intuition.
      - destruct (lookup_op P1a o) eqn:lookup_op1.
        2: { pose (P1b o) as Hbot. destruct hA as [hA1 hA2].
             specialize (Hbot hA1). admit. }
        cbn - [semantic_judgement].
        fold_repr.
        admit.
      - unfold program_link. unfold injectLocations. unfold opackage_inject_locations.
        simpl (raw_program_link _). unfold "∙1".
         match goal with
        | |- ⊨ ⦃ _ ⦄ repr ⦑ _getr ?l ?k ⦒ ≈ _ ⦃ _ ⦄ =>
          eassert (⦑ _getr l k ⦒ =
                   bind _ _ ⦑ _getr l (fun x : Value => _ret x) ⦒ (fun v => ⦑ k v ⦒)) as Hl
        end.
        { apply program_ext. cbn. reflexivity. }
        rewrite Hl.
        rewrite repr_bind.
        match goal with
        | |- ⊨ ⦃ _ ⦄ _ ≈ repr ⦑ _getr ?l ?k ⦒ ⦃ _ ⦄ =>
          eassert (⦑ _getr l k ⦒ =
                   bind _ _ ⦑ _getr l (fun x : Value => _ret x) ⦒ (fun v => ⦑ k v ⦒)) as Hr
        end.
        { apply program_ext. cbn. reflexivity. }
        rewrite Hr.
        rewrite repr_bind.
        eapply weaken_rule.
        + eapply bind_rule.
          ++ admit.
          ++ intros a1 a2. admit.
        + admit.
      - admit.
      - unfold program_link. unfold injectLocations. unfold opackage_inject_locations.
        simpl (raw_program_link _). unfold "∙1".
         match goal with
        | |- ⊨ ⦃ _ ⦄ repr ⦑ _sampler ?l ?k ⦒ ≈ _ ⦃ _ ⦄ =>
          eassert (⦑ _sampler l k ⦒ =
                   bind _ _ ⦑ _sampler l (fun x : Arit l => _ret x) ⦒ (fun v => ⦑ k v ⦒)) as Hl
        end.
        { apply program_ext. cbn. reflexivity. }
        rewrite Hl.
        rewrite repr_bind.
        match goal with
        | |- ⊨ ⦃ _ ⦄ _ ≈ repr ⦑ _sampler ?l ?k ⦒ ⦃ _ ⦄ =>
          eassert (⦑ _sampler l k ⦒ =
                   bind _ _ ⦑ _sampler l (fun x : Arit l => _ret x) ⦒ (fun v => ⦑ k v ⦒)) as Hr
        end.
        { apply program_ext. cbn. reflexivity. }
        rewrite Hr.
        rewrite repr_bind.

        admit.
    Admitted.

    Lemma get_raw_package_op_link {L} {I E} {o : opsig}
          (hin : o \in E) (arg : src o) (p1 p2 : raw_package)
          (hp1 : valid_package L I E p1)
          (hpl : valid_package L I E (raw_link p1 p2))
          : (get_raw_package_op (raw_link p1 p2) hpl o hin arg) ∙1 =
            raw_program_link ((get_raw_package_op p1 hp1 o hin arg) ∙1) p2.
    Proof.
      admit.
    Admitted.



    (* ER: How do we connect the package theory with the RHL?
           Something along the following lines should hold? *)
    Definition prove_relational {export : Interface} {L1 L2}
               (P1 : opackage L1 Game_import export)
               (P2 : opackage L2 Game_import export)
               (I : heap_choiceType * heap_choiceType -> Prop)
               (Hempty : I (emptym, emptym))
               (H : forall (op : opsig) (Hin : op \in export) (arg : src op),
                   ⊨ ⦃ fun '(s1, s2) => I (s1, s2) ⦄
                     (repr (get_opackage_op P1 op Hin arg))
                     ≈
                     (repr (get_opackage_op P2 op Hin arg))
                     ⦃ fun '(b1, s1) '(b2, s2) => I (s1, s2) /\ b1 = b2  ⦄)
      : (L1; P1) ≈[ fun A => 0 ] (L2; P2).
    Proof.
      extensionality A.
      unfold Adversary4Game in A.
      unfold AdvantageE, Pr.
      pose r' := get_package_op A RUN RUN_in_A_export.
      pose r := r' tt.
      pose Hlemma := (some_lemma_for_prove_relational _ _ _ Hempty H r emptym emptym Hempty).
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
        apply f_equal. apply f_equal.  admit. }
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
    Admitted.
  End Games.

End PackageRHL.
