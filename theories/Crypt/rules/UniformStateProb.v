From Mon Require Import FiniteProbabilities SPropMonadicStructures
  SpecificationMonads MonadExamples SPropBase.

From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples Commutativity GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings Theta_dens
  Theta_exCP LaxComp FreeProbProg UniformDistrLemmas
  Prelude choice_type StateTransformingLaxMorph RulesStateProb.

Import SPropNotations.
Import Num.Theory.

Local Open Scope ring_scope.

(* general Rules + Rules for uniform distributions over a finite
    family of non-empty finite types *)

Definition Index : Type := positive.

Definition fin_family (i : Index) : finType := [finType of chFin i].

Lemma F_w0 :
  forall (i : Index), fin_family i.
Proof.
  intros i. unfold fin_family. cbn.
  exists 0%N. eapply i.(cond_pos).
Qed.

(* extend the initial parameters for the rules  *)

Definition Uni_W : forall i, SDistr (fin_family i).
  move=> i. apply (@uniform_F (fin_family i)).
  apply F_w0.
Defined.

Definition Uni_W' : forall i, SDistr( chFin i) := Uni_W.


Definition Fail_Unit : SDistr chUnit.
  exact dnull.
Defined.

#[local] Definition FrStP := @FrStP.
(* #[local] Definition θ0 {S} {A} (c : @FrStP S A) := @θ0 S A c. *)
(* #[local] Definition θ_dens {S} {X} := @θ_dens S X. *)

(* Definition inhab (i : positive) : [finType of chFin i]. *)
(* destruct i as [i ipos]. destruct i. *)
(* - cbv in ipos. discriminate. *)
(* - cbn. unshelve econstructor. *)
(*   exact i. auto. *)
(* Defined. *)

(* Uniform distribution over F *)
Definition Uniform_F {i : Index} {S : choiceType} : @FrStP S (fin_family i).
Proof.
  rewrite /=.
  rewrite /ops_StP /ar_StP /fin_family.
  (* pose usd :=  @uniform_F [finType of chFin i] (inhab i). *)
  unshelve eapply ropr.
  - apply op_iota. unshelve econstructor.
    + exact (chFin i).
    + apply Uni_W'.
  - rewrite /=. move=> j. eapply retrFree. assumption.
Defined.

Definition Uniform ( i : Index ) { S : choiceType } { s : S } :=
  θ_dens (θ0 (@Uniform_F i S) s).

Lemma Uniform_eval (i : Index ) {S : choiceType} {s : S} :
  forall (st : S) (w : fin_family i),
    @Uniform i S s (w, st) =
    if st == s then @r (fin_family i) (F_w0 i) else 0.
Proof.
  (* move=> st w. rewrite /Uniform /=. *)
  (* case bb : (st == s). *)
  (* - rewrite  *)
  cbn.
  rewrite /SDistr_bind /SDistr_unit => st w /=.
  rewrite dletE.
  match goal with
  | |- psum ?k = _ =>
    eassert (k = _) as H
  end.
  { extensionality x.
    rewrite dunit1E.
    eassert (((x, s) == (w, st))%:R = (x == w)%:R * (s == st)%:R).
    { destruct (x == w) eqn:e1, (s == st) eqn:e2.
      all: cbn.
      all: cbn in e1.
      all: rewrite ?e1 ?e2.
      all: cbn.
      all: rewrite ?GRing.mulr1 ?GRing.mul0r ?GRing.mulr0.
      all: reflexivity.
    }
    rewrite H.
    rewrite GRing.mulrA.
    rewrite -dunit1E.
    reflexivity.
  }
  rewrite H. clear H.
  rewrite psumZr.
  2:{
    destruct (s == st). all: cbn.
    - apply (@ler01 R).
    - apply Order.POrderTheory.lexx.
  }
  rewrite -dletE.
  rewrite dlet_dunit_id.
  destruct (s == st) eqn:Heq.
  - have Heq' : st == s. apply /eqP. by move /eqP: Heq.
    rewrite Heq'. rewrite GRing.mulr1. reflexivity.
  - have Heq' : st == s = false. apply /eqP. move /eqP: Heq. congruence.
    rewrite Heq'. rewrite GRing.mulr0. reflexivity.
  Unshelve. exact (Real.ringType R).
Qed.

Definition f_dprod { F1 F2: finType } { S1 S2 : choiceType } { w0 : F1 } { w0' : F2 } {s1 : S1 } {s2 : S2}
            (f : F1 -> F2) : (F1 * S1) * (F2 * S2) -> R :=
fun '((w1,st1),(w2, st2)) => if  ((st1 == s1) && (st2 == s2) && ((f w1) == w2)) then (@r F1 w0) else 0.

Lemma item_addr0_mulr :
  forall n x,
    (* @iter R n (+%R x) 0 = x * n%:~R. *)
    @iter R n (+%R x) 0 = x *~ n.
Proof.
  intros n x.
  induction n as [| n ih].
  - cbn. reflexivity.
  - simpl. rewrite ih.
    unfold intmul. rewrite GRing.mulrS. reflexivity.
Qed.

Lemma bijective_isdistr
  {F1 F2 : finType} {w0 : F1} {w0' : F2}
  {S1 S2 : choiceType} {s1 : S1} {s2 : S2}
  {f : F1 -> F2} (f_bij : bijective f) :
  isdistr (@f_dprod F1 F2 S1 S2 w0 w0' s1 s2 f).
Proof.
  rewrite /f_dprod.
  split.
  - move => [[w1 st1] [w2 st2]].
    destruct ((st1 == s1) && (st2 == s2) && (f w1 == w2)) eqn:Heq; auto.
    exact r_nonneg.
  - rewrite /= => J uniq_J.
    rewrite [X in X<=_](bigID [pred j : _ | (j.1.2 == s1) && (j.2.2 == s2) && (f j.1.1 == j.2.1)]) /=.
    lazymatch goal with
    | |- context [ _ + ?x ] =>
      assert (e : x == 0)
    end.
    { rewrite psumr_eq0.
      - apply/allP. intros [[w1 st1] [w2 st2]] h. cbn.
        match goal with
        | |- context [ if ?b then _ else _ ] =>
          destruct b
        end.
        + cbn. reflexivity.
        + cbn. apply/eqP. reflexivity.
      - intros [[w1 st1] [w2 st2]]. cbn. intros h.
        match goal with
        | |- context [ if ?b then _ else _ ] =>
          destruct b
        end.
        1: discriminate.
        auto.
    }
    move: e => /eqP e. rewrite e. clear e.
    rewrite GRing.Theory.addr0.
    erewrite sum_oneq_eq with (G := fun i => r).
    2:{
      intros [[w1 st1] [w2 st2]]. cbn. intros h.
      rewrite h. reflexivity.
    }
    rewrite big_const_seq. cbn.
    match goal with
    | |- context [ count ?p _ ] =>
      set (P := p)
    end.
    pose (J' := [seq p <- J | P p ]).
    assert (e1 : count P J = size J').
    { rewrite size_filter. reflexivity. }
    pose (g := fun i => ((i, s1), (f i, s2))).
    pose (proj := fun (j : F1 * S1 * (F2 * S2)) => let '((i,_),_) := j in i).
    pose (g' := g \o proj).
    pose (J'' := [seq g' j | j <- J' ]).
    assert (e2 : J' = J'').
    { clear - uniq_J.
      subst J' J''. induction J as [| [[w1 st1] [w2 st2]] J ih].
      - cbn. reflexivity.
      - simpl. destruct (P _) eqn:e.
        + simpl. f_equal.
          * unfold P in e. simpl in e.
            move: e => /andP [e /eqP ?]. move: e => /andP [/eqP ? /eqP ?].
            subst. reflexivity.
          * eapply ih. cbn in uniq_J. move: uniq_J => /andP []. auto.
        + eapply ih. cbn in uniq_J. move: uniq_J => /andP []. auto.
    }
    subst g'.
    unfold J'' in e2. rewrite -> map_comp in e2.
    assert (uniq_J' : uniq J').
    { subst J'. apply filter_uniq. auto. }
    pose (I := [seq g i | i <- enum F1]).
    assert (e3 : (size J' <= size I)%N).
    { subst I. rewrite size_map.
      rewrite e2. rewrite size_map.
      eapply uniq_leq_size.
      1:{ rewrite e2 in uniq_J'. apply map_uniq in uniq_J'. auto. }
      intros x h. rewrite mem_enum. reflexivity.
    }
    rewrite -e1 in e3.
    subst I. rewrite size_map in e3.
    rewrite -cardE in e3.
    rewrite item_addr0_mulr.
    eapply Order.POrderTheory.le_trans with (y := @r _ w0 *~ #|F1|).
    + rewrite -mulrzr. rewrite -[X in _<=X]mulrzr.
      rewrite ler_pmul2l.
      * rewrite ler_int. auto.
      * unfold r. apply mulr_gt0.
        -- cbn. rewrite posnum.one_pos_gt0. reflexivity.
        -- rewrite -(@pmulr_rgt0 _ #|F1|%:~R).
            ++ rewrite -(GRing.mul1r (#|F1|%:~R / #|F1|%:~R)).
              rewrite GRing.mulrA.
              rewrite GRing.Theory.mulfK.
              ** rewrite posnum.one_pos_gt0. reflexivity.
              ** unshelve eapply card_non_zero. auto.
            ++ eapply fintype0 in w0 as h.
              destruct #|F1| eqn:e. 1: contradiction.
              rewrite ltr0n. reflexivity.
    + unfold r. rewrite -[X in X <= _]mulrzr. rewrite GRing.div1r.
      erewrite <- GRing.mulr1. rewrite -GRing.mulrA.
      rewrite GRing.Theory.mulKf.
      * auto.
      * unshelve eapply card_non_zero. auto.
Qed.

Definition UniformFsq_f { F1 F2 : finType} { w0 : F1 } { w0' : F2 }
                        { S1 S2 : choiceType } { s1 : S1 } { s2 : S2 }
                        {f : F1 -> F2} (f_bij : bijective f):
  SDistr (ChoiceAsOrd.F_choice_prod ⟨ ChoiceAsOrd.F_choice_prod ⟨ Finite.choiceType F1 , S1 ⟩ ,
                                    ChoiceAsOrd.F_choice_prod ⟨ Finite.choiceType F2 , S2 ⟩ ⟩ ).
Proof.
  unshelve eapply mkdistr.
  1:{
    exact: (@f_dprod F1 F2 S1 S2 w0 w0' s1 s2 f).
  }
  by apply: bijective_isdistr.
Defined.


Definition UniformSQ { i j : Index } { S1 S2 : choiceType } (s1 : S1) (s2 : S2)
                      { f : fin_family i -> fin_family j } (f_bij : bijective f) :=
  @UniformFsq_f (fin_family i) (fin_family j) (F_w0 i) (F_w0 j) S1 S2 s1 s2 f f_bij.


Lemma bij_same_r { F1 F2 : finType } { w0 : F1 } { w0' : F2 } { f : F1 -> F2 }
      ( bij_f : bijective f ) : @r F1 w0 = @r F2 w0'.
Proof.
  unfold r. f_equal. f_equal. f_equal.
  erewrite <- on_card_preimset with (f := f).
  2:{
    destruct bij_f as [g hfg hgf].
    exists g.
    - intros x hx. apply hfg.
    - intros x hx. apply hgf.
  }
  rewrite cardsT. reflexivity.
Qed.



Lemma UniformSQ_f_coupling { i j : Index}
                            { S1 S2 : choiceType } { s1 : S1 } { s2 : S2 }
                            { f : fin_family i -> fin_family j } (f_bij : bijective f):
  coupling (UniformSQ s1 s2 f_bij) (@Uniform i S1 s1) (@Uniform j S2 s2).
Proof.
  destruct f_bij as [f_inv Kf1 Kf2].
  rewrite /UniformFsq_f /f_dprod.
  split; apply: distr_ext; rewrite /=.
  - move => [w1 st1].
    rewrite /lmg dfstE /mkdistr psum_sum /=.
    rewrite (sum_seq1 ((f w1), s2)).
    by rewrite !refl_true !Bool.andb_true_r Uniform_eval.
    move => [w2 st2] /= H.
    have Hs : (st2 = s2).
    { destruct (st2 == s2) eqn:Heq;  apply /eqP; rewrite Heq; auto.
      exfalso. rewrite Bool.andb_false_r Bool.andb_false_l in H. by move /eqP : H.  }
    have Hf : (f w1 = w2).
    { destruct (f w1 == w2) eqn:Heq; apply /eqP; rewrite Heq; auto.
      rewrite Bool.andb_false_r in H. by move /eqP: H. }
      by rewrite Hs Hf.
    move => [w2 st2] /=.
    destruct ((st1 == s1) && (st2 == s2) && (f w1 == w2)); auto.
    exact: r_nonneg.
  - move => [w2 st2].
    rewrite /rmg dsndE /mkdistr psum_sum /=.
    rewrite (sum_seq1 ((f_inv w2), s1)).
    have Hf: (f (f_inv w2) = w2) by apply: (Kf2 w2).
    have Hs: s1 == s1 by apply /eqP.
    rewrite Hf Hs /= refl_true Bool.andb_true_r Uniform_eval.
    rewrite (@bij_same_r (fin_family i) (fin_family j) (F_w0 i) w2 f).
    reflexivity.
    by exists f_inv.
    move => [w1 st1] /= Hneq.
    have [Hfoo1 Hfoo2] : s1 = st1 /\ f w1 = w2.
    { destruct ((st1 == s1) && (f w1 == w2)) eqn: Heq.
      move /andP : Heq. move => [H1 H2].
      split; by [move /eqP : H1 | move /eqP : H2].
      exfalso. move /eqP: Hneq. rewrite Bool.andb_comm in Heq.
      by rewrite Bool.andb_comm Bool.andb_assoc Heq Bool.andb_false_l. }
    subst.
    by rewrite Kf1 refl_true.
    move => [w1 st1] /=. destruct ((st1 == s1) && (st2 == s2) && (f w1 == w2)); auto.
    exact: r_nonneg.
Qed.

Import RSemanticNotation.
#[local] Open Scope rsemantic_scope.


Theorem Uniform_bij_rule { i j : Index } { S1 S2 : choiceType }
                          { f : fin_family i -> fin_family j } (f_bij : bijective f)
                          (P : S1 * S2 -> Prop) :
  ⊨ ⦃ P ⦄ (@Uniform_F i S1) ≈ (@Uniform_F j S2) ⦃ fun '(w1, s1) '(w2, s2) => P (s1, s2) /\ (f w1 == w2) ⦄.
Proof.
  move => [s1 s2] /=.
  move => π /= [H11 H2].
  exists (UniformSQ s1 s2 f_bij).
  split.
  - by apply: UniformSQ_f_coupling.
  - rewrite /UniformSQ.
    move => [w1 st1] [w2 st2] H. apply: H2.
    rewrite /UniformFsq_f /= in H.
    have hfoo1 : (st1 == s1).
    { destruct (st1 == s1) eqn:Heq; auto.
      by rewrite Bool.andb_false_l  Order.POrderTheory.ltxx in H. }
    have hfoo2 : (st2 == s2).
    { destruct (st2 == s2) eqn:Heq; auto.
      by rewrite Bool.andb_false_r Order.POrderTheory.ltxx in H. }
    have hfoo3 : (f w1 == w2).
    { destruct (f w1 == w2) eqn:Heq; auto.
      by rewrite Bool.andb_false_r  Order.POrderTheory.ltxx in H. }
    move /eqP : hfoo1. move /eqP : hfoo2. move /eqP : hfoo3.
    move => hfoo3 hfoo2 hfoo1. subst.
    split; [assumption |  by rewrite refl_true ].
Qed.

Export RSPNotation.

(*CA: probably not necessary *)
(* Theorem Uniform_bij_rule_sq { i1 i2 j1 j2 : Index } { S1 S2 : choiceType } *)
(*         { f1 : fin_family i1 -> fin_family j1 } (f1_bij : bijective f1) *)
(*         { f2 : fin_family i2 -> fin_family j2 } (f2_bij : bijective f2) *)
(*         (P : S1 * S2 -> Prop) : *)
(*   ⊨ ⦃ P ⦄ ( ( A <- (A <- (@Uniform_F i1 S1) ;; @retrFree _ _ _ A) ;; *)
(*              (B <- (B <- (@Uniform_F i2 S1) ;; @retrFree _ _ _ B) ;; *)
(*              @retrFree _ _ _ (A, B) ))) *)

(*                 ≈ *)
(*           (( A <- (A <- (@Uniform_F j1 S2) ;; @retrFree _ _ _ A) ;; *)
(*            (B <- (B <- (@Uniform_F j2 S2) ;; @retrFree _ _ _ B) ;; *)
(*            @retrFree _ _ _ (A, B) ))) *)
(*        ⦃ fun '((A1, B1), s1) '((A2, B2), s2) => P (s1, s2) /\ (f1 A1 == A2) /\ (f2 B1 == B2) ⦄. *)
(* Proof. *)
(*   unshelve apply: seq_rule. *)
(*   { move => [A1 s1] [A2 s2]. exact: (P (s1, s2) /\ (f1 A1 == A2)). } *)
(*   apply: Uniform_bij_rule. assumption. *)
(*   move => A1 A2. *)
(*   unshelve apply: seq_rule.   *)
(*   { move => [B1 s1] [B2 s2]. exact: ((P (s1, s2) /\ (f1 A1 == A2) ) /\ (f2 B1 == B2)). } *)
(*   simpl.     *)
(*   apply: Uniform_bij_rule f2_bij (fun '(s1,s2) => P (s1, s2) /\ (f1 A1 == A2)). *)
(*   move => B1 B2. *)
(*   simpl.  *)
(*   apply: pre_hypothesis_rule => s1 s2 [[HP H1] H2]. simpl in HP.  *)
(*   move /eqP: H1. move /eqP: H2. move => H2 H1. subst.  *)
(*   unshelve apply: post_weaken_rule. *)
(*   { move => [[A B] st1] [[A' B'] st2]. *)
(*     exact: ((st1 , st2) = (s1, s2) /\ (f1 A, f2 B) = (A', B') ). } *)
(*   simpl. rewrite /fromPrePost.  Check ret_rule (A1,B1) (f1 A1, f2 B1).  *)
(*   admit.  *)
(*   simpl.   *)
(*   move => [[a1 b1] st1] [[a2 b2] st2] [H1 [H2 H3]]. subst. *)
(*   rewrite H1.  *)
(*   split; auto.  *)
(*   Admitted.  *)



Definition Fail { S : choiceType } : FrStP S chUnit.
Proof.
  unshelve eapply ropr.
    apply op_iota. econstructor. exact Fail_Unit.
  move=> _ /=. eapply retrFree. easy.
Defined.

Definition Assert {S : choiceType} (b : bool) : FrStP S chUnit.
Proof.
  destruct b.
  - apply retrFree.
    exact Datatypes.tt.
  - exact Fail.
Defined.

Lemma destruct_pair_eq {R : ringType} {A B : eqType} {a b : A} {c d : B}
  : ((a, c) == (b, d))%:R = (a == b)%:R * (c == d)%:R :> R.
Proof.
  destruct (a == b) eqn:ab, (c == d) eqn:cd.
  all: cbn; rewrite ab cd /=; try rewrite GRing.mulr1; try rewrite GRing.mulr0; reflexivity.
Qed.

Theorem assert_rule { S1 S2 : choiceType }  (b b' : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = b' ⦄ (Assert b) ≈ (Assert b') ⦃ fun _ _ => b = true /\ b' = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b, b'.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
  - discriminate.
  - exists dnull.
    split.
    + unfold coupling.
      split.
      * unfold SDistr_bind.
        unfold lmg. apply distr_ext.
        move => x0. rewrite !dlet_null.
        reflexivity.
      * unfold SDistr_bind.
        unfold rmg. apply distr_ext.
        move => x0. rewrite !dlet_null.
        reflexivity.
    + intros [a1 s1'] [a2 s2'].
      rewrite dnullE.
      rewrite Order.POrderTheory.ltxx.
      auto.
Qed.

Theorem assert_rule_left { S1 S2 : choiceType }  (b : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = true ⦄ (Assert b) ≈ (retF Datatypes.tt) ⦃ fun _ _ => b = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
Qed.

Theorem assert_rule_right { S1 S2 : choiceType }  (b : bool) :
  ⊨ ⦃ fun (_ : S1 * S2) => b = true ⦄ (retF Datatypes.tt) ≈ (Assert b) ⦃ fun _ _ => b = true ⦄.
Proof.
  intros [s1 s2].
  hnf. intros post. hnf in *.
  cbv in post. intros H.
  cbv in H. destruct H as [Hpre K].
  simpl.
  destruct b.
  all: simpl in *.
  - exists (SDistr_unit _ ((Datatypes.tt, s1), (Datatypes.tt, s2))).
    split.
    + unfold coupling.
      split.
      * unfold lmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dfst.
        rewrite dlet_unit. reflexivity.
      * unfold rmg. apply distr_ext.
        move => x0. unfold SDistr_unit, dsnd.
        rewrite dlet_unit. reflexivity.
    + auto.
  - discriminate.
Qed.
