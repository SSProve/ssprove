From Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase FiniteProbabilities.
From Coq Require Import RelationClasses Morphisms.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From Crypt Require Import Axioms ChoiceAsOrd only_prob.SubDistr.

Import SPropNotations.
Import Num.Theory.

Local Open Scope ring_scope.

(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we develop a simple theory of couplings: their interaction
with the ret and bind operators of the SDistr relative monad, and
the product coupling for subdistributions that have a sum < 1
(some normalization is required).
*)

  Lemma eqType_lem : forall (Z : eqType) (z t : Z), z = t \/ ~(z = t).
  Proof.
    intros Z z t. case Hzt : (z==t).
    left. move: Hzt => /eqP. trivial.
    right. move: Hzt => /eqP. trivial.
  Qed.

  Lemma refl_true : forall (Z : eqType) (z :Z), (z == z) = true.
  Proof.
    intros. apply /eqP. reflexivity.
  Qed.

  Lemma reflection_nonsense : forall (Z : eqType) (a x : Z), (a == x) = true -> a = x.
  Proof.
  intros Z a x. intro Hax. unshelve eapply elimT. exact (a == x).
  apply eqP. assumption.
  Qed.



Section Coupling_def.
  Context {A1 A2 : ord_choiceType}.

  Definition lmg :
  TypeCat ⦅ SDistr( F_choice_prod (npair A1 A2) ) ; SDistr( A1 )  ⦆.
    intro d. exact (dfst d).
  Defined.

  Definition rmg :
  TypeCat ⦅ SDistr( F_choice_prod (npair A1 A2) ) ; SDistr( A2 )  ⦆.
    intro d. exact (dsnd d).
  Defined.

  Definition coupling (d : SDistr( F_choice_prod (npair A1 A2) ) )
  (c1 : SDistr A1) (c2 : SDistr A2) : Prop := (lmg d = c1) /\ (rmg d = c2).

End Coupling_def.

Section Weight_preservation.
  Context {A1 A2 : ord_choiceType}.
  Context (d : SDistr ( F_choice_prod (npair A1 A2))).
  Context (c1 : SDistr A1) (c2 : SDistr A2).
  Context (hCoupl : coupling d c1 c2).

  Lemma psum_coupling_left : psum d = psum c1.
  Proof. rewrite (@psum_pair R A1 A2 d).
  f_equal.
  destruct hCoupl as [lH rH]. rewrite -lH. unfold lmg.
  apply boolp.funext. intro x1.
  rewrite dfstE. reflexivity.
    destruct d as [dd d2 d3 d4]. simpl. assumption.
  Qed.

  Lemma psum_coupling_right : psum d = psum c2.
  Proof. rewrite (@psum_pair_swap R A1 A2 d).
  f_equal.
  destruct hCoupl as [lH rH]. rewrite -rH. unfold rmg.
  apply boolp.funext. intro x2.
  rewrite dsndE. reflexivity.
    destruct d as [dd d2 d3 d4]. simpl. assumption.
  Qed.

End Weight_preservation.

Section Weight_of_SDistr_unit.
  Context {A : ord_choiceType} (a : A).

  Lemma psum_SDistr_unit : psum (SDistr_unit A a) = 1.
  Proof.
  rewrite (@psum_finseq R A (SDistr_unit A a) [::a]).
  rewrite big_cons big_nil.
  rewrite GRing.addr0. unfold SDistr_unit. rewrite dunit1E.
  rewrite refl_true. simpl. rewrite normr1. reflexivity.
    rewrite cons_uniq. apply /andP. split. trivial.
      trivial.
    unfold sub_mem. intro x. unfold in_mem. simpl. rewrite dunit1E.
    intro Hx. apply /orP. left. move: Hx => /eqP. destruct (eqType_lem A a x).
    intro Hx. apply /eqP. symmetry ; assumption.
    assert (a == x = false).
      apply Bool.not_true_is_false.
      intro Hax. unshelve eapply elimT in Hax. exact (a = x).
      contradiction. apply eqP. rewrite H0. simpl. intro H1. epose (H2 := H1 _).
      contradiction.
      Unshelve. reflexivity.
  Qed.

End Weight_of_SDistr_unit.


Section Couplings_vs_ret.

  Context {A1 A2 : ord_choiceType}.
  Context (a1 : A1) (a2 : A2) (d : SDistr( F_choice_prod (npair A1 A2) )).

  (*the left and right marginals of the unit coupling are the units for
  left and right types*)
  Lemma SDistr_unit_F_choice_prod_coupling :
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2) ->
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2).
  Proof.
    intro Hunit. split.
    - pose (retComm := @dmargin_dunit R (F_choice_prod (npair A1 A2)) A1 (a1,a2) fst).
      unfold lmg. rewrite Hunit. unfold SDistr_unit. simpl.
      apply distr_ext. assumption.
    - pose (retComm := @dmargin_dunit R (F_choice_prod (npair A1 A2)) A2 (a1,a2) snd).
      unfold rmg. rewrite Hunit. unfold SDistr_unit. simpl.
      apply distr_ext. assumption.
  Qed.

  Lemma lmg_SDistr_unit :
  lmg d = SDistr_unit A1 a1 ->
  forall (x1 : A1) (x2 : A2), ~(a1 = x1) -> d(x1,x2) = 0.
  Proof.
    intro rHcoupl. intros x1 x2. intro Hxa.
    unfold lmg in rHcoupl. unfold SDistr_unit in rHcoupl.
    assert (rHcoupl1 : dfst d x1 = dunit (T:=A1) a1 x1).
      rewrite rHcoupl. reflexivity.
    rewrite (dfstE d x1) (dunit1E a1 x1) in rHcoupl1.
    assert ((a1==x1 = false)).
      apply /eqP. assumption.
    rewrite H /= in rHcoupl1.
    epose (bla := eq0_psum _ rHcoupl1 x2).
    apply bla. Unshelve.
      eapply summable_fst.
  Qed.

  Lemma rmg_SDistr_unit :
  rmg d = SDistr_unit A2 a2 ->
  forall (x1 : A1) (x2 : A2), ~(a2 = x2) -> d(x1,x2) = 0.
  Proof.
    intro rHcoupl. intros x1 x2. intro Hxa.
    unfold rmg in rHcoupl. unfold SDistr_unit in rHcoupl.
    assert (rHcoupl1 : dsnd d x2 = dunit (T:=A2) a2 x2).
      rewrite rHcoupl. reflexivity.
    rewrite (dsndE d x2) (dunit1E a2 x2) in rHcoupl1.
    assert ((a2==x2 = false)).
      apply /eqP. assumption.
    rewrite H /= in rHcoupl1.
    epose (bla := eq0_psum _ rHcoupl1 x1).
    apply bla. Unshelve.
      eapply summable_snd.
  Qed.

  Lemma lmg_rmg_SDistr_unit
  (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2)) :
  forall (x1 : A1) (x2 : A2), ~( (x1,x2) = (a1,a2) ) -> d(x1,x2) = 0.
  Proof.
    intros. move: hCoupl => [lH rH].
    case HXA : (x1 != a1).
      - eapply lmg_SDistr_unit. assumption. unshelve eapply elimT in HXA.
        exact (~(x1 = a1)). intro. symmetry in H0. apply HXA. assumption.
        eapply Bool.iff_reflect. split.
          intro. assumption.
          intros. intro. rewrite H1 in HXA. move: HXA => /negP HXA.
          apply HXA. apply /eqP. reflexivity.
      -  unshelve eapply introN in H. exact ((x1,x2)==(a1,a2)). all: revgoals. apply eqP.
         simpl in H.
         unfold "==" in H. simpl in H. rewrite Bool.negb_andb in H.
         rewrite HXA in H. simpl in H.
        eapply rmg_SDistr_unit. assumption. move: H => /negP H.
        intro Ha2x2. rewrite Ha2x2 in H. apply H. apply /eqP. reflexivity.
  Qed.

  Lemma weight_from_mgs (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2)):
  psum d = 1.
  Proof.
    rewrite (@psum_coupling_left A1 A2 d (SDistr_unit A1 a1) (SDistr_unit A2 a2) hCoupl).
    eapply psum_SDistr_unit.
  Qed.

  Lemma d_is_one
  (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2))  :
  d(a1,a2) = 1.
  Proof.
    unshelve epose (@psum_finseq R (F_choice_prod (npair A1 A2)) d [::(a1,a2)] _ _).
      rewrite cons_uniq //=.
      move=> [x1 x2]. unfold in_mem. simpl.
      intro Hsupp. apply /orP. left.
      move: Hsupp. apply contraLR. intro Hxadiff. unfold "==". simpl.
      rewrite Bool.negb_involutive. rewrite -/(_ == _).
      apply /eqP. unshelve eapply lmg_rmg_SDistr_unit. assumption.
      move: Hxadiff => /negP Hxadiff. intro bla. rewrite bla in Hxadiff.
      apply Hxadiff. apply eq_refl.
      move: e. rewrite big_seq1. move=> e. rewrite weight_from_mgs in e.
      rewrite e. symmetry. assert (Hbnorm: `|d (a1, a2)| == d (a1, a2) -> `|d (a1, a2)| = d (a1, a2)).
      move=> /eqP. trivial.
      apply Hbnorm. rewrite -(ger0_def). destruct d as [d1 d2 d3 d4]. simpl in *.
      apply (d2 (a1,a2)). assumption.
  Qed.

  Lemma coupling_SDistr_unit_F_choice_prod :
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2) ->
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2).
  Proof.
    simpl in *. unfold SDistr_carrier in d.
    move=> hCoupl.
    apply distr_ext. move=> [x1 x2]. unfold SDistr_unit.
    assert (xa_lem : (x1,x2) = (a1,a2) \/ ~((x1,x2) = (a1,a2))).
      apply eqType_lem.
    destruct xa_lem as [xa_lem_left | xa_lem_right].
      rewrite dunit1E. rewrite xa_lem_left. rewrite refl_true. simpl.
      unshelve eapply d_is_one. assumption.
    rewrite dunit1E. assert ((a1, a2) == (x1, x2) = false).
    apply Bool.negb_true_iff. apply /negP. move=> /eqP hxa. symmetry in hxa.
    apply xa_lem_right. assumption.
    rewrite H. simpl. unshelve eapply lmg_rmg_SDistr_unit. assumption.
    assumption.
  Qed.

  Lemma coupling_vs_ret :
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2) <->
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2).
  Proof.
    split.
    -  intro dCoupl. unshelve eapply SDistr_unit_F_choice_prod_coupling.
       assumption.
    -  intro dCoupl. unshelve eapply coupling_SDistr_unit_F_choice_prod.
       assumption.
  Qed.

End Couplings_vs_ret.

Lemma msupp : forall A1 A2 s s0 (dA : SDistr _), (s, s0) \in dinsupp (T:=F_choice_prod ⟨ A1, A2 ⟩) dA -> 0 < dA (s, s0) = true.
Proof.
  move=> A1 A2 a1 a2 dA. move=> Hdinsupp. rewrite /in_mem in Hdinsupp.
  simpl in Hdinsupp. rewrite /dinsupp in Hdinsupp. rewrite lt0r.
  apply /andP. split. all: revgoals.
    move: dA Hdinsupp => [dAmap dAz dASumbl dAPsum]. simpl.
    move=> Hdinsupp. apply dAz.
  assumption.
Qed.

Section Couplings_vs_bind.
  Context {A1 A2 B1 B2 : ord_choiceType}.

  Context (c1 : SDistr A1) (f1 : TypeCat ⦅ choice_incl A1 ; SDistr B1⦆ )
  (c2 : SDistr A2) (f2 : TypeCat ⦅ choice_incl A2 ; SDistr B2⦆).

  Context (dA : SDistr ( F_choice_prod (npair A1 A2) ) ) (dA_coup : coupling dA c1 c2).

  Context (kd : TypeCat ⦅ choice_incl (F_choice_prod (npair A1 A2)) ; SDistr (F_choice_prod( npair B1 B2)) ⦆)
          (kd_pcoup : forall (x1 : A1) (x2 : A2), (dA (x1, x2) > 0) = true -> coupling (kd (x1,x2)) (f1 x1) (f2 x2)  ).

  Lemma coupling_vs_bind :
  coupling (SDistr_bind (F_choice_prod(npair A1 A2)) (F_choice_prod(npair B1 B2)) kd dA)
           (SDistr_bind A1 B1 f1 c1) (SDistr_bind A2 B2 f2 c2).
  Proof. split.
         -  unfold lmg.
            unfold SDistr_bind.
            unfold dfst.
            move: dA_coup.
            rewrite /coupling /lmg.
            intros [H1 H2].
            rewrite <- H1.
            unfold dfst.
            apply distr_ext. intro b.
            rewrite (dlet_dlet kd (fun x => dunit x.1) dA).
            rewrite (dlet_dlet _ _ dA).
            apply (@eq_in_dlet _ _ _).
            move => x12 Hsupp b2.
            destruct x12.
            simpl. rewrite (dlet_unit).
            assert (0 < dA (s, s0) = true).
            apply msupp. assumption.
            specialize (kd_pcoup s s0 H).
            unfold coupling in kd_pcoup. destruct kd_pcoup.
            unfold lmg in H0. unfold dfst in H0.
            rewrite H0. reflexivity.
            intro x. reflexivity.
         -  unfold rmg.
            unfold SDistr_bind.
            unfold dfst.
            move: dA_coup.
            rewrite /coupling /lmg.
            intros [H1 H2].
            rewrite <- H2.
            unfold dfst.
            apply distr_ext. intro b.
            rewrite (dlet_dlet kd (fun x => dunit x.2) dA).
            rewrite (dlet_dlet _ _ dA).
            apply (@eq_in_dlet _ _ _).
            move => x12 Hsupp b2.
            destruct x12.
            simpl. rewrite (dlet_unit).
            assert (0 < dA (s, s0) = true).
            apply msupp. assumption.
            specialize (kd_pcoup s s0 H).
            unfold coupling in kd_pcoup. destruct kd_pcoup.
            unfold rmg in H3. unfold dfst in H3.
            rewrite H3. reflexivity.
            intro x. reflexivity.
Qed.

End Couplings_vs_bind.


(*the rest of the file is work in progress*)

Section Forall_exists.
  (*work in progress *)

  Context {A1 A2 B1 B2 : ord_choiceType}.

  Context (c1 : SDistr A1) (f1 : TypeCat ⦅ choice_incl A1 ; SDistr B1⦆ )
  (c2 : SDistr A2) (f2 : TypeCat ⦅ choice_incl A2 ; SDistr B2⦆).

  Context (dA : SDistr ( F_choice_prod (npair A1 A2) ) ) (dA_coup : coupling dA c1 c2).

  Context (q : A1 -> A2 -> (SDistr ( F_choice_prod (npair B1 B2) )) -> Prop).

  Lemma Forall_vs_exists
  ( all_ex :  forall(a1 : A1) (a2 : A2), exists (dB : SDistr ( F_choice_prod (npair B1 B2) )),
  coupling dB (f1 a1)(f2 a2) /\ (q a1 a2 dB)   ) :
  exists (kd : TypeCat ⦅ choice_incl (F_choice_prod (npair A1 A2)) ; SDistr (F_choice_prod( npair B1 B2)) ⦆)  ,  (forall (x1 : A1) (x2 : A2), coupling (kd (x1,x2)) (f1 x1) (f2 x2)  ) /\
  forall a1 a2, q a1 a2 (kd (a1,a2)).
  Proof.
  unshelve esplit.
  -  move=> [a1 a2]. move: (all_ex a1 a2). Fail move=> [dB dBcoup].
     move=> dBex.
     apply boolp.constructive_indefinite_description in dBex.
     move: dBex => [dB [dBcoup dBq]]. exact dB.
  intuition.
  -  move: (all_ex x1 x2) => from_all_ex.
  destruct from_all_ex as [kdx1x2 kdcoupq]. simpl.

 Abort.


End Forall_exists.

Section Independent_coupling.
  (*work in progress*)

  Context {A1 A2 : ord_choiceType}.

  Context (c1 : SDistr A1) (c2 : SDistr A2).

  Definition indp := SDistr_bind _ _ (fun x => SDistr_bind _ _ (fun y => SDistr_unit _ (x, y)) c2) c1.

  Local Lemma indp_ext (x : A1) (y : A2) : indp (x, y) = c1 x * c2 y.
  Proof.
    unfold indp.
    unfold SDistr_bind, SDistr_unit.
    rewrite dletE.
    assert ((fun x0 : A1 => c1 x0 * (\dlet_(y0 <- c2) dunit (T:=prod_choiceType A1 A2) (x0, y0)) (x, y)) = (fun x0 : A1 => c1 x0 * psum (fun y0 : A2 => c2 y0 * dunit (T:=prod_choiceType A1 A2) (x0, y0)  (x, y)))) as H.
    { extensionality x0. rewrite dletE. reflexivity. }
    rewrite H. clear H.
    assert ((fun x0 : A1 =>
               c1 x0 * psum (fun y0 : A2 => c2 y0 * dunit (T:=prod_choiceType A1 A2) (x0, y0) (x, y))) =
            (fun x0 : A1 =>
               psum (fun y0 : A2 => c1 x0 * c2 y0 * (dunit (x0, y0) (x, y))))).
    { extensionality x0.
      rewrite -psumZ.
      2: { admit. }
      apply f_equal.
      extensionality y0.
      simpl. rewrite dunit1E.
      apply GRing.mulrA. }
    rewrite H. clear H.
    rewrite -(psum_pair (S := fun p => c1 (fst p) * c2 (snd p) * dunit p (x, y))).
  Admitted.

  Local Lemma independent_coupling_lmg : lmg indp = c1.
  Proof.
  Admitted.

  Local Lemma independent_coupling_rmg : rmg indp = c2.
  Proof.
  Admitted.

  Local Lemma independent_coupling : coupling indp c1 c2.
  Proof.
    unfold coupling.
    split.
    - apply independent_coupling_lmg.
    - apply independent_coupling_rmg.
  Qed.
End Independent_coupling.
