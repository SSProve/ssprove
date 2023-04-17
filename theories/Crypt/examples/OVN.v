
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition Package Prelude SigmaProtocol Schnorr DDH.

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

Module Type GroupParam.

  Parameter n : nat.
  Parameter n_pos : Positive n.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].

End GroupParam.

Module Type OVNParam.

  Parameter N : nat.
  Parameter N_pos : Positive N.

End OVNParam.

Module OVN (GP : GroupParam) (OP : OVNParam).
Import GP.
Import OP.

Set Equations Transparent.

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

(* order of g *)
Definition q' := Zp_trunc (pdiv #[g]).
Definition q : nat := q'.+2.

Lemma q_order_g : q = #[g].
Proof.
  unfold q, q'.
  apply Fp_cast.
  apply prime_order.
Qed.

Lemma q_field : (Zp_trunc #[g]) = q'.
Proof.
  unfold q'.
  rewrite pdiv_id.
  2: apply prime_order.
  reflexivity.
Qed.

Lemma expg_g : forall x, exists ix, x = g ^+ ix.
Proof.
  intros.
  apply /cycleP.
  rewrite -g_gen.
  apply: in_setT.
Qed.

Lemma group_prodC :
  @commutative gT gT mulg.
Proof.
  move => x y.
  destruct (expg_g x) as [ix ->].
  destruct (expg_g y) as [iy ->].
  repeat rewrite -expgD addnC.
  reflexivity.
Qed.

Definition Pid : finType := [finType of 'I_n].
Definition Secret : finType := Zp_finComRingType (Zp_trunc #[g]).
Definition Public : finType := FinGroup.arg_finType gT.
Definition s0 : Secret := 0.

Definition Pid_pos : Positive #|Pid|.
Proof.
  rewrite card_ord.
  eapply PositiveInFin.
  apply n_pos.
Qed.

Definition Secret_pos : Positive #|Secret|.
Proof.
  apply /card_gt0P. exists s0. auto.
Qed.

Definition Public_pos : Positive #|Public|.
Proof.
  apply /card_gt0P. exists g. auto.
Defined.

#[local] Existing Instance Pid_pos.
#[local] Existing Instance Secret_pos.
#[local] Existing Instance Public_pos.

Definition pid : choice_type := 'fin #|Pid|.
Definition secret : choice_type := 'fin #|Secret|.
Definition public: choice_type := 'fin #|Public|.

Definition nat_to_pid : nat → pid.
Proof.
  move=> n.
  eapply give_fin.
Defined.

Definition i_secret := #|Secret|.
Definition i_public := #|Public|.

Module Type CDSParams <: SigmaProtocolParams.
  Definition Witness : finType := Secret.
  Definition Statement : finType := prod_finType (prod_finType Public Public) Public.

  Definition Witness_pos : Positive #|Witness| := Secret_pos.
  Definition Statement_pos : Positive #|Statement|.
  Proof.
    unfold Statement.
    rewrite !card_prod.
    repeat apply Positive_prod.
    all: apply Public_pos.
  Qed.

  Definition R : Statement -> Witness -> bool :=
    λ (h : Statement) (x : Witness),
      let '(gx, gy, gyxv) := h in
      (gy^+x * g^+0 == gyxv) || (gy^+x * g^+1 == gyxv).

  Lemma relation_valid_left:
    ∀ (x : Secret) (gy : Public),
      R (g^+x, gy, gy^+x * g^+ 0) x.
  Proof.
    intros x gy.
    unfold R.
    apply /orP ; left.
    done.
  Qed.

  Lemma relation_valid_right:
    ∀ (x : Secret) (gy : Public),
      R (g^+x, gy, gy^+x * g^+ 1) x.
  Proof.
    intros x y.
    unfold R.
    apply /orP ; right.
    done.
  Qed.

  Parameter Message Challenge Response State : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.

  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.
  Parameter Response_pos : Positive #|Response|.
  Parameter State_pos : Positive #|State|.
  Parameter Bool_pos : Positive #|bool_choiceType|.
End CDSParams.

Module OVN (π2 : CDSParams) (Alg2 : SigmaProtocolAlgorithms π2).

  Module Sigma1 := Schnorr GP.
  Module Sigma2 := SigmaProtocol π2 Alg2.

  Obligation Tactic := idtac.
  Set Equations Transparent.

  Definition skey_loc (i : nat) : Location := (secret; (100+i)%N).
  Definition ckey_loc (i : nat) : Location := (public; (101+i)%N).

  Definition P_i_locs (i : nat) : {fset Location} := fset [:: skey_loc i ; ckey_loc i].

  Notation choiceStatement1 := Sigma1.MyAlg.choiceStatement.
  Notation choiceWitness1 := Sigma1.MyAlg.choiceWitness.
  Notation choiceTranscript1 := Sigma1.MyAlg.choiceTranscript.

  Notation " 'pid " := pid (in custom pack_type at level 2).
  Notation " 'pids " := (chProd pid pid) (in custom pack_type at level 2).
  Notation " 'public " := public (in custom pack_type at level 2).
  Notation " 'public " := public (at level 2) : package_scope.

  Notation " 'chRelation1' " := (chProd choiceStatement1 choiceWitness1) (in custom pack_type at level 2).
  Notation " 'chTranscript1' " := choiceTranscript1 (in custom pack_type at level 2).
  Notation " 'public_key " := (chProd public choiceTranscript1) (in custom pack_type at level 2).
  Notation " 'public_keys " := (chMap pid (chProd public choiceTranscript1)) (in custom pack_type at level 2).

  Notation " 'chRelation2' " := (chProd Alg2.choiceStatement Alg2.choiceWitness) (in custom pack_type at level 2).
  Notation " 'chTranscript2' " := Alg2.choiceTranscript (in custom pack_type at level 2).
  Notation " 'vote " := (chProd public Alg2.choiceTranscript) (in custom pack_type at level 2).

  Definition INIT : nat := 4.
  Definition VOTE : nat := 5.
  Definition CONSTRUCT : nat := 6.

  Definition P (i : nat) : nat := 14 + i.
  Definition Exec (i : nat) : nat := 15 + i.

  Lemma not_in_domm {T S} :
    ∀ i m,
      i \notin @domm T S m :\ i.
  Proof.
    intros.
    apply /negPn.
    rewrite in_fsetD.
    move=> /andP [H _].
    move: H => /negPn H.
    apply H.
    by rewrite in_fset1.
  Qed.

  Lemma not_in_fsetU :
    ∀ (l : Location) L0 L1,
      l \notin L0  →
      l \notin L1 →
      l \notin L0 :|: L1.
  Proof.
    intros l L0 L1 h1 h2.
    rewrite -fdisjoints1 fset1E.
    rewrite fdisjointUl.
    apply /andP ; split.
    + rewrite -fdisjoints1 fset1E in h1. apply h1.
    + rewrite -fdisjoints1 fset1E in h2. apply h2.
  Qed.

  #[local] Hint Extern 3 (is_true (?l \notin ?L0 :|: ?L1)) =>
    apply not_in_fsetU : typeclass_instances ssprove_valid_db ssprove_invariant.

  Definition get_value (m : chMap pid (chProd public choiceTranscript1)) (i : pid) :=
    match m i with
    | Some (v, _) => otf v
    | _ => 1
    end.

  Canonical finGroup_com_law := Monoid.ComLaw group_prodC.

  Definition compute_key
             (m : chMap pid (chProd public choiceTranscript1))
             (i : pid)
    :=
    let low := \prod_(k <- domm m | (k < i)%ord) (get_value m k) in
    let high := \prod_(k <- domm m | (i < k)%ord) (get_value m k) in
    low * invg high.

  Definition compute_key'
             (m : chMap pid (chProd public choiceTranscript1))
             (i j : pid)
             (x : Secret)
    :=
    if (j < i)%ord then
      let low := \prod_(k <- domm m | (k < i)%ord) (get_value m k) in
      let high := \prod_(k <- domm m | (i < k)%ord) (get_value m k) in
      (g ^+ x) * low * invg high
    else
      let low := \prod_(k <- domm m | (k < i)%ord) (get_value m k) in
      let high := \prod_(k <- domm m | (i < k)%ord) (get_value m k) in
      low * invg (high * (g ^+ x)).

  Lemma compute_key'_equiv
        (i j : pid)
        (x : Secret)
        (zk : choiceTranscript1)
        (keys : chMap pid (chProd public choiceTranscript1)):
    (i != j) →
    compute_key (setm keys j (fto (g ^+ x), zk)) i = compute_key' (remm keys j) i j x.
  Proof.
    intro ij_neq.
    unfold compute_key, compute_key'.
    simpl.
    rewrite <- setm_rem.
    rewrite domm_set domm_rem.
    set X := domm _.
    rewrite !big_fsetU1.
    2-3: subst X; apply not_in_domm.
    rewrite setm_rem.

    have set_rem_eq : forall P x,
      \big[finGroup_com_law/1]_(k <- X :\ j | P k)
        get_value (setm keys j x) k =
      \prod_(k <- X :\ j | P k)
        get_value (remm keys j) k.
    { intros.
      rewrite big_seq_cond.
      rewrite [RHS] big_seq_cond.
      unfold get_value.
      erewrite eq_bigr.
      1: done.
      intros k.
      move => /andP [k_in _].
      simpl.
      rewrite setmE remmE.
      case (k == j) eqn:eq.
      - move: eq => /eqP eq.
        rewrite eq in_fsetD1 in k_in.
        move: k_in => /andP [contra].
        rewrite eq_refl in contra.
        discriminate.
      - reflexivity.
    }

    case (j < i)%ord eqn:e.
    - rewrite !e.
      rewrite -2!mulgA.
      f_equal.
      1: unfold get_value ; by rewrite setmE eq_refl otf_fto.
      f_equal.
      + apply set_rem_eq.
      + rewrite Ord.ltNge Ord.leq_eqVlt in e.
        rewrite negb_or in e.
        move: e => /andP [_ e].
        apply negbTE in e.
        rewrite e.
        f_equal.
        apply set_rem_eq.
    - rewrite e.
      rewrite Ord.ltNge in e.
      apply negbT in e.
      apply negbNE in e.
      rewrite Ord.leq_eqVlt in e.
      move: e => /orP [contra|e].
      1: by rewrite contra in ij_neq.
      rewrite e !invMg.
      f_equal.
      { apply set_rem_eq. }
      rewrite group_prodC.
      f_equal.
      { unfold get_value. by rewrite setmE eq_refl otf_fto. }
      f_equal.
      apply set_rem_eq.
  Qed.

  Lemma compute_key_bij:
    ∀ (m : chMap pid (chProd public choiceTranscript1)) (i j: pid),
      (i != j)%ord →
      exists (a b : nat),
        (a != 0)%N /\ (a < q)%N /\
      (∀ (x : Secret) zk,
        compute_key (setm m j (fto (g ^+ x), zk)) i = g ^+ ((a * x + b) %% q)).
  Proof.
    intros m i j ne.
    simpl.
    pose low := \prod_(k <- domm m :\ j| (k < i)%ord) get_value m k.
    pose hi := \prod_(k <- domm m :\ j| (i < k)%ord) get_value m k.
    have Hlow : exists ilow, low = g ^+ ilow by apply expg_g.
    have Hhi : exists ihi, hi = g ^+ ihi by apply expg_g.
    destruct Hlow as [ilow Hlow].
    destruct Hhi as [ihi Hhi].

    have getv_remm_eq : forall P j m,
      \prod_(k <- domm m :\ j | P k) get_value (remm m j) k =
      \prod_(k <- domm m :\ j | P k) get_value m k.
    {
      clear low hi ilow ihi Hlow Hhi ne i j m.
      intros.
      rewrite big_seq_cond.
      rewrite [RHS] big_seq_cond.
      erewrite eq_bigr.
      1: done.
      intros k.
      move => /andP [k_in _].
      simpl.
      unfold get_value.
      rewrite remmE.
      case (k == j) eqn:eq.
      ++ move: eq => /eqP eq.
          rewrite eq in_fsetD1 in k_in.
          move: k_in => /andP [contra].
          rewrite eq_refl in contra.
          discriminate.
      ++ reflexivity.
    }

    case (j < i)%ord eqn:ij_rel.
    - exists 1%N.
      exists (ilow + (ihi * #[g ^+ ihi].-1))%N.
      do 2 split.
      1: rewrite q_order_g ; apply (prime_gt1 prime_order).
      intros x zk.
      rewrite compute_key'_equiv.
      2: assumption.
      unfold compute_key'.
      simpl.
      rewrite ij_rel.
      rewrite domm_rem.
      set low' := \prod_(k0 <- _ | _) _.
      set hi' := \prod_(k0 <- _ | _) _.
      have -> : low' = low by apply getv_remm_eq.
      have -> : hi' = hi by apply getv_remm_eq.
      clear low' hi'.
      rewrite Hhi Hlow.
      rewrite invg_expg.
      rewrite -!expgM.
      rewrite -!expgD.
      rewrite !addnA.
      rewrite -expg_mod_order.
      f_equal.
      f_equal.
      2: {
        unfold q. rewrite Fp_cast;
        [reflexivity | apply prime_order].
      }
      rewrite mul1n.
      done.
    - exists #[g].-1.
      exists (ilow + (ihi * #[g ^+ ihi].-1))%N.
      repeat split.
      { unfold negb.
        rewrite -leqn0.
        case (#[g].-1 <= 0)%N eqn:e.
        2: done.
        have Hgt1 := (prime_gt1 prime_order).
        rewrite -ltn_predRL in Hgt1.
        rewrite -ltnS in Hgt1.
        rewrite -addn1 in Hgt1.
        rewrite leq_add2l in Hgt1.
        eapply leq_trans in e.
        2: apply Hgt1.
        discriminate.
      }
      {
        rewrite q_order_g.
        rewrite ltn_predL.
        apply (prime_gt0 prime_order).
      }
      intros x zk.
      rewrite compute_key'_equiv.
      2: assumption.
      unfold compute_key'.
      simpl.
      rewrite ij_rel.
      rewrite domm_rem.
      set low' := \prod_(k0 <- _ | _) _.
      set hi' := \prod_(k0 <- _ | _) _.
      have -> : low' = low by apply getv_remm_eq.
      have -> : hi' = hi by apply getv_remm_eq.
      clear low' hi'.
      rewrite Hhi Hlow.
      rewrite invMg.
      rewrite -expgVn.
      rewrite !invg_expg.
      rewrite -!expgM.
      rewrite mulgA.
      rewrite -!expgD.
      rewrite !addnA.
      rewrite -expg_mod_order.
      f_equal.
      f_equal.
      2: {
        unfold q. rewrite Fp_cast;
        [reflexivity | apply prime_order].
      }
      rewrite addnAC.
      rewrite addnC.
      rewrite addnA.
      done.
  Qed.

  Lemma compute_key_set_i
        (i : pid)
        (v : (chProd public choiceTranscript1))
        (m : chMap pid (chProd public choiceTranscript1)):
    compute_key (setm m i v) i = compute_key m i.
  Proof.
    unfold compute_key.
    simpl.
    case (i \in domm m) eqn:i_in.
    all: simpl in i_in.
    - have -> : forall v, domm (setm m i v) = domm m.
      { intros.
        simpl.
        rewrite domm_set.
        rewrite -eq_fset.
        intro k.
        rewrite in_fsetU1.
        case (eq_op) eqn:e.
        + move: e => /eqP ->.
          by rewrite i_in.
        + done.
      }
      simpl.
      f_equal.
      + apply eq_big.
        1: done.
        intros k k_lt.
        unfold get_value.
        rewrite setmE.
        rewrite Ord.lt_neqAle in k_lt.
        move: k_lt => /andP [k_lt _].
        move: k_lt => /negbTE ->.
        done.
      + f_equal.
        apply eq_big.
        1: done.
        intros k k_lt.
        unfold get_value.
        rewrite setmE.
        rewrite Ord.lt_neqAle in k_lt.
        move: k_lt => /andP [k_lt _].
        rewrite eq_sym.
        move: k_lt => /negbTE ->.
        done.
    - have -> : domm m = domm (remm m i).
      {
        simpl.
        rewrite -eq_fset.
        intro k.
        rewrite domm_rem.
        rewrite in_fsetD1.
        case (eq_op) eqn:e.
        + simpl.
          move: e => /eqP ->.
          assumption.
        + done.
      }
      simpl.
      f_equal.
      + rewrite -setm_rem domm_set domm_rem.
        rewrite big_fsetU1.
        all: simpl.
        2: by rewrite in_fsetD1 eq_refl.
        rewrite Ord.ltxx.
        apply eq_big.
        1: done.
        intros k k_lt.
        unfold get_value.
        rewrite setmE remmE.
        rewrite Ord.lt_neqAle in k_lt.
        move: k_lt => /andP [k_lt _].
        move: k_lt => /negbTE ->.
        done.
      + f_equal.
        rewrite -setm_rem domm_set domm_rem.
        rewrite big_fsetU1.
        all: simpl.
        2: by rewrite in_fsetD1 eq_refl.
        rewrite Ord.ltxx.
        apply eq_big.
        1: done.
        intros k k_lt.
        unfold get_value.
        rewrite setmE remmE.
        rewrite Ord.lt_neqAle in k_lt.
        move: k_lt => /andP [k_lt _].
        rewrite eq_sym.
        move: k_lt => /negbTE ->.
        done.
  Qed.

  Lemma test_bij
        (i j : pid)
        (m : chMap pid (chProd public choiceTranscript1))
    :
      (i != j)%N →
      ∃ (f : Secret → Secret),
      ∀ (x : Secret),
        bijective f /\
          (∀ zk, compute_key (setm m j (fto (g ^+ x), zk)) i = g ^+ (f x)).
  Proof.
    simpl.
    intros ne.
    have H := compute_key_bij m i j ne.
    simpl in H.
    destruct H as [a [b [a_pos [a_leq_q H]]]].
    set a_ord := @inZp ((Zp_trunc #[g]).+1) a.
    set b_ord := @inZp ((Zp_trunc #[g]).+1) b.
    pose f' := (fun (x : Secret) => Zp_add (Zp_mul x a_ord) b_ord).
    exists f'.
    unfold f'. clear f'.
    intros x.
    have := q_order_g.
    unfold q.
    intros Hq.
    split.
    2: {
      intro zk.
      rewrite (H x zk).
      apply /eqP.
      rewrite eq_expg_mod_order.
      apply /eqP.
      simpl.
      rewrite modn_small.
      2: {
        rewrite q_order_g.
        apply ltn_pmod.
        apply (prime_gt0 prime_order).
      }
      repeat rewrite -> Zp_cast at 3.
      2-5: apply (prime_gt1 prime_order).
      symmetry.
      rewrite modn_small.
      2: {
        apply ltn_pmod.
        apply (prime_gt0 prime_order).
      }
      simpl.
      unfold q, q'.
      rewrite Fp_cast.
      2: apply prime_order.
      rewrite modnMmr.
      rewrite modnDm.
      rewrite mulnC.
      reflexivity.
    }
    assert (coprime q'.+2 a_ord) as a_ord_coprime.
    {
      rewrite -unitFpE.
      2: rewrite Hq ; apply prime_order.
      rewrite unitfE. simpl.
      rewrite Zp_cast.
      2: apply (prime_gt1 prime_order).
      unfold q, q' in a_leq_q.
      rewrite Fp_cast in a_leq_q.
      2: apply prime_order.
      rewrite modn_small.
      2: apply a_leq_q.
      erewrite <- inj_eq.
      2: apply ord_inj.
      rewrite val_Zp_nat.
      2: {
        rewrite pdiv_id.
        1: apply prime_gt1.
        1,2: rewrite Hq ; apply prime_order.
      }
      rewrite -> pdiv_id at 1.
      1,2: rewrite Hq.
      2: apply prime_order.
      unfold q in a_leq_q.
      rewrite modn_small.
      2: apply a_leq_q.
      assumption.
    }
    pose f' := (fun (x : Secret) => Zp_mul (Zp_add (Zp_opp b_ord) x) (Zp_inv a_ord)).
    exists f'.
    - intro z.
      unfold f'. clear f'.
      simpl.
      rewrite Zp_addC.
      rewrite -Zp_addA.
      have -> : (Zp_add b_ord (Zp_opp b_ord)) = Zp0.
      1: by rewrite Zp_addC Zp_addNz.
      rewrite Zp_addC.
      rewrite Zp_add0z.
      rewrite -Zp_mulA.
      rewrite Zp_mulzV.
      2: {
        rewrite -> q_field at 1.
        assumption.
      }
      rewrite Zp_mulz1.
      reflexivity.
    - intro z.
      unfold f'. clear f'.
      simpl.
      rewrite Zp_addC.
      rewrite -Zp_mulA.
      rewrite Zp_mul_addl.
      have -> : (Zp_mul (Zp_inv a_ord) a_ord) = Zp1.
      {
        rewrite Zp_mulC.
        rewrite Zp_mulzV.
        + reflexivity.
        + rewrite -> q_field at 1.
          assumption.
      }
      rewrite -Zp_mul_addl.
      rewrite Zp_mulz1.
      rewrite Zp_addA.
      have -> : (Zp_add b_ord (Zp_opp b_ord)) = Zp0.
      1: by rewrite Zp_addC Zp_addNz.
      rewrite Zp_add0z.
      reflexivity.
  Qed.

  Lemma test_bij'
        (i j : pid)
        (m : chMap pid (chProd public choiceTranscript1))
    :
      (i != j)%N →
      ∃ (f : secret → secret),
      ∀ (x : secret),
        bijective f /\
          (∀ zk, compute_key (setm m j (fto (g ^+ otf x), zk)) i = g ^+ (otf (f x))).
  Proof.
    simpl.
    intros ne.
    have [f H] := test_bij i j m ne.
    simpl in H.
    exists (fun (x : secret) => fto (f (otf x))).
    intro x.
    destruct (H (otf x)) as [f_bij H'] ; clear H.
    split.
    - exists (fun z => fto ((finv f) (otf z))).
      + apply bij_inj in f_bij.
        intro z.
        rewrite otf_fto.
        apply finv_f in f_bij.
        rewrite f_bij fto_otf.
        reflexivity.
      + apply bij_inj in f_bij.
        intro z.
        rewrite otf_fto.
        apply f_finv in f_bij.
        rewrite f_bij fto_otf.
        reflexivity.
    - intro zk.
      specialize (H' zk).
      rewrite otf_fto.
      apply H'.
  Qed.

  Definition P_i_E :=
    [interface
      #val #[ INIT ] : 'unit → 'public_key ;
      #val #[ CONSTRUCT ] : 'public_keys → 'unit ;
      #val #[ VOTE ] : 'bool → 'public
    ].

  Definition Sigma1_I :=
    [interface
      #val #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool ;
      #val #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1
    ].

  Definition P_i (i : pid) (b : bool):
    package (P_i_locs i)
      Sigma1_I
      P_i_E :=
    [package
        #def #[ INIT ] (_ : 'unit) : 'public_key
        {
          #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
          #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
          x ← sample uniform i_secret ;;
          #put (skey_loc i) := x ;;
          let y := (fto (g ^+ (otf x))) : public in
            zkp ← ZKP (y, x) ;;
            ret (y, zkp)
        }
        ;
        #def #[ CONSTRUCT ] (m : 'public_keys) : 'unit
        {
          #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
          #assert (size (domm m) == n) ;;
          let key := fto (compute_key m i) in
          #put (ckey_loc i) := key ;;
          @ret 'unit Datatypes.tt
        }
        ;
        #def #[ VOTE ] (v : 'bool) : 'public
        {
          skey ← get (skey_loc i) ;;
          ckey ← get (ckey_loc i) ;;
          if b then
            let vote := (otf ckey ^+ skey * g ^+ v) in
            @ret 'public (fto vote)
          else
            let vote := (otf ckey ^+ skey * g ^+ (negb v)) in
            @ret 'public (fto vote)
        }
    ].

  Definition EXEC_i_I :=
    [interface
      #val #[ INIT ] : 'unit → 'public_key ;
      #val #[ CONSTRUCT ] : 'public_keys → 'unit ;
      #val #[ VOTE ] : 'bool → 'public ;
      #val #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1
    ].

  Definition Exec_i_E i := [interface #val #[ Exec i ] : 'bool → 'public].

  Definition Exec_i (i j : pid) (m : chMap pid (chProd public choiceTranscript1)):
    package fset0
      EXEC_i_I
      (Exec_i_E i)
    :=
    [package
        #def #[ Exec i ] (v : 'bool) : 'public
        {
          #import {sig #[ INIT ] : 'unit → 'public_key} as Init ;;
          #import {sig #[ CONSTRUCT ] : 'public_keys → 'unit} as Construct ;;
          #import {sig #[ VOTE ] : 'bool → 'public} as Vote ;;
          #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
          pk ← Init Datatypes.tt ;;
          x ← sample uniform i_secret ;;
          let y := (fto (g ^+ (otf x))) : public in
            zkp ← ZKP (y, x) ;;
            let m' := setm (setm m j (y, zkp)) i pk in
              Construct m' ;;
              vote ← Vote v ;;
              @ret 'public vote
        }
    ].

  Module DDHParams <: DDHParams.
    Definition Space := Secret.
    Definition Space_pos := Secret_pos.
  End DDHParams.

  Module DDH := DDH DDHParams GP.

  #[tactic=notac] Equations? Aux (b : bool) (i j : pid) m f':
    package DDH.DDH_locs
      (DDH.DDH_E :|:
         [interface #val #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1]
      )
      [interface #val #[ Exec i ] : 'bool → 'public]
    := Aux b i j m f' :=
    [package
        #def #[ Exec i ] (v : 'bool) : 'public
        {
          #import {sig #[ DDH.SAMPLE ] : 'unit → 'public × 'public × 'public} as DDH ;;
          #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
          abc ← DDH Datatypes.tt ;;
          x_i ← get DDH.secret_loc1 ;;
          x_j ← get DDH.secret_loc2 ;;
          let '(y_i, (y_j, c)) := abc in
          let y_j' := fto (g ^+ ((finv f') x_j)) in
            zkp1 ← ZKP (y_i, x_i) ;;
            zkp2 ← ZKP (y_j', (finv f') x_j) ;;
            let m' := (setm (setm m j (y_j', zkp2)) i (y_i, zkp1)) in
            #assert (size (domm m') == n) ;;
              @ret 'public (fto ((otf c) *  g ^+ (if b then v else (negb v))))
        }
    ].
  Proof.
    ssprove_valid.
    all: rewrite in_fsetU.
    all: apply /orP.
    {
      left.
      unfold DDH.DDH_E.
      rewrite fset_cons -fset0E fsetU0.
      by apply /fset1P.
    }
    {
      right.
      rewrite fset_cons -fset0E fsetU0.
      by apply /fset1P.
    }
    {
      right.
      rewrite fset_cons -fset0E fsetU0.
      by apply /fset1P.
    }
  Qed.

  Module RO1 := Sigma1.Sigma.Oracle.
  Module RO2 := Sigma2.Oracle.

  Definition combined_locations :=
    (Sigma1.MyAlg.Sigma_locs :|: RO1.RO_locs).

  Equations? Exec_i_realised b m (i j : pid) : package (P_i_locs i :|: combined_locations) [interface] (Exec_i_E i) :=
    Exec_i_realised b m i j :=
      {package (Exec_i i j m) ∘ (par ((P_i i b) ∘ (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO))
                                      (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO))}.
  Proof.
    ssprove_valid.
    10: apply fsub0set.
    8:{ rewrite fsetUid. apply fsubsetxx. }
    9: apply fsubsetxx.
    7:{ erewrite fsetUid. apply fsubsetxx. }
    4: apply fsubsetUr.
    3: apply fsubsetUl.
    all: unfold combined_locations.
    - apply fsubsetUl.
    - apply fsubsetUr.
    - eapply fsubset_trans. 2: eapply fsubsetUr.
      apply fsubsetUl.
    - eapply fsubset_trans. 2: eapply fsubsetUr.
      apply fsubsetUr.
    - unfold EXEC_i_I, P_i_E, Sigma1_I.
      rewrite !fset_cons.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      rewrite -fset0E fsetU0 fset0U.
      apply fsubsetUr.
  Qed.


  Lemma loc_helper_commit i:
    Sigma1.MyAlg.commit_loc \in P_i_locs i :|: combined_locations.
  Proof.
    unfold combined_locations.
    unfold Sigma1.MyAlg.Sigma_locs.
    rewrite in_fsetU.
    apply /orP ; right.
    rewrite fset_cons.
    rewrite in_fsetU.
    apply /orP ; left.
    rewrite in_fsetU1.
    apply /orP ; left.
    done.
  Qed.

  Lemma loc_helper_queries i:
    RO1.queries_loc \in P_i_locs i :|: combined_locations.
  Proof.
    unfold combined_locations.
    unfold RO1.RO_locs.
    rewrite in_fsetU.
    apply /orP ; right.
    rewrite fset_cons.
    rewrite in_fsetU.
    apply /orP ; right.
    rewrite in_fsetU1.
    apply /orP ; left.
    done.
  Qed.

  Lemma loc_helper_skey i:
    skey_loc i \in P_i_locs i :|: combined_locations.
  Proof.
    unfold P_i_locs.
    rewrite in_fsetU.
    apply /orP ; left.
    rewrite fset_cons.
    rewrite in_fsetU1.
    apply /orP ; left.
    done.
  Qed.

  Lemma loc_helper_ckey i:
    ckey_loc i \in P_i_locs i :|: combined_locations.
  Proof.
    unfold P_i_locs.
    rewrite in_fsetU.
    apply /orP ; left.
    rewrite !fset_cons.
    rewrite in_fsetU1.
    apply /orP ; right.
    rewrite in_fsetU1.
    apply /orP ; left.
    done.
  Qed.

  #[local] Hint Resolve loc_helper_commit : loc_db.
  #[local] Hint Resolve loc_helper_queries : loc_db.
  #[local] Hint Resolve loc_helper_skey: loc_db.
  #[local] Hint Resolve loc_helper_ckey: loc_db.

  #[program] Definition Exec_i_realised_code m (i j : pid) (vote : 'bool):
    code (P_i_locs i :|: combined_locations) [interface] 'public :=
    {code
     x ← sample uniform i_secret ;;
     #put skey_loc i := x ;;
     #assert Sigma1.MyParam.R (otf (fto (expgn_rec (T:=gT) g (otf x)))) (otf x) ;;
     x1 ← sample uniform Sigma1.MyAlg.i_witness ;;
     #put Sigma1.MyAlg.commit_loc := x1 ;;
     x2 ← get RO1.queries_loc ;;
     match x2 (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)))) with
     | Some a =>
         v ← get Sigma1.MyAlg.commit_loc ;;
         x3 ← sample uniform i_secret ;;
         #assert Sigma1.MyParam.R (otf (fto (expgn_rec (T:=gT) g (otf x3)))) (otf x3) ;;
         x5 ← sample uniform Sigma1.MyAlg.i_witness ;;
         #put Sigma1.MyAlg.commit_loc := x5 ;;
         v0 ← get RO1.queries_loc ;;
         match v0 (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)))) with
         | Some a0 =>
             x6 ← get Sigma1.MyAlg.commit_loc ;;
             let x4 :=
             (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)), a0, fto (Zp_add (otf x6) (Zp_mul (otf a0) (otf x3))))
             in
         #assert eqn
                    (size
                       (domm (T:=[ordType of 'I_#|'I_n|]) (S:='I_#|gT| * ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|))
                          (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                             (fto (expgn_rec (T:=gT) g (otf x)),
                             (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a, fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))))) n ;;
          #put ckey_loc i := fto
                              (compute_key
                                 (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                                    (fto (expgn_rec (T:=gT) g (otf x)),
                                    (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a,
                                    fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))) i) ;;
         v0 ← get skey_loc i ;;
         v1 ← get ckey_loc i ;;
         @ret 'public (fto (expgn_rec (T:=gT) (otf v1) v0 * expgn_rec (T:=gT) g vote))
         | None =>
             a0 ← sample uniform RO1.i_random ;;
             #put RO1.queries_loc := setm v0
                                      (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)))) a0 ;;
             x6 ← get Sigma1.MyAlg.commit_loc ;;
             let x4 := (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)), a0, fto (Zp_add (otf x6) (Zp_mul (otf a0) (otf x3)))) in
         #assert eqn
                    (size
                       (domm (T:=[ordType of 'I_#|'I_n|]) (S:='I_#|gT| * ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|))
                          (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                             (fto (expgn_rec (T:=gT) g (otf x)),
                             (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a, fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))))) n ;;
          #put ckey_loc i := fto
                              (compute_key
                                 (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                                    (fto (expgn_rec (T:=gT) g (otf x)),
                                    (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a,
                                    fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))) i) ;;
         v0 ← get skey_loc i ;;
         v1 ← get ckey_loc i ;;
         @ret 'public (fto (expgn_rec (T:=gT) (otf v1) v0 * expgn_rec (T:=gT) g vote))
         end
     | None =>
         a ← sample uniform RO1.i_random ;;
         #put RO1.queries_loc := setm x2
                                  (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)))) a ;;
         v ← get Sigma1.MyAlg.commit_loc ;;
         x3 ← sample uniform i_secret ;;
         #assert Sigma1.MyParam.R (otf (fto (expgn_rec (T:=gT) g (otf x3)))) (otf x3) ;;
         x5 ← sample uniform Sigma1.MyAlg.i_witness ;;
         #put Sigma1.MyAlg.commit_loc := x5 ;;
         v0 ← get RO1.queries_loc ;;
         match v0 (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)))) with
         | Some a0 =>
             x6 ← get Sigma1.MyAlg.commit_loc ;;
             let x4 := (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)), a0, fto (Zp_add (otf x6) (Zp_mul (otf a0) (otf x3)))) in
             #assert eqn
                 (size
                 (domm (T:=[ordType of 'I_#|'I_n|]) (S:='I_#|gT| * ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|))
                         (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                             (fto (expgn_rec (T:=gT) g (otf x)),
                                 (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a, fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))))) n ;;
             #put ckey_loc i := fto
                                 (compute_key
                                     (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                                             (fto (expgn_rec (T:=gT) g (otf x)),
                                             (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a,
                                                 fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))) i) ;;
            v0 ← get skey_loc i ;;
            v1 ← get ckey_loc i ;;
            @ret 'public (fto (expgn_rec (T:=gT) (otf v1) v0 * expgn_rec (T:=gT) g vote))
        | None =>
                   a0 ← sample uniform RO1.i_random ;;
                   #put RO1.queries_loc := setm v0
                                            (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)))) a0 ;;
                   x6 ← get Sigma1.MyAlg.commit_loc ;;
                   let x4 := (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)), a0, fto (Zp_add (otf x6) (Zp_mul (otf a0) (otf x3)))) in
         #assert eqn
                    (size
                       (domm (T:=[ordType of 'I_#|'I_n|]) (S:='I_#|gT| * ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|))
                          (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                             (fto (expgn_rec (T:=gT) g (otf x)),
                             (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a, fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))))) n ;;
          #put ckey_loc i := fto
                              (compute_key
                                 (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                                    (fto (expgn_rec (T:=gT) g (otf x)),
                                    (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a,
                                    fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))) i) ;;
         v0 ← get skey_loc i ;;
         v1 ← get ckey_loc i ;;
         @ret 'public (fto (expgn_rec (T:=gT) (otf v1) v0 * expgn_rec (T:=gT) g vote))
               end
     end
    }.
  Next Obligation.
    intros.
    ssprove_valid ; auto with loc_db.
    destruct (v1 _) ; ssprove_valid ; auto with loc_db.
    - destruct (v5 _) ; ssprove_valid ; auto with loc_db.
    - destruct (v6 _) ; ssprove_valid ; auto with loc_db.
  Qed.

  #[program] Definition Exec_i_realised_code_runnable m (i j : pid) (vote : 'bool):
    code (P_i_locs i :|: combined_locations) [interface] 'public :=
    {code
     x ← sample uniform i_secret ;;
     #put skey_loc i := x ;;
     #assert Sigma1.MyParam.R (otf (fto (expgn_rec (T:=gT) g (otf x)))) (otf x) ;;
     x1 ← sample uniform Sigma1.MyAlg.i_witness ;;
     #put Sigma1.MyAlg.commit_loc := x1 ;;
     x2 ← get RO1.queries_loc ;;
         a ← sample uniform RO1.i_random ;;
         #put RO1.queries_loc := setm x2
                                  (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)))) a ;;
         v ← get Sigma1.MyAlg.commit_loc ;;
         x3 ← sample uniform i_secret ;;
         #assert Sigma1.MyParam.R (otf (fto (expgn_rec (T:=gT) g (otf x3)))) (otf x3) ;;
         x5 ← sample uniform Sigma1.MyAlg.i_witness ;;
         #put Sigma1.MyAlg.commit_loc := x5 ;;
         v0 ← get RO1.queries_loc ;;
                   a0 ← sample uniform RO1.i_random ;;
                   #put RO1.queries_loc := setm v0
                                            (Sigma1.Sigma.prod_assoc (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)))) a0 ;;
                   x6 ← get Sigma1.MyAlg.commit_loc ;;
                   let x4 := (fto (expgn_rec (T:=gT) g (otf x3)), fto (expgn_rec (T:=gT) g (otf x5)), a0, fto (Zp_add (otf x6) (Zp_mul (otf a0) (otf x3)))) in
         #assert eqn
                    (size
                       (domm (T:=[ordType of 'I_#|'I_n|]) (S:='I_#|gT| * ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|))
                          (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                             (fto (expgn_rec (T:=gT) g (otf x)),
                             (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a, fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))))) n ;;
          #put ckey_loc i := fto
                              (compute_key
                                 (setm (T:=[ordType of 'I_#|'I_n|]) (setm (T:=[ordType of 'I_#|'I_n|]) m j (fto (expgn_rec (T:=gT) g (otf x3)), x4)) i
                                    (fto (expgn_rec (T:=gT) g (otf x)),
                                    (fto (expgn_rec (T:=gT) g (otf x)), fto (expgn_rec (T:=gT) g (otf x1)), a,
                                    fto (Zp_add (otf v) (Zp_mul (otf a) (otf x)))))) i) ;;
         v0 ← get skey_loc i ;;
         v1 ← get ckey_loc i ;;
         @ret 'public (fto (expgn_rec (T:=gT) (otf v1) v0 * expgn_rec (T:=gT) g vote))
    }.
  Next Obligation.
    intros.
    ssprove_valid ; auto with loc_db.
  Qed.

  Lemma code_pkg_equiv m i j (vote : 'bool):
    ⊢
    ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    get_op_default (Exec_i_realised true m i j) ((Exec i), ('bool, 'public)) vote
    ≈
    Exec_i_realised_code m i j vote
    ⦃ eq ⦄.
  Proof.
    unfold Exec_i_realised.
    rewrite get_op_default_link.
    erewrite get_op_default_spec.
    2: {
      cbn.
      rewrite eqnE eq_refl.
      done.
    }
    ssprove_code_simpl.
    simpl.
    repeat choice_type_eqP_handle.
    rewrite !cast_fun_K.
    ssprove_code_simpl.
    simpl.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    simpl.
    ssprove_sync_eq=>x.
    simpl.
    ssprove_code_simpl_more.
    ssprove_sync_eq.
    ssprove_sync_eq=>rel1.
    ssprove_sync_eq=>r1.
    ssprove_sync_eq.

    (* ssprove_sync_eq=>queries.
    destruct (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ otf x), fto (g ^+ otf r1)))) eqn:e.
    all: rewrite e.
    - simpl.
      ssprove_code_simpl.
      ssprove_sync_eq=>?. *)
  Admitted.

  #[tactic=notac] Equations? Aux_realised (b : bool) (i j : pid) m f' :
    package (DDH.DDH_locs :|: P_i_locs i :|: combined_locations) Game_import [interface #val #[ Exec i ] : 'bool → 'public] :=
    Aux_realised b i j m f' := {package Aux b i j m f' ∘ (par DDH.DDH_real (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) }.
  Proof.
    ssprove_valid.
    4:{ rewrite fsetUid. rewrite -fset0E. apply fsub0set. }
    6: apply fsubsetxx.
    3:{ rewrite -fsetUA. apply fsubsetxx. }
    4:{ rewrite -fsetUA. apply fsubsetUl. }
    all: unfold combined_locations.
    - eapply fsubset_trans. 2: apply fsubsetUr.
      apply fsubsetUl.
    - eapply fsubset_trans. 2: apply fsubsetUr.
      apply fsubsetUr.
    - unfold DDH.DDH_E.
      apply fsetUS.
      rewrite !fset_cons.
      apply fsubsetUr.
  Qed.

  #[tactic=notac] Equations? Aux_ideal_realised (b : bool) (i j : pid) m f' :
    package (DDH.DDH_locs :|: P_i_locs i :|: combined_locations) Game_import [interface #val #[ Exec i ] : 'bool → 'public] :=
    Aux_ideal_realised b i j m f' := {package Aux b i j m f' ∘ (par DDH.DDH_ideal (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) }.
  Proof.
    ssprove_valid.
    4:{ rewrite fsetUid. rewrite -fset0E. apply fsub0set. }
    6: apply fsubsetxx.
    3:{ rewrite -fsetUA. apply fsubsetxx. }
    4:{ rewrite -fsetUA. apply fsubsetUl. }
    all: unfold combined_locations.
    - eapply fsubset_trans. 2: apply fsubsetUr.
      apply fsubsetUl.
    - eapply fsubset_trans. 2: apply fsubsetUr.
      apply fsubsetUr.
    - unfold DDH.DDH_E.
      apply fsetUS.
      rewrite !fset_cons.
      apply fsubsetUr.
  Qed.

  Notation inv i := (heap_ignore (P_i_locs i :|: DDH.DDH_locs)).

  #[local] Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  (** We extend swapping to schemes.
    This means that the ssprove_swap tactic will be able to swap any command
    with a scheme without asking a proof from the user.
  *)
  #[local] Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
    eapply r_swap_scheme_cmd ; ssprove_valid
    : ssprove_swap.

  Lemma P_i_aux_equiv (i j : pid) m:
    fdisjoint Sigma1.MyAlg.Sigma_locs DDH.DDH_locs →
    i != j →
    (∃ f,
      bijective f ∧
      (∀ b, (Exec_i_realised b m i j) ≈₀ Aux_realised b i j m f)).
  Proof.
    intros Hdisj ij_neq.
    have [f' Hf] := test_bij' i j m ij_neq.
    simpl in Hf.
    exists f'.
    split.
    {
      assert ('I_#|'Z_#[g]|) as x.
      { rewrite card_ord.
        eapply Ordinal.
        rewrite ltnS.
        apply ltnSn.
      }
      specialize (Hf x).
      destruct Hf.
      assumption.
    }
    intro b.
    eapply eq_rel_perf_ind with (inv := inv i).
    {
      ssprove_invariant.
      rewrite -!fsetUA.
      apply fsetUS.
      do 2 (apply fsubsetU ; apply /orP ; right).
      apply fsubsetUl.
    }
    simplify_eq_rel v.
    rewrite !setmE.
    rewrite !eq_refl.
    ssprove_code_simpl.
    repeat simplify_linking.
    ssprove_sync => x_i.

    rewrite !cast_fun_K.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    
    ssprove_swap_seq_rhs [:: 4 ; 5 ; 6 ; 7]%N.
    ssprove_swap_seq_rhs [:: 2 ; 3 ; 4 ; 5 ; 6]%N.
    ssprove_swap_seq_rhs [:: 0 ; 1 ; 2 ; 3 ; 4 ; 5]%N.
    ssprove_contract_put_get_rhs.
    apply r_put_rhs.
    ssprove_swap_seq_lhs [:: 0 ; 1 ; 2 ; 3]%N.
    unfold Sigma1.MyParam.R.
    have Hord : ∀ x, (nat_of_ord x) = (nat_of_ord (otf x)).
    {
      unfold otf.
      intros n x.
      rewrite enum_val_ord.
      done.
    }
    rewrite -Hord otf_fto eq_refl.
    simpl.
    ssprove_sync => r_i.
    apply r_put_vs_put.
    ssprove_restore_pre.
    { ssprove_invariant.
      apply preserve_update_r_ignored_heap_ignore.
      - unfold DDH.DDH_locs.
        rewrite in_fsetU.
        apply /orP ; right.
        rewrite fset_cons.
        rewrite in_fsetU.
        apply /orP ; left.
        by apply /fset1P.
      - apply preserve_update_mem_nil.
    }
    ssprove_sync.
    ssprove_swap_seq_lhs [:: 0 ]%N.
    ssprove_swap_seq_rhs [:: 2 ; 1 ; 0]%N.
    ssprove_sync => queries.
    destruct (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ x_i), fto (g ^+ otf r_i)))) eqn:e.
    all: rewrite e; simpl.
    all: ssprove_code_simpl_more.
    - ssprove_swap_seq_lhs [:: 0 ; 1 ; 2 ; 3 ; 4 ; 5]%N.
      ssprove_swap_seq_lhs [:: 0 ; 1 ]%N.
      eapply r_uniform_bij.
      { apply Hf.
        + rewrite card_ord.
          rewrite Zp_cast.
          2: apply (prime_gt1 prime_order).
          eapply Ordinal.
          apply (prime_gt1 prime_order).
      }
      intro x.
      specialize (Hf x).
      destruct Hf as [bij_f Hf].
      apply bij_inj in bij_f.
      apply finv_f in bij_f.
      ssprove_contract_put_get_rhs.
      rewrite bij_f.
      rewrite -Hord !otf_fto !eq_refl.
      simpl.
      apply r_put_rhs.
      ssprove_restore_pre.
      {
        apply preserve_update_r_ignored_heap_ignore.
        - unfold DDH.DDH_locs.
          rewrite !fset_cons.
          rewrite !in_fsetU.
          apply /orP ; right.
          apply /orP ; right.
          apply /orP ; left.
          by apply /fset1P.
        - apply preserve_update_mem_nil.
      }
      apply r_get_remember_lhs.
      intros ?.
      apply r_get_remember_rhs.
      intros ?.
      ssprove_forget_all.
      ssprove_sync=>r_j.
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      clear e queries.
      ssprove_sync.
      ssprove_swap_seq_lhs [:: 0]%N.
      ssprove_sync=>queries.
      destruct (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ x), fto (g ^+ otf r_j)))) eqn:e.
      all: rewrite e.
      all: ssprove_code_simpl.
      all: ssprove_code_simpl_more.
      + ssprove_swap_seq_lhs [:: 0 ; 1]%N.
        simpl.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_swap_lhs 1%N.
        {
          move: H0 => /eqP.
          erewrite eqn_add2r.
          intros contra.
          discriminate.
        }
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_restore_pre.
        {
          repeat apply preserve_update_l_ignored_heap_ignore.
          1,2: unfold P_i_locs ; rewrite in_fsetU.
          1,2: apply /orP ; left ; rewrite !fset_cons ;
               rewrite -fset0E fsetU0 ; rewrite in_fsetU.
          - apply /orP ; right.
            by apply /fset1P.
          - apply /orP ; left.
            by apply /fset1P.
          - apply preserve_update_mem_nil.
        }
        rewrite otf_fto.
        rewrite compute_key_set_i.
        set zk := (fto (g ^+ x), fto (g ^+ otf r_j), s1, fto (otf x2 + otf s1 * otf x)).
        clearbody zk.
        specialize (Hf zk).
        rewrite !Hord.
        rewrite Hf.
        rewrite -!Hord.
        rewrite -expgM.
        rewrite mulnC.
        case b; apply r_ret ; done.
      + ssprove_swap_seq_lhs [:: 0 ; 1 ; 2 ; 3]%N.
        simpl.
        ssprove_sync=>e_j.
        apply r_put_vs_put.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_swap_lhs 1%N.
        {
          move: H0 => /eqP.
          erewrite eqn_add2r.
          intros contra.
          discriminate.
        }
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_restore_pre.
        {
          repeat apply preserve_update_l_ignored_heap_ignore.
          1,2: unfold P_i_locs ; rewrite in_fsetU.
          1,2: apply /orP ; left ; rewrite !fset_cons ;
               rewrite -fset0E fsetU0 ; rewrite in_fsetU.
          - apply /orP ; right.
            by apply /fset1P.
          - apply /orP ; left.
            by apply /fset1P.
          - ssprove_invariant.
        }
        rewrite otf_fto.
        rewrite compute_key_set_i.
        set zk := (fto (g ^+ x), fto (g ^+ otf r_j), e_j, fto (otf x2 + otf e_j * otf x)).
        clearbody zk.
        specialize (Hf zk).
        rewrite !Hord.
        rewrite Hf.
        rewrite -!Hord.
        rewrite -expgM.
        rewrite mulnC.
        case b; apply r_ret ; done.
    - ssprove_swap_seq_lhs [:: 0 ; 1 ; 2 ; 3 ; 4 ; 5  ; 6 ; 7]%N.
      ssprove_swap_seq_lhs [:: 2 ; 1 ; 0 ]%N.
      eapply r_uniform_bij.
      { apply Hf.
        + rewrite card_ord.
          rewrite Zp_cast.
          2: apply (prime_gt1 prime_order).
          eapply Ordinal.
          apply (prime_gt1 prime_order).
      }
      intro x.
      specialize (Hf x).
      destruct Hf as [bij_f Hf].
      apply bij_inj in bij_f.
      apply finv_f in bij_f.
      ssprove_contract_put_get_rhs.
      rewrite bij_f.
      rewrite -Hord !otf_fto !eq_refl.
      simpl.
      apply r_put_rhs.
      ssprove_restore_pre.
      {
        apply preserve_update_r_ignored_heap_ignore.
        - unfold DDH.DDH_locs.
          rewrite !fset_cons.
          rewrite !in_fsetU.
          apply /orP ; right.
          apply /orP ; right.
          apply /orP ; left.
          by apply /fset1P.
        - apply preserve_update_mem_nil.
      }
      ssprove_sync=>e_i.
      apply r_put_vs_put.
      apply r_get_remember_lhs.
      intros ?.
      apply r_get_remember_rhs.
      intros ?.
      ssprove_forget_all.
      rewrite -Hord eq_refl.
      simpl.
      ssprove_sync=>r_j.
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      clear e queries.
      ssprove_sync.
      ssprove_swap_seq_lhs [:: 0]%N.
      ssprove_sync=>queries.
      destruct (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ x), fto (g ^+ otf r_j)))) eqn:e.
      all: rewrite e.
      all: ssprove_code_simpl.
      all: ssprove_code_simpl_more.
      + ssprove_swap_seq_lhs [:: 0 ; 1]%N.
        simpl.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_swap_lhs 1%N.
        {
          move: H0 => /eqP.
          erewrite eqn_add2r.
          intros contra.
          discriminate.
        }
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_restore_pre.
        {
          repeat apply preserve_update_l_ignored_heap_ignore.
          1,2: unfold P_i_locs ; rewrite in_fsetU.
          1,2: apply /orP ; left ; rewrite !fset_cons ;
               rewrite -fset0E fsetU0 ; rewrite in_fsetU.
          - apply /orP ; right.
            by apply /fset1P.
          - apply /orP ; left.
            by apply /fset1P.
          - apply preserve_update_mem_nil.
        }
        rewrite otf_fto.
        rewrite compute_key_set_i.
        set zk := (fto (g ^+ x), fto (g ^+ otf r_j), s, fto (otf x2 + otf s * otf x)).
        clearbody zk.
        specialize (Hf zk).
        rewrite !Hord.
        rewrite Hf.
        rewrite -!Hord.
        rewrite -expgM.
        rewrite mulnC.
        case b; apply r_ret ; done.
      + ssprove_swap_seq_lhs [:: 0 ; 1 ; 2 ; 3]%N.
        simpl.
        ssprove_sync=>e_j.
        apply r_put_vs_put.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_swap_lhs 1%N.
        {
          move: H0 => /eqP.
          erewrite eqn_add2r.
          intros contra.
          discriminate.
        }
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_contract_put_get_lhs.
        apply r_put_lhs.
        ssprove_restore_pre.
        {
          repeat apply preserve_update_l_ignored_heap_ignore.
          1,2: unfold P_i_locs ; rewrite in_fsetU.
          1,2: apply /orP ; left ; rewrite !fset_cons ;
               rewrite -fset0E fsetU0 ; rewrite in_fsetU.
          - apply /orP ; right.
            by apply /fset1P.
          - apply /orP ; left.
            by apply /fset1P.
          - ssprove_invariant.
        }
        rewrite otf_fto.
        rewrite compute_key_set_i.
        set zk := (fto (g ^+ x), fto (g ^+ otf r_j), e_j, fto (otf x2 + otf e_j * otf x)).
        clearbody zk.
        specialize (Hf zk).
        rewrite !Hord.
        rewrite Hf.
        rewrite -!Hord.
        rewrite -expgM.
        rewrite mulnC.
        case b; apply r_ret ; done.
  Qed.

  Lemma Hord (x : secret): (nat_of_ord x) = (nat_of_ord (otf x)).
  Proof.
      unfold otf.
      rewrite enum_val_ord.
      done.
  Qed.

  Lemma vote_hiding_bij (c : secret) (v : bool):
    fto (otf (fto (g ^+ c)) * g ^+ v) =
      fto
        (otf (fto (g ^+ (if v then fto (Zp_add (otf c) Zp1) else fto (Zp_add (otf c) (Zp_opp Zp1))))) *
           g ^+ (~~ v)).
  Proof.
    f_equal.
    rewrite !otf_fto.
    rewrite -!expgD.
    have h' : ∀ (x : Secret), nat_of_ord x = (nat_of_ord (fto x)).
    {
        unfold fto.
        intros k.
        rewrite enum_rank_ord.
        done.
    }
    case v.
    ++ apply /eqP.
       rewrite eq_expg_mod_order.
       rewrite addn0.
       have h : ∀ (x : secret), (((nat_of_ord x) + 1) %% q'.+2)%N = (nat_of_ord (Zp_add (otf x) Zp1)).
       {
         intro k.
         unfold Zp_add.
         simpl.
         rewrite -Hord.
         apply /eqP.
         rewrite eq_sym.
         apply /eqP.
         rewrite -> Zp_cast at 2.
         2: apply (prime_gt1 prime_order).
         rewrite -> Zp_cast at 1.
         2: apply (prime_gt1 prime_order).
         rewrite modnDmr.
         rewrite Fp_cast.
         2: apply prime_order.
         reflexivity.
       }
       rewrite -h'.
       rewrite -h.
       rewrite -modn_mod.
       rewrite Fp_cast.
       2: apply prime_order.
       1: apply eq_refl.
    ++ apply /eqP.
       rewrite eq_expg_mod_order.
       rewrite addn0.
       unfold Zp_add, Zp_opp, Zp1.
       simpl.
       repeat rewrite -> Zp_cast at 12.
       2-4: apply (prime_gt1 prime_order).
       rewrite -!Hord.
       have -> : (#[g] - 1 %% #[g])%N = #[g].-1.
       { rewrite modn_small.
         2: apply (prime_gt1 prime_order).
         by rewrite -subn1.
       }
       rewrite modn_small.
       2:{
         destruct c as [c Hc].
         move: Hc.
         simpl.
         unfold DDH.i_space, DDHParams.Space, Secret.
         rewrite card_ord.
         rewrite Zp_cast.
         2: apply (prime_gt1 prime_order).
         done.
       }
       have -> : (#[g].-1 %% #[g])%N = #[g].-1.
       {
         rewrite modn_small.
         1: reflexivity.
         apply ltnSE.
         rewrite -subn1 -2!addn1.
         rewrite subnK.
         2: apply (prime_gt0 prime_order).
         rewrite addn1.
         apply ltnSn.
       }
       rewrite -h'.
       simpl.
       rewrite -> Zp_cast at 9.
       2: apply (prime_gt1 prime_order).
       rewrite modnDml.
       rewrite -subn1.
       rewrite -addnA.
       rewrite subnK.
       2: apply (prime_gt0 prime_order).
       rewrite -modnDmr.
       rewrite modnn.
       rewrite addn0.
       rewrite modn_small.
       1: apply eq_refl.
       destruct c as [h Hc].
       move: Hc.
       unfold DDH.i_space, DDHParams.Space, Secret.
       simpl.
       rewrite card_ord.
       rewrite Zp_cast.
       2: apply (prime_gt1 prime_order).
       done.
  Qed.

  Lemma vote_hiding (i j : pid) m:
    i != j →
    ∀ LA A ϵ_DDH,
      ValidPackage LA [interface #val #[ Exec i ] : 'bool → 'public] A_export A →
      fdisjoint Sigma1.MyAlg.Sigma_locs DDH.DDH_locs →
      fdisjoint LA DDH.DDH_locs →
      fdisjoint LA (P_i_locs i) →
      fdisjoint LA combined_locations →
      (∀ D, DDH.ϵ_DDH D <= ϵ_DDH) →
    AdvantageE (Exec_i_realised true m i j) (Exec_i_realised false m i j) A <= ϵ_DDH + ϵ_DDH.
  Proof.
    intros ij_neq LA A ϵ_DDH Va Hdisj Hdisj2 Hdisj3 Hdisj4 Dadv.
    have [f' [bij_f Hf]] := P_i_aux_equiv i j m Hdisj ij_neq.
    ssprove triangle (Exec_i_realised true m i j) [::
      (Aux_realised true i j m f').(pack) ;
      (Aux true i j m f') ∘ (par DDH.DDH_ideal (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) ;
      (Aux false i j m f') ∘ (par DDH.DDH_ideal (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) ;
      (Aux_realised false i j m f').(pack)
    ] (Exec_i_realised false m i j) A as ineq.
    eapply le_trans.
    2: {
      instantiate (1 := 0 + ϵ_DDH + 0 + ϵ_DDH + 0).
      by rewrite ?GRing.addr0 ?GRing.add0r.
    }
    eapply le_trans. 1: exact ineq.
    clear ineq.
    repeat eapply ler_add.
    {
      apply eq_ler.
      specialize (Hf true LA A Va).
      apply Hf.
      - rewrite fdisjointUr.
        apply /andP ; split ; assumption.
      - rewrite fdisjointUr.
        apply /andP ; split.
        2: assumption.
        rewrite fdisjointUr.
        apply /andP ; split ; assumption.
    }
    {
      unfold Aux_realised.
      rewrite -Advantage_link.
      rewrite par_commut.
      have -> : (par DDH.DDH_ideal (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) =
               (par (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO) DDH.DDH_ideal).
      { apply par_commut. ssprove_valid. }
      erewrite Advantage_par.
      3: apply DDH.DDH_real.
      3: apply DDH.DDH_ideal.
      2: {
        ssprove_valid.
        - eapply fsubsetUr.
        - apply fsubsetUl.
      }
      1: rewrite Advantage_sym ; apply Dadv.
      - ssprove_valid.
      - unfold trimmed.
        rewrite -link_trim_commut.
        f_equal.
        unfold trim.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fsetU !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
      - unfold trimmed.
        unfold trim.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
      - unfold trimmed.
        unfold trim.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
    }
    2:{
      unfold Aux_realised.
      rewrite -Advantage_link.
      rewrite par_commut.
      have -> : (par DDH.DDH_real (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) =
               (par (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO) DDH.DDH_real).
      { apply par_commut. ssprove_valid. }
      erewrite Advantage_par.
      3: apply DDH.DDH_ideal.
      3: apply DDH.DDH_real.
      2: {
        ssprove_valid.
        - eapply fsubsetUr.
        - apply fsubsetUl.
      }
      1: apply Dadv.
      - ssprove_valid.
      - unfold trimmed.
        rewrite -link_trim_commut.
        f_equal.
        unfold trim.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fsetU !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
      - unfold trimmed.
        unfold trim.
        unfold DDH.DDH_E.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
      - unfold trimmed.
        unfold trim.
        unfold DDH.DDH_E.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite !filterm_set.
        simpl.
        rewrite !in_fset1 !eq_refl.
        rewrite filterm0.
        done.
    }
    2: {
      apply eq_ler.
      specialize (Hf false LA A Va).
      rewrite Advantage_sym.
      apply Hf.
      - rewrite fdisjointUr.
        apply /andP ; split ; assumption.
      - rewrite fdisjointUr.
        apply /andP ; split.
        2: assumption.
        rewrite fdisjointUr.
        apply /andP ; split ; assumption.
    }
    apply eq_ler.
    eapply eq_rel_perf_ind with (inv := inv i).
    5: apply Va.
    1,2: apply Aux_ideal_realised.
    3: {
      rewrite fdisjointUr.
      apply /andP ; split.
      2: assumption.
      rewrite fdisjointUr.
      apply /andP ; split ; assumption.
    }
    3: {
      rewrite fdisjointUr.
      apply /andP ; split.
      2: assumption.
      rewrite fdisjointUr.
      apply /andP ; split ; assumption.
    }
    {
      ssprove_invariant.
      rewrite fsetUC.
      rewrite -!fsetUA.
      apply fsetUS.
      apply fsubsetUl.
    }
    simplify_eq_rel v.
    rewrite !setmE.
    rewrite !eq_refl.
    simpl.
    repeat simplify_linking.
    rewrite !cast_fun_K.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_sync=>x_i.
    ssprove_sync=>x_j.
    pose f_v := (fun (x : secret) =>
                   if v then
                   fto (Zp_add (otf x) Zp1)
                   else
                   fto (Zp_add (otf x) (Zp_opp Zp1))
                ).
    assert (bijective f_v) as bij_fv.
    {
      exists (fun x =>
           if v then
             fto (Zp_add (otf x) (Zp_opp Zp1))
           else
             fto (Zp_add (otf x) Zp1)
        ).
      - intro x.
        unfold f_v.
        case v.
        + rewrite otf_fto.
          rewrite -Zp_addA.
          rewrite Zp_addC.
          have -> : (Zp_add Zp1 (Zp_opp Zp1)) = (Zp_add (Zp_opp Zp1) Zp1).
          { intro n. by rewrite Zp_addC. }
          rewrite Zp_addNz.
          rewrite Zp_add0z.
          by rewrite fto_otf.
        + rewrite otf_fto.
          rewrite -Zp_addA.
          rewrite Zp_addC.
          rewrite Zp_addNz.
          rewrite Zp_add0z.
          by rewrite fto_otf.
      - intro x.
        unfold f_v.
        case v.
        + rewrite otf_fto.
          rewrite -Zp_addA.
          rewrite Zp_addNz.
          rewrite Zp_addC.
          rewrite Zp_add0z.
          by rewrite fto_otf.
        + rewrite otf_fto.
          rewrite -Zp_addA.
          rewrite Zp_addC.
          have -> : (Zp_add Zp1 (Zp_opp Zp1)) = (Zp_add (Zp_opp Zp1) Zp1).
          { intro n. by rewrite Zp_addC. }
          rewrite Zp_addNz.
          rewrite Zp_add0z.
          by rewrite fto_otf.
    }
    eapply r_uniform_bij.
    1: apply bij_fv.
    intro c.
    ssprove_swap_seq_rhs [:: 1 ; 2]%N.
    ssprove_swap_seq_rhs [:: 0 ]%N.
    ssprove_swap_seq_lhs [:: 1 ; 2]%N.
    ssprove_swap_seq_lhs [:: 0 ]%N.
    apply r_put_vs_put.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    unfold Sigma1.MyParam.R.
    rewrite -Hord otf_fto eq_refl.
    simpl.
    ssprove_sync=>r_i.
    apply r_put_vs_put.
    ssprove_restore_pre.
    {
      ssprove_invariant.
      apply preserve_update_r_ignored_heap_ignore.
      {
        rewrite in_fsetU.
        apply /orP ; right.
        unfold DDH.DDH_locs.
        rewrite !fset_cons -fset0E fsetU0.
        rewrite in_fsetU.
        apply /orP ; right.
        rewrite in_fsetU.
        apply /orP ; right.
        by apply /fset1P.
      }
      apply preserve_update_l_ignored_heap_ignore.
      2: apply preserve_update_mem_nil.
      rewrite in_fsetU.
      apply /orP ; right.
      unfold DDH.DDH_locs.
      rewrite !fset_cons -fset0E fsetU0.
      rewrite in_fsetU.
      apply /orP ; right.
      rewrite in_fsetU.
      apply /orP ; right.
      by apply /fset1P.
    }
    ssprove_sync.
    ssprove_sync=>queries.
    case (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ x_i), fto (g ^+ otf r_i)))) eqn:e.
    all: rewrite e.
    all: ssprove_code_simpl ; simpl.
    all: ssprove_code_simpl_more ; simpl.
    - apply r_get_remember_lhs.
      intros ?.
      apply r_get_remember_rhs.
      intros ?.
      ssprove_forget_all.
      rewrite -Hord otf_fto eq_refl.
      simpl.
      ssprove_sync=>e_j.
      apply r_put_lhs.
      apply r_put_rhs.
      clear e queries.
      ssprove_restore_pre.
      1: ssprove_invariant.
      ssprove_sync.
      ssprove_sync=>queries.
      case (queries (Sigma1.Sigma.prod_assoc (fto (g ^+ finv f' x_j), fto (g ^+ otf e_j)))) eqn:e.
      all: rewrite e.
      all: simpl; ssprove_code_simpl.
      all: ssprove_code_simpl_more.
      + apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        apply r_ret.
        intros ???.
        split.
        2: assumption.
        unfold f_v.
        apply vote_hiding_bij.
      + ssprove_sync=>e_i.
        apply r_put_vs_put.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_restore_pre.
        1: ssprove_invariant.
        apply r_ret.
        intros ???.
        split.
        2: assumption.
        unfold f_v.
        apply vote_hiding_bij.
    - ssprove_sync=>e_i.
      apply r_put_vs_put.
      apply r_get_remember_lhs.
      intros ?.
      apply r_get_remember_rhs.
      intros ?.
      ssprove_forget_all.
      rewrite -Hord otf_fto.
      rewrite -Hord eq_refl.
      simpl.
      ssprove_sync=>r_j.
      apply r_put_lhs.
      apply r_put_rhs.
      ssprove_restore_pre.
      1: ssprove_invariant.
      ssprove_sync.
      ssprove_sync=>queries'.
      case (queries' (Sigma1.Sigma.prod_assoc (fto (g ^+ finv f' x_j), fto (g ^+ otf r_j)))) eqn:e'.
      all: rewrite e'.
      all: simpl; ssprove_code_simpl.
      all: ssprove_code_simpl_more.
      + apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        apply r_ret.
        intros ???.
        split.
        2: assumption.
        unfold f_v.
        apply vote_hiding_bij.
      + ssprove_sync=>e_j.
        apply r_put_vs_put.
        apply r_get_remember_lhs.
        intros ?.
        apply r_get_remember_rhs.
        intros ?.
        ssprove_forget_all.
        apply r_assertD.
        {
          intros ??.
          rewrite !domm_set.
          done.
        }
        intros _ _.
        ssprove_restore_pre.
        1: ssprove_invariant.
        apply r_ret.
        intros ???.
        split.
        2: assumption.
        unfold f_v.
        apply vote_hiding_bij.
  Qed.

End OVN.
End OVN.
