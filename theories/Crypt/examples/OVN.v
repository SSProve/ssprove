
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_composition Package Prelude SigmaProtocol Schnorr.

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
Definition q' := #[g].-2.
Definition q : nat := q'.+2.

Lemma group_prodC :
  @commutative gT gT mulg.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.

Definition Pid : finType := [finType of 'I_n].
Definition Secret := Zp_finComRingType q'.
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
Qed.

#[local] Existing Instance Pid_pos.
#[local] Existing Instance Secret_pos.
#[local] Existing Instance Public_pos.

Definition pid : chUniverse := 'fin #|Pid|.
Definition secret : chUniverse := 'fin #|Secret|.
Definition public: chUniverse := 'fin #|Public|.

Definition nat_to_pid : nat → pid.
Proof.
  move=> n.
  eapply give_fin.
Defined.

Definition i_secret := #|Secret|.
Definition i_public := #|Public|.

Module Type CDSParams <: SigmaProtocolParams.
  Definition Witness : finType := Secret.
  Definition Statement : finType := (prod_finType (prod_finType Public Public) Public).

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
      let '(gx, gy, gyv) := h in
      (gx * g ^+ invg x == gyv ^+ invg x * invg gy * invg (g ^+ 0)) ||
      (gx == gyv * invg gy * invg (g ^+ 1)).

  Lemma relation_valid_left:
    ∀ (x : Secret) (gy : Public),
      R (g^+x, gy, gy^+x * g^+ 0) x.
  Proof.
    intros x gy.
    unfold R.
    rewrite expg0.
    rewrite mulg1.
    apply /orP ; left.
    rewrite invg1 mulg1.
    have Hgy: exists y, gy = g^+y.
    { apply /cycleP. rewrite -g_gen. apply: in_setT. }
    destruct Hgy as [y Hgy]. subst.
    simpl.
  Admitted.

  Lemma relation_valid_right:
    ∀ (x : Secret) (gy : Public),
      R (g^+x, gy, gy^+x * g^+ 1) x.
  Proof.
    intros x y.
    unfold R.
    rewrite expg0.
    rewrite invg1.
    rewrite mulg1.
    apply /orP ; right.
  Admitted.


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

  Module Sigma1 := (Schnorr GP).
  Module Sigma2 := (SigmaProtocol π2 Alg2).

  Obligation Tactic := idtac.
  Set Equations Transparent.

  Definition secret_keys_loc : Location := (chMap pid secret; 0%N).
  Definition secret_locs : {fset Location} := fset [:: secret_keys_loc].

  Definition constructed_keys_loc : Location := (chMap pid public; 1%N).
  Definition public_keys_loc : Location := (chMap pid (chProd public Sigma1.MyAlg.choiceTranscript) ; 2%N).
  Definition votes_loc : Location := (chMap pid (chProd public Alg2.choiceTranscript) ; 3%N).
  Definition public_locs : {fset Location} := fset [:: public_keys_loc ; votes_loc ; constructed_keys_loc].

  Definition all_locs : {fset Location} := (secret_locs :|: public_locs).

  Notation choiceStatement1 := Sigma1.MyAlg.choiceStatement.
  Notation choiceWitness1 := Sigma1.MyAlg.choiceWitness.
  Notation choiceTranscript1 := Sigma1.MyAlg.choiceTranscript.

  Notation " 'pid " := pid (in custom pack_type at level 2).
  Notation " 'pids " := (chProd pid pid) (in custom pack_type at level 2).
  Notation " 'public " := public (in custom pack_type at level 2).
  Notation " 'public " := public (at level 2) : package_scope.
  Notation " 'votes " := (chMap pid (chProd public Alg2.choiceTranscript)) (in custom pack_type at level 2).

  Notation " 'chRelation1' " := (chProd choiceStatement1 choiceWitness1) (in custom pack_type at level 2).
  Notation " 'chTranscript1' " := choiceTranscript1 (in custom pack_type at level 2).
  Notation " 'public_keys " := (chMap pid (chProd public choiceTranscript1)) (in custom pack_type at level 2).
  Notation " 'public_key " := (chProd public choiceTranscript1) (in custom pack_type at level 2).

  Notation " 'chRelation2' " := (chProd Alg2.choiceStatement Alg2.choiceWitness) (in custom pack_type at level 2).
  Notation " 'chTranscript2' " := Alg2.choiceTranscript (in custom pack_type at level 2).
  Notation " 'vote " := (chProd public Alg2.choiceTranscript) (in custom pack_type at level 2).

  Definition pack_statement2 (gx : Public) (gy : Public) (gyv : Public) : Alg2.choiceStatement.
  Proof.
    unfold Alg2.choiceStatement, π2.Statement, Public.
    apply fto ; repeat apply pair.
    - apply gx.
    - apply gy.
    - apply gyv.
  Defined.

  Definition pack_relation2 (gx : Public) (gy : Public) (gyv : Public) (x : Secret) : (chProd Alg2.choiceStatement Alg2.choiceWitness) :=
    (pack_statement2 gx gy gyv, fto x).

  Definition INIT : nat := 4.
  Definition RUNVOTES : nat := 5.
  Definition GETVOTES : nat := 6.
  Definition VOTE : nat := 7.
  Definition CONSTRUCT : nat := 8.
  Definition VOTE_I : nat := 9.

  Definition SET_ELEM : nat := 10.
  Definition QUERY : nat := 11.

  Definition SET_PK i : nat := 10 + i.
  Definition GET_PK i : nat := 10 + N + i.
  Definition SET_VOTE : nat := 13.
  Definition GET_VOTE : nat := 13.

  #[local] Hint Extern 1 (is_true (_ \in all_locs)) =>
    unfold all_locs; rewrite - fset_cat; auto_in_fset : typeclass_instances ssprove_valid_db.

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

  Definition prod_gT (xs : list gT) : gT :=
    foldr (λ a b, a * b) 1 xs.

  Lemma prod_gT_aux xs ys y:
    prod_gT (xs ++ y :: ys) = prod_gT (y :: xs ++ ys).
  Proof.
    induction xs.
    - done.
    - simpl.
      rewrite IHxs.
      simpl.
      rewrite group_prodC.
      rewrite -mulgA.
      f_equal.
      rewrite group_prodC.
      done.
  Qed.

  Lemma prod_gT_cat xs ys:
    prod_gT (xs ++ ys) = prod_gT xs * prod_gT ys.
  Proof.
    induction ys.
    - simpl.
      by rewrite cats0 mulg1.
    - simpl.
      have -> : prod_gT xs * (a * prod_gT ys) = prod_gT xs * prod_gT ys * a.
      { rewrite -mulgA. f_equal. by rewrite group_prodC. }
      rewrite -IHys.
      rewrite prod_gT_aux.
      simpl.
      rewrite group_prodC.
      done.
  Qed.

  Definition get_value (m : chMap pid (chProd public choiceTranscript1)) (i : pid) :=
    match m i with
    | Some (v, _) => otf v
    | _ => 1
    end.

  Definition map_prod (m : chMap pid (chProd public choiceTranscript1)) :=
    (* foldr (fun i b => *)
    (*          match m i with *)
    (*          | Some (v, _) => otf v * b *)
    (*          | _ => b *)
    (*          end *)
    (*       ) 1 (domm m). *)
    \prod_(i <- domm m) (get_value m i).

  Lemma helper
        (i : pid)
        (v : chProd public choiceTranscript1)
        (m : chMap pid (chProd public choiceTranscript1)):
    setm m i v = setm (remm m i) i v.
  Proof.
    simpl.
    apply eq_fmap.
    intro k.
    rewrite !setmE remmE.
    case (eq_op) ; done.
  Qed.

  Canonical finGroup_com_law := Monoid.ComLaw group_prodC.

  Lemma map_prod_setm
        (i : pid)
        (v : chProd public choiceTranscript1)
        (m : chMap pid (chProd public choiceTranscript1)):
    map_prod (setm m i v) = map_prod (remm m i) * (otf v.1).
  Proof.
    unfold map_prod.
    simpl.
    rewrite helper.
    rewrite domm_set.
    simpl.
    set X := domm _.
    rewrite big_fsetU1.
    2: {
      subst X.
      rewrite domm_rem.
      unfold not.
      apply /negPn.
      unfold not.
      rewrite in_fsetD => H.
      move: H => /andP H.
      destruct H as [H _].
      move: H => /negPn H.
      apply H.
      by rewrite in_fset1.
    }
    simpl.
    unfold get_value.
    rewrite !setmE.
    rewrite eq_refl.
    destruct v as [x ?].
    rewrite group_prodC.
    f_equal.
    rewrite !big_seq.
    subst X.
    rewrite domm_rem.
    erewrite eq_bigr.
    1: done.
    intros k k_in.
    rewrite -helper.
    simpl.
    rewrite setmE remmE.
    case (eq_op) eqn:eq.
    - move: eq => /eqP eq.
      rewrite eq in k_in.
      rewrite in_fsetD1 in k_in.
      move: k_in => /andP [contra].
      unfold negb in contra.
      rewrite eq_refl in contra.
      discriminate.
    - done.
  Qed.

  Lemma domm_set':
    ∀ (T : ordType) (S : Type) (m : {fmap T → S}) (k : T) (v : S), domm (T:=T) (S:=S) (setm (T:=T) m k v) = k |: domm (T:=T) (S:=S) (remm m k).
  Proof.
    intros T S m k v.
    apply/eq_fset => k';
    apply /(sameP dommP) /(iffP idP);
    rewrite setmE in_fsetU1.
    - case /orP=> [->|].
      + eauto.
      + move=> /dommP.
        rewrite remmE.
        intros [v' ?].
        case eq_op in H.
        ++ discriminate.
        ++ case eq_op; eauto.
    - rewrite mem_domm.
      rewrite remmE.
      intros H.
      apply /orP.
      case (k' == k) eqn:eq.
      + by left.
      + right.
        destruct H as [v' ->].
        done.
  Qed.

  Definition compute_key
             (m : chMap pid (chProd public choiceTranscript1))
             (i : pid)
    :=
    let low := \prod_(k <- domm m | (k < i)%ord) (get_value m k) in
    let high := \prod_(k <- domm m | (i < k)%ord) (get_value m k) in
    low * invg high.

  Definition get_value_no_zkp (m : chMap pid public) (i : pid) :=
    match m i with
    | Some v => otf v
    | _ => 1
    end.

  Definition compute_key_no_zkp
             (m : chMap pid public)
             (i : pid)
    :=
    let low := \prod_(k <- domm m | (k < i)%ord) (get_value_no_zkp m k) in
    let high := \prod_(k <- domm m | (i < k)%ord) (get_value_no_zkp m k) in
    low * invg high.

  Lemma compute_key_ignore_zkp
             (m : chMap pid (chProd public choiceTranscript1))
             (i j : pid)
             zk x:
    compute_key (setm m j (x, zk)) i = compute_key_no_zkp (setm (mapm fst m) j x) i.
  Proof.
    unfold compute_key, compute_key_no_zkp.
    simpl.
    rewrite !domm_set.
    rewrite domm_map.
    f_equal.
    - erewrite eq_bigr.
      1: done.
      intros k k_lt.
      unfold get_value, get_value_no_zkp.
      rewrite !setmE mapmE.
      case (eq_op).
      1: reflexivity.
      destruct (m k) eqn:eq_m.
      + rewrite eq_m.
        destruct s.
        done.
      + by rewrite eq_m.
    - f_equal.
      erewrite eq_bigr.
      1: done.
      intros k k_lt.
      unfold get_value, get_value_no_zkp.
      rewrite !setmE mapmE.
      case (eq_op).
      1: reflexivity.
      destruct (m k) eqn:eq_m.
      + rewrite eq_m.
        destruct s.
        done.
      + by rewrite eq_m.
  Qed.

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

  Lemma filterm_step
        (i : pid)
        (keys : chMap pid (chProd public choiceTranscript1))
        (pred : pid → (chProd public choiceTranscript1) → bool)
    :
    filterm pred keys =
      match (keys i) with
      | Some e => if (pred i e) then setm (filterm (λ k v, (pred k v) && (k != i)) keys) i e
                               else (filterm (λ k v, (pred k v)) keys)
      | _ => (filterm (λ k v, (pred k v)) keys)
      end.
  Proof.
    simpl.
    case (keys i) eqn:eq ; rewrite eq.
    2: done.
    case (pred i s) eqn:eq_pred.
    2: done.
    rewrite -eq_fmap.
    intros k.
    case (k == i) eqn:eq_k.
    + rewrite filtermE.
      rewrite setmE.
      rewrite filtermE.
      rewrite eq_k.
      move: eq_k => /eqP eq_k.
      rewrite -eq_k in eq.
      rewrite -eq_k in eq_pred.
      rewrite eq.
      simpl.
      rewrite eq_pred.
      done.
    + rewrite filtermE.
      rewrite setmE.
      rewrite filtermE.
      rewrite eq_k.
      simpl.
      case (keys k) eqn:eq'.
      ++ rewrite eq'.
         simpl.
         rewrite Bool.andb_true_r.
         done.
      ++ rewrite eq'.
         done.
  Qed.

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
    case (j < i)%ord eqn:e.
    - rewrite e.
      rewrite helper.
      simpl.
      rewrite domm_set domm_rem.
      set X := domm _.
      rewrite !big_fsetU1.
      2: {
        subst X.
        apply /negPn.
        rewrite in_fsetD => H.
        move: H => /andP H.
        destruct H as [H _].
        move: H => /negPn H.
        apply H.
        by rewrite in_fset1.
      }
      2: {
        subst X.
        apply /negPn.
        rewrite in_fsetD => H.
        move: H => /andP H.
        destruct H as [H _].
        move: H => /negPn H.
        apply H.
        by rewrite in_fset1.
      }
      rewrite -helper.
      rewrite e.
      simpl.
      rewrite -mulgA.
      rewrite -mulgA.
      f_equal.
      { unfold get_value. by rewrite setmE eq_refl otf_fto. }
      f_equal.
      + simpl.
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        unfold get_value.
        erewrite eq_bigr.
        1: done.
        intros k k_in.
        move: k_in => /andP [k_in k_lt].
        simpl.
        rewrite setmE remmE.
        case (k == j) eqn:eq.
        ++ move: eq => /eqP eq.
           rewrite eq in_fsetD1 in k_in.
           move: k_in => /andP [contra].
           rewrite eq_refl in contra.
           discriminate.
        ++ by rewrite eq.
    + rewrite Ord.ltNge in e.
      rewrite Ord.leq_eqVlt in e.
      rewrite negb_or in e.
      move: e => /andP e.
      destruct e as [_ e].
      rewrite -eqbF_neg in e.
      move: e => /eqP e.
      rewrite e.
      f_equal.
      rewrite big_seq_cond.
      rewrite [RHS] big_seq_cond.
      unfold get_value.
      erewrite eq_bigr.
      1: done.
      intros k k_in.
      move: k_in => /andP [k_in k_lt].
      simpl.
      rewrite setmE remmE.
      case (k == j) eqn:eq.
      ++ move: eq => /eqP eq.
          rewrite eq in_fsetD1 in k_in.
          move: k_in => /andP [contra].
          rewrite eq_refl in contra.
          discriminate.
      ++ by rewrite eq.
    - rewrite e.
      rewrite helper.
      simpl.
      rewrite domm_set domm_rem.
      set X := domm _.
      rewrite !big_fsetU1.
      2: {
        subst X.
        apply /negPn.
        rewrite in_fsetD => H.
        move: H => /andP H.
        destruct H as [H _].
        move: H => /negPn H.
        apply H.
        by rewrite in_fset1.
      }
      2: {
        subst X.
        apply /negPn.
        rewrite in_fsetD => H.
        move: H => /andP H.
        destruct H as [H _].
        move: H => /negPn H.
        apply H.
        by rewrite in_fset1.
      }
      rewrite -helper e.
      rewrite Ord.ltNge in e.
      apply negbT in e.
      apply negbNE in e.
      rewrite Ord.leq_eqVlt in e.
      move: e => /orP [contra|e].
      1: by rewrite contra in ij_neq.
      rewrite e.
      simpl.
      rewrite !invMg.
      f_equal.
      {
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        erewrite eq_bigr.
        1: done.
        intros k H.
        unfold get_value.
        rewrite remmE setmE.
        case (k == j) eqn:eq_k.
        + move: H => /andP [H _].
          rewrite in_fsetD1 in H.
          move: eq_k => /eqP eq_k.
          move: H => /andP [H _].
          rewrite eq_k in H.
          by rewrite eq_refl in H.
        + by rewrite eq_k.
      }
      rewrite group_prodC.
      f_equal.
      { unfold get_value. by rewrite setmE eq_refl otf_fto. }
      f_equal.
      rewrite big_seq_cond.
      rewrite [RHS] big_seq_cond.
      unfold get_value.
      erewrite eq_bigr.
      1: done.
      intros k k_in.
      move: k_in => /andP [k_in k_lt].
      simpl.
      rewrite setmE remmE.
      case (k == j) eqn:eq.
      ++ move: eq => /eqP eq.
          rewrite eq in_fsetD1 in k_in.
          move: k_in => /andP [contra].
          rewrite eq_refl in contra.
          discriminate.
      ++ by rewrite eq.
  Qed.

  Lemma compute_key_bij:
    ∀ (m : chMap pid (chProd public choiceTranscript1)) (i j: pid),
      (i != j)%ord →
      exists (a b : nat), ∀ (x : Secret) zk,
        compute_key (setm m j (fto (g ^+ x), zk)) i = g ^+ ((a * x + b) %% q).
  Proof.
    simpl.
    intros m i j ne.
    pose low := \prod_(k <- domm m :\ j| (k < i)%ord) get_value m k.
    pose hi := \prod_(k <- domm m :\ j| (i < k)%ord) get_value m k.
    have Hlow : exists ilow, low = g ^+ ilow.
    { apply /cycleP. rewrite -g_gen.
      apply: in_setT. }
    have Hhi : exists ihi, hi = g ^+ ihi.
    { apply /cycleP. rewrite -g_gen.
      apply: in_setT. }
    destruct Hlow as [ilow Hlow].
    destruct Hhi as [ihi Hhi].
    case (j < i)%ord eqn:ij_rel.
    - exists 1%N.
      exists (ilow + (ihi * #[g ^+ ihi].-1))%N.
      intros x zk.
      rewrite compute_key'_equiv.
      2: assumption.
      unfold compute_key'.
      simpl.
      rewrite ij_rel.
      rewrite domm_rem.
      set low' := \prod_(k0 <- _ | _) _.
      set hi' := \prod_(k0 <- _ | _) _.
      have -> : low' = low.
      {
        unfold low, low'.
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        erewrite eq_bigr.
        1: done.
        intros k k_in.
        move: k_in => /andP [k_in k_lt].
        simpl.
        unfold get_value.
        rewrite remmE.
        case (k == j) eqn:eq.
        ++ move: eq => /eqP eq.
            rewrite eq in_fsetD1 in k_in.
            move: k_in => /andP [contra].
            rewrite eq_refl in contra.
            discriminate.
        ++ by rewrite eq.
      }
      have -> : hi' = hi.
      {
        unfold hi, hi'.
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        erewrite eq_bigr.
        1: done.
        intros k k_in.
        move: k_in => /andP [k_in k_lt].
        simpl.
        unfold get_value.
        rewrite remmE.
        case (k == j) eqn:eq.
        ++ move: eq => /eqP eq.
            rewrite eq in_fsetD1 in k_in.
            move: k_in => /andP [contra].
            rewrite eq_refl in contra.
            discriminate.
        ++ by rewrite eq.
      }
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
        unfold q. rewrite Zp_cast;
        [reflexivity | apply (prime_gt1 prime_order)].
      }
      rewrite mul1n.
      done.
    - exists #[g].-1.
      exists (ilow + (ihi * #[g ^+ ihi].-1))%N.
      intros x zk.
      rewrite compute_key'_equiv.
      2: assumption.
      unfold compute_key'.
      simpl.
      rewrite ij_rel.
      rewrite domm_rem.
      set low' := \prod_(k0 <- _ | _) _.
      set hi' := \prod_(k0 <- _ | _) _.
      have -> : low' = low.
      {
        unfold low, low'.
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        erewrite eq_bigr.
        1: done.
        intros k k_in.
        move: k_in => /andP [k_in k_lt].
        simpl.
        unfold get_value.
        rewrite remmE.
        case (k == j) eqn:eq.
        ++ move: eq => /eqP eq.
            rewrite eq in_fsetD1 in k_in.
            move: k_in => /andP [contra].
            rewrite eq_refl in contra.
            discriminate.
        ++ by rewrite eq.
      }
      have -> : hi' = hi.
      {
        unfold hi, hi'.
        rewrite big_seq_cond.
        rewrite [RHS] big_seq_cond.
        erewrite eq_bigr.
        1: done.
        intros k k_in.
        move: k_in => /andP [k_in k_lt].
        simpl.
        unfold get_value.
        rewrite remmE.
        case (k == j) eqn:eq.
        ++ move: eq => /eqP eq.
            rewrite eq in_fsetD1 in k_in.
            move: k_in => /andP [contra].
            rewrite eq_refl in contra.
            discriminate.
        ++ by rewrite eq.
      }
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
        unfold q. rewrite Zp_cast;
        [reflexivity | apply (prime_gt1 prime_order)].
      }
      rewrite addnAC.
      rewrite addnC.
      rewrite addnA.
      done.
  Qed.

  Lemma filterm_remove_i_lt
        (i : pid) (v : (chProd public choiceTranscript1))
        (keys : chMap pid (chProd public choiceTranscript1)) :
    filterm (fun k v => Ord.lt k i) (setm keys i v) =
    filterm (fun k v => Ord.lt k i) keys.
  Proof.
    simpl.
    rewrite -eq_fmap => k.
    case (k == i) eqn:eq_k.
    - rewrite !filtermE setmE.
      simpl.
      rewrite eq_k.
      move: eq_k => /eqP eq_k.
      rewrite -eq_k.
      rewrite Ord.ltxx.
      destruct (keys k) eqn:eq.
      all: by rewrite eq.
    - rewrite !filtermE setmE.
      rewrite eq_k.
      done.
  Qed.

  Lemma filterm_remove_i_gt
        (i : pid) (v : (chProd public choiceTranscript1))
        (keys : chMap pid (chProd public choiceTranscript1)) :
    filterm (fun k v => Ord.lt i k) (setm keys i v) =
    filterm (fun k v => Ord.lt i k) keys.
  Proof.
    simpl.
    rewrite -eq_fmap => k.
    case (k == i) eqn:eq_k.
    - rewrite !filtermE setmE.
      simpl.
      rewrite eq_k.
      move: eq_k => /eqP eq_k.
      rewrite -eq_k.
      rewrite Ord.ltxx.
      destruct (keys k) eqn:eq.
      all: by rewrite eq.
    - rewrite !filtermE setmE.
      rewrite eq_k.
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
    - have -> : domm (setm m i v) = domm m.
      {
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
      + rewrite helper domm_set domm_rem.
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
        rewrite helper domm_set domm_rem.
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
    destruct H as [a [b H]].
    pose f' := (fun (x : Secret) => @inZp q'.+1 (a * x + b)).
    exists f'.
    unfold f'. clear f'.
    intros x.
    split.
    {
      assert ('I_#|gT| * 'I_#|gT| * 'I_#|'Z_Sigma1.q| * 'I_#|'Z_Sigma1.q|) as zk.
      {
        repeat apply pair.
        1,2: eapply Ordinal ; apply /card_gt0P ; by exists g.
        - rewrite card_ord Zp_cast.
          1: eapply Ordinal.
          1,2: apply (prime_gt1 prime_order).
        - rewrite card_ord Zp_cast.
          1: eapply Ordinal.
          1,2: apply (prime_gt1 prime_order).
      }
      specialize (H x zk).
      pose f' := (fun (x : Secret) => @inZp q'.+1 (x - b)).
      exists f'.
      - intro z.
        unfold f'.
        rewrite -!Zp_nat.
        intuition simpl.
        admit.
      - admit.
    }
    intro zk.
    rewrite (H x zk).
    done.
  Admitted.

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
        simpl.
        rewrite otf_fto.
        apply f_finv in f_bij.
        rewrite f_bij fto_otf.
        reflexivity.
    - intro zk.
      specialize (H' zk).
      rewrite otf_fto.
      apply H'.
  Qed.

  Definition KEY_GAME b (i j : pid):
    package all_locs
      [interface]
      [interface val #[ QUERY ] : 'public → ('public × 'public)]
    :=
    [package
       def #[ QUERY ] (h : 'public) : ('public × 'public)
       {
         x_i ← sample uniform i_secret ;;
         x_j ← sample uniform i_secret ;;
         pkeys ← get public_keys_loc ;;
         let pkeys' := mapm fst pkeys in
         let y_i := (fto (g ^+ (otf x_i))) in
         let y_j := (fto (g ^+ (otf x_j))) in
           if b then
             ret (y_i, (fto (compute_key_no_zkp (setm pkeys' j y_j) i)))
           else
             ret (y_i, y_j)
       }
    ].

  Definition Init (id : pid) :
    code all_locs
      [interface
         val #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1 ;
         val #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool
      ] (chProd public choiceTranscript1) :=
    {code
      #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
      #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
      x ← sample uniform i_secret ;;
      secrets ← get secret_keys_loc ;;
      put secret_keys_loc := setm secrets id x ;;
      let y := (fto (g ^+ (otf x))) : public in
        zkp ← ZKP (y, x) ;;
        public ← get public_keys_loc ;;
        put public_keys_loc := setm public id (y, zkp) ;;
        ret (y, zkp)
    }.

  Definition Construct_key (i : pid) :
    code all_locs
      [interface
         val #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool
      ] 'unit :=
    {code
      #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
      keys ← get public_keys_loc ;;
      #assert (size (domm keys) == n) ;;
      let key := compute_key keys i in
      constructed_keys ← get constructed_keys_loc ;;
      put constructed_keys_loc := setm constructed_keys i (fto key) ;;
      @ret 'unit Datatypes.tt
    }.

  Definition SETUP_I :=
      [interface
         val #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1 ;
         val #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool
      ].

  Definition SETUP_E := [interface val #[ INIT ] : 'unit → 'unit].

  Equations? SETUP_real (m : chMap pid (chProd public choiceTranscript1))
           (i j : pid)
    :
    package all_locs
      SETUP_I
      SETUP_E :=
    SETUP_real m i j :=
    [package
        def #[ INIT ] (_ : 'unit) : 'unit
        {
          zkp1 ← Init i ;;
          zkp2 ← Init j ;;
          put public_keys_loc := (setm (setm m j zkp2) i zkp1) ;;
          Construct_key i ;;
          @ret 'unit Datatypes.tt
        }
    ].
  Proof.
    ssprove_valid.
    all: eapply valid_injectMap.
    2,4,6: eapply valid_injectLocations.
    3,5: apply Init.
    5: apply Construct_key.
    all: try fsubset_auto.
    all: apply fsubsetxx.
  Qed.

  Definition SETUP_ideal (m : chMap pid (chProd public choiceTranscript1))
             (i j : pid)
             (f : secret → secret):
    package all_locs
      SETUP_I
      SETUP_E :=
    [package
        def #[ INIT ] (_ : 'unit) : 'unit
        {
        #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
        #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
        zkp1 ← Init i ;;
        x ← sample uniform i_secret ;;
        secrets ← get secret_keys_loc ;;
        put secret_keys_loc := setm secrets j x ;;
        let y := (fto (g ^+ (otf ((finv f) x)))) : public in
          zkp2 ← ZKP (y, (finv f) x) ;;
          public ← get public_keys_loc ;;
          put public_keys_loc := setm public j (y, zkp2) ;;
          put public_keys_loc := (setm (setm m j (y, zkp2)) i zkp1) ;;
          keys ← get public_keys_loc ;;
          #assert (size (domm keys) == n) ;;
          let key := g ^+ (otf x) in
            constructed_keys ← get constructed_keys_loc ;;
            put constructed_keys_loc := setm constructed_keys i (fto key) ;;
            @ret 'unit Datatypes.tt
        }
    ].

  Module RO1 := Sigma1.Sigma.Oracle.
  Module RO2 := Sigma2.Oracle.

  Definition combined_locations :=
    ((all_locs :|: (Sigma1.MyAlg.Sigma_locs :|: Sigma1.MyAlg.Simulator_locs :|: RO1.RO_locs)) :|:
    ((all_locs :|: (Sigma1.MyAlg.Sigma_locs :|: Sigma1.MyAlg.Simulator_locs :|: RO1.RO_locs)) :|:
     (all_locs :|: (Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: RO2.RO_locs))))
    :|: fset [:: secret_keys_loc].

  Equations? SETUP_realised b m (i j : pid) f : package combined_locations [interface] [interface val #[ INIT ] : 'unit → 'unit] :=
    SETUP_realised b m i j f :=
      {package (if b then SETUP_real m i j else SETUP_ideal m i j f)
               ∘ Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO}.
  Proof.
    ssprove_valid.
    5: apply fsubsetxx.
    {
    eapply valid_package_inject_export.
    2: eapply valid_package_inject_import.
    3: apply Sigma1.Sigma.Fiat_Shamir.
    all: fsubset_auto.
    }
    + unfold combined_locations, all_locs.
    rewrite -!fsetUA.
    do 2 (apply fsubsetU; apply /orP ; right).
    apply fsubsetUl.
    + unfold combined_locations, all_locs.
    rewrite -!fsetUA.
    do 4 (apply fsubsetU; apply /orP ; right).
    apply fsubsetUl.
    + unfold combined_locations, all_locs.
    rewrite -!fsetUA.
    apply fsetUS.
    apply fsubsetUl.
  Qed.

  Notation inv := (heap_ignore secret_locs).
  Instance Invariant_inv : Invariant combined_locations combined_locations inv.
  Proof.
    ssprove_invariant.
    unfold combined_locations, all_locs, secret_locs.
    rewrite fset_cons.
    rewrite -!fsetUA.
    apply fsetUSS.
    - rewrite fset1E. apply fsubsetxx.
    - apply fsubsetU.
      apply /orP ; left.
      apply fsubsetxx.
  Qed.

  Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  (** We extend swapping to schemes.
    This means that the ssprove_swap tactic will be able to swap any command
    with a scheme without asking a proof from the user.
  *)
  Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
    eapply r_swap_scheme_cmd ; ssprove_valid
    : ssprove_swap.

  Lemma constructed_key_random m (i j : pid):
    (i != j)%N →
    ∃ f,
    ∀ LA A LSim Sim,
      ValidPackage LA SETUP_E A_export A →
      fdisjoint LA (LSim :|: combined_locations) →
      fdisjoint LSim secret_locs →
    AdvantageE (SETUP_realised true m i j f) (SETUP_realised false m i j f) A <=
      (Sigma1.Sigma.ϵ_fiat_shamir_zk LSim Sim (A ∘ SETUP_real m i j))
      + (Sigma1.Sigma.ϵ_fiat_shamir_zk LSim Sim (A ∘ SETUP_ideal m i j f)).
    (* (SETUP_realised true m i j f) ≈₀ (SETUP_realised false m i j f). *)
  Proof.
    intro ne.
    have [f' Hf] := test_bij' i j m ne.
    simpl in Hf.
    exists f'.
    intros LA A LSim Sim Va Hdisj Hdisj_secret.
    ssprove triangle (SETUP_realised true m i j f') [::
      (SETUP_real m i j ∘ (Sigma1.Sigma.Fiat_Shamir_SIM LSim Sim) ∘ RO1.RO) ;
      (SETUP_ideal m i j f' ∘ (Sigma1.Sigma.Fiat_Shamir_SIM LSim Sim) ∘ RO1.RO)
    ] (SETUP_realised false m i j f') A as ineq.
    eapply le_trans.
    2: {
      instantiate (1 := Sigma1.Sigma.ϵ_fiat_shamir_zk LSim Sim (A ∘ SETUP_real m i j)
                        + 0
                        + Sigma1.Sigma.ϵ_fiat_shamir_zk LSim Sim (A ∘ SETUP_ideal m i j f')).
      by rewrite GRing.addr0.
    }
    eapply le_trans. 1: exact ineq.
    clear ineq.
    repeat eapply ler_add.
    {
      unfold SETUP_realised.
      rewrite -Advantage_link.
      done.
    }
    2:{
      unfold SETUP_realised.
      rewrite -Advantage_link.
      rewrite Advantage_sym.
      done.
    }
    apply eq_ler.
    eapply eq_rel_perf_ind with (inv := inv).
    6,7: apply Hdisj.
    3: {
      ssprove_invariant.
      erewrite fsetUid.
      unfold combined_locations, all_locs, secret_locs.
      rewrite fset_cons.
      rewrite -!fsetUA.
      apply fsubsetU; apply /orP; right.
      apply fsetUSS.
      - rewrite fset1E. apply fsubsetxx.
      - apply fsubsetU.
        apply /orP ; left.
        apply fsubsetxx.
    }
    4: apply Va.
    {
      ssprove_valid.
      {
        eapply valid_package_inject_import.
        2: eapply valid_package_inject_export.
        3: apply (Sigma1.Sigma.Fiat_Shamir_SIM LSim Sim).
        all: fsubset_auto.
      }
      1: eapply fsubsetUl.
      1: apply fsubsetUr.
      {
        unfold combined_locations, all_locs.
        apply fsubsetU ; apply /orP ; right.
        rewrite -!fsetUA.
        apply fsetUS.
        apply fsubsetUl.
      }
      {
        apply fsetUS.
        unfold combined_locations, RO1.RO_locs.
        rewrite -!fsetUA.
        do 4 (apply fsubsetU ; apply /orP ; right).
        apply fsubsetUl.
      }
    }
    {
      ssprove_valid.
      {
        eapply valid_package_inject_import.
        2: eapply valid_package_inject_export.
        3: apply (Sigma1.Sigma.Fiat_Shamir_SIM LSim Sim).
        all: fsubset_auto.
      }
      1: eapply fsubsetUl.
      1: apply fsubsetUr.
      {
        unfold combined_locations, all_locs.
        apply fsubsetU ; apply /orP ; right.
        rewrite -!fsetUA.
        apply fsetUS.
        apply fsubsetUl.
      }
      {
        apply fsetUS.
        unfold combined_locations, RO1.RO_locs.
        rewrite -!fsetUA.
        do 4 (apply fsubsetU ; apply /orP ; right).
        apply fsubsetUl.
      }
    }
    simplify_eq_rel t.
    ssprove_code_simpl.
    rewrite !cast_fun_K.
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_sync=>x_i.
    apply r_get_remember_lhs=>sks_lhs.
    apply r_get_remember_rhs=>sks_rhs.
    ssprove_forget_all.
    apply r_put_lhs.
    apply r_put_rhs.
    ssprove_sync=>rel_i.
    ssprove_code_simpl.
    ssprove_restore_pre.
    { ssprove_invariant. }
    eapply rsame_head_alt.
    1: exact _.
    {
      intros l lin.
      apply get_pre_cond_heap_ignore.
      move: Hdisj_secret => /fdisjointP Hdisj_secret.
      apply Hdisj_secret.
      assumption.
    }
    {
      intros l v lin.
      apply put_pre_cond_heap_ignore.
    }
    intro zkp_i.
    ssprove_sync=>pkeys.
    apply r_put_vs_put.
    ssprove_restore_pre.
    { ssprove_invariant. }
    eapply r_uniform_bij.
    { apply Hf.
      + rewrite card_ord.
        rewrite Zp_cast.
        2: apply (prime_gt1 prime_order).
        eapply Ordinal.
        apply (prime_gt1 prime_order).
    }
    intro x.
    clear sks_lhs sks_rhs.
    apply r_get_remember_lhs=>sks_lhs.
    apply r_get_remember_rhs=>sks_rhs.
    ssprove_forget_all.
    apply r_put_lhs.
    apply r_put_rhs.
    ssprove_code_simpl_more.
    apply r_assertD.
    {
      intros [s0 s1] _.
      unfold Sigma1.MyParam.R.
      rewrite !otf_fto !eq_refl.
      reflexivity.
    }
    intros _ _.
    ssprove_code_simpl.
    specialize (Hf x).
    destruct Hf as [bij_f Hf].
    apply bij_inj in bij_f.
    apply finv_f in bij_f.
    rewrite !bij_f.
    ssprove_restore_pre.
    1: ssprove_invariant.
    eapply rsame_head_alt.
    1: exact _.
    {
      intros l lin.
      apply get_pre_cond_heap_ignore.
      move: Hdisj_secret => /fdisjointP Hdisj_secret.
      apply Hdisj_secret.
      assumption.
    }
    {
      intros l v lin.
      apply put_pre_cond_heap_ignore.
    }
    intro zkp_j.
    clear pkeys.
    ssprove_sync=>pkeys.
    apply r_put_vs_put.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_restore_pre.
    { ssprove_invariant. }
    (* TODO: ssprove_code_simpl_more fails here. *)
    eapply rel_jdg_replace_sem.
    2: {
      ssprove_code_simpl_more_aux.
      eapply rreflexivity_rule.
    }
    2: {
      ssprove_code_simpl_more_aux.
      eapply rreflexivity_rule.
    }
    cmd_bind_simpl ; cbn beta.
    ssprove_sync=>_.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intro ckeys.
    rewrite compute_key_set_i.
    specialize (Hf zkp_j).
    rewrite Hf.
    apply r_put_vs_put.
    ssprove_restore_mem.
    1: ssprove_invariant.
    apply r_ret ; done.
  Qed.


  Notation inv := (heap_ignore secret_locs).

  Proof.
    ssprove_invariant.
    unfold combined_locations, all_locs, secret_locs.
    rewrite fset_cons.
    rewrite -!fsetUA.
    apply fsetUSS.
    - rewrite fset1E. apply fsubsetxx.
    - apply fsubsetU.
      apply /orP ; left.
      apply fsubsetxx.
  Qed.

  Lemma notin_inv_helper :
    ∀ l,
      l != secret_keys_loc →
      (is_true (l \notin secret_locs)).
  Proof.
    intros l h1.
    unfold secret_locs.
    unfold "\notin".
    rewrite !fset_cons -fset0E.
    rewrite in_fset.
    unfold "\in".
    simpl.
    apply /orP.
    unfold not.
    intros [H |] .
    - apply reflection_nonsense in H.
      rewrite H in h1.
      by rewrite eq_refl in h1.
    - done.
  Qed.

  #[local] Hint Extern 3 (is_true (?l \notin (fset [:: secret_keys_loc]))) =>
    apply notin_inv_helper : typeclass_instances ssprove_valid_db ssprove_invariant.

  Lemma constructed_key_random :
    SETUP_realised true  ≈₀ SETUP_realised false.
  Proof.
  intros l A Va Hdisj1 Hdisj2.
  ssprove triangle (SETUP_realised true) [::
        (SETUP_aux).(pack) ∘ (par (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO_Random) Ledger)
      ] (SETUP_realised false) A as ineq.
  apply AdvantageE_le_0.
  eapply ler_trans. 1: exact: ineq.
  clear ineq.
  apply ler_naddr; last first.
  all: apply eq_ler.
  - eapply eq_rel_perf_ind with (inv := inv).
    1,3,5: exact _.
    3,4: assumption.
    1: {
      ssprove_valid.
      {
        eapply valid_package_inject_export.
        2: apply RO1.RO_Random.
        fsubset_auto.
      }
      7: apply fsubsetxx.
      1: instantiate (1 := (Sigma1.MyAlg.Sigma_locs :|: RO1.RO_locs)).
      - apply fsubsetUl.
      - apply fsubsetUr.
      - unfold combined_locations, all_locs.
        rewrite -!fsetUA.
        do 3 (apply fsubsetU; apply /orP ; right).
        apply fsetUS.
        do 1 (apply fsubsetU; apply /orP ; right).
        apply fsetUS.
        do 2 (apply fsubsetU; apply /orP ; right).
        apply fsubsetUl.
      - rewrite -fset0E fsetU0. apply fsub0set.
      - rewrite !fset_cons !fset1E.
        rewrite -!fsetUA.
        rewrite fsubUset. apply /andP ; split.
        1: apply fsubsetU ; apply /orP ; right ; apply fsubsetUl.
        apply fsetUS.
        rewrite fsubUset. apply /andP ; split.
        + do 2 (apply fsubsetU; apply /orP ; right).
          apply fsubsetUl.
        + do 4 (apply fsubsetU; apply /orP ; right).
          rewrite -fset0E fsetU0.
          apply fsubsetUl.
      - unfold combined_locations, all_locs.
        rewrite -!fsetUA.
        apply fsetUS.
        apply fsubsetUl.
    }
    simplify_eq_rel ij.
    ssprove_code_simpl.
    rewrite !cast_fun_K.
    destruct ij as [i j].
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl.
    ssprove_sync=>x_i.
    apply r_get_remember_lhs=>skeys_lhs.
    apply r_get_remember_rhs=>skeys_rhs.
    ssprove_forget_all.
    ssprove_swap_seq_lhs [:: 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1]%N.
    ssprove_swap_seq_rhs [:: 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1]%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>rel_i.
    ssprove_sync=>r_i.
    ssprove_swap_lhs 1%N.
    ssprove_swap_rhs 1%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_i.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>pkeys.
    ssprove_swap_seq_lhs [:: 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1]%N.
    ssprove_swap_seq_rhs [:: 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1]%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>x_j.
    apply r_put_vs_put.
    ssprove_sync=>rel_j.
    ssprove_sync=>r_j.
    ssprove_swap_lhs 1%N.
    ssprove_swap_rhs 1%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_j.
    ssprove_swap_seq_lhs [:: 4 ; 3 ; 2 ; 1]%N.
    ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1]%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>all_pkeys.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>ckeys.
    apply r_put_vs_put.
    ssprove_swap_rhs 1%N.
    ssprove_sync=>all_votes.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>ckeys'.
    set key := (compute_key _ _). clearbody key.
    have Hkey : exists ikey, key = g ^+ ikey.
    { apply /cycleP. rewrite -g_gen. apply in_setT. }
    destruct Hkey as [ikey Hkey].
    rewrite Hkey.
    eapply r_transL.
    { apply r_dead_sample_L.
      1: apply LosslessOp_uniform.
      apply rreflexivity_rule.
    }
    clear all_pkeys all_votes Hdisj1 Hdisj2 rel_i rel_j.
    eapply r_uniform_bij.
    { instantiate (
          1 := λ y,
            (* if (y <= ikey)%N then *)
            (y + (ikey - y))%N).
            (* else *)
            (*   fto (inZp (y + ((q - y) + ikey))%N)). *)
      eexists.
      - intros y.
        case (y <= ikey)%N eqn:e.
        simpl.
        rewrite subnKC.
        + reflexivity.
        + apply e.
    }

    1: shelve.
    intro y_j.
    apply r_put_vs_put.
    ssprove_restore_pre.
      {
        unfold inv, preserve_update_pre.
        unfold remember_pre.
        intros ?? Pre ??.
        apply Pre in H.
        case (ℓ == constructed_keys_loc) eqn:eq; last first.
        - rewrite !get_set_heap_neq.
          + apply H.
          + by apply Bool.negb_true_iff.
          + by apply Bool.negb_true_iff.
        - apply reflection_nonsense in eq.
          rewrite eq.
          rewrite !get_set_heap_eq.
          clear hin Pre H eq rel_i all_votes all_pkeys.
          set key := (compute_key _ _). clearbody key.
          f_equal.
          f_equal.
          have Hkey : exists ikey, key = g ^+ ikey.
          { apply /cycleP. rewrite -g_gen. apply in_setT. }
          destruct Hkey as [ikey Hkey].
          rewrite Hkey.
          rewrite -expgnE.
          have Hs: exists ik, g ^+ ikey = g ^+ (y_j + ik)%N.
          {
            case (y_j <= ikey)%N eqn:e.
            - exists (ikey-y_j)%N.
              simpl.
              rewrite subnKC.
              + reflexivity.
              + apply e.
            - have Hq : (y_j + (q - y_j))%N = q.
              + rewrite subnKC.
                1: reflexivity.
                destruct y_j as [y_j Hy_j].
                simpl in Hy_j.
                simpl.
                clear e.
                unfold q.
                rewrite card_ord Zp_cast in Hy_j.
                {
                  rewrite -ltnS.
                  unfold q in Hy_j.
                  apply leqW, Hy_j.
                }
                apply prime_gt1.
                apply prime_order.
              + exists ((q - y_j) + ikey)%N.
                rewrite addnA.
                rewrite Hq.
                rewrite expgD.
                rewrite expg_order.
                rewrite mul1g.
                reflexivity.
          }
          destruct Hs as [ik Hs].
          rewrite Hs.
          apply /eqP.
          rewrite eq_expg_mod_order.
          assert (Positive i_secret) as i_secret_pos.
          1: apply Secret_pos.
          pose f := λ (x : Arit (uniform #|Sigma1.MyParam.Witness|)), fto (inZp (x + ik)%N) : Arit (uniform i_secret).
          pose f' := f i_secret_pos i_secret_pos.
          Show Existentials.
          instantiate (1 := f').
      }
      Unshelve.
      3: done.
      2: by exists id.
              2: { done. }
              apply r_ret.
      }





    ssprove_swap_seq_lhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3 ]%N.
    ssprove_swap_seq_rhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3 ]%N.
    ssprove_swap_seq_lhs [:: 17 ; 16 ; 15 ; 14 ; 13 ; 12 ; 11 ]%N.
    ssprove_swap_seq_rhs [:: 17 ; 16 ; 15 ; 14 ; 13 ; 12 ; 11 ]%N.
    (* ssprove_swap_seq_rhs [:: 27 ; 26 ; 25 ; 24 ; 23 ; 22 ; 21 ; 20 ; 19 ; 18 ; 17 ; 16 ; 15]%N. *)
    (* ssprove_swap_seq_rhs [:: 29 ; 28]%N. *)
    ssprove_swap_seq_rhs [:: 23 ; 22 ; 21]%N.
    ssprove_swap_seq_rhs [:: 25 ; 24 ; 23 ; 22 ; 21 ; 20 ; 19 ; 18 ; 17 ; 16 ; 15 ; 14]%N.
    ssprove_swap_lhs 6%N.
    ssprove_swap_rhs 6%N.
    ssprove_swap_rhs 18%N.
    ssprove_swap_rhs 25%N.
    (* eapply r_uniform_bij. *)
    (* 1: shelve. *)
    (* intros x_i. *)
    ssprove_sync=>x_i.
    apply r_get_remember_lhs=>skeys_lhs.
    apply r_get_remember_rhs=>skeys_rhs.
    ssprove_forget_all.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    eapply r_put_vs_put.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>rel_i.
    ssprove_sync=>r_i.
    ssprove_sync=>e_i.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    eapply r_put_vs_put.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>pkeys.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    eapply r_put_vs_put.
    eapply r_uniform_bij.
    1: shelve.
    intros x_j.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_restore_pre.
    1: ssprove_invariant.
    apply r_assertD.
    {
      unfold Sigma1.MyParam.R.
      rewrite !otf_fto !eq_refl.
      reflexivity.
    }
    intros rel_j_lhs rel_j_rhs.
    ssprove_sync=>r_j.
    ssprove_swap_lhs 1%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_j.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    ssprove_swap_seq_lhs [:: 3 ; 2 ; 1]%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    apply r_assertD.
    {
      intros [??] _.
      admit.
    }
    intros all_pkeys_lhs all_pkeys_rhs.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>ckeys.
    ssprove_swap_lhs 0%N.
    ssprove_sync=>all_votes.
    destruct ((setm (T:=[ordType of 'I_#|'I_n|])
              (setm (T:=[ordType of 'I_#|'I_n|]) skeys_rhs i x_i) j x_j j)) eqn:e.
    all: rewrite e ; clear e.
    +
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      ssprove_sync=>ckeys'.
      apply r_put_vs_put.
      ssprove_restore_pre.
      {
        unfold inv, preserve_update_pre.
        unfold remember_pre.
        intros ?? Pre ??.
        apply Pre in H.
        case (ℓ == constructed_keys_loc) eqn:eq; last first.
        - rewrite !get_set_heap_neq.
          + apply H.
          + by apply Bool.negb_true_iff.
          + by apply Bool.negb_true_iff.
        - apply reflection_nonsense in eq.
          rewrite eq.
          rewrite !get_set_heap_eq.
          clear hin Pre H eq rel_i all_votes all_pkeys_lhs all_pkeys_rhs.
          set key := (compute_key _ _).
          f_equal.
          f_equal.
          have Hkey : exists ikey, key = g ^+ ikey.
          { apply /cycleP. rewrite -g_gen. apply in_setT. }
          destruct Hkey as [ikey Hkey].
          rewrite Hkey.
          rewrite -expgnE.
          have Hs: exists ik, g ^+ ikey = g ^+ (s + ik).
          {
            case (s <= ikey)%N eqn:e.
            - exists (ikey-s)%N.
              simpl.
              rewrite subnKC.
              + reflexivity.
              + apply e.
            -
              have Hq : (s + (q - s))%N = q.
              + rewrite subnKC.
                1: reflexivity.
                destruct s as [s Hs].
                simpl in Hs.
                simpl.
                clear e.
                unfold q.
                rewrite card_ord Zp_cast in Hs.
                {
                  rewrite -ltnS.
                  unfold q in Hs.
                  apply leqW, Hs.
                }
                apply prime_gt1.
                apply prime_order.
              + exists ((q - s) + ikey)%N.
                rewrite addnA.
                rewrite Hq.
                rewrite expgD.
                rewrite expg_order.
                rewrite mul1g.
                reflexivity.
          }
          destruct Hs as [ik Hs].
          rewrite Hs.
          symmetry.
          apply /eqP.
          rewrite eq_expg_mod_order.
          apply /eqP.
          have (k' : nat) := val_Zp_nat _ ikey.
          k
      }
    rewrite H.


    ssprove_swap_seq_lhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3]%N.
    ssprove_swap_seq_rhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3]%N.
    ssprove_swap_seq_lhs [:: 24 ; 23]%N.
    ssprove_swap_seq_rhs [:: 25 ; 24 ; 23]%N.
    ssprove_swap_seq_lhs [:: 23 ; 22 ; 21 ; 20 ; 19]%N.
    ssprove_swap_seq_rhs [:: 23 ; 22 ; 21 ; 20 ; 19]%N.
    ssprove_swap_seq_lhs [:: 16]%N.
    ssprove_swap_seq_lhs [:: 7]%N.
    ssprove_swap_seq_rhs [:: 16]%N.
    ssprove_swap_seq_rhs [:: 7]%N.
    ssprove_swap_seq_rhs [:: 25 ; 24 ; 23 ; 22 ; 21 ; 20 ; 19 ; 18 ; 17 ; 16 ; 15 ; 14 ; 13 ; 12]%N.




    apply r_const_sample_R.
    1: apply LosslessOp_uniform.
    intro x_i_rhs.
    ssprove_swap_seq_rhs [:: 19 ; 18 ; 17 ; 16 ; 15 ; 14 ; 13 ; 12 ; 11 ; 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0]%N.
    ssprove_swap_seq_lhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3]%N.
    ssprove_swap_seq_rhs [:: 10 ; 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3]%N.
    ssprove_swap_seq_lhs [:: 24 ; 23]%N.
    ssprove_swap_seq_rhs [:: 25 ; 24 ; 23]%N.
    ssprove_swap_seq_lhs [:: 23 ; 22 ; 21 ; 20 ; 19]%N.
    ssprove_swap_seq_rhs [:: 23 ; 22 ; 21 ; 20 ; 19]%N.
    ssprove_swap_seq_lhs [:: 16]%N.
    ssprove_swap_seq_lhs [:: 7]%N.
    ssprove_swap_seq_rhs [:: 16]%N.
    ssprove_swap_seq_rhs [:: 7]%N.
    ssprove_swap_seq_rhs [:: 25 ; 24 ; 23 ; 22 ; 21 ; 20 ; 19 ; 18 ; 17 ; 16 ; 15 ; 14 ; 13 ; 12]%N.
    eapply r_uniform_bij.
    1: shelve.
    intro y_i.
    apply r_get_remember_lhs=>skeys_lhs.
    apply r_get_remember_rhs=>skeys_rhs.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    apply r_assertD.
    {
      intros ??.
      unfold Sigma1.MyParam.R.
      rewrite !otf_fto.
      by rewrite !eq_refl.
    }
    intros rel_i_lhs rel_i_rhs.
    ssprove_sync=>r_i.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_i.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_restore_mem.
    1: ssprove_invariant.
    apply r_const_sample_R.
    1: apply LosslessOp_uniform.
    intro x_j_rhs.
    eapply r_uniform_bij.
    1: shelve.
    intro y_j.
    apply r_put_vs_put.
    apply r_assertD.
    {
      intros ??.
      unfold Sigma1.MyParam.R.
      rewrite !otf_fto.
      by rewrite !eq_refl.
    }
    intros rel_j_lhs rel_j_rhs.
    ssprove_sync=>r_j.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_j.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_restore_pre.
    1: ssprove_invariant.
    apply r_assertD.
    {
      intros ??.
      unfold Sigma1.MyParam.R.
      rewrite !otf_fto.
      by rewrite !eq_refl.
    }
    ssprove_sync=>all_pkeys.
    ssprove_swap_rhs 0%N.
    ssprove_sync=>ckeys.
    ssprove_swap_seq_lhs [:: 1]%N.
    ssprove_swap_seq_rhs [:: 3 ; 2]%N.
    eapply r_transL.
    { apply r_dead_sample_L.
      1: apply LosslessOp_uniform.
      apply rreflexivity_rule.
    }
    eapply r_uniform_bij.
    1: shelve.
    intros y_i.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>all_votes.
    ssprove_restore_pre.
    {
      unfold inv, preserve_update_pre.
      unfold remember_pre.
      intros ?? Pre ??.
      apply Pre in H.
      case (ℓ == constructed_keys_loc) eqn:eq; last first.
      - rewrite !get_set_heap_neq.
        + apply H.
        + by apply Bool.negb_true_iff.
        + by apply Bool.negb_true_iff.
      - apply reflection_nonsense in eq.
        rewrite eq.
        rewrite !get_set_heap_eq.
        clear hin all_pkeys Pre H eq rel_i rel_j all_votes.
        set key := (compute_key _ _).
        f_equal.
        f_equal.
        have Hkey : exists ikey, key = g ^+ ikey.
        { apply /cycleP. rewrite -g_gen. apply in_setT. }
        destruct Hkey as [ikey Hkey].
        rewrite Hkey.
        rewrite -expgnE.
        symmetry.
        apply /eqP.
        rewrite eq_expg_mod_order.
        apply /eqP.
        have (k' : nat) := val_Zp_nat _ ikey.
        intros.
        rewrite -x.
        2,3: admit.
        Definition f (c : nat) :
          nat -> nat := fun x => c.
        have : (forall c, bijective (f c)).
        {
          intro c.
          unfold f.
          eexists.
          all: intro y.
          - done.
            instantiate (1 := id).

        }
        instantiate (1 := fun y => ikey%:R).
        rewrite -val_Zp_nat.

        simpl.
        eexists.


    }
    eapply r_transL.
    { apply r_dead_sample_L.
      1: apply LosslessOp_uniform.
      apply rreflexivity_rule.
    }
    eapply r_uniform_bij.
    1: shelve.
    intros y_j.
    apply r_put_vs_put.
    ssprove_restore_pre.
    {
      unfold inv, preserve_update_pre.
      unfold remember_pre.
      intros ?? Pre ??.
      apply Pre in H.
      case (ℓ == constructed_keys_loc) eqn:eq; last first.
      - rewrite !get_set_heap_neq.
        + apply H.
        + by apply Bool.negb_true_iff.
        + by apply Bool.negb_true_iff.
        + by apply Bool.negb_true_iff.
        + by apply Bool.negb_true_iff.
      - apply reflection_nonsense in eq.
        rewrite eq.
        rewrite !get_set_heap_eq.
        unfold compute_key.
        f_equal.
        f_equal.
        unfold map_prod.
        simpl.
        set lower := (foldr _ _ _).
        set higher := (foldr _ _ _).
        instantiate
          (1 := λ (x : Arit (uniform i_secret)), x + lower).
        simpl.
      - rewrite Bool.eqb_true_iff in eq.
        rewrite eq_refl in eq.
        erewrite <- get_heap_set_heap.
    }
      ssprove_sync=>all_votes.
      ssprove_sync=>y_j.
      apply r_put_vs_put.
      ssprove_restore_pre.
      {
        Set Typeclasses Debug.
        apply preserve_update_cons_sym_heap_ignore.
        apply preserve_update_r_ignored_heap_ignore.
        a
      }
      apply r_ret.
      intros ?? Inv.
    }

    ssprove_swap_seq_rhs [:: 8 ; 7 ; 6 ; 5 ; 4 ; 3 ; 2 ; 1 ; 0]%N.
    eapply r_transL.
    1: {
      apply r_dead_sample_L.
      1: apply LosslessOp_uniform.
      apply rreflexivity_rule.
    }
    eapply r_uniform_bij.
    2: {
      intros y_i.
      apply r_put_vs_put.
      ssprove_sync=>rel.
      ssprove_sync=>r_j.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 0%N.
      ssprove_sync=>e_j.
      ssprove_contract_put_get_lhs.
      ssprove_contract_put_get_rhs.
      apply r_put_vs_put.
      ssprove_contract_put_get_lhs.
      ssprove_contract_put_get_rhs.
      apply r_put_vs_put.
      ssprove_sync=>all_pkeys.
      ssprove_restore_pre.
      1: ssprove_invariant.
      apply r_get_remember_lhs=>ckeys_lhs.
      apply r_get_remember_rhs=>ckeys_rhs.
      ssprove_swap_seq_lhs [:: 3 ; 2 ; 1]%N.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1]%N.
      ssprove_contract_put_get_lhs.
      ssprove_contract_put_get_rhs.
      ssprove_forget_all.
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      ssprove_sync=>pkeys'.
      ssprove_sync=>all_votes.
      ssprove_sync=>y_j.
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      apply r_ret.
      intros ?? Inv ; split.
      - reflexivity.
      - apply Inv.
    }
    Unshelve.
    2: {
      done.
    }
    exists id; done.
  - eapply eq_rel_perf_ind with (inv := inv).
    1,3,5: exact _.
    3,4: assumption.
    1: {
      ssprove_valid.
      5: apply fsubsetxx.
      1: {
        eapply valid_package_inject_export.
        2: eapply valid_package_inject_import.
        3: apply Sigma1.Sigma.Fiat_Shamir.
        - fsubset_auto.
        - fsubset_auto.
      }
      all: unfold combined_locations.
      all: rewrite -!fsetUA.
      - do 2 (apply fsubsetU; apply /orP ; right).
        apply fsubsetUl.
      - do 4 (apply fsubsetU; apply /orP ; right).
        apply fsubsetUl.
      - apply fsetUSS.
        + apply fsubsetxx.
        + apply fsubsetUl.
    }
    simplify_eq_rel ij.
    ssprove_code_simpl.
    rewrite !cast_fun_K.
    destruct ij as [i j].
    ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_code_simpl.
    ssprove_sync=>pkeys.
    ssprove_sync=>xi.
    ssprove_swap_seq_lhs [:: 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3; 2]%N.
    ssprove_swap_seq_rhs [:: 9 ; 8 ; 7 ; 6 ; 5 ; 4 ; 3; 2]%N.
    apply r_get_remember_lhs=>skeys_lhs.
    apply r_get_remember_rhs=>skeys_rhs.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>rel_i.
    ssprove_sync=>r_i.
    ssprove_swap_lhs 0%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync=>e_i.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_restore_mem.
    1: ssprove_invariant.
    ssprove_sync=>x_j.
    apply r_put_vs_put.
    ssprove_sync=>rel_j.
    ssprove_sync=>r_j.
    ssprove_swap_lhs 1%N.
    ssprove_swap_rhs 1%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>e_j.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    apply r_put_vs_put.
    ssprove_sync=>all_pkeys.
    ssprove_restore_pre.
    1: ssprove_invariant.
    apply r_get_remember_lhs=>ckeys_lhs.
    apply r_get_remember_rhs=>ckeys_rhs.
    ssprove_swap_seq_lhs [:: 2 ; 1]%N.
    ssprove_swap_seq_rhs [:: 3 ; 2 ; 1]%N.
    ssprove_contract_put_get_lhs.
    ssprove_contract_put_get_rhs.
    ssprove_forget_all.
    apply r_put_vs_put.
    ssprove_restore_pre.
    1: ssprove_invariant.
    ssprove_sync=>pkeys'.
    ssprove_sync=>all_votes.
    eapply r_transL.
    { apply r_dead_sample_L.
      1: apply LosslessOp_uniform.
      apply rreflexivity_rule. }
    eapply r_uniform_bij.
    2: {
      intro y_j.
      apply r_put_vs_put.
      ssprove_restore_pre.
      1: ssprove_invariant.
      apply r_ret.
      intros ?? Inv ; split.
      - done.
      - done.
    }
    exists id ; done.
  Qed.

  Definition Init_realised := (Init_real ∘ Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO).

  Lemma Init_realised_valid:
    ValidPackage (all_locs :|: (Sigma1.MyAlg.Sigma_locs :|: RO1.RO_locs)) Game_import [interface val #[ INIT ] : 'pid → 'unit] Init_realised.
  Proof.
    unfold Init_realised.
    eapply valid_link.
    1: exact _.
    eapply valid_link.
    2: exact _.
    eapply valid_package_inject_export.
    2: apply Sigma1.Sigma.Fiat_Shamir.
    rewrite !fset_cons.
    rewrite fsetUC.
    apply fsetUSS.
    { rewrite -fset0E. apply fsub0set. }
    rewrite -fset0E fset0U.
    apply fsubsetxx.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E Init_realised) =>
    apply Init_realised_valid : typeclass_instances ssprove_valid_db.

  Definition Construct_key_realised := (Construct_key_real ∘ Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO).

  Lemma Construct_key_realised_valid:
    ValidPackage (all_locs :|: (Sigma1.MyAlg.Sigma_locs :|: RO1.RO_locs)) Game_import [interface val #[ CONSTRUCT ] : 'pid → 'unit] Construct_key_realised.
  Proof.
    unfold Construct_key_realised.
    eapply valid_link.
    1: exact _.
    eapply valid_link.
    2: exact _.
    eapply valid_package_inject_export.
    2: apply Sigma1.Sigma.Fiat_Shamir.
    rewrite !fset_cons.
    apply fsetUSS.
    { apply fsubsetxx. }
    rewrite -fset0E. apply fsub0set.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E Construct_key_realised) =>
    apply Construct_key_realised_valid : typeclass_instances ssprove_valid_db.

  Definition Vote_i_realised := (Vote_i_real ∘ Sigma2.Fiat_Shamir ∘ RO2.RO).

  Lemma Vote_i_realised_valid:
    ValidPackage (all_locs :|: (Alg2.Sigma_locs :|: RO2.RO_locs)) Game_import [interface val #[ VOTE_I ] : ('pid × 'bool) → 'unit] Vote_i_realised.
  Proof.
    unfold Vote_i_realised.
    eapply valid_link.
    1: exact _.
    eapply valid_link.
    2: exact _.
    eapply valid_package_inject_export.
    2: apply Sigma2.Fiat_Shamir.
    rewrite !fset_cons.
    rewrite fsetUC.
    apply fsetUSS.
    { rewrite -fset0E. apply fsub0set. }
    rewrite -fset0E fset0U.
    rewrite fset1E.
    apply fsubsetxx.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E Vote_i_realised) =>
    apply Vote_i_realised_valid : typeclass_instances ssprove_valid_db.

  Definition Vote_i_ideal_realised := (Vote_i_ideal ∘ Sigma2.Fiat_Shamir ∘ RO2.RO).

  Lemma Vote_i_ideal_realised_valid:
    ValidPackage (all_locs :|: (Alg2.Sigma_locs :|: RO2.RO_locs)) Game_import [interface val #[ VOTE_I ] : ('pid × 'bool) → 'unit] Vote_i_ideal_realised.
  Proof.
    unfold Vote_i_realised.
    eapply valid_link.
    1: exact _.
    eapply valid_link.
    2: exact _.
    eapply valid_package_inject_export.
    2: apply Sigma2.Fiat_Shamir.
    rewrite !fset_cons.
    rewrite fsetUC.
    apply fsetUSS.
    { rewrite -fset0E. apply fsub0set. }
    rewrite -fset0E fset0U.
    apply fsubsetxx.
  Qed.

  Definition Sigma2_E :=
    [interface
          val #[ Sigma2.VERIFY ] : chTranscript2 → 'bool ;
          val #[ Sigma2.RUN ] : chRelation2 → chTranscript2
    ].

  Definition Sigma2_locs :=
    (Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: RO2.RO_locs).

  Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  Hint Extern 1 (ValidPackage ?L ?I ?E Vote_i_ideal_realised) =>
    apply Vote_i_ideal_realised_valid : typeclass_instances ssprove_valid_db.

  Lemma sigma_preserves_inv :
    ∀ L0 L1,
    fdisjoint L0 L1 →
    ∀ ℓ : Location,
      ℓ \in L1
            → get_pre_cond ℓ (λ '(s₀, s₁), heap_ignore L0 (s₀, s₁)).
  Proof.
    intros L0 L1 Hdisj l lin.
    apply get_pre_cond_heap_ignore.
    case (l \in L0) eqn:RO.
    + exfalso.
      eapply disjoint_in_both.
      1: apply Hdisj.
      2: apply lin.
      apply RO.
    + done.
  Qed.

  Lemma fdisjoint_left :
    ∀ (T : ordType) (s1 s2 s3 : {fset T}),
      fdisjoint (T:=T) s1 (s2 :|: s3) →
      fdisjoint (T:=T) s1 s2.
  Proof.
    intros T s1 s2 s3 h.
    rewrite fdisjointUr in h.
    apply Bool.andb_true_iff in h.
    destruct h.
    assumption.
  Qed.

  Lemma fdisjoint_right :
    ∀ (T : ordType) (s1 s2 s3 : {fset T}),
      fdisjoint (T:=T) s1 (s2 :|: s3) →
      fdisjoint (T:=T) s1 s3.
  Proof.
    intros T s1 s2 s3.
    rewrite fsetUC.
    apply fdisjoint_left.
  Qed.

  Ltac ssprove_sync_sigma :=
    eapply rsame_head_alt ;
    (try apply prog_valid) ;
    (try (intros ??? ; apply put_pre_cond_heap_ignore)) ;
    (try (eapply sigma_preserves_inv ;
          try (eapply fdisjoint_left ; eassumption) ;
          try (eapply fdisjoint_right ; eassumption))).

  Ltac reduce_valid_par :=
    repeat eapply valid_par_upto ;
    repeat try match goal with
      | [ |- ValidPackage _ _ _ _ ] => exact _
      | [ |- Parable _ _ ] => ssprove_valid
    end.

  Ltac restore_inv :=
    repeat eapply preserve_update_r_ignored_heap_ignore ;
    try apply preserve_update_mem_nil ;
    try unfold RO1.RO_locs, RO2.RO_locs ;
    try rewrite fset_cons -fset0E fsetU0 ;
    try auto_in_fset.

  Notation inv := (heap_ignore (RO1.RO_locs :|: RO2.RO_locs)).
  Instance Invariant_inv : Invariant combined_locations combined_locations inv.
  Proof.
    ssprove_invariant.
    unfold combined_locations.
    apply fsubsetU.
    apply /orP; left.
    apply fsubsetU.
    apply /orP; left.
    rewrite fsubUset.
    apply /andP ; split.
    + apply fsubsetU.
      apply /orP; left.
      rewrite !fsetUA.
      apply fsubsetUr.
    + apply fsubsetU.
      apply /orP; right.
      apply fsubsetU.
      apply /orP; right.
      rewrite !fsetUA.
      apply fsubsetUr.
  Qed.

  Definition OVN_i_I :=
      [interface val #[ INIT ] : 'pid → 'unit ;
                 val #[ CONSTRUCT ] : 'pid → 'unit ;
                 val #[ VOTE_I ] : ('pid × 'bool) → 'unit].

  Definition OVN_i_E :=
      [interface val #[ VOTE ] : ('pid × 'bool) → 'unit].

  Equations? OVN_i_real : package combined_locations [interface] OVN_i_E :=
    OVN_i_real := {package OVN_i ∘ (par Init_realised (par Construct_key_realised Vote_i_realised))}.
  Proof.
    ssprove_valid.
    1-4: apply fsubsetxx.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsubsetxx.
    - rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - unfold combined_locations.
      apply fsubsetUr.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      rewrite fsubUset.
      apply /andP ; split.
      + rewrite fsetUC.
        rewrite -fsetUA.
        apply fsubsetUl.
      + apply fsubsetU.
        apply /orP ; right.
        apply fsubsetU.
        apply /orP ; right.
        repeat apply fsetUS.
        apply fsubsetU.
        apply /orP ; right.
        apply fsetUS.
        apply fsetUS.
        apply fsetUS.
        apply fsetUS.
        rewrite fsetUC.
        rewrite -fsetUA.
        apply fsubsetUl.
  Qed.

  Equations? Aux0 : package combined_locations [interface] OVN_i_E :=
    Aux0 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_real ∘ Sigma2.RUN_interactive)))}.
  Proof.
    ssprove_valid.
    1:{ eapply valid_package_inject_export.
        2: eapply valid_package_inject_locations.
        3: apply Sigma2.RUN_interactive.
        + rewrite !fset_cons -fset0E.
          apply fsubsetUr.
        + apply fsubsetxx.
    }
    - instantiate (1 := all_locs :|: Alg2.Sigma_locs).
      apply fsubsetUl.
    - apply fsubsetUr.
    - apply fsubsetxx.
    - apply fsubsetxx.
    - apply fsubsetxx.
    - apply fsubsetxx.
    - unfold Game_import.
      rewrite -fset0E !fsetU0.
      apply fsubsetxx.
    - rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - unfold combined_locations.
      apply fsubsetUr.
    - unfold combined_locations. apply fsubsetU.
      apply /orP ; left.
      apply fsetUSS.
      + apply fsetUS.
        apply fsetSU.
        apply fsubsetUl.
      + apply fsetUSS.
        ++ apply fsetUS.
           apply fsetSU.
           apply fsubsetUl.
        ++ apply fsetUS.
           rewrite -fsetUA.
           apply fsubsetUl.
  Qed.

  Equations? Aux1 : package combined_locations [interface] OVN_i_E :=
    Aux1 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_real ∘ Sigma2.SHVZK_real_aux ∘ Sigma2.SHVZK_real)))}.
  Proof.
    ssprove_valid.
    1-2, 12: apply fsubsetxx.
    1: instantiate (1 := all_locs :|: Alg2.Sigma_locs).
    - apply fsubsetUl.
    - apply fsubsetUr.
    - apply fsubsetxx.
    - apply fsubsetxx.
    - apply fsubsetxx.
    - unfold combined_locations.
      apply fsubsetU.
      apply /orP. left.
      apply fsetUSS.
      + apply fsetUS.
        apply fsetSU.
        apply fsubsetUl.
      + apply fsetUSS.
        ++ apply fsetUS.
           apply fsetSU.
           apply fsubsetUl.
        ++ apply fsetUS.
           rewrite -fsetUA.
           apply fsubsetUl.
    - unfold Game_import.
      rewrite -fset0E !fsetU0.
      apply fsubsetxx.
    - unfold OVN_i_E.
      rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - apply fsubsetUr.
  Qed.

  Equations? Aux2 : package combined_locations [interface] OVN_i_E :=
    Aux2 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_real ∘ Sigma2.SHVZK_real_aux ∘ Sigma2.SHVZK_ideal)))}.
  Proof.
    ssprove_valid.
    1: instantiate (1 := Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: all_locs).
    4,5-7,12: apply fsubsetxx.
    - rewrite -fsetUA ; apply fsubsetUl.
    - rewrite -fsetUA fsetUC -fsetUA. apply fsubsetUl.
    - apply fsubsetUr.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      apply fsetUS.
      rewrite fsubUset.
      apply /andP ; split.
      + apply fsubsetU.
        apply /orP ; right.
        apply fsubsetU.
        apply /orP ; right.
        apply fsubsetUl.
      + rewrite fsubUset.
        apply /andP ; split.
        ++ apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetUl.
        ++ apply fsetUS.
           apply fsubsetUl.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsub0set.
    - unfold OVN_i_E. rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - unfold combined_locations. apply fsubsetUr.
  Qed.

  Equations? Aux3 : package combined_locations [interface] OVN_i_E :=
    Aux3 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_ideal ∘ Sigma2.SHVZK_real_aux ∘ Sigma2.SHVZK_ideal)))}.
  Proof.
    ssprove_valid.
    1: instantiate (1 := Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: all_locs).
    4,5-7,12: apply fsubsetxx.
    - rewrite -fsetUA ; apply fsubsetUl.
    - rewrite -fsetUA fsetUC -fsetUA. apply fsubsetUl.
    - apply fsubsetUr.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      apply fsetUS.
      rewrite fsubUset.
      apply /andP ; split.
      + apply fsubsetU.
        apply /orP ; right.
        apply fsubsetU.
        apply /orP ; right.
        apply fsubsetUl.
      + rewrite fsubUset.
        apply /andP ; split.
        ++ apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetUl.
        ++ apply fsetUS.
           apply fsubsetUl.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsub0set.
    - unfold OVN_i_E. rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - unfold combined_locations. apply fsubsetUr.
  Qed.

  Equations? Aux4 : package combined_locations [interface] OVN_i_E :=
    Aux4 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_ideal ∘ Sigma2.SHVZK_real_aux ∘ Sigma2.SHVZK_real)))}.
  Proof.
    ssprove_valid.
    1: instantiate (1 := Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: all_locs).
    4,5-7,12: apply fsubsetxx.
    - rewrite -fsetUA ; apply fsubsetUl.
    - rewrite -fsetUA ; apply fsubsetUl.
    - apply fsubsetUr.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      apply fsetUS.
      rewrite fsubUset.
      apply /andP ; split.
      + apply fsubsetU.
        apply /orP ; right.
        apply fsubsetU.
        apply /orP ; right.
        apply fsubsetUl.
      + rewrite fsubUset.
        apply /andP ; split.
        ++ apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetUl.
        ++ apply fsetUS.
           apply fsubsetUl.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsub0set.
    - unfold OVN_i_E. rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - unfold combined_locations. apply fsubsetUr.
  Qed.

  Equations? Aux5 : package combined_locations [interface] OVN_i_E :=
    Aux5 := {package OVN_i ∘ (par Init_realised
                                  (par Construct_key_realised
                                       (Vote_i_ideal ∘ Sigma2.RUN_interactive)))}.
  Proof.
    ssprove_valid.
    2: instantiate (1 := Alg2.Sigma_locs :|: Alg2.Simulator_locs :|: all_locs).
    11, 4-6: apply fsubsetxx.
    - ssprove_valid.
      1: eapply valid_package_inject_export.
      2: apply Sigma2.RUN_interactive.
      + rewrite !fset_cons -fset0E.
        apply fsubsetUr.
    - apply fsubsetUr.
    - rewrite -fsetUA. apply fsubsetUl.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      apply fsetUS.
      rewrite fsubUset.
      apply /andP ; split.
      + apply fsubsetU.
        apply /orP ; right.
        apply fsubsetU.
        apply /orP ; right.
        apply fsubsetUl.
      + rewrite fsubUset.
        apply /andP ; split.
        ++ apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetU.
           apply /orP ; right.
           apply fsubsetUl.
        ++ apply fsetUS.
           apply fsubsetUl.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsub0set.
    - unfold OVN_i_E. rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - apply fsubsetUr.
  Qed.

  Equations? OVN_i_ideal : package combined_locations [interface] OVN_i_E :=
    OVN_i_ideal := {package OVN_i ∘ (par Init_realised
                                         (par Construct_key_realised
                                              Vote_i_ideal_realised))}.
  Proof.
    ssprove_valid.
    1-4: apply fsubsetxx.
    - unfold Game_import.
      rewrite -fset0E !fset0U.
      apply fsub0set.
    - unfold OVN_i_E. rewrite !fset_cons !fset1E -fset0E !fsetU0.
      rewrite fsetSU ; [ done | apply fsubsetxx].
    - apply fsubsetUr.
    - unfold combined_locations.
      rewrite -!fsetUA.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      repeat apply fsetUS.
      apply fsubsetU.
      apply /orP ; right.
      apply fsetUS.
      apply fsetUS.
      apply fsetUS.
      apply fsetUS.
      rewrite fsetUC -fsetUA.
      apply fsubsetUl.
  Qed.


  Theorem OVN_vote_hiding:
    ∀ LA A,
      ValidPackage LA OVN_i_E A_export A →
      fdisjoint LA combined_locations →
      fdisjoint (RO1.RO_locs :|: RO2.RO_locs) (Alg1.Sigma_locs :|: Alg1.Simulator_locs) →
      fdisjoint (RO1.RO_locs :|: RO2.RO_locs) (Alg2.Sigma_locs :|: Alg2.Simulator_locs) →
      AdvantageE OVN_i_real OVN_i_ideal A <=
          Sigma2.ɛ_SHVZK (((A ∘ par (par Construct_key_realised Vote_i_realised)
                                (ID [interface val #[INIT] : 'pid → 'unit ])) ∘ Init_real)
                              ∘ Sigma2.SHVZK_real_aux)
          + Sigma2.ɛ_SHVZK (((A ∘ par (par Construct_key_realised Vote_i_ideal_realised)
                                            (ID [interface val #[INIT] : 'pid → 'unit ])) ∘ Init_real)
                                ∘ Sigma2.SHVZK_real_aux).
  Proof.
    intros LA A Va Hdisj Hdisj_RO1 Hdisj_RO2.
    unfold Init_realised.
    ssprove triangle OVN_i_real [::
      (Aux0).(pack) ;
      (Aux1).(pack) ;
      (Aux2).(pack) ;
      (Aux3).(pack) ;
      (Aux5).(pack)
    ] OVN_i_ideal A as ineq.
    eapply ler_trans. 1: exact: ineq.
    clear ineq.
    apply ler_naddr.
    1:{
      eapply eq_ler.
      eapply eq_rel_perf_ind with (inv := inv).
      6,7: apply Hdisj.
      1-3,5: exact _.
      simplify_eq_rel h.
      ssprove_code_simpl.
      destruct h as [h w].
      rewrite ?cast_fun_K ; ssprove_code_simpl.
      ssprove_code_simpl_more ; ssprove_code_simpl.
      ssprove_sync=>r.
      ssprove_sync=>sk.
      ssprove_sync=>?.
      ssprove_sync=>rel.
      ssprove_sync_sigma=>a.
      ssprove_contract_put_get_rhs.
      ssprove_contract_put_get_lhs.
      eapply r_put_vs_put.
      rewrite emptymE.
      ssprove_sync=>e.
      eapply r_put_vs_put.
      ssprove_restore_pre.
      { restore_inv.
        restore_inv.
      }
      ssprove_sync_sigma=>z.
        ssprove_sync=>pks.
        ssprove_sync=>?.
        eapply r_ret.
        split ; done.
      - ssprove_sync=>pks.
        ssprove_sync=>cks.
        ssprove_sync=>?.
        eapply r_ret.
        split ; done.
      - destruct h as [h w].
        ssprove_sync=>cks.
        ssprove_sync=>pks.
        destruct (cks h) eqn:eqcks.
        all: rewrite eqcks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        simpl.
        destruct (pks h) eqn:eqpks.
        all: rewrite eqpks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        ssprove_code_simpl_more.
        ssprove_code_simpl.
        ssprove_sync=>rel.
        ssprove_sync_sigma=>a.
        ssprove_contract_put_get_lhs.
        ssprove_contract_put_get_rhs.
        eapply r_put_vs_put.
        rewrite emptymE.
        ssprove_sync=>e.
        eapply r_put_vs_put.
        ssprove_restore_pre.
        1: ssprove_invariant.
        ssprove_sync_sigma=>z.
        ssprove_sync=>votes.
        eapply r_put_vs_put.
        ssprove_restore_pre.
        1: ssprove_invariant.
        apply r_ret ; split ; done.
    }
    apply ler_naddr.
    1:{
      eapply eq_ler.
      eapply eq_rel_perf_ind with (inv := inv).
      6,7: apply Hdisj.
      1-3,5: exact _.
      simplify_eq_rel h.
      all: ssprove_code_simpl.
      all: rewrite ?cast_fun_K ; ssprove_code_simpl.
      all: ssprove_code_simpl_more ; ssprove_code_simpl.
      - ssprove_sync=>r.
        ssprove_sync=>sks.
        ssprove_sync=>?.
        ssprove_swap_lhs 0%N.
        ssprove_sync=>rel.
        ssprove_swap_lhs 0%N.
        ssprove_sync_sigma=>a.
        ssprove_sync=>e.
        ssprove_sync_sigma=>z.
        ssprove_sync=>pks.
        ssprove_sync=>?.
        apply r_ret ; split ; done.
      - ssprove_sync=>pks.
        ssprove_sync=>cks.
        ssprove_sync=>?.
        eapply r_ret.
        split ; done.
      - destruct h as [h w].
        ssprove_sync=>cks.
        ssprove_sync=>pks.
        destruct (cks h) eqn:eqcks.
        all: rewrite eqcks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        simpl.
        destruct (pks h) eqn:eqpks.
        all: rewrite eqpks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        ssprove_code_simpl_more.
        ssprove_code_simpl.
        ssprove_sync=>rel.
        ssprove_sync_sigma=>a.
        ssprove_contract_put_get_lhs.
        ssprove_contract_put_get_rhs.
        eapply r_put_vs_put.
        rewrite emptymE.
        ssprove_sync=>e.
        eapply r_put_vs_put.
        ssprove_restore_pre.
        1: ssprove_invariant.
        ssprove_sync_sigma=>z.
        ssprove_sync=>votes.
        eapply r_put_vs_put.
        ssprove_restore_pre.
        1: ssprove_invariant.
        apply r_ret ; split ; done.
    }
    apply ler_add.
    2:{ unfold Aux3, Aux5, pack.
        rewrite par_commut.
        rewrite Advantage_sym.
        rewrite par_commut.
        erewrite Advantage_par.
        - unfold Sigma1.ɛ_SHVZK.
          rewrite -Advantage_link.
          rewrite -Advantage_link.
          done.
        - ssprove_valid.
          1,3: apply fsubsetxx.
          unfold Game_import.
          rewrite -fset0E fset0U.
          apply fsub0set.
        - ssprove_valid.
          4,5: apply fsubsetxx.
          + apply Init_real.
          + apply Sigma1.SHVZK_real_aux.
          + apply Sigma1.SHVZK_real.
          + instantiate (1 := all_locs :|: Alg1.Sigma_locs) ; apply fsubsetUl.
          + apply fsubsetUr.
        - ssprove_valid.
          + apply Init_real.
          + apply Sigma1.SHVZK_real_aux.
          + apply Sigma1.SHVZK_ideal.
          + instantiate (1 := Alg1.Simulator_locs :|: Alg1.Sigma_locs) ; apply fsubsetUr.
          + apply fsubsetUl.
          + apply fsubsetUl.
          + apply fsubsetUr.
        - ssprove_valid.
        - apply trimmed_package_par.
          1: ssprove_valid.
          + unfold Construct_key_realised, trimmed.
            rewrite -link_trim_commut.
            f_equal.
            apply trimmed_package_cons, trimmed_empty_package.
          + unfold Vote_i_ideal_realised, trimmed.
            rewrite -link_trim_commut.
            f_equal.
            apply trimmed_package_cons, trimmed_empty_package.
        - unfold trimmed.
          rewrite -link_trim_commut.
          f_equal.
          apply trimmed_package_cons, trimmed_empty_package.
        - unfold trimmed.
          rewrite -link_trim_commut.
          f_equal.
          apply trimmed_package_cons, trimmed_empty_package.
    }
    apply ler_naddr.
    1: {
      eapply eq_ler.
      eapply eq_rel_perf_ind with (inv := inv).
      6,7: apply Hdisj.
      1-3,5: exact _.
      simplify_eq_rel h.
      all: ssprove_code_simpl.
      all: rewrite ?cast_fun_K ; ssprove_code_simpl.
      all: ssprove_code_simpl_more ; ssprove_code_simpl.
      - ssprove_sync=>r.
        ssprove_sync=>sks.
        ssprove_sync=>?.
        ssprove_sync=>e.
        ssprove_sync=>rel.
        ssprove_sync_sigma=>a.
        ssprove_sync=>pks.
        ssprove_sync=>_.
        apply r_ret ; split ; done.
      - ssprove_sync=>pks.
        ssprove_sync=>cks.
        ssprove_sync=>?.
        eapply r_ret.
        split ; done.
      - destruct h as [h w].
        ssprove_sync=>cks.
        ssprove_sync=>pks.
        destruct (cks h) eqn:eqcks.
        all: rewrite eqcks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        simpl.
        destruct (pks h) eqn:eqpks.
        all: rewrite eqpks.
        2: ssprove_sync=>? ; apply r_ret; split ; done.
        ssprove_code_simpl_more.
        ssprove_code_simpl.
        eapply r_assertD.
        {
          intros [h0 h1] ?.
          destruct w.
          all: simpl ; unfold pack_statement2 ; rewrite !otf_fto .
          all: rewrite π2.relation_valid_left π2.relation_valid_right ; reflexivity.
        }
        intros rel_left rel_right.
        ssprove_sync_sigma.
    apply ler_naddl.
    2:{ rewrite par_commut.
        rewrite Advantage_sym.
        rewrite par_commut.
        rewrite Advantage_sym.
        erewrite Advantage_par.
        - unfold Sigma1.ɛ_SHVZK.
          rewrite -Advantage_link.
          rewrite -Advantage_link.
          done.
        - ssprove_valid.
          1: apply fsubsetxx.
          { unfold Game_import. rewrite -fset0E fset0U. apply fsubsetxx. }
          apply fsubsetxx.
        - repeat apply valid_link ; exact _.
        - eapply valid_link.
          2: eapply valid_link ; exact _.
          exact _.
        - ssprove_valid.
        - apply trimmed_package_par.
          1: ssprove_valid.
          + unfold Construct_key_realised, trimmed.
            rewrite -link_trim_commut.
            f_equal.
            apply trimmed_package_cons, trimmed_empty_package.
          + unfold Vote_i_realised, trimmed.
            rewrite -link_trim_commut.
            f_equal.
            apply trimmed_package_cons, trimmed_empty_package.
        - unfold trimmed.
          rewrite -link_trim_commut.
          f_equal.
          apply trimmed_package_cons, trimmed_empty_package.
        - unfold trimmed.
          rewrite -link_trim_commut.
          f_equal.
          apply trimmed_package_cons, trimmed_empty_package.
    }
    apply ler_naddr.
    1:{ apply eq_ler.
        eapply eq_rel_perf_ind with (inv := inv).
        6,7: apply Hdisj.
        3,5: exact _.
        2: apply Aux1.
        1: apply Aux0.
        simplify_eq_rel h.
        all: ssprove_code_simpl.
        all: rewrite ?cast_fun_K ; ssprove_code_simpl.
        all: ssprove_code_simpl_more ; ssprove_code_simpl.
        - ssprove_sync=>x.
          ssprove_sync=>sk.
          ssprove_sync=>?.
          ssprove_swap_rhs 0%N.
          ssprove_sync=>rel.
          ssprove_swap_rhs 0%N.
          { eapply rsamplerC. }
          ssprove_sync_sigma=>a.
          ssprove_sync=>e.
          ssprove_sync_sigma=>z.
          ssprove_sync=>pk.
          ssprove_sync=>_.
          apply r_ret.
          split ; done.
        - ssprove_sync=>pk.
          ssprove_sync=>key.
          ssprove_sync=>?.
          apply r_ret.
          split ; done.
        - destruct h.
          ssprove_sync=>key.
          ssprove_sync=>sk.
          destruct (key s) eqn:keyeq.
          all: rewrite keyeq.
          2:{ ssprove_sync=>?.
              apply r_ret.
              split ; done.
          }
          simpl.
          destruct (sk s) eqn:skeq.
          all: rewrite skeq.
          2:{ ssprove_sync=>?.
              apply r_ret.
              split ; done.
          }
          ssprove_code_simpl_more.
          ssprove_code_simpl.
          ssprove_sync=>rel.
          ssprove_sync_sigma=>a.
          ssprove_contract_put_get_lhs.
          ssprove_contract_put_get_rhs.
          ssprove_sync=>?.
          rewrite emptymE.
          ssprove_sync=>e.
          ssprove_sync=>_.
          ssprove_sync_sigma=>z.
          ssprove_sync=>votes.
          ssprove_sync=>_.
          apply r_ret.
          split ; done.
    }
    apply eq_ler.
    eapply eq_rel_perf_ind with (inv := inv).
    6,7: apply Hdisj.
    3,5: exact _.
    2: apply Aux0.
    1: exact _.
    simplify_eq_rel h.
    + ssprove_code_simpl.
      rewrite !cast_fun_K.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_sync=>x.
      ssprove_sync=>sk.
      ssprove_sync=>?.
      ssprove_sync=>rel.
      ssprove_sync_sigma=>a.
      ssprove_contract_put_get_lhs.
      rewrite emptymE.
      apply r_put_lhs.
      ssprove_sync=>e.
      apply r_put_lhs.
      ssprove_restore_pre.
      { ssprove_invariant.
        repeat eapply preserve_update_l_ignored_heap_ignore.
        3: apply preserve_update_mem_nil.
        all: unfold RO1.RO_locs, RO2.RO_locs.
        + rewrite fset_cons -fset0E fsetU0. auto_in_fset.
        + rewrite fset_cons -fset0E fsetU0. auto_in_fset.
      }
      ssprove_sync_sigma=>z.
      ssprove_sync=>?.
      ssprove_sync=>?.
      eapply r_ret.
      split; done.
    + ssprove_sync=>x.
      ssprove_sync=>key.
      ssprove_sync=>?.
      apply r_ret.
      move=> s0 s1 H.
      split ; done.
    + ssprove_code_simpl.
      destruct h as [h w].
      rewrite !cast_fun_K.
      ssprove_code_simpl.
      ssprove_sync=>key.
      ssprove_sync=>sk.
      destruct (key h) eqn:eq_key.
      all: rewrite eq_key.
      2: { ssprove_sync=>x.
          apply r_ret.
          move=> s0 s1 H.
          split; done.
      }
      simpl.
      destruct (sk h) eqn:eq_sk.
      all: rewrite eq_sk.
      2:{ ssprove_sync=>x.
          apply r_ret.
          move=> s0 s1 H.
          split ; done.
      }
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_sync=>rel.
      ssprove_sync_sigma=>a.
      ssprove_contract_put_get_lhs.
      ssprove_contract_put_get_rhs.
      ssprove_sync=>?.
      rewrite emptymE.
      ssprove_sync=>e.
      ssprove_sync=>_.
      ssprove_sync_sigma=>z.
      ssprove_sync=>votes.
      ssprove_sync=>_.
      apply r_ret.
      split ; done.
  Qed.
