From Coq Require Import Utf8 Lia.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal NominalPrelude HybridArgument.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.
#[local] Open Scope package_scope.


Definition done : Location := (4%N, 'bool).

Definition IGUESS n `{Positive n} :=
  [interface [ 2%N ] : { 'fin n ~> 'fin n × 'bool }].

Definition GUESS n `{Positive n}
  : bool → game (IGUESS n) := λ b,
  [package [fmap done] ;
    [ 2%N ] : { 'fin n ~> 'fin n × 'bool } (g) {
      d ← get done ;;
      if d then
        fail
      else
        #put done := true ;;
        r ← sample uniform n ;;
        ret (r, b && (r == g))%B
    }
  ].

Lemma Pr_GUESS_true {LA} {T'} {A : raw_code T'} {b} {h} {n} `{Positive n} :
  fseparate LA [fmap done] →
  ValidCode LA (IGUESS n) A →
  get_heap h done = true →
  Pr_code (code_link A (GUESS n b)) h
  = Pr_code (code_link A (GUESS n (~~ b))) h.
Proof.
  intros SEP VA.
  move: h.
  induction VA => h HEAP; cbn [code_link].
  - rewrite Pr_code_ret //.
  - fmap_invert H0.
    simplify_linking.
    cbn [bind].
    rewrite 2!Pr_code_get HEAP.
    rewrite 2!Pr_code_bind.
    rewrite Pr_code_fail.
    by rewrite 2!dlet_null_ext.
  - rewrite 2!Pr_code_get.
    by apply H2.
  - rewrite 2!Pr_code_put.
    apply IHVA.
    rewrite get_set_heap_neq //.
    apply fhas_in in H0.
    destruct SEP as [SEP].
    move: SEP => /fdisjointP.
    intros H''.
    specialize (H'' _ H0).
    rewrite domm_set domm0 in H''.
    apply /negP.
    move=> /eqP H'''.
    rewrite H''' in H''.
    rewrite in_fsetU in_fset1 eq_refl // in H''.
  - rewrite 2!Pr_code_sample.
    apply eq_dlet => x.
    by apply H1.
Qed.

Lemma Pr_GUESS {LA} {T'} {A : raw_code T'} {b} {t} {h} {n} `{Positive n} :
  fseparate LA [fmap done] →
  ValidCode LA (IGUESS n) A →
  (dfst (Pr_code (code_link A (GUESS n b)) h) t
    <= dfst (Pr_code (code_link A (GUESS n (~~ b))) h) t + n%:R^-1)%R.
Proof.
  intros SEP VA.
  move: h.
  induction VA => h; cbn [code_link].
  - rewrite Num.Theory.lerDl.
    rewrite Num.Theory.invr_ge0 //.
  - fmap_invert H0.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind].
    rewrite 2!Pr_code_get.
    destruct (get_heap h done) eqn:E.
    { rewrite 2!Pr_code_bind Pr_code_fail.
      rewrite 2!dlet_null_ext /(dfst _) dlet_null_ext.
      rewrite dnullE Num.Theory.lerDl.
      rewrite Num.Theory.invr_ge0 //.
    }
    cbn [bind]. 
    rewrite 2!Pr_code_put.
    rewrite 2!Pr_code_sample.
    do 2 rewrite dlet_dlet dlet_uniform.
    under eq_bigr => i _.
    { erewrite Pr_GUESS_true; do 2 try done.
      2: rewrite get_set_heap_eq //. over. }
    cbn beta.
    rewrite -{3}(GRing.mul1r n%:R^-1)%R.
    rewrite -GRing.mulrDl.
    apply Num.Theory.ler_pM => //.
    1: apply Num.Theory.sumr_ge0 => i _ //.
    1: rewrite Num.Theory.invr_ge0 //.
    rewrite GRing.addrC (bigD1 x) //.
    apply Num.Theory.lerD.
    1: apply le1_mu1.
    rewrite (bigD1 x erefl) //.
    rewrite -(GRing.add0r (bigop.body _ _ _)).
    apply Num.Theory.lerD => //.
    apply Num.Theory.ler_sum => j /negP H'.
    destruct (j == x)%B eqn:E' => //.
    rewrite E' //.
    rewrite andbC /= andbC //.
  - rewrite 2!Pr_code_get.
    by apply H2.
  - rewrite 2!Pr_code_put.
    apply IHVA.
  - rewrite 2!Pr_code_sample.
    do 2 rewrite dlet_dlet dletE.
    eapply Order.le_trans.
    1: apply le_psum.
    1: move=> y; apply /andP; split.
    1: apply Num.Theory.mulr_ge0 => //.
    1: apply Num.Theory.ler_pM; [ | | | apply H1 ]; done.
    1: eapply eq_summable.
    1: intros y; rewrite GRing.mulrDr; reflexivity.
    1: apply summableD.
    1: apply summable_mu_wgtd => y.
    1: apply /andP; split; [ done |].
    1: apply le1_mu1.
    1: apply summableZr.
    1: apply summable_mu.
    under eq_psum.
    1: intros y; rewrite GRing.mulrDr; over.
    rewrite psumD.
    2,3: intros y; apply Num.Theory.mulr_ge0 => //.
    2: rewrite Num.Theory.invr_ge0 //.
    2: apply summable_mu_wgtd.
    2: intros y; apply /andP; split; [ done |].
    2: apply le1_mu1.
    2: apply summable_mu_wgtd.
    2: intros y; apply /andP; split.
    2: rewrite Num.Theory.invr_ge0 //.
    2: rewrite Num.Theory.invf_le1.
    2: rewrite Num.Theory.ler1n //.
    2: rewrite Num.Theory.ltr0n //.
    apply Num.Theory.lerD => //.
    rewrite psumZr.
    2: rewrite Num.Theory.invr_ge0 //.
    apply Num.Theory.ler_piMl.
    1: rewrite Num.Theory.invr_ge0 //.
    apply le1_mu.
Qed.

Lemma Adv_GUESS {A} {n} `{Positive n} :
  ValidPackage (loc A) (IGUESS n) A_export A →
  (AdvOf (GUESS n) A <= n%:R^-1)%R.
Proof.
  intros VA.
  pose (π := fresh ([fmap done] : Locations, as_nom (GUESS n true), as_nom (GUESS n false)) (A, loc A)).
  rewrite -{1}(@rename_alpha _ A π).
  unfold Adv.
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite 2!Pr_Pr_rand 2!resolve_link.

  apply (rename_valid π) in VA.
  assert (H' : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H').

  rewrite Num.Theory.ler_distlC.
  apply /andP; split.
  - rewrite Num.Theory.lerBlDr.
    apply: Pr_GUESS.
    rewrite fseparate_disj.
    eauto with nominal_db.
  - apply: Pr_GUESS.
    rewrite fseparate_disj.
    eauto with nominal_db.
Qed.

Definition IGUESSL n `{Positive n} :=
  [interface [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool }].

Definition GUESSL n `{Positive n} l
  : bool → game (IGUESSL n) := λ b,
  [package [fmap done] ;
    [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool } (g) {
      #assert length g <= l ;;
      d ← get done ;;
      #assert ~~ d ;;
      #put done := true ;;
      r ← sample uniform n ;;
      ret (r, b && (r \in g))%B
    }
  ].

Definition doneh : Location := (5%N, 'bool).

Definition GUESSH n `{Positive n} l
  : package (unionm (IPICK nat) (IGUESS n)) (IGUESSL n) :=
  [package [fmap doneh] ;
    [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool } (g) {
      #assert length g <= l ;;
      d ← get doneh ;;
      #assert ~~ d ;;
      #put doneh := true ;;
      i ← call [ pick ] tt ;;
      let g := drop i g in
      let h := head (chCanonical _) g in
      let t := behead g in 
      '(r, b) ← call [ 2%N ] h ;;
      ret (r, ((g != nil) && b) || (r \in t))%B
    }
  ].

Lemma Multi_pf b l n `{Positive n} :
  perfect (IGUESSL n) (GUESSL n l b)
    (GUESSH n l ∘ (GUESS n true || PICK (if b then 0 else l))).
Proof.
  ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore [fmap doneh] ⋊ couple_rhs done doneh eq)).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  - ssprove_code_simpl.
    ssprove_sync => Hlen.
    apply r_get_remember_rhs => d'.
    ssprove_swap_rhs 1.
    ssprove_swap_rhs 0.
    apply r_get_vs_get_remember => d.
    ssprove_rem_rel 0 => {d'}<-.
    ssprove_sync => H'.
    rewrite -(negbK d) {}H' {d} /=.
    ssprove_swap_rhs 0%N.
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_sync => r.
    ssprove_restore_mem.
    { ssprove_invariant. }
    apply r_ret => s0 s1 H'; split => //.
    f_equal. destruct b => /=.
    + rewrite drop0.
      by destruct m.
    + rewrite drop_oversize //.
Qed.
  
Lemma guess_hyb l n `{Positive n} A : 
  ValidPackage (loc A) (IGUESSL n) A_export A →
  AdvOf (GUESSL n l) A = (AdvOf (GUESS n) (A ∘ (GUESSH n l) ∘ (ID (IGUESS n) || RAND (unif l))) *+ l)%R.
Proof.
  intros VA.
  eapply (Adv_hybrid (Multi := λ b, GUESSL n l b) (Game := λ b, GUESS n b)).
  1-4: ssprove_valid.
  1,2: apply Multi_pf.
  intros i _.
  ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore emptym ⋊ couple_rhs done doneh implb)).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  - ssprove_code_simpl.
    ssprove_sync => Hlen.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros d.
    ssprove_sync => H'.
    rewrite -(negbK d) {d}H' /=.
    ssprove_swap_lhs 0%N.
    ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember => d'.
    ssprove_rem_rel 0%N.
    rewrite implybF; destruct d' => _ //.
    do 2 apply r_put_vs_put.
    ssprove_sync => r.
    ssprove_restore_mem. { ssprove_invariant. }
    apply r_ret => s0 s1 H'; split => //.
    f_equal.
    change (i.+1) with (1 + i)%N.
    rewrite andbC -drop_drop /= .
    destruct (drop i m) eqn:E; rewrite E //= drop0.
    by destruct l0.
Qed.

Definition IReplacement n `{Positive n} :=
  [interface [ 3 ] : { 'unit ~> 'fin n }].

Definition WReplacement n `{Positive n}
  : game (IReplacement n) :=
  [package emptym ;
    [ 3 ] : { 'unit ~> 'fin n } (g) {
      r ← sample uniform n ;;
      ret r
    }
  ].

Definition prev_loc n `{Positive n} : Location := (5%N, chList 'fin n).

Definition WOReplacement n `{Positive n}
  : game (IReplacement n) :=
  [package [fmap prev_loc n ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      r ← sample uniform n ;;
      prev ← get prev_loc n ;;
      #assert r \notin prev ;;
      #put prev_loc n := r :: prev ;;
      ret r
    }
  ].

Definition Replacement n `{Positive n} b :=
  if b then WReplacement n else WOReplacement n.

Definition count_loc : Location := (6, 'nat).

Definition Counter n `{Positive n} k
  : package (IReplacement n) (IReplacement n) :=
  [package [fmap count_loc ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      c ← get count_loc ;;
      #assert c < k ;;
      #put count_loc := c.+1 ;;
      r ← call [ 3%N ] tt ;;
      ret r
    }
  ].

Definition HReplacement n `{Positive n} k i
  : package (IGUESSL n) (IReplacement n) :=
  [package [fmap count_loc ; prev_loc n ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      c ← get count_loc ;;
      #assert (c < k)%N ;;
      prev ← get prev_loc n ;;
      #put count_loc := c.+1 ;;
      if (c < i)%N then
        r ← sample uniform n ;;
        #assert r \notin prev ;;
        #put prev_loc n := r :: prev ;;
        ret r
      else if (c > i)%N then
        r ← sample uniform n ;;
        ret r
      else
        '(r, b) ← call [ 3%N ] prev ;;
        #assert ~~ b ;;
        ret r
    }
  ].

Definition CReplacement n `{Positive n} k b : nom_package :=
  Counter n k ∘ (if b then WReplacement n else WOReplacement n).

Lemma replace_hyb_0 {n} `{Positive n} {q} :
  perfect (IReplacement n) (CReplacement n q true)
    (HReplacement n q 0 ∘ GUESSL n 0 true).
Proof.
  unfold CReplacement. ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore [fmap prev_loc n; done ]
    ⋊ couple_rhs count_loc (prev_loc n) (λ c prev, length prev <= c)%N
    ⋊ couple_rhs count_loc done (λ c d, (c != 0)%N = d)%N
  )).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl.
  apply r_get_vs_get_remember => c.
  ssprove_sync => Hq.
  destruct c => //=.
  - ssprove_code_simpl_more.
    apply r_get_remember_rhs => prev.
    ssprove_rem_rel 1%N => H'.
    rewrite H' /=.
    ssprove_swap_rhs 0%N.
    apply r_get_remember_rhs => d.
    ssprove_rem_rel 0%N => <- /=.
    rewrite leqn0 in H'.
    move: H' => /eqP.
    rewrite List.length_zero_iff_nil => -> {prev} /=.
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_sync => r.
    ssprove_restore_mem.
    { ssprove_invariant. }
    by apply r_ret.
  - apply r_get_remember_rhs => prev.
    apply r_put_vs_put.
    ssprove_sync => r.
    ssprove_restore_mem.
    { ssprove_invariant.
      intros H'. apply ltnW, H'.
    }
    by apply r_ret.
Qed.

Lemma replace_hyb_q {n} `{Positive n} {q} :
  perfect (IReplacement n) (CReplacement n q false)
    (HReplacement n q q ∘ GUESSL n q true).
Proof.
  unfold CReplacement. ssprove_share. eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl.
  ssprove_sync_eq => c.
  ssprove_sync => Hq.
  rewrite -> Hq => //=.
  ssprove_code_simpl_more.
  ssprove_swap_seq_lhs [:: 1%N; 0%N ].
  eapply rpost_weaken_rule.
  { apply rreflexivity_rule. }
  intros [? ?] [? ?] E. by noconf E.
Qed.

Lemma hybrid_cases (c i : nat) (T : Type) :
  ((c < i)%coq_nat → T) →
  ((c = i) → T) →
  ((c = i.+1) → T) →
  ((c > i.+1)%coq_nat → T) →
  T.
Proof.
  intros H1 H2 H3 H4.
  destruct (c < i)%N eqn:E1; move: E1 => /ltP // E1.
  destruct (c == i)%B eqn:E2; move: E2 => /eqP // E2.
  destruct (c == i.+1)%B eqn:E3; move: E3 => /eqP // E3.
  destruct (c > i.+1)%N eqn:E4; move: E4 => /ltP // E4. lia.
Qed.

Ltac replace_true e :=
  progress ( replace e with true in * by (symmetry; apply /ltP; lia) ).

Ltac replace_false e :=
  progress ( replace e with false in * by (symmetry; apply /ltP; lia) ).

Lemma replace_hyb_i {n} `{Positive n} {q i} : i < q →
  perfect (IReplacement n) (HReplacement n q i ∘ GUESSL n i true)
    (HReplacement n q i.+1 ∘ GUESSL n i.+1 false).
Proof.
  intros H'.
  unfold CReplacement. ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore [fmap prev_loc n; done ]
    ⋊ couple_lhs count_loc (prev_loc n) (λ c prev, length prev <= c)%N
    ⋊ rel_app [:: (lhs, count_loc); (lhs, prev_loc n); (rhs, prev_loc n)]
      (λ c pl pr, c < i.+1 → pl = pr)
    ⋊ couple_lhs count_loc done (λ c d, (c > i)%N = d)%N
    ⋊ couple_rhs count_loc done (λ c d, (c > i.+1)%N = d)%N
  )).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl.
  apply r_get_vs_get_remember => c.
  ssprove_sync => Hq.
  apply r_get_remember_lhs => prev.
  apply r_get_remember_rhs => prev'.
  ssprove_rem_rel 2%N => Hprev.
  apply (hybrid_cases c i) => H''.
  - replace_true (c < i) => /=.
    replace_true (c < i.+1) => /=.
    rewrite -Hprev {Hprev prev'} //.
    apply r_put_vs_put.
    ssprove_sync => r.
    ssprove_sync => Hr.
    apply r_put_vs_put.
    ssprove_restore_mem.
    { ssprove_invariant; admit. }
    by apply r_ret.
  - subst.
    replace_false (i < i) => /=.
    replace_true (i < i.+1) => /=.
    rewrite -Hprev {Hprev prev'} //.
    ssprove_code_simpl_more.
    ssprove_swap_lhs 1%N.
    ssprove_swap_lhs 0%N.
    apply r_get_remember_lhs => d.
    ssprove_rem_rel 1%N.
    replace_false (i < i) => <- /=.
    ssprove_rem_rel 3%N => -> /=.

Admitted.

Lemma replace_hyb2 q n `{Positive n} A : 
  ValidPackage (loc A) (IReplacement n) A_export A →
  (AdvOf (CReplacement n q) A <= n%:R^-1 *+ 'C(q, 2))%R.
Proof.
  intros VA.
  rewrite -triangular_sum.
  rewrite -(GRing.mulr_natl n%:R^-1).
  rewrite GRing.natr_sum.
  rewrite GRing.mulr_suml.
  under eq_bigr.
  1: intros i _; rewrite GRing.mulr_natl; over.
  eapply Order.le_trans. {
    eapply (Adv_hybrid_dep
      (Game := λ i b, HReplacement n q i ∘ GUESSL n i b)%sep).
    1,2,3: intros; ssprove_valid.
    1: apply replace_hyb_0.
    1: apply replace_hyb_q.
    1: intros. by apply replace_hyb_i. }
  apply Num.Theory.ler_sum_nat => i H'.
  rewrite Adv_reduction.
  rewrite guess_hyb.
  rewrite Num.Theory.lerMn2r.
  apply /orP; right.
  apply Adv_GUESS.
  ssprove_valid.
Qed.
