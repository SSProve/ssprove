Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Import NominalPrelude
  TotalProbability HybridArgument.
Import PackageNotation.
#[local] Open Scope package_scope.

From SSProve.Crypt.examples.PKE Require Import Scheme.
Import PKE.


Notation "x ← 'get' n [ i ] ;; c" :=
    ( y ← get n ;;
      #assert isSome (y i) as Hi ;;
      let x := getSome (y i) Hi in c )
    (at level 100, n at next level, right associativity,
    format "x  ←  get  n  [  i  ]  ;;  '//' c")
    : package_scope.

Notation "'#put' n [ i ] ':=' u ;; c" :=
    ( y ← get n ;; #put n := setm y i u ;; c )
    (at level 100, u at next level, right associativity,
    format "#put  n  [  i  ]  :=  u  ;;  '//' c")
    : package_scope.


Section MultiInstanceDef.

(* Multi-CPA *)
Definition IMI_CPA P n := [interface
  [ GEN ] : { 'fin n ~> P.(Pub) } ;
  [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) }
].

Definition pks_loc P := mkloc 51 (emptym : chMap nat P.(Pub)).

Definition MI_CPA P n b :
  game (IMI_CPA P n) :=
  [package [fmap pks_loc P ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      '(_, pk) ← P.(keygen) ;;
      #put pks_loc P [ j ] := pk ;;
      ret pk
    } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } '(j, m) {
      pk ← get pks_loc P [ j ] ;;
      if b then
        P.(enc) pk m
      else
        P.(sample_Cip)
    }
  ].

Definition counts_loc := mkloc 52 (emptym : chMap nat nat).

Definition MI_COUNT P n q :
  package (IMI_CPA P n) (IMI_CPA P n) :=
  [package [fmap counts_loc ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      call [ GEN ] : { 'fin n ~> P.(Pub) } j
    } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } '(j, m) {
      counts ← get counts_loc ;;
      let countj := odflt 0 (counts j) in
      #assert countj < q ;;
      c ← call [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } (j, m) ;;
      #put counts_loc :=
        setm counts j countj.+1 ;;
      ret c
    }
  ].

End MultiInstanceDef.

#[local] Open Scope sep_scope.

Notation MI_MT_CPA P n q :=
  (λ b, MI_COUNT P n q ∘ MI_CPA P n b).

Section MultiInstance.

Definition HYB_MI_CPA P n q :
  package (unionm (ICPA P) (IPICK nat))
    (IMI_CPA P n) :=
  [package [fmap pks_loc P ; counts_loc ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      i ← call [ PICK ] : { unit ~> nat } tt ;;
      pk ← (
        if i == j then
          call [ GEN ] tt
        else
          '(_, pk) ← P.(keygen) ;;
          ret pk
      ) ;;
      #put pks_loc P [ j ] := pk ;;
      ret pk
    } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } '(j, m) {
      counts ← get counts_loc ;;
      let countj := odflt 0 (counts j) in
      #assert countj < q ;;
      pk ← get pks_loc P [ j ] ;;
      i ← call [ PICK ] : { unit ~> nat } tt ;;
      c ← (
        if j < i then
          c ← P.(sample_Cip) ;; ret c
        else if i < j then
          c ← P.(enc) pk m ;; ret c
        else
          call [ QUERY ] m
      ) ;;
      #put counts_loc :=
        setm counts j countj.+1 ;;
      ret c
    }
  ].

Lemma rsame_head_scheme {A B}
  {m : raw_code A} {f₀ f₁ : A → raw_code B}
  {pre : precond} {post : postcond B B}
  `{Vm : ValidCode emptym [interface] A m} :
  (∀ a : A, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄)
  → ⊢ ⦃ pre ⦄ x ← m ;; f₀ x ≈ x ← m ;; f₁ x ⦃ post ⦄.
Proof.
  intros. eapply rsame_head_alt; [ exact _ | .. | done ].
  1,2: intros; exfalso; eapply fhas_empty; eassumption.
Qed.

Notation inv P q := (
  heap_ignore ([fmap mpk_loc P ; count_loc ])
  ⋊ couple_rhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks q = mpk)
  ⋊ couple_rhs counts_loc count_loc (λ cs c, odflt 0 (cs q) = c)
).

Ltac ssprove_ret :=
  ssprove_restore_mem; [ ssprove_invariant; try done | by apply r_ret ].

Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme : ssprove_code_simpl.

Lemma MI_CPA_0_n P n q b :
  perfect (IMI_CPA P n) (MI_MT_CPA P n q b)
    (HYB_MI_CPA P n q ∘ (MT_CPA P q true ||
       CONST (if b then 0 else n))).
Proof.
  ssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv P (if b then 0 else n))).
  { by ssprove_invariant. }
  simplify_eq_rel arg.
  - ssprove_code_simpl.
    destruct ((if b then 0 else n) == arg)%B eqn:E.
    + rewrite E /=.
      ssprove_code_simpl.
      apply rsame_head_scheme => [[sk pk]].
      ssprove_swap_rhs 0.
      apply r_get_vs_get_remember => [pks].
      apply r_put_rhs, r_put_vs_put.
      ssprove_ret.
      move: E => /eqP -> H'.
      by rewrite setmE eq_refl.
    + rewrite E /=.
      ssprove_code_simpl.
      apply rsame_head_scheme => [[sk pk]].
      apply r_get_vs_get_remember => [pks].
      apply r_put_vs_put.
      ssprove_ret.
      by rewrite setmE E.
  - destruct arg as [j m]. simpl.
    ssprove_code_simpl.
    apply r_get_vs_get_remember => [counts].
    ssprove_sync => Hcnt.
    destruct b; [ destruct (0 < j) eqn:E |]; simpl.
    + ssprove_code_simpl.
      apply r_get_vs_get_remember => [pks].
      ssprove_code_simpl_more.
      ssprove_sync => Hpks.
      apply rsame_head_scheme => [pk].
      apply r_put_vs_put.
      ssprove_ret.
      by rewrite setmE -(negbK (0%N == j)%B) eq_sym -lt0n E.
    + simpl in *. ssprove_code_simpl.
      apply r_get_vs_get_remember => [pks].
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_sync => Hpks.
      ssprove_swap_seq_rhs [:: 2; 3; 1 ]%N.
      apply r_get_remember_rhs => [c].
      apply r_get_remember_rhs => [mpk].
      ssprove_rem_rel 1%N => ?.
      ssprove_rem_rel 0%N => ?; subst.
      rewrite lt0n in E.
      move: E => /eqP E. subst.
      rewrite {}E {j} in Hcnt, Hpks |- *.
      rewrite Hcnt /=.
      destruct (pks 0) eqn:E'.
      2: assert (Hpks' := Hpks).
      2: by rewrite E' in Hpks'.
      move: Hpks. rewrite E' /= => _.
      apply r_put_rhs.
      apply rsame_head_scheme => [c].
      apply r_put_vs_put.
      ssprove_ret.
      by rewrite setmE eq_refl.
    + rewrite ltn_ord.
      ssprove_sync => pks.
      ssprove_code_simpl_more.
      ssprove_sync => Hpks.
      ssprove_code_simpl.
      apply rsame_head_scheme => [c].
      apply r_put_vs_put.
      ssprove_ret.
      by rewrite setmE -(negbK (n == j)%B) neq_ltn ltn_ord orbC.
Qed.

Notation inv' P i := (
  heap_ignore ([fmap mpk_loc P ; count_loc ])
  ⋊ couple_lhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks i%N = mpk)
  ⋊ couple_lhs counts_loc count_loc (λ cs c, odflt 0 (cs i%N) = c)
  ⋊ couple_rhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks i.+1%N = mpk)
  ⋊ couple_rhs counts_loc count_loc (λ cs c, odflt 0 (cs i.+1%N) = c)
).

Lemma eq_succ (k : nat) : (k.+1 == k)%B = false.
Proof. rewrite gtn_eqF //. Qed.

Lemma MI_CPA_i P n q i :
  perfect (IMI_CPA P n)
    (HYB_MI_CPA P n q ∘
      (MT_CPA P q false || CONST i   ))
    (HYB_MI_CPA P n q ∘
      (MT_CPA P q true  || CONST i.+1)).
Proof.
  ssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv' P i)).
  { by ssprove_invariant. }
  simplify_eq_rel arg.
  - ssprove_code_simpl.
    destruct (i == arg)%B eqn:E; [| destruct (i.+1 == arg)%B eqn:E' ].
    + rewrite E /=.
      ssprove_code_simpl.
      move: E => /eqP {i}->.
      rewrite gtn_eqF //=.
      apply rsame_head_scheme => [[sk pk]].
      ssprove_swap_lhs 0%N.
      ssprove_code_simpl.
      apply r_get_vs_get_remember => pks.
      apply r_put_lhs, r_put_vs_put.
      ssprove_ret.
      * by rewrite setmE eq_refl.
      * by rewrite setmE eq_succ.
    + rewrite E E' /=.
      ssprove_code_simpl.
      apply rsame_head_scheme => [[sk pk]].
      ssprove_swap_rhs 0%N.
      apply r_get_vs_get_remember => pks.
      apply r_put_rhs, r_put_vs_put.
      ssprove_ret.
      * by rewrite setmE E.
      * by rewrite setmE E'.
    + rewrite E E' /=.
      ssprove_code_simpl.
      apply rsame_head_scheme => [[sk pk]].
      apply r_get_vs_get_remember => pks.
      apply r_put_vs_put.
      ssprove_ret.
      * by rewrite setmE E.
      * by rewrite setmE E'.
  - destruct arg as [j m] => /=.
    ssprove_code_simpl.
    apply r_get_vs_get_remember => counts.
    ssprove_sync => Hcnt.
    destruct j as [j Hj].
    simpl in *.
    hybrid_cases j i.
    + ssprove_sync => pks.
      ssprove_sync => Hpks.
      apply rsame_head_scheme => [c].
      apply r_put_vs_put.
      ssprove_ret.
      * rewrite setmE -(negbK (i == j)%B) neq_ltn. by replace_many.
      * rewrite setmE -(negbK (i.+1 == j)%B) neq_ltn. by replace_many.
    + ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_lhs [:: 4; 5 ]%N.
      apply r_get_vs_get_remember => pks.
      ssprove_sync => Hpks.
      apply r_get_remember_lhs => c.
      ssprove_rem_rel 2%N => <-. rewrite Hcnt.
      apply r_get_remember_lhs => pk.
      ssprove_rem_rel 3%N => Hpk. rewrite -Hpk Hpks /=.
      apply r_put_lhs, rsame_head_scheme => [cip].
      apply r_put_vs_put.
      ssprove_ret.
      * by rewrite setmE eq_refl.
      * by rewrite setmE eq_succ.
    + ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 4; 5 ]%N.
      apply r_get_vs_get_remember => pks.
      ssprove_sync => Hpks.
      apply r_get_remember_rhs => c.
      ssprove_rem_rel 0%N => <-. rewrite Hcnt.
      apply r_get_remember_rhs => pk.
      ssprove_rem_rel 1%N => Hpk. rewrite -Hpk /=.
      destruct (pks i.+1) as [ pk' |] eqn:E.
      2: assert (Hpks' := Hpks).
      2: by rewrite E in Hpks'.
      move: Hpks. rewrite E /= => _.
      apply r_put_rhs, rsame_head_scheme => [cip].
      apply r_put_vs_put.
      ssprove_ret.
      * by rewrite setmE eq_sym eq_succ.
      * by rewrite setmE eq_refl.
    + ssprove_sync => pks.
      ssprove_sync => Hpks.
      apply rsame_head_scheme => [c].
      apply r_put_vs_put.
      ssprove_ret.
      * rewrite setmE -(negbK (i == j)%B) neq_ltn.
        by replace_many.
      * rewrite setmE -(negbK (i.+1 == j)%B) neq_ltn.
        by replace_many.
Qed.

#[local] Open Scope ring_scope.
#[local] Open Scope sep_scope.

(* Single-to-Multiple hybrid reduction package *)
Notation STM P n q := (HYB_MI_CPA P n q ∘
  (ID (ICPA P) || RAND (unif n))).

Theorem Adv_MI_CPA_SI P n q A
  `{Adversary (IMI_CPA P n) A} :
  AdvOf (MI_MT_CPA P n q) A =
    AdvOf (MT_CPA P q) (A ∘ STM P n q) *+ n.
Proof.
  eapply @Adv_hybrid.
  1-4: intros; ssprove_valid.
  1-2: apply MI_CPA_0_n.
  intros i _; apply MI_CPA_i.
Qed.

End MultiInstance.
