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

Context (P : scheme) (n : nat).

(* Multi-CPA *)
Definition I_MCPA :=
  [interface
    [ GEN ] : { 'fin n ~> P.(Pub) } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) }
  ].

Definition pks_loc := mkloc 51 (emptym : chMap nat P.(Pub)).

Definition MCPA b :
  game I_MCPA :=
  [package [fmap pks_loc ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      '(_, pk) ← P.(keygen) ;;
      #put pks_loc [ j ] := pk ;;
      ret pk
    } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } '(j, m) {
      pk ← get pks_loc [ j ] ;;
      if b then
        P.(enc) pk m
      else
        P.(sample_Cip)
    }
  ].

Definition counts_loc := mkloc 52 (emptym : chMap nat nat).

Definition MCOUNT q :
  package I_MCPA I_MCPA :=
  [package [fmap counts_loc ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      pk ← call [ GEN ] : { 'fin n ~> P.(Pub) } j ;;
      ret pk
    } ;
    [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } '(j, m) {
      counts ← get counts_loc ;;
      let countj := odflt 0 (counts j) in
      #assert (countj < q)%N ;;
      c ← call [ QUERY ] : { 'fin n × P.(Mes) ~> P.(Cip) } (j, m) ;;
      #put counts_loc := setm counts j countj.+1 ;;
      ret c
    }
  ].

End MultiInstanceDef.


Section MultiInstance.

Context (P : scheme) (n : nat).

Definition HMCPA q :
  package (unionm (I_CPA P) (IPICK nat)) (I_MCPA P n) :=
  [package [fmap pks_loc P ; counts_loc ] ;
    [ GEN ] : { 'fin n ~> P.(Pub) } (j) {
      i ← call [pick] : { unit ~> nat } tt ;;
      pk ← (
        if (i == j)%N then
          pk ← call [GEN] tt ;;
          ret pk
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
      #assert (countj < q)%N ;;
      pk ← get pks_loc P [ j ] ;;
      i ← call [pick] : { unit ~> nat } tt ;;
      c ← (
        if (j < i)%N then
          c ← P.(sample_Cip) ;; ret c
        else if (i < j)%N then
          c ← P.(enc) pk m ;; ret c
        else
          c ← call [QUERY] m ;; ret c
      ) ;;
      #put counts_loc := setm counts j countj.+1 ;;
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

Notation inv q := (
  heap_ignore ([fmap mpk_loc P ; count_loc ])
  ⋊ couple_rhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks q = mpk)
  ⋊ couple_rhs counts_loc count_loc (λ cs c, odflt 0 (cs q) = c)
).

Ltac ssprove_ret :=
  ssprove_restore_mem; [ ssprove_invariant; try done | by apply r_ret ].

Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme : ssprove_code_simpl.

Lemma MCPA_0_n q b : perfect (I_MCPA P n)
  (MCOUNT P n q ∘ MCPA P n b)
  (HMCPA q ∘ (MT_CPA P q true || PICK (if b then 0 else n))).
Proof.
  ssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv (if b then 0 else n))).
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

Notation inv' i := (
  heap_ignore ([fmap mpk_loc P ; count_loc ])
  ⋊ couple_lhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks i%N = mpk)
  ⋊ couple_lhs counts_loc count_loc (λ cs c, odflt 0 (cs i%N) = c)
  ⋊ couple_rhs (pks_loc P) (mpk_loc P) (λ pks mpk, pks i.+1%N = mpk)
  ⋊ couple_rhs counts_loc count_loc (λ cs c, odflt 0 (cs i.+1%N) = c)
).

Lemma eq_succ (k : nat) : (k.+1 == k)%B = false.
Proof. rewrite gtn_eqF //. Qed.

Lemma MCPA_i q i : perfect (I_MCPA P n)
  (HMCPA q ∘ (MT_CPA P q false || PICK i   ))
  (HMCPA q ∘ (MT_CPA P q true  || PICK i.+1)).
Proof.
  ssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv' i)).
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

(* Single-to-Multiple hybrid reduction package *)
Notation STM q := (HMCPA q%N ∘ (ID (I_CPA P) || RAND (unif n)))%sep.

Theorem Adv_MI_CPA_SI q A `{ValidPackage (loc A) (I_MCPA P n) A_export A} :
  AdvOf (λ b, MCOUNT P n q ∘ MCPA P n b)%sep A
    = AdvOf (MT_CPA P q) (A ∘ STM q) *+ n.
Proof.
  eapply @Adv_hybrid.
  1-4: intros; ssprove_valid.
  1-2: apply MCPA_0_n.
  intros i _; apply MCPA_i.
Qed.

End MultiInstance.
