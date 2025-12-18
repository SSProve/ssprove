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

From SSProve.Crypt.examples.PKE Require Import Scheme CyclicGroup LDDH.

Import PKE GroupScope.
#[local] Open Scope F_scope.

Section OneToMany.

Context (P : scheme).

Definition mpk_loc' := mkloc 45 (None : option P.(Pub)).
Definition count_loc' := mkloc 46 (0 : nat).

Definition SLIDE n :
  package (unionm (I_CPA P) (IPICK nat)) (I_CPA P) :=
  [package [fmap count_loc' ; mpk_loc' ] ;
    [ GEN ] : { 'unit ~> P.(Pub) } 'tt {
      pk ← call [GEN] tt ;;
      #put mpk_loc' := Some pk ;;
      ret pk
    } ;
    [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
      count ← get count_loc' ;;
      #assert (count < n)%N ;;
      #put count_loc' := count.+1 ;;
      i ← call [pick] tt ;;
      pk ← getSome mpk_loc' ;;
      if (count < i)%N then
        c ← P.(sample_Cip) ;; ret c
      else if (i < count)%N then
        c ← P.(enc) pk m ;; ret c
      else
        c ← call [QUERY] m ;;
        ret c
    }
  ].

Definition R (i : 'nat) (c : 'nat) (c' : 'nat)
  := c = (c' > i)%N.

Notation inv i := (
  heap_ignore ([fmap mpk_loc' ; count_loc ; count_loc' ])
  ⋊ couple_cross (mpk_loc P) mpk_loc' eq
  ⋊ couple_cross count_loc count_loc' eq
  ⋊ couple_rhs count_loc count_loc' (R i)
).

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

Lemma PK_CPA_SLIDE_perfect {n} b : perfect (I_CPA P)
  (MT_CPA P n b) (SLIDE n ∘ (OT_CPA P true || PICK (if b then 0 else n))).
Proof.
  ssprove_share.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv (if b then 0 else n))).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  - destruct m; simpl.
    simplify_linking.
    ssprove_code_simpl.
    apply rsame_head_scheme => [[_ pk]].
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_restore_pre.
    2: by apply r_ret.
    ssprove_invariant.

  - ssprove_code_simpl; simpl.
    ssprove_code_simpl_more.
    apply r_get_remember_lhs => c.
    apply r_get_remember_rhs => cr.
    ssprove_rem_rel 1%N => {cr}<-.
    ssprove_sync => H.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    apply r_get_remember_lhs => mpk.
    apply r_get_remember_rhs => mpk'.
    ssprove_rem_rel 2%N => {mpk'}<-.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    ssprove_sync => H'.
    destruct mpk as [pk|] => //= {H'}.
    destruct b; [ destruct c | ]; simpl.
    + ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => cr.
      ssprove_rem_rel 0%N.
      unfold R; simpl; move=> -> {cr} //=.

      ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
      eapply @r_get_remind_rhs.
      1: eapply Remembers_syncs; exact _. (* !! *)
      apply r_put_rhs.
      apply r_put_vs_put => //=.
      eapply rsame_head_scheme => x.
      ssprove_restore_mem.
      { ssprove_invariant. }
      by apply r_ret.

    + apply r_put_vs_put.
      rewrite code_link_scheme. (* !! *)
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
    + rewrite H.
      apply r_put_vs_put.
      rewrite code_link_scheme.
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      rewrite /R 2!ltnNge H (ltnW H) //.
Qed.

Notation inv' i := (
  heap_ignore [fmap count_loc ]
  ⋊ couple_lhs (mpk_loc P) mpk_loc' eq
  ⋊ couple_rhs (mpk_loc P) mpk_loc' eq
  ⋊ couple_lhs count_loc count_loc' (R i%N)
  ⋊ couple_rhs count_loc count_loc' (R i.+1)
).

Lemma SLIDE_succ_perfect {n} {i} : perfect (I_CPA P)
  (SLIDE n ∘ (OT_CPA P false || PICK i   ))
  (SLIDE n ∘ (OT_CPA P true  || PICK i.+1)).
Proof.
  ssprove_share.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv' i)).
  { by ssprove_invariant. }
  simplify_eq_rel m.
  - destruct m; simpl.
    simplify_linking.
    ssprove_code_simpl.
    eapply rsame_head_alt.
    1-3: try apply prog_valid; intros; exfalso; eapply fhas_empty; eassumption.
    move=> [_ pk].
    apply r_put_vs_put.
    apply r_put_vs_put.
    ssprove_restore_pre.
    2: by apply r_ret.
    by ssprove_invariant.

  - ssprove_code_simpl.
    rewrite 2!code_link_scheme.
    apply r_get_vs_get_remember.
    intros c.
    ssprove_code_simpl.
    ssprove_sync => /ltP H.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros mpk.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    ssprove_sync => H'.
    hybrid_cases c i.
    + apply r_put_vs_put.
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      { ssprove_invariant; unfold R; by replace_many. }
      by apply r_ret.
    + ssprove_code_simpl.
      ssprove_swap_lhs 0%N.
      apply r_get_remember_lhs => c'.
      ssprove_rem_rel 1%N.
      rewrite //= /R ltnn => -> {c'}.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_lhs [:: 1%N ; 0%N ].
      apply r_get_remember_lhs => mpk'.
      ssprove_rem_rel 3%N => {mpk'}->.
      apply r_put_vs_put.
      apply r_put_lhs.
      rewrite H' //=.
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      { ssprove_invariant; by replace_many. }
      by apply r_ret.
    + ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => c'.
      ssprove_rem_rel 0%N.
      rewrite //= /R ltnn => -> {c'}.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      destruct mpk as [pk|] => //=.
      ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
      apply r_get_remember_rhs => mpk'.
      ssprove_rem_rel 2%N => -> //= {mpk'}.
      apply r_put_vs_put.
      apply r_put_rhs.
      rewrite code_link_scheme.
      eapply rsame_head_scheme => x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant; by replace_many.
    + apply r_put_vs_put.
      rewrite 2!code_link_scheme.
      apply rsame_head_scheme => c'.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant; unfold R; by replace_many.
Qed.

#[local] Open Scope ring_scope.

(* One-to-Many hybrid reduction package *)
Notation OTM n := (SLIDE n%N ∘ (ID (I_CPA P) || RAND (unif n%N)))%sep.

Theorem Adv_MT_CPA_OT n A `{ValidPackage (loc A) (I_CPA P) A_export A} :
  AdvOf (MT_CPA P n) A = AdvOf (OT_CPA P) (A ∘ OTM n) *+ n.
Proof.
  eapply @Adv_hybrid.
  1-4: intros; ssprove_valid.
  1-2: apply: PK_CPA_SLIDE_perfect.
  intros i _; apply: SLIDE_succ_perfect.
Qed.

End OneToMany.
