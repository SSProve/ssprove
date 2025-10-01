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

From SSProve.Crypt Require Import NominalPrelude Stat.
Import PackageNotation.
#[local] Open Scope package_scope.

From SSProve.Crypt.examples.PKE Require Import Scheme CyclicGroup LDDH.

Import PKE GroupScope.
#[local] Open Scope F_scope.

Section OneToMany.

Context (P : scheme).

Definition mpk_loc' : Location := (45%N, 'option P.(Pub)).
Definition count_loc' : Location := (46%N, 'nat).

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
  := (if (c' > i)%N then (c == 1%N)%B else (c == 0%N)%B).

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
      unfold R; simpl; move=> /eqP -> {cr} //=.

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

Ltac replace_true e :=
  replace e with true in * by (symmetry; apply /ltP; lia).

Ltac replace_false e :=
  replace e with false in * by (symmetry; apply /ltP; lia).

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
    apply (hybrid_cases c i) => E.
    + replace_true (c < i).
      replace_true (c < i.+1).
      apply r_put_vs_put.
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant; unfold R.
      * replace_false (i < c).
        by replace_false (i < c.+1).
      * replace_false (i.+1 < c).
        by replace_false (i.+1 < c.+1).
    + subst; replace_false (i < i).
      ssprove_code_simpl.
      ssprove_swap_lhs 0%N.
      apply r_get_remember_lhs => c'.
      ssprove_rem_rel 1%N.
      rewrite //= /R.
      replace_false (i < i).
      move=> /eqP -> {c'}.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_lhs [:: 1%N ; 0%N ].
      apply r_get_remember_lhs => mpk'.
      ssprove_rem_rel 3%N => {mpk'}->.
      apply r_put_vs_put.
      apply r_put_lhs.
      rewrite H' //=.
      replace_true (i < i.+1).
      apply rsame_head_scheme => x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      * by replace_true (eqn (i.+1 - i.+1)%Nrec 0).
      * replace_false (eqn (i.+2 - i.+1)%Nrec 0).
        by replace_false (eqn (i.+2 - i)%Nrec 0).
    + subst; replace_true (i < i.+1).
      replace_false (i.+1 < i.+1).
      replace_false (i.+1 < i).
      ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => c'.
      ssprove_rem_rel 0%N.
      rewrite //= /R.
      replace_false (i.+1 < i.+1).
      move=> /eqP -> {c'}.
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
      ssprove_invariant.
      * replace_true (eqn (i.+1 - i.+2)%Nrec 0).
        by replace_true (eqn (i.+1 - i.+1)%Nrec 0).
      * by replace_true (eqn (i.+2 - i.+2)%Nrec 0).
    + replace_false (c < i).
      replace_true (i < c).
      replace_false (c < i.+1).
      replace_true (i.+1 < c).
      apply r_put_vs_put.
      rewrite 2!code_link_scheme.
      apply rsame_head_scheme => c'.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant; unfold R.
      * replace_true (i < c.+1).
        by replace_true (i < c).
      * replace_true (i.+1 < c).
        by replace_true (i.+1 < c.+1).
Qed.

#[local] Open Scope ring_scope.

(* One-to-Many hybrid reduction package *)
Notation OTM n := (SLIDE n%N ∘ (ID (I_CPA P) || RAND (unif n%N)))%sep.

Theorem Adv_MT_CPA_OT n (A : nom_package)
  `{ValidPackage (loc A) (I_CPA P) A_export A} :
  AdvOf (MT_CPA P n) A = AdvOf (OT_CPA P) (A ∘ OTM n) *+ n.
Proof.
  eapply testing_hybrid.
  1-4: ssprove_valid.
  1-2: apply: PK_CPA_SLIDE_perfect.
  intros i; apply: SLIDE_succ_perfect.
Qed.

End OneToMany.
