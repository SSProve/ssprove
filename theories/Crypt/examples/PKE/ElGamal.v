Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation.
#[local] Open Scope package_scope.

From SSProve.Crypt.examples.PKE Require Import Scheme CyclicGroup LDDH.

Import PKE GroupScope.
#[local] Open Scope F_scope.

Section ElGamal.

Context (G : CyclicGroup).

Definition elgamal : scheme := {|
    Sec := 'exp G
  ; Pub := 'el G
  ; Mes := 'el G
  ; Cip := 'el G × 'el G
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el G| ;;
      c₂ ← sample uniform #|el G| ;;
      ret (c₁, c₂)
    }
  ; keygen :=
    {code
      sk ← sample uniform #|exp G| ;;
      ret (sk, 'g ^ sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp G| ;;
      ret ('g ^ r, m * (pk ^ r))
    }
  ; dec := λ sk '(c₁, c₂),
    {code
      ret (c₂ * (c₁ ^- sk))
    }
  |}.

Theorem correct_elgamal
  : perfect (I_CORR elgamal) (CORR0 elgamal) (CORR1 elgamal).
Proof.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros sk.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros r.
  apply r_ret => s0 s1.
  split; subst; [| done ].
  unfold mulf, expfn, expfni.
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


Lemma bij_op_exp : bijective (λ a : 'exp G, 'g ^ a : 'el G).
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite 2!otf_fto -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    unfold mulf, expfn, expfni.
    rewrite 2!otf_fto -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ b : 'exp G, m * ('g ^ b) : 'el G).
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a)%g)).
  + intros x.
    rewrite 3!otf_fto -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    unfold mulf, expfn, expfni.
    rewrite 3!otf_fto -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.

Definition RED :
  package (I_LDDH G) (I_CPA elgamal) :=
  [package [fmap count_loc ; mpk_loc elgamal ] ;
    [ GEN ] 'tt {
      pk ← call [ GETA ] tt ;;
      #put mpk_loc elgamal := Some pk ;;
      ret pk
    } ;
    [ QUERY ] '(m) {
      c ← get count_loc ;;
      #assert (c < 1) ;;
      #put count_loc := c.+1;;
      _ ← getSome mpk_loc elgamal ;;
      '(r, sh) ← call [ GETBC ] tt ;;
      ret (r, m * sh)
    }
  ].

Notation inv0 := (
  heap_ignore ([fmap mga_loc G ])
  ⋊ triple_rhs count_loc (mpk_loc elgamal) (mga_loc G)
      (λ c pk ga, c = 0 → pk = ga)
).

Lemma PK_OTSR_RED_DDH_perfect b :
  perfect (I_CPA elgamal) (OT_CPA elgamal b) (RED ∘ LDDH G b).
Proof.
  ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ inv0).
  1: simpl; ssprove_invariant; try auto; fmap_solve.
  simplify_eq_rel m.
  - destruct m.
    simpl; simplify_linking.
    ssprove_sync => a.
    apply r_put_rhs.
    apply r_put_vs_put.
    ssprove_restore_pre.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - apply r_get_vs_get_remember.  1: ssprove_invariant.  move=> c.
    ssprove_code_simpl.
    ssprove_sync => H.
    ssprove_swap_lhs 0%N.
    ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember. 1: ssprove_invariant. move=> mpk.
    ssprove_code_simpl_more.
    ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
    apply r_get_remember_rhs => mga.
    eapply (r_rem_triple_rhs count_loc (mpk_loc elgamal) (mga_loc G)).
    1-4: exact _.
    move=> //= H'.
    apply r_put_vs_put.
    ssprove_sync => H1.
    destruct mpk as [pk|] => //= {H1}.
    destruct c as [|c] => //= {H}.
    specialize (H' erefl); subst.
    apply r_put_rhs.

    ssprove_restore_mem.
    1: {
      ssprove_invariant.
      intros h0 h1 [[[[[H0 H1] H2] H3] H4] H5].
      rewrite //= /triple_rhs.
      by get_heap_simpl.
    }

    destruct b; simpl.
    + ssprove_sync => b.
      by apply r_ret.
    + eapply rsymmetry.
      eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
      eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
      by eapply r_ret.
Qed.

Lemma OT_CPA_elgamal (A : adversary (I_CPA elgamal)) :
  AdvOf (OT_CPA elgamal) A = AdvOf (LDDH G) (A ∘ RED).
Proof. rewrite (AdvOf_perfect PK_OTSR_RED_DDH_perfect) Adv_reduction //. Qed.

End ElGamal.

Definition OT_CPA_elgamal_Z3 := OT_CPA_elgamal Z3.
