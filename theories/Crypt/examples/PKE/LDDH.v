Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  fingroup reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve Require Import NominalPrelude Async.
From SSProve.Crypt.examples.PKE Require Import CyclicGroup.

Import PackageNotation.
#[local] Open Scope package_scope.

Import Num.Def Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import GroupScope.

#[local] Open Scope F_scope.


Section LDDH.
  Context (G : CyclicGroup).

  Definition GETA := 50%N.
  Definition GETBC := 51%N.

  (* Lazy DDH *)

  Definition I_LDDH :=
    [interface
      [ GETA  ] : { 'unit ~> 'el G } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G }
    ].

  Definition mga_loc := mkloc 3 (None : option 'el G).

  Definition LDDH bit :
    game I_LDDH :=
    [package [fmap mga_loc ] ;
      [ GETA ] 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc := Some ('g ^ a) ;;
        ret ('g ^ a)
      } ;
      [ GETBC ] 'tt {
        ga ← getSome mga_loc ;;
        #put mga_loc := None ;;
        b ← sample uniform #|exp G| ;;
        if bit then
          ret ('g ^ b, ga ^ b)
        else
          c ← sample uniform #|exp G| ;;
          ret ('g ^ b, 'g ^ c)
      }
    ].

End LDDH.


Section DDH.
  Context (G : CyclicGroup).

  Definition GETABC := 52%N.

  Definition I_DDH :=
    [interface
      [ GETABC ] : { 'unit ~> 'el G × 'el G × 'el G }
    ].

  Definition DDH bit :
    game I_DDH :=
    [package emptym ;
      [ GETABC ] 'tt {
        a ← sample uniform #|exp G| ;;
        b ← sample uniform #|exp G| ;;
        if bit then
          ret ('g ^ a, 'g ^ b, ('g ^ a) ^ b)
        else
          c ← sample uniform #|exp G| ;;
          ret ('g ^ a, 'g ^ b, 'g ^ c)
      }
    ].
End DDH.


Section Reduction.
  Context (G : CyclicGroup).

  Definition sample_bc bit (a : 'exp G) : dist ('el G × 'el G) := {code
    b ← sample uniform #|exp G| ;;
    if bit then
      ret ('g ^ b, ('g ^ a) ^ b)
    else
      c ← sample uniform #|exp G| ;;
      ret ('g ^ b, 'g ^ c)
  }.

  Definition ADDH :
    package (I_ASYNC ('exp G) ('el G × 'el G)) (I_LDDH G) :=
    [package emptym ;
      [ GETA ] 'tt {
        a ← sample uniform #|exp G| ;;
        _ ← call [ PRIME ] a ;;
        ret ('g ^ a)
      } ;
      [ GETBC ] 'tt {
        '(gb, gc) ← call [ TRIGGER ] tt ;;
        ret (gb, gc)
      }
    ].

  Ltac ssprove_perfect I := 
    ssprove_share; apply prove_perfect;
    eapply (eq_rel_perf_ind _ _ I);
      [ ssprove_invariant; try done |].

  Lemma LDDH_ADDH b : perfect (I_LDDH G) (LDDH G b) (ADDH ∘ LAZY _ _ (sample_bc b)).
  Proof.
    ssprove_perfect (heap_ignore [fmap mga_loc G ; lazy_loc ('exp G)]
      ⋊ couple_cross (mga_loc G) (lazy_loc ('exp G)) (λ mga ma, mga = omap (λ a, 'g ^ a) ma)).
    simplify_eq_rel arg.
    - destruct arg. simpl.
      ssprove_code_simpl.
      ssprove_sync => a.
      apply r_put_vs_put.
      ssprove_restore_pre. { ssprove_invariant. }
      by apply r_ret.
    - destruct arg. simpl.
      ssprove_code_simpl; simpl.
      apply r_get_remember_lhs => mga.
      apply r_get_remember_rhs => ma.
      ssprove_code_simpl_more.
      ssprove_rem_rel 0%N.
      destruct mga, ma => //= Heq; [| apply r_fail ].
      noconf Heq.
      apply r_put_vs_put.
      ssprove_sync => b'.
      ssprove_restore_mem. { ssprove_invariant. }
      destruct b => /=.
      + by apply r_ret.
      + ssprove_sync => c.
        by apply r_ret.
  Qed.

  Definition mgbc_loc := mkloc 52%N (None : 'option ('el G × 'el G)).

  Definition RDDH :
    package (I_DDH G) (I_LDDH G) :=
    [package [fmap mgbc_loc ];
      [ GETA ] 'tt {
        '(ga, gb, gc) ← call [ GETABC ] tt ;;
        #put mgbc_loc := Some (gb, gc) ;;
        ret ga
      } ;
      [ GETBC ] 'tt {
        gbc ← getSome mgbc_loc ;;
        #put mgbc_loc := None ;; 
        ret gbc
      }
    ].

  Lemma ADDH_RDDH b : perfect (I_LDDH G) (ADDH ∘ EAGER _ _ (sample_bc b)) (RDDH ∘ DDH G b).
  Proof.
    ssprove_perfect (heap_ignore [fmap mgbc_loc ; eager_loc ('el G × 'el G) ]
      ⋊ couple_cross (eager_loc ('el G × 'el G)) mgbc_loc eq).
    simplify_eq_rel arg.
    - destruct arg. simpl.
      ssprove_code_simpl; simpl.
      ssprove_sync => a.
      ssprove_sync => b'.
      destruct b => /=.
      + apply r_put_vs_put.
        ssprove_restore_pre. { ssprove_invariant. }
        by apply r_ret.
      + ssprove_sync => c.
        apply r_put_vs_put.
        ssprove_restore_pre. { ssprove_invariant. }
        by apply r_ret.
    - destruct arg. simpl.
      ssprove_code_simpl; simpl.
      apply r_get_remember_lhs => lhs.
      apply r_get_remember_rhs => mgbc.
      ssprove_rem_rel 0%N => {lhs}->.
      ssprove_code_simpl_more.
      ssprove_sync => Hmgbc.
      destruct mgbc as [ [gb gc] |] => //=.
      apply r_put_vs_put.
      ssprove_restore_mem. { ssprove_invariant. }
      by apply r_ret.
  Qed.

  Lemma LDDH_DDH {A} {VA : ValidPackage (loc A) (I_LDDH G) A_export A} :
    AdvOf (LDDH G) A = AdvOf (DDH G) (A ∘ RDDH).
  Proof.
    rewrite (AdvOf_perfect LDDH_ADDH).
    rewrite Adv_reduction -(Adv_perfect_l (ASYNC_perfect _ _ _ _)).
    rewrite -(Adv_perfect_r (ASYNC_perfect _ _ _ _)).
    by rewrite -Adv_reduction (AdvOf_perfect ADDH_RDDH) Adv_reduction.
  Qed.
End Reduction.
