Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Crypt Require Import Rules.

From Crypt Require Import pkg_preamble.
From Crypt Require Import pkg_chUniverse.
From Crypt Require Import pkg_core_definition.
From Crypt Require Import pkg_laws.
From Crypt Require Import pkg_rhl.

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype seq.


Module PackageTheory (π : ProbRulesParam).

  Import π.
  Module M := (PackageRHL π).
  Import M.

  Open Scope fset.
  Open Scope fset_scope.
  Open Scope type_scope.

  (* Open Scope package_scope. *)

  Definition link'' {I M E} (p1 : package M E) (p2 : package I M) : package I E.
    exact (p1 ∘ p2)%pack.
  Qed.

  Lemma getm_def_map_interface_Some :
    ∀ A (I : seq opsig) (f : ∀ x, x \in I → A) n y,
      getm_def [interface (ide x, f x h) | h # x ∈ I] n = Some y →
      ∃ z h, getm_def I n = Some z ∧ y = f (n, z) h.
  Admitted.
  
  Open Scope pack.
    Let I0 : Interface :=
      [interface val #[3] : nat → nat].

    Let I1 : Interface :=
      [interface
        val #[0] : bool → bool ;
        val #[1] : nat → unit ;
        val #[2] : unit → bool
      ].

    Let I2 : Interface :=
      [interface
        val #[4] : bool × bool → bool
      ].

    Let p0 : opackage fset0 [interface] I0 :=
      [package
        def #[3] (x : nat) : nat {
          ret x
        }
      ].


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings Rules
  StateTransfThetaDens StateTransformingLaxMorph FreeProbProg.
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.

    Let p1 : opackage fset0 [interface] I1 :=
      [package
        def #[0] (z : bool) : bool {
          ret z
        } ;
        def #[1] (y : nat) : unit {
          ret Datatypes.tt
        } ;
        def #[2] (u : unit) : bool {
          ret false
        }
      ].

    Let p2 : opackage fset0 [interface] I2 :=
      [package
        def #[4] (x : bool × bool) : bool {
          let '(u,v) := x in ret v
        }
      ].

    Let b1 : bundle := {|
      locs := fset0 ;
      import := [interface] ;
      export := _ ;
      pack := p1
    |}.

    Ltac in_fset_auto :=
      rewrite in_fset ; auto.

    Ltac package_obtac :=
      Tactics.program_simplify ;
      CoreTactics.equations_simpl ;
      try Tactics.program_solve_wf ;
      try in_fset_auto.

    Obligation Tactic := package_obtac.

    (** Note that because fsets are locked, ordering the export interface
        differently would not work.

        The program attribute is there to infer automatically the proofs
        corresponding to opr/putr/getr.
    *)
    #[program] Definition btest : bundle := {|
      locs := [fset 0] ;
      import := [interface val #[0] : nat → nat] ;
      export := [interface
        val #[1] : nat → nat ;
        val #[2] : unit → unit
      ] ;
      pack := [package
        def #[2] (_ : unit) : unit {
          putr 0 _ 0 (ret Datatypes.tt)
        } ;
        def #[1] (x : nat) : nat {
          getr 0 _ (λ n,
            opr (0, (chNat, chNat)) _ n (λ m,
              putr 0 _ m (ret m)
            )
          )
        }
      ]
    |}.

    (* The exact same definition but using the notations for the monad. *)
    #[program] Definition btest' : bundle := {|
      locs := [fset 0] ;
      import := [interface val #[0] : nat → nat] ;
      export := [interface
        val #[1] : nat → nat ;
        val #[2] : unit → unit
      ] ;
      pack := [package
        def #[2] (_ : unit) : unit {
          put 0 := 0 ;;
          ret Datatypes.tt
        } ;
        def #[1] (x : nat) : nat {
          n ← get 0 ;;
          m ← op [ #[0] : nat → nat ] n ;;
          put 0 := m ;;
          ret m
        }
      ]
    |}.
End PackageTheory.
