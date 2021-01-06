(*
  This file showcases the use of packages.
 *)


From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Crypt Require Import RulesStateProb Package.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module NotationExamples (π : RulesParam).

  Import π.
  Module M := (Package_Make π).
  Import M.

  Local Open Scope package_scope.

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
      val #[2] : unit → option (fin 2)
    ] ;
    pack := [package
      def #[2] (_ : unit) : option (fin 2) {
        put 0 := 0 ;;
        ret (Some _)
      } ;
      def #[1] (x : nat) : nat {
        n ← get 0 ;;
        m ← op [ #[0] : nat → nat ] n ;;
        put 0 := m ;;
        ret m
      }
    ]
  |}.
  Next Obligation.
    exists 1. auto.
  Defined.

End NotationExamples.
