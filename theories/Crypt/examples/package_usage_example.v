(*
  This file showcases the use of packages.
 *)


From Stdlib Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import RulesStateProb Package Prelude fmap_extra.
Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope package_scope.

Definition I0 : Interface :=
  [interface #val #[3] : 'nat → 'nat].

Definition I1 : Interface :=
  [interface
    #val #[0] : 'bool → 'bool ;
    #val #[1] : 'nat → 'unit ;
    #val #[2] : 'unit → 'bool
  ].

Definition I2 : Interface :=
  [interface
    #val #[4] : 'bool × 'bool → 'bool
  ].

Definition pempty : package [interface] [interface] :=
  [package emptym].

Definition p0 : package [interface] I0 :=
  [package emptym ;
    #def #[3] (x : 'nat) : 'nat {
      ret x
    }
  ].

Definition p1 : package [interface] I1 :=
  [package emptym ;
    #def #[0] (z : 'bool) : 'bool {
      ret z
    } ;
    #def #[1] (y : 'nat) : 'unit {
      ret tt
    } ;
    #def #[2] (u : 'unit) : 'bool {
      ret false
    }
  ].

Definition foo (x : bool) : code emptym [interface] bool :=
  {code let u := x in ret u}.

Definition bar (b : bool) : code emptym [interface] nat :=
  {code if b then ret 0 else ret 1}.

Definition p2 : package [interface] I2 :=
  [package emptym ;
    #def #[4] (x : 'bool × 'bool) : 'bool {
      let '(u,v) := x in ret v
    }
  ].

Definition test₁ :
  package
    [interface #val #[0] : 'nat → 'nat]
    [interface
      #val #[1] : 'nat → 'nat ;
      #val #[2] : 'unit → 'unit
    ]
  :=
  [package [fmap (0, 'nat) ] ;
    #def #[1] (x : 'nat) : 'nat {
      getr (0, 'nat) (λ n : nat,
        opr (0, ('nat, 'nat)) n (λ m,
          putr (0, 'nat) m (ret m)
        )
      )
    } ;
    #def #[2] (_ : 'unit) : 'unit {
      putr (0, 'nat) 0 (ret tt)
    }
  ].

Definition sig := {sig #[0] : 'nat → 'nat }.

#[program] Definition test₂ :
  package
    [interface #val #[0] : 'nat → 'nat ]
    [interface
      #val #[1] : 'nat → 'nat ;
      #val #[2] : 'unit → 'option ('fin 2) ;
      #val #[3] : {map 'nat → 'nat} → 'option 'nat
    ]
  :=
  [package [fmap (0, 'nat)] ;
    #def #[1] (x : 'nat) : 'nat {
      n ← get (0, 'nat) ;;
      m ← op sig ⋅ n ;;
      n ← get (0, 'nat) ;;
      m ← op sig ⋅ n ;;
      #put (0, 'nat) := m ;;
      ret m
    } ;
    #def #[2] (_ : 'unit) : 'option ('fin 2) {
      #put (0, 'nat) := 0 ;;
      ret (Some (gfin 1))
    } ;
    #def #[3] (m : {map 'nat → 'nat}) : 'option 'nat {
      ret (getm m 0)
    }
  ].

(* Testing the #import notation *)
Definition test₃ :
  package
    [interface
      #val #[0] : 'nat → 'bool ;
      #val #[1] : 'bool → 'unit
    ]
    [interface
      #val #[2] : 'nat → 'nat ;
      #val #[3] : 'bool × 'bool → 'bool
    ]
  :=
  [package emptym ;
    #def #[2] (n : 'nat) : 'nat {
      #import {sig #[0] : 'nat → 'bool } as f ;;
      #import {sig #[1] : 'bool → 'unit } as g ;;
      b ← f n ;;
      if b then
        g false ;;
        ret 0
      else ret n
    } ;
    #def #[3] (b : 'bool × 'bool) : 'bool {
      let (b0, b1) := b in
      ret b0
    }
  ].

(** Information is redundant between the export interface and the package
    definition, so it can safely be skipped.
*)
Definition test₄ : package [interface] _ :=
  [package emptym ;
    #def #[ 0 ] (n : 'nat) : 'nat {
      ret (n + n)%N
    } ;
    #def #[ 1 ] (b : 'bool) : 'nat {
      if b then ret 0 else ret 13
    }
  ].

Definition ℓ : Location := (0, 'nat).

#[tactic=notac] Equations? foo : code emptym [interface] 'nat :=
  foo := {code
    n ← get ℓ ;;
    ret n
  }.
Proof.
  ssprove_valid.
Abort.
