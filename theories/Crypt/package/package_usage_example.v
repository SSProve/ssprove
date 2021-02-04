(*
  This file showcases the use of packages.
 *)


From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Crypt Require Import RulesStateProb Package Prelude.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module NotationExamples (π : RulesParam).

  Import π.
  Module M := (Package_Make π).
  Import M.
  Import PackageNotation.

  Local Open Scope package_scope.

  Definition I0 : Interface :=
    [interface val #[3] : 'nat → 'nat].

  Definition I1 : Interface :=
    [interface
      val #[0] : 'bool → 'bool ;
      val #[1] : 'nat → 'unit ;
      val #[2] : 'unit → 'bool
    ].

  Definition I2 : Interface :=
    [interface
      val #[4] : 'bool × 'bool → 'bool
    ].

  Lemma valid_empty_package :
    ∀ L I,
      valid_package L I [interface] emptym.
  Proof.
    intros L I.
    intros [id [S T]] ho. eapply fromEmpty. eauto.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [::])) =>
    eapply valid_empty_package
    : typeclass_instances.

  Definition pempty : package fset0 [interface] [interface] :=
    [package].

  Lemma valid_package1 :
    ∀ L I i A B f,
      (∀ x, valid_program L I (f x)) →
      valid_package L I (fset [:: (i, (A, B))]) (mkfmap [:: (i, (A ; B ; f))]).
  Proof.
    intros L I i A B f hf.
    intros o ho. rewrite in_fset in ho.
    rewrite mem_seq1 in ho. move: ho => /eqP ho. subst o.
    cbn. exists f.
    destruct (eqn i i) eqn:e.
    2:{ move: e => /eqP. contradiction. }
    intuition auto.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [:: (?i, (?A ; ?B ; ?f))])) =>
    eapply valid_package1 ;
    intro ; eapply valid_program_from_class
    : typeclass_instances.

  Definition p0 : package fset0 [interface] I0 :=
    [package
      def #[3] (x : 'nat) : 'nat {
        ret x
      }
    ].

  Definition p1 : opackage fset0 [interface] I1 :=
    [package
      def #[0] (z : 'bool) : 'bool {
        ret z
      } ;
      def #[1] (y : 'nat) : 'unit {
        ret Datatypes.tt
      } ;
      def #[2] (u : 'unit) : 'bool {
        ret false
      }
    ].

  Definition p2 : opackage fset0 [interface] I2 :=
    [package
      def #[4] (x : 'bool × 'bool) : 'bool {
        let '(u,v) := x in ret v
      }
    ].

  Definition b1 : bundle := {|
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
    locs := [fset (chNat; 0)] ;
    import := [interface val #[0] : 'nat → 'nat] ;
    export := [interface
      val #[1] : 'nat → 'nat ;
      val #[2] : 'unit → 'unit
    ] ;
    pack := [package
      def #[2] (_ : 'unit) : 'unit {
        putr (chNat; 0) _ 0 (ret Datatypes.tt)
      } ;
      def #[1] (x : 'nat) : 'nat {
        getr (chNat; 0) _ (λ n : nat,
          opr (0, (chNat, chNat)) _ n (λ m,
            putr (chNat; 0) _ m (ret m)
          )
        )
      }
    ]
  |}.

  (* A similar definition but using the notations for the monad. *)
  #[program] Definition btest' : bundle := {|
    locs := [fset ('nat; 0)] ;
    import := [interface val #[0] : 'nat → 'nat ] ;
    export := [interface
      val #[1] : 'nat → 'nat ;
      val #[2] : 'unit → 'option ('fin 2) ;
      val #[3] : {map 'nat → 'nat} → 'option 'nat
    ] ;
    pack := [package
      def #[3] (m : {map 'nat → 'nat}) : 'option 'nat {
        ret (getm m 0)
      } ;
      def #[2] (_ : 'unit) : 'option ('fin 2) {
        put ('nat; 0) := 0 ;;
        ret (Some (gfin 1))
      } ;
      def #[1] (x : 'nat) : 'nat {
        n ← get ('nat; 0) ;;
        m ← op [ #[0] : 'nat → 'nat ] n ;;
        n ← get ('nat; 0) ;;
        m ← op [ #[0] : 'nat → 'nat ] n ;;
        put ('nat; 0) := m ;;
        ret m
      }
    ]
  |}.

End NotationExamples.
