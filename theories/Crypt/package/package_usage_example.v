(*
  This file showcases the use of packages.
 *)


From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Crypt Require Import RulesStateProb Package Prelude.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.


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
      valid_package L I (fset [:: (i, (A, B))]) (mkfmap [:: (i, mkdef A B f)]).
  Proof.
    intros L I i A B f hf.
    intros o ho. rewrite in_fset in ho.
    rewrite mem_seq1 in ho. move: ho => /eqP ho. subst o.
    cbn. exists f.
    destruct (eqn i i) eqn:e.
    2:{ move: e => /eqP. contradiction. }
    intuition auto.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E (mkfmap [:: (?i, mkdef ?A ?B ?f)])) =>
    eapply valid_package1 ;
    intro ; eapply valid_program_from_class
    : typeclass_instances.

  Definition p0 : package fset0 [interface] I0 :=
    [package
      def #[3] (x : 'nat) : 'nat {
        ret x
      }
    ].

  Lemma flat_valid_package :
    ∀ L I E p,
      valid_package L I E p →
      flat E.
  Proof.
    intros L I E p hp.
    intros i [u1 u2] [v1 v2] h1 h2.
    specialize (hp _ h1) as h1'.
    specialize (hp _ h2) as h2'.
    simpl in *.
    destruct h1' as [f [ef _]].
    destruct h2' as [g [eg _]].
    rewrite ef in eg. noconf eg.
    reflexivity.
  Qed.

  Lemma valid_package_cons :
    ∀ L I i A B f E p,
      valid_package L I (fset E) (mkfmap p) →
      (∀ x, valid_program L I (f x)) →
      i \notin (λ '(i,_), i) @: fset E →
      valid_package L I (fset ((i, (A, B)) :: E))
        (mkfmap ((i, mkdef A B f) :: p)).
  Proof.
    intros L I i A B f E p hp hf hi.
    intros o ho. rewrite in_fset in ho. rewrite in_cons in ho.
    move: ho => /orP [ho | ho].
    - move: ho => /eqP ho. subst o.
      rewrite mkfmapE. cbn. exists f.
      destruct (eqn i i) eqn:e.
      2:{ move: e => /eqP. contradiction. }
      intuition auto.
    - rewrite -in_fset in ho.
      specialize (hp _ ho).
      destruct o as [id [S T]].
      destruct hp as [g [eg hg]].
      rewrite mkfmapE. cbn.
      destruct (eqn id i) eqn:e.
      1:{
        move: e => /eqP e. subst id.
        eapply mem_imfset with (f := λ '(i,_), i) in ho.
        unfold "\notin" in hi. rewrite ho in hi.
        discriminate.
      }
      rewrite mkfmapE in eg.
      exists g. intuition auto.
  Qed.

  Hint Extern 2 (ValidPackage ?L ?I ?E (mkfmap ((?i, mkdef ?A ?B ?f) :: ?p)))
    =>
    eapply valid_package_cons ; [
      eapply valid_package_from_class
    | intro ; eapply valid_program_from_class
    | unfold "\notin" ; rewrite imfset_fset ; rewrite in_fset ; eauto
    ]
    : typeclass_instances.

  Definition p1 : package fset0 [interface] I1 :=
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

  Hint Extern 2 (ValidProgram ?L ?I (let u := ?t in ?p)) =>
    cbn zeta ; exact _
    : typeclass_instances.

  Obligation Tactic := idtac.

  Fail Definition foo (x : bool) : program fset0 [interface] bool_choiceType :=
    {program let u := x in ret u}.
  (* Next Obligation.
    intro x. cbn zeta. exact _. *)

  Hint Extern 2 (ValidProgram ?L ?I (match ?t with _ => _ end)) =>
    destruct t
    : typeclass_instances.

  Definition bar (b : bool) : program fset0 [interface] nat_choiceType :=
    {program if b then ret 0 else ret 1}.

  Definition p2 : package fset0 [interface] I2 :=
    [package
      def #[4] (x : 'bool × 'bool) : 'bool {
        let '(u,v) := x in ret v
      }
    ].

  (* Definition b1 : bundle := {|
    locs := fset0 ;
    import := [interface] ;
    export := _ ;
    pack := p1
  |}. *)

  Definition test :
    package
      [fset (chNat; 0)]
      [interface val #[0] : 'nat → 'nat]
      [interface
        val #[1] : 'nat → 'nat ;
        val #[2] : 'unit → 'unit
      ]
    :=
    [package
      def #[1] (x : 'nat) : 'nat {
        getr ('nat; 0) (λ n : nat,
          opr (0, ('nat, 'nat)) n (λ m,
            putr ('nat; 0) m (ret m)
          )
        )
      } ;
      def #[2] (_ : 'unit) : 'unit {
        putr ('nat; 0) 0 (ret Datatypes.tt)
      }
    ].

  (* For some reason, typeclasses resolution doens't work?
    Maybe it's not triggered at the right time.
  *)
  #[program] Definition test' :
    package
      [fset ('nat; 0)]
      [interface val #[0] : 'nat → 'nat ]
      [interface
        val #[1] : 'nat → 'nat ;
        val #[2] : 'unit → 'option ('fin 2) ;
        val #[3] : {map 'nat → 'nat} → 'option 'nat
      ]
    :=
    [package
      def #[1] (x : 'nat) : 'nat {
        n ← get ('nat; 0) ;;
        m ← op [ #[0] : 'nat → 'nat ] n ;;
        n ← get ('nat; 0) ;;
        m ← op [ #[0] : 'nat → 'nat ] n ;;
        put ('nat; 0) := m ;;
        ret m
      } ;
      def #[2] (_ : 'unit) : 'option ('fin 2) {
        put ('nat; 0) := 0 ;;
        ret (Some (gfin 1))
      } ;
      def #[3] (m : {map 'nat → 'nat}) : 'option 'nat {
        ret (getm m 0)
      }
    ]
  .
  Next Obligation.
    exact _.
  Qed.

End NotationExamples.
