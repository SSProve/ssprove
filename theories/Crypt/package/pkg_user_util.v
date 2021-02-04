(** Tactics to help prove things abouve packages

  TODO

**)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrbool eqtype seq eqtype choice.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb pkg_rhl pkg_tactics pkg_chUniverse.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Module PackageUserUtil (π : RulesParam).

  Include (PackageRHL π).
  Import PackageNotation.

  (* TODO MOVE *)
  Lemma getm_def_map :
    ∀ (T : ordType) (S S' : Type) (s : seq (T * S)) (k : T) (f : S → S'),
      getm_def [seq let '(a,b) := x in (a, f b) | x <- s] k =
      omap f (getm_def s k).
  Proof.
    intros T S S' s k f.
    induction s as [| [a b] s ih].
    - cbn. reflexivity.
    - cbn. destruct (k == a).
      + reflexivity.
      + apply ih.
  Qed.

  Lemma opsig_in_unfold :
    ∀ {o : opsig} {E : Interface},
      o \in E →
      (ide o, (chsrc o, chtgt o)) \in E.
  Proof.
    intros [i [S T]] E h. cbn. auto.
  Defined.

  Open Scope pack.

  (* Actually more general than interfaces here. *)
  Ltac _invert_interface_in h :=
    tryif (rewrite mem_seq1 in h)
    then (move: h => /eqP h ; subst)
    else (
      rewrite in_cons in h ;
      let e := fresh "e" in
      let h' := fresh "h'" in
      move: h => /orP [/eqP e | h'] ; [
        subst
      | _invert_interface_in h'
      ]
    ).

  Ltac invert_interface_in h :=
    let h' := fresh h in
    pose proof h as h' ;
    cbn in h' ;
    _invert_interface_in h'.

  (* Ltac eq_up_to_inv_simplify :=
    apply eq_up_to_inv_from_alt2 ;
    package_link_simplify ;
    let id := fresh "id" in
    let h := fresh "h" in
    let x := fresh "x"  in
    intros id h x ;
    invert_interface_in h ;
    repeat opackage_transport_simplify ;
    package_pdef_simpl ;
    program_link_simpl. *)

End PackageUserUtil.
