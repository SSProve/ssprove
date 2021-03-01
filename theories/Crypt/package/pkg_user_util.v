(** Tactics to help prove things abouve packages

  TODO

  Here are some ideas for improvement:

  - A swapping tactic. I imagine something like

    ssprove swap lhs 2

    to swap commands in the lhs at depth 2.
    It would basically try to play by hand the rules I did in PRF/ElGamal.
    For instance applying rsamplerC_cmd automatically.

  - More generally some tactics to apply the rules, hopefully ones that are not
    as slow when failing, maybe providing clearer error messages.
    It would be useful to infer the cmd_sample etc. and more importantly to
    deal with higher order unification for cmd_put.
    Something like

    ssprove reflexivity

    could try to apply the reflexivity rule, and even use weakening
    automatically if necessary? Maybe not.

  - Provide a new notation

    #import [ #[0] : 'nat → 'nat ] as inc ;; p

    which behaves as

    let inc := λ x, cmd_op (0, 'nat, 'nat) x in p

    The idea being that by using #import, linking now should work as a
    substitution if computation is done in the right order (so zeta last).

    The good thing with this notation is that its meaning can be changed
    later on to be an actual constructor of program, replacing opr.
    Same as this notation, with discipline placing imports at the start,
    linking will become seemless.
    Better kept for later though, because it's another refactoring, though
    not as big as the current one.
    Problem: It doesn't work when linking several times. After the first
    linking, #import might no longer be in first position.

    It might be better to have programs without #import first, then
    consider things which can be prefixed by as many #import as one wants.

    It might also make sense not to have op/import as a command.

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
    rewrite in_fset in h' ;
    cbn in h' ;
    _invert_interface_in h' ;
    noconf h'.

End PackageUserUtil.
