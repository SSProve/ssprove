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
    later on to be an actual constructor of code, replacing opr.
    Same as this notation, with discipline placing imports at the start,
    linking will become seemless.
    Better kept for later though, because it's another refactoring, though
    not as big as the current one.
    Problem: It doesn't work when linking several times. After the first
    linking, #import might no longer be in first position.

    It might be better to have codes without #import first, then
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

  (** Preliminary work *)

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

  Ltac lookup_op_squeeze :=
    let f := fresh "f" in
    let e := fresh "e" in
    destruct lookup_op as [f|] eqn:e ; [
    | exfalso ;
      simpl in e ;
      destruct chUniverse_eqP ; [| contradiction ] ;
      destruct chUniverse_eqP ; [| contradiction ] ;
      discriminate
    ] ;
    eapply lookup_op_spec in e ; simpl in e ;
    rewrite setmE in e ; rewrite eq_refl in e ;
    noconf e.

  Ltac chUniverse_eqP_handle :=
    let e := fresh "e" in
    destruct chUniverse_eqP as [e|] ; [| contradiction ] ;
    assert (e = erefl) by eapply uip ;
    subst e.

  Ltac simplify_eq_rel m :=
    let id := fresh "id" in
    let So := fresh "S" in
    let To := fresh "T" in
    let hin := fresh "hin" in
    intros id So To m hin ;
    invert_interface_in hin ;
    rewrite ?get_op_default_link ;
    (* First we need to squeeze the codes out of the packages *)
    unfold get_op_default ;
    lookup_op_squeeze ;
    lookup_op_squeeze ;
    cbn.

  Ltac ssprove_match_commut_gen :=
    repeat lazymatch goal with
    | |- _ = ?rr =>
      lazymatch rr with
      | x ← sample ?op ;; _ =>
        let x' := fresh x in
        eapply (f_equal (sampler _)) ;
        eapply functional_extensionality with (f := λ x', _) ; intro x'
      | x ← get ?ℓ ;; _ =>
        let x' := fresh x in
        eapply (f_equal (getr _)) ;
        eapply functional_extensionality with (f := λ x', _) ; intro x'
      | put ?ℓ := ?v ;; _ =>
        eapply (f_equal (putr _ _))
      | x ← cmd ?c ;; _ =>
        let x' := fresh x in
        eapply (f_equal (cmd_bind _)) ;
        eapply functional_extensionality with (f := λ x', _) ; intro x'
      | x ← ?c ;; _ =>
        let x' := fresh x in
        eapply (f_equal (bind _)) ;
        eapply functional_extensionality with (f := λ x', _) ; intro x'
      | code_link (match ?x with _ => _ end) _ =>
        instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
        destruct x ; cbn - [lookup_op] ;
        lazymatch goal with
        | |- context [ code_link (match _ with _ => _ end) _ ] =>
          idtac
        | |- _ =>
          reflexivity
        end
      | match ?x with _ => _ end =>
        instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
        destruct x ; cbn - [lookup_op] ;
        lazymatch goal with
        | |- context [ code_link (match _ with _ => _ end) _ ] =>
          idtac
        | |- _ =>
          reflexivity
        end
      end
    end.

  Ltac ssprove_code_link_commute_aux rr :=
    lazymatch rr with
    | context [ code_link (match _ with _ => _ end) _ ] =>
      let T := type of rr in
      let tm := fresh "tm" in
      evar (tm : T) ;
      replace rr with tm ; subst tm ; [| solve [ ssprove_match_commut_gen ] ]
    | _ => idtac
    end.

  Ltac ssprove_code_link_commute :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ ?ll ≈ ?rr ⦃ _ ⦄ =>
      ssprove_code_link_commute_aux ll ;
      ssprove_code_link_commute_aux rr
    | |- _ =>
      fail "ssprove_code_link_commute: goal should be syntactic judgment"
    end.

  Ltac simplify_linking :=
    repeat chUniverse_eqP_handle ;
    cbn.

  (** Working in the program logic *)

  (* Simplication of cmd_bind *)
  Ltac cmd_bind_simpl_once :=
    try change (cmd_bind (cmd_sample ?op) ?k) with (sampler op k) ;
    try change (cmd_bind (cmd_get ?ℓ) ?k) with (getr ℓ k) ;
    try change (cmd_bind (cmd_put ?ℓ ?v) ?k) with (put ℓ := v ;; k Datatypes.tt).

  Ltac cmd_bind_simpl :=
    repeat cmd_bind_simpl_once.

  (* Right-biased application of rsame_head *)
  Ltac ssprove_same_head_r :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
      lazymatch c with
      | x ← sample ?op ;; _ =>
        eapply (rsame_head_cmd (cmd_sample op))
      | put ?ℓ := ?v ;; _ =>
        eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put ℓ v))
      | x ← get ?ℓ ;; _ =>
        eapply (rsame_head_cmd (cmd_get ℓ))
      | x ← cmd ?c ;; _ =>
        eapply (rsame_head_cmd c)
      | _ => fail "No head found"
      end
    | |- _ => fail "The goal should be a syntactic judgment"
    end.

  (* Apply rswap_cmd_eq by reading rhs *)
  (* TODO Guard it by checking post = eq and even pre? *)
  Ltac ssprove_rswap_cmd_eq_rhs :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
      lazymatch c with
      | x ← sample ?op ;; y ← sample ?op' ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_sample op') (cmd_sample op))
      | x ← sample ?op ;; y ← get ?ℓ ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_get ℓ) (cmd_sample op))
      | x ← sample ?op ;; put ?ℓ := ?v ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_put ℓ v) (cmd_sample op) (λ x y, _))
      | x ← get ?ℓ ;; y ← sample ?op ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_sample op) (cmd_get ℓ))
      | x ← get ?ℓ ;; y ← get ?ℓ' ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_get ℓ') (cmd_get ℓ))
      | x ← get ?ℓ ;; put ?ℓ' := ?v ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_put ℓ' v) (cmd_get ℓ) (λ x y, _))
      | put ?ℓ := ?v ;; x ← sample ?op ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_sample op) (cmd_put ℓ v) (λ x y, _))
      | put ?ℓ := ?v ;; x ← get ?ℓ' ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_get ℓ') (cmd_put ℓ v) (λ x y, _))
      | put ?ℓ := ?v ;; put ?ℓ' := ?v' ;;  _ =>
        eapply (rswap_cmd_eq _ _ _ (cmd_put ℓ' v') (cmd_put ℓ v) (λ x y, _))
      | _ => fail "No swappable pair found."
      end
    | |- _ => fail "The goal should be a syntactic judgment."
    end.

  (* Apply rswap_cmd by reading rhs *)
  Ltac ssprove_rswap_cmd_rhs :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
      lazymatch c with
      | x ← sample ?op ;; y ← sample ?op' ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_sample op') (cmd_sample op))
      | x ← sample ?op ;; y ← get ?ℓ ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_get ℓ) (cmd_sample op))
      | x ← sample ?op ;; put ?ℓ := ?v ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_put ℓ v) (cmd_sample op) (λ x y, _))
      | x ← get ?ℓ ;; y ← sample ?op ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_sample op) (cmd_get ℓ))
      | x ← get ?ℓ ;; y ← get ?ℓ' ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_get ℓ') (cmd_get ℓ))
      | x ← get ?ℓ ;; put ?ℓ' := ?v ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_put ℓ' v) (cmd_get ℓ) (λ x y, _))
      | put ?ℓ := ?v ;; x ← sample ?op ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_sample op) (cmd_put ℓ v) (λ x y, _))
      | put ?ℓ := ?v ;; x ← get ?ℓ' ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_get ℓ') (cmd_put ℓ v) (λ x y, _))
      | put ?ℓ := ?v ;; put ?ℓ' := ?v' ;;  _ =>
        eapply (rswap_cmd _ _ _ _ (cmd_put ℓ' v') (cmd_put ℓ v) (λ x y, _))
      | _ => fail "No swappable pair found"
      end
    | |- _ => fail "The goal should be a syntactic judgment"
    end.

  (* TODO: Are there more cases we can consider? *)
  Ltac ssprove_swap_side_cond :=
    lazymatch goal with
    | |- ⊢ ⦃ _ ⦄ _ ← cmd (cmd_sample _) ;; _ ← cmd (cmd_sample _) ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC_cmd
    | |- ⊢ ⦃ _ ⦄ _ ← cmd _ ;; _ ← cmd (cmd_sample _) ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC_cmd
    | |- ⊢ ⦃ _ ⦄ _ ← cmd (cmd_sample _) ;; _ ← cmd _ ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC'_cmd
    | |- ⊢ ⦃ _ ⦄ _ ← sample _ ;; _ ← sample _ ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC_cmd
    | |- ⊢ ⦃ _ ⦄ _ ← cmd _ ;; _ ← sample _ ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC_cmd
    | |- ⊢ ⦃ _ ⦄ _ ← sample _ ;; _ ← cmd _ ;; _ ≈ _ ⦃ _ ⦄ =>
      apply rsamplerC'_cmd
    end.

  (* TODO Tactic to solve automatically condition when possible *)
  Ltac ssprove_swap_aux n :=
    lazymatch eval cbv in n with
    | S ?n => ssprove_same_head_r ; intro ; ssprove_swap_aux n
    | 0%N => ssprove_rswap_cmd_eq_rhs ; try ssprove_swap_side_cond
    | _ => fail "Wrong number: " n
    end.

  (** Swapping tactic in RHS

    Argument n correspond to depth at which to swap.
    0 will swap the toplevel, 1 will swap under one command, and so on.
  *)
  Ltac ssprove_swap_rhs n :=
    eapply r_transR ; [
      ssprove_swap_aux n
    | cmd_bind_simpl ; cbn beta
    ].

  (** Swapping tactic in LHS

    Argument n correspond to depth at which to swap.
    0 will swap the toplevel, 1 will swap under one command, and so on.
  *)
  Ltac ssprove_swap_lhs n :=
    eapply r_transL ; [
      ssprove_swap_aux n
    | cmd_bind_simpl ; cbn beta
    ].

End PackageUserUtil.
