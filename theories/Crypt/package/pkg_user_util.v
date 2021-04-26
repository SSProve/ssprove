(** Tactics to help prove things abouve packages

  Massaging perfect equivalence goals
  -----------------------------------

  - [simplify_eq_rel m]
    Will deal with a goal of the form [eq_up_to_inv] by reducing it to
    syntactical judgments about its procedures.

  - [ssprove_code_link_simpl]
    Will operate on a syntactic judgment [⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄] and deal
    with code linking apearing in [l] and/or [r], in particular making it
    commute with pattern-matching.

  - [simplify_linking]
    Will deal with residual [chUniverse_eqP] coming from linking.


  Tools for relation program logic
  --------------------------------

  - [ssprove_same_head_r]
    Applies the rule that states that both pieces of code have the same head
    (meaning the same command at top-level).
    It is right-biased and as such will work even if the left-hand side is
    an evar.

  - [ssprove_swap_rhs n]
    Swap in the right-hand side.
    Argument n correspond to depth at which to swap.
    0 will swap the toplevel, 1 will swap under one command, and so on.

  - [ssprove_swap_lhs n]
    Similar but in the left-hand side.

**)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect ssrbool eqtype seq eqtype choice.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb pkg_rhl pkg_tactics chUniverse.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Import PackageNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(** Preliminary work *)

Lemma opsig_in_unfold :
  ∀ {o : opsig} {E : Interface},
    o \in E →
    (ide o, (chsrc o, chtgt o)) \in E.
Proof.
  intros [i [S T]] E h. cbn. auto.
Defined.

Open Scope pack.

Ltac invert_in_seq h :=
  tryif (rewrite mem_seq1 in h)
  then (move: h => /eqP h ; subst)
  else (
    rewrite in_cons in h ;
    move: h => /orP [/eqP h | h] ; [
      subst
    | invert_in_seq h
    ]
  ).

Ltac invert_interface_in h :=
  let h' := fresh h in
  pose proof h as h' ;
  rewrite in_fset in h' ;
  cbn in h' ;
  invert_in_seq h' ;
  [ noconf h' .. ].

Ltac lookup_op_squeeze :=
  let f := fresh "f" in
  let e := fresh "e" in
  destruct lookup_op as [f|] eqn:e ; [
  | exfalso ;
    simpl in e ;
    repeat (destruct chUniverse_eqP ; [| contradiction ]) ;
    discriminate
  ] ;
  eapply lookup_op_spec in e ; simpl in e ;
  repeat (
    rewrite setmE in e ;
    tryif (rewrite eq_refl in e)
    then idtac
    else lazymatch type of e with
    | (if ?b then _ else _) = _ =>
      change b with false in e ;
      simpl in e
    end
  ) ;
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
  simpl.

Lemma code_link_assert :
  ∀ b p,
    code_link (assert b) p = assert b.
Proof.
  intros b p.
  unfold assert. rewrite code_link_if. cbn. reflexivity.
Qed.

Lemma code_link_assertD :
  ∀ A b k p,
    code_link (@assertD A b (λ x, k x)) p =
    #assert b as x ;; code_link (k x) p.
Proof.
  intros A b k p.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma bind_cong :
  ∀ A B u v f g,
    u = v →
    f = g →
    @bind A B u f = bind v g.
Proof.
  intros A B u v f g ? ?. subst.
  reflexivity.
Qed.

Lemma rel_jdg_replace :
  ∀ (A B : choiceType) (pre : precond) (post : postcond A B) l l' r r',
    ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄ →
    l = l' →
    r = r' →
    ⊢ ⦃ pre ⦄ l' ≈ r' ⦃ post ⦄.
Proof.
  intros A B pre post l l' r r' h ? ?.
  subst. auto.
Qed.

Ltac ssprove_match_commut_gen1 :=
  lazymatch goal with
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
    | @assertD ?A ?b (λ x, _) =>
      let x' := fresh x in
      eapply (f_equal (@assertD A b)) ;
      eapply functional_extensionality with (f := λ x', _) ; intro x'
    | x ← cmd ?c ;; _ =>
      let x' := fresh x in
      eapply (f_equal (cmd_bind _)) ;
      eapply functional_extensionality with (f := λ x', _) ; intro x'
    | x ← ?c ;; _ =>
      let x' := fresh x in
      (* eapply (f_equal (bind _)) ;
      eapply functional_extensionality with (f := λ x', _) ; intro x' *)
      eapply bind_cong ; [
      | eapply functional_extensionality with (f := λ x', _) ; intro x'
      ]
    | code_link (#assert ?b as x ;; _) =>
      rewrite code_link_assertD ; cbn - [lookup_op]
    | code_link (x ← _ ;; _) _ =>
      rewrite code_link_bind ; cbn - [lookup_op]
    | code_link (assert _) _ =>
      rewrite code_link_assert
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
    | _ =>
      reflexivity
    end
  end.

Ltac ssprove_match_commut_gen :=
  repeat ssprove_match_commut_gen1.

Ltac ssprove_code_link_simpl :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ _ ⦃ _ ⦄ =>
    eapply rel_jdg_replace ; [
    | solve [ ssprove_match_commut_gen ]
    | solve [ ssprove_match_commut_gen ]
    ]
  | |- _ =>
    fail "ssprove_code_link_simpl: goal should be syntactic judgment"
  end.

Ltac simplify_linking :=
  repeat chUniverse_eqP_handle ;
  simpl.

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

(** Automation of flat proofs *)
#[export] Hint Extern 3 (flat ?I) =>
  let n := fresh "n" in
  let h₀ := fresh "h₀" in
  let h₁ := fresh "h₁" in
  intros n ? ? h₀ h₁ ;
  invert_interface_in h₀ ;
  invert_interface_in h₁ ;
  chUniverse_eq_prove
  : typeclass_instances packages.

(* Could be more general with no fset0 for locations *)
Lemma code_link_scheme :
  ∀ A c p,
    @ValidCode fset0 [interface] A c →
    code_link c p = c.
Proof.
  intros A c p h.
  induction h.
  - reflexivity.
  - eapply fromEmpty. rewrite fset0E. eauto.
  - simpl. f_equal. apply functional_extensionality.
    intro. eauto.
  - simpl. f_equal. eauto.
  - simpl. f_equal. apply functional_extensionality.
    intro. eauto.
Qed.