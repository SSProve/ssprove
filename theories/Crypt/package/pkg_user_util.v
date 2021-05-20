(** Tactics to help prove things abouve packages

  Massaging perfect equivalence goals
  -----------------------------------

  - [simplify_eq_rel m]
    Will deal with a goal of the form [eq_up_to_inv] by reducing it to
    syntactical judgments about its procedures.

  - [ssprove_code_simpl]
    Will operate on a syntactic judgment [⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄] and deal
    with code linking apearing in [l] and/or [r], in particular making it
    commute with pattern-matching.
    It subsumes [simplify_linking] but might not be always necessary.

    Note: It can be extended by adding hints to the [ssprove_code_simpl]
    database, with cost lower than [100].

  - [ssprove_code_simpl_more]
    Applying this tactic will simplify a relational judgment further, by
    applying relation rules instead of syntactical equalities.
    For now only useful to re-associate #assert with respect to bind.
    Might require to be applied several times, and interleaved with
    [ssprove_code_simpl].

  - [simplify_linking]
    Will deal with residual [chUniverse_eqP] coming from linking.


  Tools for relation program logic
  --------------------------------

  - [ssprove_sync]
    Applies the rule that states that both pieces of code have the same head
    (meaning the same command at top-level).
    It is right-biased and as such will work even if the left-hand side is
    an evar.

    Note: This tactic also tries to preserve the precondition automatically.
    It is not always possible and it will sometimes require you to prove
    preservation of the precondition manually.
    Extension to the [ssprove_invariant] hint database can extend automation.

  - [ssprove_sync_eq]
    Specialised version of [ssprove_sync] where the precondition is merely
    equality of heaps. No precondition preservation is needed in this particular
    case.

  - [ssprove_swap_rhs n]
    Swap in the right-hand side.
    Argument n correspond to depth at which to swap.
    0 will swap the toplevel, 1 will swap under one command, and so on.

  - [ssprove_swap_lhs n]
    Similar but in the left-hand side.

  - [ssprove_swap_seq_rhs s]
    Applies [ssprove_swap_rhs] in sucession, starting from the first element
    of the sequence [s].

  - [ssprove_swap_seq_lhs s]
    Similar but in the left-hand side.

  - [ssprove_forget]
    Remove the last rem_lhs/rem_rhs from the precondition.

  - [ssprove_forget_all]
    Remove all reminders from precondition.

**)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Crypt Require Import Axioms Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb pkg_advantage pkg_lookup pkg_semantics
  pkg_heap pkg_invariants pkg_distr pkg_rhl pkg_tactics chUniverse.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

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

Ltac simplify_linking :=
  repeat chUniverse_eqP_handle ;
  simpl.

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

Create HintDb ssprove_code_simpl.

#[export] Hint Extern 100 =>
  reflexivity
  : ssprove_code_simpl.

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
    | x ← (y ← _ ;; _) ;; _ =>
      rewrite bind_assoc
    | x ← (match ?u with _ => _ end) ;; _ =>
      instantiate (1 := ltac:(let _ := type of u in destruct u)) ;
      destruct u ; simpl
    | x ← (let _ := ?u in _) ;; _ =>
      instantiate (1 := ltac:(let _ := type of u in destruct u)) ;
      destruct u ; simpl
    | x ← ?c ;; _ =>
      let x' := fresh x in
      eapply bind_cong ; [
      | eapply functional_extensionality with (f := λ x', _) ; intro x'
      ]
    | code_link (@assertD ?A ?b _) _ =>
      rewrite (code_link_assertD A) ; simpl
    | code_link (x ← _ ;; _) _ =>
      rewrite code_link_bind ; simpl
    | code_link (assert _) _ =>
      rewrite code_link_assert
    | code_link (match ?x with _ => _ end) _ =>
      instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
      destruct x ; simpl
    | match ?x with _ => _ end =>
      instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
      destruct x ; simpl
    | code_link (let _ := ?x in _) _ =>
      instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
      destruct x ; simpl
    | let _ := ?x in _ =>
      instantiate (1 := ltac:(let _ := type of x in destruct x)) ;
      destruct x ; simpl
    | _ =>
      typeclasses eauto with ssprove_code_simpl
    end
  end.

Ltac ssprove_match_commut_gen :=
  repeat (ssprove_match_commut_gen1 ; simplify_linking).

Ltac ssprove_code_simpl :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ _ ⦃ _ ⦄ =>
    eapply rel_jdg_replace ; [
    | solve [ ssprove_match_commut_gen ]
    | solve [ ssprove_match_commut_gen ]
    ]
  | |- _ =>
    fail "ssprove_code_simpl: goal should be syntactic judgment"
  end.

(** Working in the program logic *)

(* Simplication of cmd_bind *)
Ltac cmd_bind_simpl_once :=
  try change (cmd_bind (cmd_sample ?op) ?k) with (sampler op k) ;
  try change (cmd_bind (cmd_get ?ℓ) ?k) with (getr ℓ k) ;
  try change (cmd_bind (cmd_put ?ℓ ?v) ?k) with (put ℓ := v ;; k Datatypes.tt).

Ltac cmd_bind_simpl :=
  repeat cmd_bind_simpl_once.

(* No clear way of having cmd_assertD *)
(* Definition cmd_assertD {A : chUniverse} (b : bool) : command A :=
  (if b as b' return b = b' → raw_code A then k else λ _, fail) erefl. *)

(* Right-biased application of rsame_head *)
Ltac ssprove_sync_eq :=
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
    | @assertD ?A ?b _ =>
      eapply (r_assertD_same A b)
    | _ => fail "No head found"
    end
  | |- _ => fail "The goal should be a syntactic judgment"
  end.

Ltac notin_fset_auto :=
  let bot := fresh "bot" in
  rewrite in_fset ; apply /negP ; intro bot ;
  repeat (
    tryif (rewrite in_cons in bot)
    then (
      move: bot => /orP [/eqP bot | bot] ; [ noconf bot |]
    )
    else rewrite in_nil in bot ; discriminate
  ).

#[export] Hint Extern 20 (is_true (_ \notin _)) =>
  solve [ notin_fset_auto ]
  : ssprove_invariant.

#[export] Hint Extern 20 (is_true (_ \in _)) =>
  solve [ auto_in_fset ]
  : ssprove_invariant.

(* Right-biased same head, but more genenal *)
(* TODO Use that instead of the one above, which would have _eq in the name *)
Ltac ssprove_sync :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
    lazymatch c with
    | x ← sample ?op ;; _ =>
      (* Maybe make it one lemma, safer and probably less time consuming *)
      eapply (rsame_head_cmd_alt (cmd_sample op)) ; [
        eapply cmd_sample_preserve_pre
      | idtac
      ]
    | put ?ℓ := ?v ;; _ =>
      eapply (@rsame_head_cmd_alt _ _ (λ z, _) (λ z, _) (cmd_put ℓ v)) ; [
        eapply cmd_put_preserve_pre ; ssprove_invariant
      | idtac
      ]
    | x ← get ?ℓ ;; _ =>
      eapply (rsame_head_cmd_alt (cmd_get ℓ)) ; [
        eapply cmd_get_preserve_pre ; ssprove_invariant
      | idtac
      ]
    | x ← cmd ?c ;; _ =>
      eapply (rsame_head_cmd_alt c)
    | @assertD ?A ?b _ =>
      eapply (r_assertD_same A b)
    | _ => fail "No head found"
    end
  | |- _ => fail "The goal should be a syntactic judgment"
  end.

(* Apply rswap_cmd_eq by reading rhs *)
(* TODO Guard it by checking post = eq and even pre? *)
(* TODO: Maybe forget about the redundant bits? *)
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
    | @assertD ?A ?b (λ e, x ← sample ?op ;; _) =>
      eapply (rswap_cmd_assertD_eq _ A b (cmd_sample op) (λ x y, _))
    | @assertD ?A ?b (λ e, x ← get ?ℓ ;; _) =>
      eapply (rswap_cmd_assertD_eq _ A b (cmd_get ℓ) (λ x y, _))
    | @assertD ?A ?b (λ e, put ?ℓ := ?v ;; _) =>
      eapply (rswap_cmd_assertD_eq _ A b (cmd_put ℓ v) (λ x y, _))
    | x ← sample ?op ;; @assertD ?A ?b _ =>
      eapply (rswap_assertD_cmd_eq _ A b (cmd_sample op) (λ x y, _))
    | x ← get ?ℓ ;; @assertD ?A ?b _ =>
      eapply (rswap_assertD_cmd_eq _ A b (cmd_get ℓ) (λ x y, _))
    | put ?ℓ := ?v ;; @assertD ?A ?b _ =>
      eapply (rswap_assertD_cmd_eq _ A b (cmd_put ℓ v) (λ x y, _))
    | @assertD ?A ?b (λ e, #assert _ as e' ;; _) =>
      eapply (rswap_assertD_assertD_eq A _ _ (λ e' e, _))
    | x ← ?c ;; y ← sample ?op ;; _ =>
      eapply (rswap_cmd_bind_eq (cmd_sample op) c)
    | x ← ?c ;; y ← get ?ℓ ;; _ =>
      eapply (rswap_cmd_bind_eq (cmd_get ℓ) c)
    | x ← ?c ;; put ?ℓ := ?v ;; _ =>
      eapply (rswap_cmd_bind_eq (cmd_put ℓ v) c (λ x y, _))
    | x ← sample ?op ;; y ← ?c ;; _ =>
      eapply (rswap_bind_cmd_eq c (cmd_sample op))
    | x ← get ?ℓ ;; y ← ?c ;; _ =>
      eapply (rswap_bind_cmd_eq c (cmd_get ℓ))
    | put ?ℓ := ?v ;; y ← ?c ;; _ =>
      eapply (rswap_bind_cmd_eq c (cmd_put ℓ v) (λ x y, _))
    | _ => fail "No swappable pair found."
    end
  | |- _ => fail "The goal should be a syntactic judgment."
  end.

(* Apply rswap_cmd by reading rhs *)
(* TODO: Still useful? *)
(* Ltac ssprove_rswap_cmd_rhs :=
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
  end. *)

Ltac neq_loc_auto :=
  let e := fresh "e" in
  apply /negP ;
  move /eqP => e ;
  noconf e.

#[export] Hint Extern 20 (is_true (_ != _)) =>
  solve [ neq_loc_auto ]
  : ssprove_invariant.

(** Extensible database to deal with swapping side conditions *)
Create HintDb ssprove_swap.

#[export] Hint Extern 100 =>
  shelve
  : ssprove_swap.

Ltac ssprove_swap_auto :=
  (unshelve typeclasses eauto with ssprove_swap) ; shelve_unifiable.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd _ ;; _ ← cmd (cmd_sample _) ;; _ ≈ _ ⦃ _ ⦄) =>
  apply rsamplerC_cmd
  : ssprove_swap.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_sample _) ;; _ ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
  apply rsamplerC'_cmd
  : ssprove_swap.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_get _) ;; _ ← cmd (cmd_get _) ;; _ ≈ _ ⦃ _ ⦄) =>
  apply r_get_swap
  : ssprove_swap.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_get ?ℓ') ;; _ ← cmd (cmd_put ?ℓ ?v) ;; _ ≈ _ ⦃ _ ⦄) =>
  apply (r_get_put_swap' ℓ ℓ' v) ;
  neq_loc_auto
  : ssprove_swap.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_put ?ℓ ?v) ;; _ ← cmd (cmd_get ?ℓ') ;; _ ≈ _ ⦃ _ ⦄) =>
  apply (r_put_get_swap' ℓ ℓ' v) ;
  neq_loc_auto
  : ssprove_swap.

#[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_put _ _) ;; _ ← cmd (cmd_put _ _) ;; _ ≈ _ ⦃ _ ⦄) =>
  apply r_put_swap ;
  neq_loc_auto
  : ssprove_swap.

(* TODO Tactic to solve automatically condition when possible *)
Ltac ssprove_swap_aux n :=
  lazymatch eval cbv in n with
  | S ?n => ssprove_sync_eq ; intro ; ssprove_swap_aux n
  | 0%N => ssprove_rswap_cmd_eq_rhs ; ssprove_swap_auto
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

Ltac ssprove_swap_seq_rhs l :=
  lazymatch l with
  | ?n :: ?l =>
    ssprove_swap_rhs n ; [ .. | ssprove_swap_seq_rhs l ]
  | _ =>
    idtac
  end.

Ltac ssprove_swap_seq_lhs l :=
  lazymatch l with
  | ?n :: ?l =>
    ssprove_swap_lhs n ; [ .. | ssprove_swap_seq_lhs l ]
  | _ =>
    idtac
  end.

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

Lemma rel_jdg_replace_sem :
  ∀ (A B : choiceType) (pre : precond) (post : postcond A B) l l' r r',
    ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ l ≈ l' ⦃ eq ⦄ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ r ≈ r' ⦃ eq ⦄ →
    ⊢ ⦃ pre ⦄ l' ≈ r' ⦃ post ⦄.
Proof.
  intros A B pre post l l' r r' h hl hr.
  eapply r_transL. 1: eauto.
  eapply r_transR. 1: eauto.
  auto.
Qed.

Ltac ssprove_code_simpl_more_aux :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ ?c ⦃ _ ⦄ =>
    lazymatch c with
    | @bind _ (chElement ?B) (@assertD ?A ?b ?k1) ?k2 =>
      eapply r_transR ; [
        (* How do I recover the other chUniverse otherwise? *)
        eapply (r_bind_assertD_sym A B b k1 k2)
      | simpl
      ]
    | @bind _ _ (@assertD ?A _ _) _ =>
      eapply r_transR ; [
        eapply (r_bind_assertD_sym A)
      | simpl
      ]
    | x ← sample ?op ;; _ =>
      let x' := fresh x in
      ssprove_sync_eq ; intro x'
    | put ?ℓ := ?v ;; _ =>
      ssprove_sync_eq ; intro
    | x ← get ?ℓ ;; _ =>
      let x' := fresh x in
      ssprove_sync_eq ; intro x'
    | x ← cmd ?c ;; _ =>
      let x' := fresh x in
      ssprove_sync_eq ; intro x'
    | @assertD ?A ?b (λ x, _) =>
      let x' := fresh x in
      ssprove_sync_eq ; intro x'
    | _ => eapply rreflexivity_rule
    end
  | |- _ => fail "The goal should be a syntactic judgment"
  end.

Ltac ssprove_code_simpl_more :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ _ ⦃ _ ⦄ =>
    eapply rel_jdg_replace_sem ; [
    | solve [ repeat ssprove_code_simpl_more_aux ]
    | solve [ repeat ssprove_code_simpl_more_aux ]
    ] ;
    cmd_bind_simpl ; cbn beta
  | |- _ =>
    fail "ssprove_code_simpl_more: goal should be syntactic judgment"
  end.

Ltac ssprove_contract_get_aux :=
  eapply contract_get.

Ltac ssprove_contract_get_lhs :=
  eapply r_transL ; [
    ssprove_contract_get_aux
  | cmd_bind_simpl ; cbn beta
  ].

Ltac ssprove_contract_get_rhs :=
  eapply r_transR ; [
    ssprove_contract_get_aux
  | cmd_bind_simpl ; cbn beta
  ].

Ltac ssprove_contract_put_aux :=
  eapply contract_put.

Ltac ssprove_contract_put_lhs :=
  eapply r_transL ; [
    ssprove_contract_put_aux
  | cmd_bind_simpl ; cbn beta
  ].

Ltac ssprove_contract_put_rhs :=
  eapply r_transR ; [
    ssprove_contract_put_aux
  | cmd_bind_simpl ; cbn beta
  ].

Ltac ssprove_contact_put_get_aux :=
  eapply r_put_get.

Ltac ssprove_contract_put_get_lhs :=
  eapply r_transL ; [
    ssprove_contact_put_get_aux
  | cmd_bind_simpl ; cbn beta
  ].

Ltac ssprove_contract_put_get_rhs :=
  eapply r_transR ; [
    ssprove_contact_put_get_aux
  | cmd_bind_simpl ; cbn beta
  ].

Definition sameSome {A B} (x : option A) (y : option B) :=
  isSome x = isSome y.

Lemma sameSome_None_l :
  ∀ {A B : eqType} (x : option A) (y : option B),
    sameSome x y →
    x == None →
    y == None.
Proof.
  intros A B x y hs hN.
  move: hN => /eqP hN. subst.
  apply /eqP. unfold sameSome in hs.
  destruct y. 1: discriminate.
  reflexivity.
Qed.

(* TODO Find better name *)
Definition sameSomeRel {A B} (R : A → B → Prop) x y :=
  match x, y with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.

Lemma sameSomeRel_sameSome :
  ∀ {A B} R x y,
    @sameSomeRel A B R x y →
    sameSome x y.
Proof.
  intros A B R x y h.
  destruct x, y. all: try contradiction.
  all: reflexivity.
Qed.

Ltac ssprove_forget :=
  lazymatch goal with
  | |- ⊢ ⦃ λ '(s₀, s₁), (_ ⋊ rem_rhs _ _) (s₀, s₁) ⦄ _ ≈ _ ⦃ _ ⦄ =>
    apply r_forget_rhs
  | |- ⊢ ⦃ λ '(s₀, s₁), (_ ⋊ rem_lhs _ _) (s₀, s₁) ⦄ _ ≈ _ ⦃ _ ⦄ =>
    apply r_forget_lhs
  end.

Ltac ssprove_forget_all :=
  repeat ssprove_forget.

Ltac update_pre_fold :=
  repeat change (set_lhs ?ℓ ?v ?pre) with (update_pre [:: hpv_l ℓ v ] pre) ;
  repeat change (set_rhs ?ℓ ?v ?pre) with (update_pre [:: hpv_r ℓ v ] pre) ;
  repeat change (update_pre ?l1 (update_pre ?l2 ?pre))
  with (update_pre (l1 ++ l2) pre).

Ltac remember_pre_fold :=
  repeat change (?pre ⋊ rem_lhs ?ℓ ?v) with (remember_pre [:: hpv_l ℓ v ] pre) ;
  repeat change (?pre ⋊ rem_rhs ?ℓ ?v) with (remember_pre [:: hpv_r ℓ v ] pre) ;
  repeat change (remember_pre ?l1 (remember_pre ?l2 ?pre))
  with (remember_pre (l1 ++ l2) pre).

Ltac ssprove_restore_pre :=
  update_pre_fold ;
  eapply r_restore_pre ; [
    cbn
  | idtac
  ].

Ltac ssprove_restore_mem :=
  update_pre_fold ;
  remember_pre_fold ;
  eapply r_restore_mem ; [
    cbn
  | idtac
  ].

Ltac lookup_hpv_l_eq_solve :=
  repeat (
    tryif rewrite lookup_hpv_l_eq
    then reflexivity
    else rewrite lookup_hpv_l_neq
  ) ; neq_loc_auto.

Ltac lookup_hpv_r_eq_solve :=
  repeat (
    tryif rewrite lookup_hpv_r_eq
    then reflexivity
    else rewrite lookup_hpv_r_neq
  ) ; neq_loc_auto.

#[export] Hint Extern 11 (preserve_update_mem _ _ (couple_lhs _ _ _)) =>
  eapply preserve_update_couple_lhs_lookup ; [
    lookup_hpv_l_eq_solve ..
  | idtac
  ]
  : ssprove_invariant.

#[export] Hint Extern 11 (preserve_update_mem _ _ (couple_rhs _ _ _)) =>
  eapply preserve_update_couple_rhs_lookup ; [
    lookup_hpv_r_eq_solve ..
  | idtac
  ]
  : ssprove_invariant.

#[export] Hint Extern 11 (preserve_update_mem _ _ (triple_rhs _ _ _ _)) =>
  eapply preserve_update_triple_rhs_lookup ; [
    lookup_hpv_r_eq_solve ..
  | idtac
  ]
  : ssprove_invariant.

#[export] Hint Extern 12 (preserve_update_mem _ _ (couple_lhs _ _ _)) =>
  eapply preserve_update_couple_lhs_lookup_None ; [
    repeat rewrite lookup_hpv_l_neq ; [
      reflexivity
    | solve [ neq_loc_auto ] ..
    ] ..
  ]
  : ssprove_invariant.

#[export] Hint Extern 12 (preserve_update_mem _ _ (couple_rhs _ _ _)) =>
  eapply preserve_update_couple_rhs_lookup_None ; [
    repeat rewrite lookup_hpv_r_neq ; [
      reflexivity
    | solve [ neq_loc_auto ] ..
    ] ..
  ]
  : ssprove_invariant.

#[export] Hint Extern 12 (preserve_update_mem _ _ (triple_rhs _ _ _ _)) =>
  eapply preserve_update_triple_rhs_lookup_None ; [
    repeat rewrite lookup_hpv_r_neq ; [
      reflexivity
    | solve [ neq_loc_auto ] ..
    ] ..
  ]
  : ssprove_invariant.

Ltac get_heap_simpl :=
  repeat
  tryif rewrite get_set_heap_eq
  then idtac
  else (rewrite get_set_heap_neq ; [| neq_loc_auto ]).

#[local] Open Scope ring_scope.

Lemma eq_ler :
  ∀ (x y : R),
    x = y →
    x <= y.
Proof.
  intros x y e. subst. apply lerr.
Qed.

Ltac fdisjoint_auto :=
  let h := fresh "h" in
  apply /fdisjointP ;
  intros ? h ;
  rewrite in_fset in h ;
  rewrite in_fset ;
  invert_in_seq h ;
  reflexivity.

#[export] Hint Extern 15 (FDisjoint _ _) =>
  fdisjoint_auto
  : typeclass_instances packages.

Ltac fsubset_auto :=
  let h := fresh "h" in
  apply /fsubsetP ;
  intros ? h ;
  rewrite in_fset ; rewrite in_fset in h ;
  invert_in_seq h ;
  inseq_try.