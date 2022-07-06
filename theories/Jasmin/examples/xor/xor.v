Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
From Jasmin Require Import expr.
From CoqWord Require Import word.
(* From Jasmin Require Import x86_extra. *)
From JasminSSProve Require Import jasmin_translate jasmin_utils.
From Crypt Require Import Prelude Package pkg_user_util.

Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

Local Open Scope string.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Context (f : funname).

Definition xor :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.131" |};
          v_info :=
           xO
            (xO xH) |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "y.132" |};
          v_info :=
           xI
            (xO xH) |}];
       f_body :=
        [MkI
          (xO
            (xI
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.133" |};
              v_info :=
               xO
                (xO
                  (xI xH)) |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "x.131" |};
               v_info :=
                xI
                 (xI
                   (xO xH)) |};
             gs := Slocal |}));
         MkI
          (xO
            (xI xH))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.133" |};
              v_info :=
               xI
                (xO
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Papp2 (Olxor U64)
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.133" |};
                v_info :=
                 xO
                  (xO
                    (xO xH)) |};
              gs := Slocal |})
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.132" |};
                v_info :=
                 xI
                  (xI xH) |};
              gs := Slocal |})))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.133" |};
          v_info :=
           xI
            (xO
              (xI xH)) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.

Definition tr_P := Eval simpl in translate_prog' xor.
Definition default_prog' := (1%positive, fun s_id : p_id => (ret tt)).
Definition default_call := (1%positive, fun (s_id : p_id) (x : [choiceType of seq typed_chElement]) => ret x).
Definition get_tr sp n := List.nth_default default_call sp n.
Definition tr_xor := Eval simpl in (get_tr tr_P.2 0).

Opaque translate_for.

Goal forall goal w1 w2, tr_xor.2 1%positive [('word U64; w1); ('word U64; w2)] = goal .
  intros goal.
  unfold tr_xor.
  unfold get_tr.
  simpl_fun.

  repeat setjvars.

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).

Admitted.

Lemma eq_rect_K :
  forall (A : eqType) (x : A) (P : A -> Type) h e,
    @eq_rect A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

(* Lemma injective_translate_var2 : *)
(*   forall fn x y, x != y -> translate_var fn x != translate_var fn y. *)
(* Proof. *)
(*   intros. *)
(*   apply /negP. *)
(*   intros contra. *)
(*   move: contra => /eqP contra. *)
(*   eapply injective_translate_var in contra. *)
(*   move: H => /eqP. easy. *)
(*   exact xor. *)
(*   apply x86_correct. *)
(*   Unshelve. *)
(*   2: exact progUnit. *)
(* Qed. *)

Hint Resolve injective_translate_var2 : ssprove_swap.

(* #[export] Hint Extern 9 (⊢ ⦃ _ ⦄ _ ← cmd (cmd_put ?ℓ ?v) ;; _ ← cmd (cmd_get ?ℓ') ;; _ ≈ _ ⦃ _ ⦄) => *)
(*   apply (r_put_get_swap' ℓ ℓ' v) *)
(*   : ssprove_swap. *)
(* #[export] Hint Extern 10 (⊢ ⦃ _ ⦄ _ ← cmd _ ;; _ ← cmd (cmd_sample _) ;; _ ≈ _ ⦃ _ ⦄) => *)
Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.
  (* shelve. *)
  (* repeat match goal with *)
  (* | |- translate_var _ _ != translate_var _ _ => eapply injective_translate_var3; auto *)
  (* end. *)
Import ListNotations.
Lemma f_xor_correct : forall w1 w2, ⊢ ⦃ fun _ => True ⦄ tr_xor.2 1%positive [('word U64; w1); ('word U64; w2)] ⇓ [('word U64; wxor w1 w2)] ⦃ fun _ => True ⦄.
Proof.
  (* preprocessing *)
  intros w1 w2.
  simpl_fun.
  repeat setjvars.

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).
  intros.

  (* proof *)
  ssprove_swap_lhs 1%nat.
  ssprove_contract_put_get_lhs.
  ssprove_swap_seq_lhs [:: 1 ; 0 ; 2 ; 1].
  ssprove_contract_put_get_lhs.
  ssprove_swap_seq_lhs [:: 1 ; 0 ; 2 ; 1].
  ssprove_contract_put_get_lhs.
  ssprove_swap_seq_lhs [:: 0 ; 2 ; 1 ].
  ssprove_contract_put_lhs.
  ssprove_swap_seq_lhs [:: 2 ; 1 ].
  ssprove_contract_put_get_lhs.
  repeat eapply u_put.
  eapply u_ret_eq.
  easy.
Qed.
