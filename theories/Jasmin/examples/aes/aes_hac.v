Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool
  ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
Set Warnings "-notation-overridden".
From Jasmin Require Import expr.
Set Warnings "notation-overridden".
From Jasmin Require Import x86_instr_decl x86_extra.
From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.

Set Bullet Behavior "Strict Subproofs".
(* Set Default Goal Selector "!". *) (* I give up on this for now. *)

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import micromega.Lia.
From mathcomp.word Require Import word ssrZ.
From JasminSSProve Require Import aes_jazz jasmin_utils.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality Hacspec_Lib.
Open Scope hacspec_scope.

Notation call fn := (translate_call _ fn _).

Section Hacspec.

<<<<<<< HEAD
  (* NB: this redefines neq_loc_auto, which helps some tactics, since checking for inequality by computation is not feasible for translated variables *)
  Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

  Ltac destruct_pre :=
    repeat
      match goal with
      | [ H : set_lhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : set_rhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : _ /\ _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : (_ ⋊ _) _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : exists _, _ |- _ ] =>
          let o := fresh in
          destruct H as [o]
      end; simpl in *; subst.

  Lemma det_jkey id0 rcon rkey temp2 : deterministic (JKEY_COMBINE id0 rcon rkey temp2).
  Proof.
    unfold translate_call, translate_call_body.
    Opaque translate_call.
    simpl.

    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
    Transparent translate_call.
  Defined.

  Lemma det_key_combine rcon rkey temp2 : deterministic (is_state (key_combine rcon rkey temp2)).
  Proof.
    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
  Defined.

  Lemma unfold_det_run : forall {A : choiceType} c [h : @deterministic A c] s, @det_run A c h s = match h with
                                                                                             | deterministic_ret x => (x, s)
                                                                                             | deterministic_get ℓ k hk => det_run (k (get_heap s ℓ)) (h := hk _) s
                                                                                             | deterministic_put ℓ v k hk => det_run k (h := hk) (set_heap s ℓ v)
                                                                                             end.
  Proof. destruct h ; reflexivity. Qed.

  Ltac bind_jazz_hac := match goal with
                        | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] =>
                            apply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ Q _) ; [ | intros ; unfold pre_to_post ]
                        end.

  Ltac remove_get_in_lhs :=
    eapply better_r_get_remind_lhs ;
    unfold Remembers_lhs , rem_lhs ;
    [ intros ? ? k ;
      destruct_pre ;
      repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq ;
      reflexivity | ].

  Notation JVSHUFPS i rkey temp1 temp2 := (trc VSHUFPS i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]).
  
  Lemma key_combined_eq id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
        JKEY_COMBINE id0 rcon rkey temp2
        ≈
        is_state (key_combine rcon rkey temp2)
        ⦃ fun '(v0, _) '(v1, _) =>
            exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                     /\ (o1, o2) = v1 ⦄.
  Proof.
    set (JKEY_COMBINE _ _ _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    (* unfold ssprove_jasmin_prog in r. *)
    simpl in r.

    subst r.
    rewrite !zero_extend_u.
    unfold key_combine.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    remove_get_in_lhs.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] =>
        eapply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (pre_to_post true_precond) _) ; [ | intros ; unfold pre_to_post ]
    end.

    {
    apply forget_precond.
    rewrite !zero_extend_u.

    unfold tr_app_sopn_tuple.
    unfold sopn_sem.
    unfold sopn.get_instr_desc.
    unfold asm_opI.
    unfold asm_op_instr.
    unfold semi, arch_extra.get_instr_desc.
    unfold instr_desc, _asm_op_decl, instr_desc_op, _asm, x86_extra.
    unfold x86_sem.x86.
    unfold x86_op_decl.
    unfold x86_instr_desc.
    unfold id_semi.
    unfold Ox86_VPSHUFD_instr.
    unfold ".1".
    unfold x86_VPSHUFD.
    unfold wpshufd.

    set (totce _) at 2.
    cbn in t.
    unfold totce in t.

    set (chCanonical _).
    cbn in s.
    subst s.

    set (tr_app_sopn _ _ _ _).
    cbn in y.
    subst y.
    hnf.

    unfold totce.
    subst t.
    unfold ".π2".

    unfold wpshufd_128.
    unfold iota.
    unfold map.
    set (wpshufd1 _ _ _).
    set (wpshufd1 _ _ _).
    set (wpshufd1 _ _ _).
    set (wpshufd1 _ _ _).
    unfold vpshufd.
    set (fun _ : T Hacspec_Lib_Pre.int128 => _).
    set (_ shift_right _).

    apply (@r_bind _ _ _ _ (ret w) b (fun w => ret (wrepr U128 (wcat_r [w; w0; w1; w2]))) y true_precond (fun _ _ => True)).
    - apply r_ret ; reflexivity.
    - intros.
      subst y. hnf. clear b.
      set (fun _ : T Hacspec_Lib_Pre.int128 => _).
      set (_ shift_right _).
      apply (@r_bind _ _ _ _ (ret w0) b (fun _ => ret (wrepr U128 (wcat_r [_; _; _; _]))) y (fun '(_, _) => True) (fun _ _ => True)).
      + apply r_ret ; reflexivity.
      + intros.
        subst y. hnf. clear b.

        set (fun _ : T Hacspec_Lib_Pre.int128 => _).
      set (_ shift_right _).
      apply (@r_bind _ _ _ _ (ret w1) b (fun _ => ret (wrepr U128 (wcat_r [_; _; _; _]))) y (fun '(_, _) => True) (fun _ _ => True)).
      * apply r_ret ; reflexivity.
      * intros.
        subst y. hnf. clear b.

        
        set (fun _ : T Hacspec_Lib_Pre.int128 => _).
        set (_ shift_right _).
        apply (@r_bind _ _ _ _ (ret w2) b (fun _ => ret (wrepr U128 (wcat_r [_; _; _; _]))) y (fun '(_, _) => True) (fun _ _ => True)).
        -- apply r_ret ; reflexivity.
        -- intros.
           subst y. hnf. clear b.
           unfold wcat_r.

           Set Printing Coercions.

           unfold lift_to_both0, lift_to_both.
           unfold is_pure.
           unfold "_ .| _".
           unfold Hacspec_Lib_Pre.int_or.
           unfold word.wor.
           unfold lift_to_both.
           unfold lift_scope.
           unfold is_state.
           unfold lift_to_code.
           unfold lift_code_scope.
           unfold prog.

           apply r_ret.
           intros.

           unfold T_ct, eq_rect_r, Logic.eq_sym, Hacspec_Lib_Pre.int, ChoiceEq, Hacspec_Lib_Pre.int_obligation_1, ct, eq_rect.

           unfold pre_to_post.
           split ; [ | reflexivity ].
           
           rewrite Z.lor_comm.
           rewrite (Z.lor_comm (urepr a₀0)).
           rewrite (Z.lor_comm (urepr a₀1)).
           rewrite (Z.lor_comm (urepr a₀2)).

           unfold wor at 1.

           
           
           simpl.
           
           replace (int_to_Z (Posz 32)) with (Hacspec_Lib_Pre.usize 32).
                      
           unfold "_ shift_left _".
           unfold Hacspec_Lib_Pre.shift_left_.
           unfold wshl.
           unfold lsl.
           
           
           unfold lift_scope, lift_to_both0, lift_to_both, is_pure, is_state.
           
           apply (@r_bind _ _ _ _ (ret w2) b (fun _ => ret (wrepr U128 (wcat_r [_; _; _; _]))) y (fun '(_, _) => True) (fun _ _ => True)).

    }
    
    set (U8 %/ 2).
    assert (n = 4). admit.
    replace n with 4%nat in *.
    unfold curry.
    
    Set Printing Coercions.
    unfold nat_of_wsize.
    unfold wsize_size_minus_1.
    unfold nat7.
    unfold "%/".
    unfold edivn.
    cbn.
    
    unfold embed_tuple.
    
    unfold encode_tuple.
    unfold lchtuple.
    unfold tr_app_sopn.
    unfold embed_tuple.
    cbn.

    rewrite !zero_extend_u.
    apply r_ret.
    intros.
    
    
    unfold tr_app_sopn.

    
    bind_jazz_hac.
    Set Printing Implicit.
    Set Printing Coercions.
    shelve.

    do 5 (apply better_r_put_lhs ; do 2 remove_get_in_lhs ; bind_jazz_hac ; [shelve | ]).

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    apply r_ret.

    intros.
    destruct_pre.
    eexists.
    eexists.
    split ; [ reflexivity | ].
    cbn.
    rewrite !zero_extend_u.
    reflexivity.

    
=======
  Lemma foo id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
      JKEY_COMBINE id0 rcon rkey temp2
      ≈
      is_state (key_combine rcon rkey temp2)
      ⦃ fun '(v0, _) '(v1, _) =>
          exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                   /\ (o1, o2) = v1 ⦄.
  Proof.
    unfold translate_call, translate_call_body.
    Opaque translate_call.

    simpl.
    unfold sopn_sem, tr_app_sopn_tuple, tr_app_sopn_single.
    simpl.

>>>>>>> 1c0c1bbe99e9078b09debae9e69a87fc6b4915d9
  Admitted.

  Lemma bar id0 rcon rkey temp2 :
    ⊢ ⦃ fun '(_, _) => True ⦄
      JKEY_EXPAND id0 rcon rkey temp2
      ≈
      key_expand (wrepr U8 rcon) rkey temp2
      ⦃ fun '(v0, _) '(v1, _) =>
          exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                   /\ (o1, o2) = v1 ⦄.
  Proof.
    Transparent translate_call.
    unfold translate_call, translate_call_body.
    Opaque translate_call.
    simpl.
Admitted.
