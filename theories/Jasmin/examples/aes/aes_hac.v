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
                            apply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (pre_to_post P) _) ; [ | intros ; unfold pre_to_post ]
                        end.

  Ltac remove_get_in_lhs :=
    eapply better_r_get_remind_lhs ;
    unfold Remembers_lhs , rem_lhs ;
    [ intros ? ? k ;
      destruct_pre ;
      repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq ;
      reflexivity | ].

  Lemma foo id0 rcon rkey temp2 :
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
    bind_jazz_hac.
    admit.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    bind_jazz_hac.
    admit.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    bind_jazz_hac.
    admit.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    bind_jazz_hac.
    admit.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    bind_jazz_hac.
    admit.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    remove_get_in_lhs.
    bind_jazz_hac.
    admit.

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
