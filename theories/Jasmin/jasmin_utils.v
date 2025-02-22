From Coq Require String Ascii.

From Jasmin Require Import expr.

From SSProve.Crypt Require Import Prelude Package.
From SSProve.Jasmin Require Import jasmin_translate.

From Ltac2 Require Ltac2 Printf.
From Ltac2 Require String Char Fresh Ident.


Module JasminCodeNotation.

  Notation " ⸨ ws ⸩ a .[ ptr * scale ] " := (chArray_get ws a ptr scale)
                                            (format " ⸨ ws ⸩  a .[ ptr * scale ] ").
  Notation " a [ w / p ] " :=
    (chArray_set a AAscale p w)
      (at level 99, no associativity,
        format " a [ w / p ] ").

  Notation "$$ i" := (translate_var _ {| vtype := _; vname := i |})
                       (at level 99, format "$$ i").

  Notation "$$$ i" := ({| v_var := {| vtype := _; vname := i |}; v_info := _ |})
                        (at level 99,
                          format "$$$ i").

  Notation "'for var ∈ seq" := (translate_for _ ($$$var) seq)
                                (at level 99).
End JasminCodeNotation.

Module jtac.

Import JasminNotation JasminCodeNotation.

Import Ltac2.Ltac2 Ltac2.Printf.

Ltac2 rec ltac_int_of_pos (p : constr) : int :=
  let res :=
    lazy_match! p with
    | xH => 1
    | xO ?p' => Int.mul 2 (ltac_int_of_pos p')
    | xI ?p' => Int.add (Int.mul 2 (ltac_int_of_pos p')) 1
    end in
  if Int.lt res 0
  then Control.throw (Out_of_bounds (Some (fprintf "ltac_int_of_pos: value is too large: %t" p)))
  else res.

Ltac2 ltac_int_of_Z (z : constr) : int :=
  lazy_match! z with
  | Z0 => 0
  | Zpos ?p => ltac_int_of_pos p
  | Zneg ?p => Int.sub 0 (ltac_int_of_pos p)
  end.

Ltac2 ltac_char_of_ascii (c : constr) : char :=
  let c := constr:(Z.of_nat (Ascii.nat_of_ascii $c)) in
  let c := eval cbv in $c in
  Char.of_int (ltac_int_of_Z c).

Ltac2 ltac_string_of_string (s : constr) : string :=
  let s := eval cbv in $s in
  let rec ltac_copy_to_string (s : constr) (out : string) (i : int) : unit :=
    lazy_match! s with
    | EmptyString => ()
    | String ?c ?s => String.set out i (ltac_char_of_ascii c) ;
                      ltac_copy_to_string s out (Int.add i 1)
    end
  in
  let len := constr:(Z.of_nat (String.length $s)) in
  let len := eval cbv in $len in
  let out := String.make (ltac_int_of_Z len) (Char.of_int 0) in
  ltac_copy_to_string s out 0 ;
  out.

Ltac2 base_length (s : string) : int :=
  let full_stop := 46 in
  let n := String.length s in
  let rec f i len_ext :=
    if Int.equal i 0
    then None
    else
      let i := Int.sub i 1 in
      let c := String.get s i in
      let len_ext := Int.add 1 len_ext in
      if Int.equal full_stop (Char.to_int c)
      then Some len_ext
      else f i len_ext
  in
  match f n 0 with
  | None => n
  | Some l => Int.sub n l end.

Ltac2 basename (s : string) : string :=
  let len := base_length s in
  if Int.equal len 0 then s else
  let s' := String.make len (Char.of_int 0) in
  let rec cp i :=
    if Int.equal i 0 then () else
      let i := Int.sub i 1 in
      String.set s' i (String.get s i) ; cp i
  in cp len ;
     s'.

Ltac2 setjvars () :=
  lazy_match! goal with
  | [ |- context [ $$ ?i ] ] =>
      let s := basename (ltac_string_of_string i) in
      match Ident.of_string s with
      | None => Control.throw (Tactic_failure (Some (fprintf "Not a valid ident: %s (was: %t)" s i)))
      | Some id =>
          let x := Fresh.fresh (Fresh.Free.of_goal ()) id in
          set ($x := $$ $i) in *
      end
  end.

End jtac.

Ltac setjvars := ltac2:(jtac.setjvars ()).

Ltac prog_unfold := unfold translate_prog', translate_prog,
    translate_call, translate_call_body,
    translate_write_lvals, translate_write_var, translate_instr,
    coerce_chtuple_to_list, bind_list', bind_list_trunc_aux,
    wsize_size, trunc_list,
    List.nth_default.


#[export] Hint Rewrite coerce_typed_code_K eq_rect_K eq_rect_r_K : prog_rewrite.

Ltac simpl_fun :=
  repeat (match goal with
         | _ => progress autorewrite with prog_rewrite
         | _ => prog_unfold; simpl
         end).

Import PackageNotation.

Ltac swap_first_occ loc :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ ?c1 ⦃ _ ⦄ =>
      lazymatch c1 with
      | #put _ := _ ;; #put loc := _ ;; _ => ssprove_rswap_cmd_eq_rhs; ssprove_swap_auto
      | #put _ := _ ;; _ ← get loc ;; _ => ssprove_rswap_cmd_eq_rhs; ssprove_swap_auto
      | _ ← get _ ;; #put loc := _ ;; _ => ssprove_rswap_cmd_eq_rhs; ssprove_swap_auto
      | _ ← get _ ;; _ ← get loc ;; _ => ssprove_rswap_cmd_eq_rhs; ssprove_swap_auto
      | _ => ssprove_sync_eq ; try intro ; swap_first_occ loc
      end
  end.

Ltac swap_loc loc :=
  eapply r_transL; [ solve [ swap_first_occ loc ] | cmd_bind_simpl ; cbn beta ].

Ltac swap_loc_ignore_head loc :=
  eapply r_transL; [ solve [ ssprove_sync_eq ; try intro ; swap_first_occ loc ] | cmd_bind_simpl ; cbn beta ].

Ltac set_at_head loc :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ ?c1 ≈ _ ⦃ _ ⦄ =>
      lazymatch c1 with
      | #put loc := _ ;; _ => idtac
      | _ ← get loc ;; _ => idtac
      | _ => swap_loc loc; set_at_head loc
      end
  end.

Ltac set_at_snd loc :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ ?c1 ≈ _ ⦃ _ ⦄ =>
      lazymatch c1 with
      | #put _ := _ ;; #put loc := _ ;; _ => idtac
      | #put _ := _ ;; _ ← get loc ;; _ => idtac
      | _ ← get _ ;; #put loc := _ ;; _ => idtac
      | _ ← get _ ;; _ ← get loc ;; _ => idtac
      | _ => swap_loc_ignore_head loc; set_at_snd loc
      end
  end.

Ltac clear_loc loc := set_at_head loc; set_at_snd loc; first [ ssprove_contract_put_get_lhs | ssprove_contract_put_lhs ].

Ltac clear_get_aux c1 :=
  lazymatch c1 with
  | _ ← get ?loc ;; _ => clear_loc loc
  | #put _ := _ ;; ?c2 => clear_get_aux c2
  end.

Ltac clear_get :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ ?c1 ≈ _ ⦃ _ ⦄ => clear_get_aux c1
  end.
