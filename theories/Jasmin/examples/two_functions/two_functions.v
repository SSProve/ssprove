Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
From Jasmin Require Import expr.
(* From Jasmin Require Import x86_extra. *)
From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Context (f : funname).

Definition two_functions :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.134" |};
          v_info :=
           xO
            (xO xH) |}];
       f_body :=
        [MkI
          (xI
            (xO xH))
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res_y.135" |};
              v_info :=
               xO
                (xO
                  (xO xH)) |}])
           (xI
            (xI xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.134" |};
                v_info :=
                 xO
                  (xI xH) |};
              gs := Slocal |}]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res_y.135" |};
          v_info :=
           xI
            (xO
              (xO xH)) |}];
       f_extra := tt |});
     (xI (xI xH),
      {| f_info :=
        xO
         (xI (xO xH));
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.136" |};
          v_info :=
           xI
            (xI
              (xO xH)) |}];
       f_body :=
        [MkI
          (xO
            (xO
              (xI xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res_x.137" |};
              v_info :=
               xO
                (xI
                  (xI xH)) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.136" |};
                v_info :=
                 xI
                  (xO
                    (xI xH)) |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res_x.137" |};
          v_info :=
           xI
            (xI
              (xI xH)) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.


Import PackageNotation.
Notation coe_cht := coerce_to_choice_type.
Notation coe_tyc := coerce_typed_code.
Notation " 'array " := (chMap 'int ('word U8)) (at level 2) : package_scope.
Notation " 'array " := (chMap 'int ('word U8)) (in custom pack_type at level 2).
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (at level 2) : package_scope.
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (in custom pack_type at level 2).
Notation " ⸨ ws ⸩ a .[ ptr * scale ] " := (chArray_get ws a ptr scale)
    (format " ⸨ ws ⸩  a .[ ptr * scale ] ").
Notation " a [ w / p ] " :=
  (chArray_set a AAscale p w)
    (at level 99, no associativity,
      format " a [ w / p ] ").

From Equations Require Import Equations.
Set Equations With UIP.
Set Equations Transparent.

From extructures Require Import ord fset fmap.

Definition tr_P := Eval simpl in tr_p two_functions.
Definition default_prog' := (1%positive, (ret tt)).
Definition default_call := (1%positive, fun (x : [choiceType of seq typed_chElement]) => ret x).
Definition get_tr sp n := List.nth_default default_call sp n.
Definition tr_f := Eval simpl in (get_tr tr_P 1).
Definition tr_g := Eval simpl in (get_tr tr_P 0).


Lemma eq_rect_K :
  forall (A : eqType) (x : A) (P : A -> Type) h e,
    @eq_rect A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

From CoqWord Require Import word.

Notation "$ i" := (_ ; nat_of_fun_var _ {| vtype := _; vname := i |})
                    (at level 99, format "$ i").

Notation "$$ i" := ({| v_var := {| vtype := _; vname := i |}; v_info := _ |})
                    (at level 99,
                      format "$$ i").

Notation "'for var ∈ seq" := (translate_for _ ($$var) seq)
                                      (at level 99).

Ltac prog_unfold := unfold get_tr, translate_prog', tr_p, translate_prog,
    translate_call,
    translate_write_lvals, translate_write_var, translate_instr,
    translate_var,
    coerce_chtuple_to_list, bind_list', bind_list_trunc_aux,
    wsize_size, trunc_list,
    List.nth_default.
Hint Rewrite coerce_typed_code_K eq_rect_K eq_rect_r_K : prog_rewrite.

Opaque translate_for.
Ltac simpl_fun :=
  repeat (match goal with
         | _ => progress autorewrite with prog_rewrite
         | _ => prog_unfold; simpl
         end).

Goal forall goal v, tr_g.2 [v] = goal.
  intros goal v.
  unfold tr_g.
  unfold get_tr. unfold tr_P.
  simpl_fun.

  (* BSH: the setoid_rewrites takes forever if we do not 'set' these names first *)
  set (array32 := sarr 32%positive).
  set (x := $"x.136").
  try set (res_x := $"res_x.137").
  try set (y := $"y.134").
  try set (yy := $$"y.134").
  try set (res_y := $"res_y.135").

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).

Admitted.


Goal forall goal v, tr_f.2 [('word U64; v)] = goal .
  intros goal v.
  unfold tr_f.
  unfold get_tr. unfold tr_P. unfold translate_prog'.
  simpl_fun.

  (* BSH: the setoid_rewrites takes forever if we do not 'set' these names first *)
  set (array32 := sarr 32%positive).
  set (x := $"x.136").
  try set (res_x := $"res_x.137").
  try set (y := $"y.134").
  try set (res_y := $"res_y.135").

  repeat setoid_rewrite (@zero_extend_u U64).
  repeat setoid_rewrite coerce_to_choice_type_K.

Admitted.
