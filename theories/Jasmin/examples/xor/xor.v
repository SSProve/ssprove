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

Definition tr_xor := translate_prog xor.

Eval cbn in tr_xor.
Goal tr_xor = tr_xor.
  unfold tr_xor at 2.
  unfold translate_prog, translate_fundef.
  unfold translate_cmd.
  simpl.
  unfold translate_var. simpl.
  set (x := ('word U64; nat_of_fun_ident 2%positive "x.131")).
  set (r := ('word U64; nat_of_fun_ident 2%positive "r.133")).
  set (y := ('word U64; nat_of_fun_ident 2%positive "y.132")).
  (* does nothing; too many binders? *)
  (* repeat setoid_rewrite zero_extend_u. *)
