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

Definition add1_body := [MkI
          (xO
            (xO
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.131" |};
              v_info :=
               xO
                (xI
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "arg.130" |};
               v_info :=
                xI
                 (xO
                   (xO xH)) |};
             gs := Slocal |}));
         MkI
          (xI
            (xO xH))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.131" |};
              v_info :=
               xI
                (xI xH) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.131" |};
                v_info :=
                 xO
                  (xI xH) |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))].

Definition add1 :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "arg.130" |};
          v_info :=
           xO
            (xO xH) |}];
       f_body :=
        add1_body;
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.131" |};
          v_info :=
           xI
            (xI
              (xO xH)) |}];
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

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.
From extructures Require Import fmap.

Definition body_tr :=
  translate_cmd P emptym xH add1_body.
Eval cbn in body_tr.
Goal body_tr = body_tr.
  unfold body_tr at 2.
  unfold translate_cmd.
  simpl.
  unfold translate_var. simpl.
  set (arg := ('word U64; nat_of_fun_ident 1%positive "arg.130")).
  set (z := ('word U64; nat_of_fun_ident 1%positive "z.131")).
  rewrite !coerce_to_choice_type_K.
  repeat setoid_rewrite zero_extend_u.
  unfold wsize_size.
  unfold wrepr. simpl. unfold nat63; unfold nat31; unfold nat15; unfold nat7.
