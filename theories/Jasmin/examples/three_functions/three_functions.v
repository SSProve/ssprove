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
From Crypt Require Import Prelude Package.

Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

Local Open Scope string.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Context (f : funname).

Definition three_functions :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.139" |};
          v_info :=
           xO
            (xO xH) |}];
       f_body :=
        [MkI
          (xI
            (xO
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.139" |};
              v_info :=
               xI
                (xI
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.139" |};
                v_info :=
                 xO
                  (xI
                    (xO xH)) |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO
                      (xI
                        (xO xH))))))))));
         MkI
          (xI
            (xO xH))
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res_z.140" |};
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
                  vname := "z.139" |};
                v_info :=
                 xO
                  (xI xH) |};
              gs := Slocal |}]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res_z.140" |};
          v_info :=
           xO
            (xO
              (xI xH)) |}];
       f_extra := tt |});
     (xI (xI xH),
      {| f_info :=
        xI
         (xO (xI xH));
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.141" |};
          v_info :=
           xO
            (xI
              (xI xH)) |}];
       f_body :=
        [MkI
          (xI
            (xI
              (xI xH)))
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res_y.142" |};
              v_info :=
               xO
                (xI
                  (xO
                    (xO xH))) |}])
           (xI
            (xO
              (xO
                (xO xH))))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.141" |};
                v_info :=
                 xO
                  (xO
                    (xO
                      (xO xH))) |};
              gs := Slocal |}]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res_y.142" |};
          v_info :=
           xI
            (xI
              (xO
                (xO xH))) |}];
       f_extra := tt |});
     (xI
       (xO
         (xO (xO xH))),
      {| f_info :=
        xO
         (xO
           (xI
             (xO xH)));
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.143" |};
          v_info :=
           xI
            (xO
              (xI
                (xO xH))) |}];
       f_body :=
        [MkI
          (xO
            (xI
              (xI
                (xO xH))))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res_x.144" |};
              v_info :=
               xO
                (xO
                  (xO
                    (xI xH))) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.143" |};
                v_info :=
                 xI
                  (xI
                    (xI
                      (xO xH))) |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res_x.144" |};
          v_info :=
           xI
            (xO
              (xO
                (xI xH))) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.




Definition tr_P := Eval simpl in tr_p three_functions.
Definition default_prog' := (1%positive, (ret tt)).
Definition default_call := (1%positive, fun (x : [choiceType of seq typed_chElement]) => ret x).
Definition get_tr sp n := List.nth_default default_call sp n.
Definition tr_f := Eval simpl in (get_tr tr_P 2).
Definition tr_g := Eval simpl in (get_tr tr_P 1).
Definition tr_h := Eval simpl in (get_tr tr_P 0).


Opaque translate_for.

Goal forall goal v, tr_f.2 [('word U64; v)] = goal .
  intros goal v.
  unfold tr_f.
  unfold get_tr. unfold tr_P. unfold translate_prog'.
  unfold  get_tr , tr_p.
  simpl_fun.

  repeat setjvars.

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).

Admitted.

Goal forall goal v, tr_g.2 [v] = goal.
  intros goal v.
  unfold tr_g.
  unfold get_tr. unfold tr_P.
  simpl_fun.

  repeat setjvars.

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).

Admitted.

Goal forall goal v, tr_h.2 [v] = goal.
  intros goal v.
  unfold tr_h.
  unfold get_tr. unfold tr_P.
  simpl_fun.

  repeat setjvars.

  repeat setoid_rewrite coerce_to_choice_type_K.
  repeat setoid_rewrite (@zero_extend_u U64).

Admitted.
