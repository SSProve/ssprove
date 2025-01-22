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
From SSProve.Jasmin Require Import jasmin_translate.
From SSProve.Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.




Definition ssprove_jasmin_prog : uprog.
Proof.
  refine {| p_funcs :=
 [ ( (* h *) xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "z.157"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := (sword U64)
                                ; vname := "z.157"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp2 (Oadd (Op_w U64))
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "z.157"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Papp1 (Oword_of_int U64)
                       (Pconst (Zpos (xO (xI (xO (xI (xO xH)))))))))));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res_z.158"  |}
                    ; v_info := dummy_var_info |}]
                (xO xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "z.157"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res_z.158"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* g *) xO xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "y.159"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res_y.160"  |}
                    ; v_info := dummy_var_info |}]
                (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "y.159"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res_y.160"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* f *) xI xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "x.161"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res_x.162"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp2 (Oadd (Op_w U64))
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "x.161"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Papp1 (Oword_of_int U64) (Pconst (Zpos (xH))))))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res_x.162"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.

Defined.
Notation H := ( xH ).
Notation G := ( xO xH ).
Notation F := ( xI xH ).
