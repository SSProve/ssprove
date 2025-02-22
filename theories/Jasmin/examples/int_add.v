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
 [ ( (* add *) xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [sint; sint]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "n.152"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "m.153"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.154"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sint
                                    ; vname := "n.152"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var := {| vtype := sint
                                     ; vname := "m.153"  |}
                         ; v_info := dummy_var_info |})
                     AT_inline (sint)
                     ((Papp2 (Oadd Op_int)
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "m.153"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Pconst (Zpos (xH))))))]) ]
      ; f_tyout := [sint]
      ; f_res :=
          [{| v_var := {| vtype := sint
                        ; vname := "m.153"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* odd *) xO xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "n.155"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "m.156"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.157"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp1 (Oint_of_word U64)
                     (Pvar
                        {| gv := {| v_var :=
                                      {| vtype := (sword U64)
                                       ; vname := "n.155"  |}
                                  ; v_info := dummy_var_info |} ; gs := Slocal |})))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "m.156"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Papp2 (Oadd (Op_w U64))
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := (sword U64)
                                           ; vname := "m.156"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Papp1 (Oword_of_int U64) (Pconst (Zpos (xH)))))))]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "m.156"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.

Defined.
Notation ADD := ( xH ).
Notation ODD := ( xO xH ).
