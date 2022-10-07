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




Definition ssprove_jasmin_prog : uprog.
Proof.
  refine {| p_funcs :=
 [ ( (* double *) xH,
     {| f_info := xO xH
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "n.141"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.142"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp1 (Oint_of_word U64)
                     (Pvar
                        {| gv := {| v_var :=
                                      {| vtype := (sword U64)
                                       ; vname := "n.141"  |}
                                  ; v_info := dummy_var_info |} ; gs := Slocal |})))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "n.141"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Papp2 (Oadd (Op_w U64))
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := (sword U64)
                                           ; vname := "n.141"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Papp1 (Oword_of_int U64) (Pconst (Zpos (xH)))))))]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "n.141"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.
Defined.
