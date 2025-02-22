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
 [ ( (* f *) xH,
     {| f_info := FunInfo.witness
      ; f_tyin := []
      ; f_params := []
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var := {| vtype := sint
                                ; vname := "x.149"  |}
                    ; v_info := dummy_var_info |}]
                (xO xH) [(Pconst (Z0))]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := (sword U64)
                                ; vname := "y.148"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := sint
                                      ; vname := "x.149"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "y.148"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* incr *) xO xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [sint]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "n.150"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := sint
                                ; vname := "m.151"  |}
                    ; v_info := dummy_var_info |})
                AT_inline (sint)
                ((Papp2 (Olsl Op_int)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := sint
                                      ; vname := "n.150"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pconst (Zpos (xI (xO (xO (xO (xO (xO xH))))))))))) ]
      ; f_tyout := [sint]
      ; f_res :=
          [{| v_var := {| vtype := sint
                        ; vname := "m.151"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.

Defined.
Notation F := ( xH ).
Notation INCR := ( xO xH ).
