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
 [ ( (* add_inline *) xH,
     {| f_info := FunInfo.witness
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO xH))))));
            (sarr (xO (xO (xO (xO (xO xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xO xH))))))
                 ; vname := "x.149"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xO xH))))))
                  ; vname := "y.150"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "xr.152"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO xH))))))
                                   ; vname := "x.149"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "yr.153"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO xH))))))
                                   ; vname := "y.150"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.154"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "xr.152"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Oaddcarry (U64))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "xr.152"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "yr.153"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xO xH))))))
                         ; vname := "res.151"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Z0)))
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "xr.152"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.155"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xO (xO xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "xr.152"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO xH))))))
                                        ; vname := "x.149"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.155"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "yr.153"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xO xH))))))
                                         ; vname := "y.150"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.155"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lvar
                         {| v_var :=
                              {| vtype := sbool
                               ; vname := "cf.154"  |}
                          ; v_info := dummy_var_info |};
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "xr.152"  |}
                           ; v_info := dummy_var_info |}]
                      AT_keep (Oaddcarry (U64))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "xr.152"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "yr.153"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sbool
                                          ; vname := "cf.154"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xO (xO xH))))))
                               ; vname := "res.151"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.155"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "xr.152"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xO xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xO xH))))))
                 ; vname := "res.151"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.

Defined.
Notation ADD_INLINE := ( xH ).
