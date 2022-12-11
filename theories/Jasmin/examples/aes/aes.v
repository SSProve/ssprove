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

Set Bullet Behavior "Strict Subproofs".
(* Set Default Goal Selector "!". *) (* I give up on this for now. *)

Definition ssprove_jasmin_prog : uprog.
Proof.
  refine {| p_funcs :=
 rev [ ( (* RCON *) xI (xI (xO (xO xH))),
     {| f_info := xO (xO (xO (xI xH)))
      ; f_tyin := [sint]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "i.322"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var := {| vtype := sint
                                ; vname := "c.323"  |}
                    ; v_info := dummy_var_info |})
                AT_inline (sint)
                ((Pif (sint)
                    (Papp2 (Oeq Op_int)
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "i.322"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})
                       (Pconst (Zpos (xH))))
                    (Pconst (Zpos (xH)))
                    (Pif (sint)
                       (Papp2 (Oeq Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.322"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xO xH))))
                       (Pconst (Zpos (xO xH)))
                       (Pif (sint)
                          (Papp2 (Oeq Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.322"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))
                          (Pconst (Zpos (xO (xO xH))))
                          (Pif (sint)
                             (Papp2 (Oeq Op_int)
                                (Pvar
                                   {| gv := {| v_var :=
                                                 {| vtype := sint
                                                  ; vname := "i.322"  |}
                                             ; v_info := dummy_var_info |} ; gs := Slocal |})
                                (Pconst (Zpos (xO (xO xH)))))
                             (Pconst (Zpos (xO (xO (xO xH)))))
                             (Pif (sint)
                                (Papp2 (Oeq Op_int)
                                   (Pvar
                                      {| gv := {| v_var :=
                                                    {| vtype := sint
                                                     ; vname := "i.322"  |}
                                                ; v_info := dummy_var_info |} ; gs := Slocal |})
                                   (Pconst (Zpos (xI (xO xH)))))
                                (Pconst (Zpos (xO (xO (xO (xO xH))))))
                                (Pif (sint)
                                   (Papp2 (Oeq Op_int)
                                      (Pvar
                                         {| gv := {| v_var :=
                                                       {| vtype := sint
                                                        ; vname := "i.322"  |}
                                                   ; v_info := dummy_var_info |} ; gs := Slocal |})
                                      (Pconst (Zpos (xO (xI xH)))))
                                   (Pconst (Zpos (xO (xO (xO (xO (xO xH)))))))
                                   (Pif (sint)
                                      (Papp2 (Oeq Op_int)
                                         (Pvar
                                            {| gv := {| v_var :=
                                                          {| vtype := sint
                                                           ; vname :=
                                                               "i.322"  |}
                                                      ; v_info :=
                                                          dummy_var_info |} ; gs := Slocal |})
                                         (Pconst (Zpos (xI (xI xH)))))
                                      (Pconst
                                         (Zpos (xO (xO (xO (xO (xO (xO xH))))))))
                                      (Pif (sint)
                                         (Papp2 (Oeq Op_int)
                                            (Pvar
                                               {| gv := {| v_var :=
                                                             {| vtype := sint
                                                              ; vname :=
                                                                  "i.322"  |}
                                                         ; v_info :=
                                                             dummy_var_info |} ; gs := Slocal |})
                                            (Pconst (Zpos (xO (xO (xO xH))))))
                                         (Pconst
                                            (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))))
                                         (Pif (sint)
                                            (Papp2 (Oeq Op_int)
                                               (Pvar
                                                  {| gv := {| v_var :=
                                                                {| vtype :=
                                                                    sint
                                                                 ; vname :=
                                                                    "i.322"  |}
                                                            ; v_info :=
                                                                dummy_var_info |} ; gs := Slocal |})
                                               (Pconst
                                                  (Zpos (xI (xO (xO xH))))))
                                            (Pconst
                                               (Zpos (xI (xI (xO (xI xH))))))
                                            (Pconst
                                               (Zpos (xO (xI (xI (xO (xI xH)))))))))))))))))) ]
      ; f_tyout := [sint]
      ; f_res :=
          [{| v_var := {| vtype := sint
                        ; vname := "c.323"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* key_combine *) xO (xI (xI (xO xH))),
     {| f_info := xI (xI (xI (xO xH)))
      ; f_tyin := [(sword U128); (sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "rkey.319"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "temp1.320"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "temp2.321"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp1.320"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep
                (Oasm (* VPSHUFD_128 *) (BaseOp (None, (VPSHUFD U128))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "temp1.320"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (PappN (Opack U8 PE2)
                     [(Pconst (Zpos (xI xH))); (Pconst (Zpos (xI xH)));
                       (Pconst (Zpos (xI xH))); (Pconst (Zpos (xI xH)))])]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp2.321"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep
                (Oasm (* VSHUFPS_128 *) (BaseOp (None, (VSHUFPS U128))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "temp2.321"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "rkey.319"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (PappN (Opack U8 PE2)
                     [(Pconst (Z0)); (Pconst (Zpos (xH))); (Pconst (Z0));
                       (Pconst (Z0))])]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "rkey.319"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Papp2 (Olxor U128)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "rkey.319"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "temp2.321"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |}))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp2.321"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep
                (Oasm (* VSHUFPS_128 *) (BaseOp (None, (VSHUFPS U128))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "temp2.321"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "rkey.319"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (PappN (Opack U8 PE2)
                     [(Pconst (Zpos (xO xH))); (Pconst (Z0));
                       (Pconst (Zpos (xI xH))); (Pconst (Z0))])]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "rkey.319"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Papp2 (Olxor U128)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "rkey.319"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "temp2.321"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |}))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "rkey.319"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Papp2 (Olxor U128)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "rkey.319"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "temp1.320"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U128); (sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "rkey.319"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "temp2.321"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* key_expand *) xO (xI (xO (xO xH))),
     {| f_info := xI (xO (xI (xO xH)))
      ; f_tyin := [sint; (sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "rcon.315"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "rkey.316"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "temp2.317"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp1.318"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep
                (Oasm (* VAESKEYGENASSIST *)
                   (BaseOp (None, VAESKEYGENASSIST)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "rkey.316"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Papp1 (Oword_of_int U8)
                     (Pvar
                        {| gv := {| v_var :=
                                      {| vtype := sint
                                       ; vname := "rcon.315"  |}
                                  ; v_info := dummy_var_info |} ; gs := Slocal |}))]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "rkey.316"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U128)
                          ; vname := "temp2.317"  |}
                     ; v_info := dummy_var_info |}]
                (xO (xI (xI (xO xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "rkey.316"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "temp1.318"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "temp2.317"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U128); (sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "rkey.316"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "temp2.317"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* keys_expand *) xO (xO (xI xH)),
     {| f_info := xO (xO (xI (xO xH)))
      ; f_tyin := [(sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.310"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U128
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                         ; vname := "rkeys.311"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Z0)))
                AT_none ((sword U128))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.310"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp2.312"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* set0_128 *) (ExtOp (Oset0 U128))) []);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "round.313"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))),
                  (Pconst (Zpos (xI (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := sint
                              ; vname := "rcon.314"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xI (xO (xO xH))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "round.313"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sword U128)
                               ; vname := "key.310"  |}
                          ; v_info := dummy_var_info |};
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U128)
                                ; vname := "temp2.312"  |}
                           ; v_info := dummy_var_info |}]
                      (xO (xI (xO (xO xH))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "rcon.314"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U128)
                                          ; vname := "key.310"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U128)
                                          ; vname := "temp2.312"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U128
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                               ; vname := "rkeys.311"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "round.313"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U128))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U128)
                                         ; vname := "key.310"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                 ; vname := "rkeys.311"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* keys_expand_inv *) xI (xO (xO xH)),
     {| f_info := xI (xO (xO (xO xH)))
      ; f_tyin := [(sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.305"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U128
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                         ; vname := "rkeys.306"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Z0)))
                AT_none ((sword U128))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.305"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "temp2.307"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* set0_128 *) (ExtOp (Oset0 U128))) []);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "round.308"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))),
                  (Pconst (Zpos (xI (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := sint
                              ; vname := "rcon.309"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xI (xO (xO xH))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "round.308"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sword U128)
                               ; vname := "key.305"  |}
                          ; v_info := dummy_var_info |};
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U128)
                                ; vname := "temp2.307"  |}
                           ; v_info := dummy_var_info |}]
                      (xO (xI (xO (xO xH))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "rcon.309"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U128)
                                          ; vname := "key.305"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U128)
                                          ; vname := "temp2.307"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cif
                      (Papp2 (Oneq Op_int)
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "round.308"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Pconst (Zpos (xO (xI (xO xH))))))
                      [MkI InstrInfo.witness
                        (Copn
                           [Laset AAscale U128
                              {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                    ; vname := "rkeys.306"  |}
                               ; v_info := dummy_var_info |}
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "round.308"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})]
                           AT_keep
                           (Oasm (* AESIMC *) (BaseOp (None, AESIMC)))
                           [(Pvar
                               {| gv := {| v_var :=
                                             {| vtype := (sword U128)
                                              ; vname := "key.305"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})])]
                      [MkI InstrInfo.witness
                        (Cassgn
                           (Laset AAscale U128
                              {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                    ; vname := "rkeys.306"  |}
                               ; v_info := dummy_var_info |}
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "round.308"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |}))
                           AT_none ((sword U128))
                           ((Pvar
                               {| gv := {| v_var :=
                                             {| vtype := (sword U128)
                                              ; vname := "key.305"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})))])]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                 ; vname := "rkeys.306"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* aes_rounds *) xI (xI (xO xH)),
     {| f_info := xO (xO (xO (xO xH)))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xI (xI (xO xH)))))))); (sword U128)]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                 ; vname := "rkeys.301"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.302"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.303"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "in.302"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.303"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Papp2 (Olxor U128)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "state.303"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pget AAscale U128
                       {| gv := {| v_var :=
                                     {| vtype :=
                                          (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                      ; vname := "rkeys.301"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |}
                       (Pconst (Z0))))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "round.304"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))),
                  (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Copn
                     [Lvar
                        {| v_var :=
                             {| vtype := (sword U128)
                              ; vname := "state.303"  |}
                         ; v_info := dummy_var_info |}]
                     AT_keep (Oasm (* AESENC *) (BaseOp (None, AESENC)))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := (sword U128)
                                        ; vname := "state.303"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pget AAscale U128
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                         ; vname := "rkeys.301"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "round.304"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))])]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.303"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* AESENCLAST *) (BaseOp (None, AESENCLAST)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "state.303"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pget AAscale U128
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                    ; vname := "rkeys.301"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}
                     (Pconst (Zpos (xO (xI (xO xH))))))]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "state.303"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* AddRoundKey *) xO (xI (xI xH)),
     {| f_info := xI (xI (xI xH))
      ; f_tyin := [(sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "state.299"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "rk.300"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.299"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Papp2 (Olxor U128)
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "state.299"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U128)
                                      ; vname := "rk.300"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "state.299"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* invaes_rounds *) xO (xO (xO xH)),
     {| f_info := xI (xO (xI xH))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xI (xI (xO xH)))))))); (sword U128)]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                 ; vname := "rkeys.294"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.295"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.296"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "in.295"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "rk.297"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U128))
                ((Pget AAscale U128
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                   ; vname := "rkeys.294"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Zpos (xO (xI (xO xH))))))));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.296"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "state.296"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "rk.297"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "round.298"  |}
                  ; v_info := dummy_var_info |})
                ((DownTo, (Pconst (Z0))), (Pconst (Zpos (xI (xO (xO xH))))))
                [MkI InstrInfo.witness
                  (Copn
                     [Lvar
                        {| v_var :=
                             {| vtype := (sword U128)
                              ; vname := "state.296"  |}
                         ; v_info := dummy_var_info |}]
                     AT_keep (Oasm (* AESDEC *) (BaseOp (None, AESDEC)))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := (sword U128)
                                        ; vname := "state.296"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pget AAscale U128
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                         ; vname := "rkeys.294"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "round.298"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))])]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "state.296"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* AESDECLAST *) (BaseOp (None, AESDECLAST)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "state.296"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pget AAscale U128
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                    ; vname := "rkeys.294"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}
                     (Pconst (Z0)))]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "state.296"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* aes *) xO (xI xH),
     {| f_info := xO (xI (xO xH))
      ; f_tyin := [(sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.290"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.291"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                         ; vname := "rkeys.293"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO (xI xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.290"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "out.292"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                   ; vname := "rkeys.293"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "in.291"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "out.292"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* invaes *) xI xH,
     {| f_info := xI (xI xH)
      ; f_tyin := [(sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.286"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.287"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                         ; vname := "rkeys.289"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.286"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "out.288"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO (xO xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI (xO xH))))))))
                                   ; vname := "rkeys.289"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "in.287"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "out.288"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* aes_jazz *) xO (xO xH),
     {| f_info := xI (xO xH)
      ; f_tyin := [(sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.283"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.284"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "out.285"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.283"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "in.284"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "out.285"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* invaes_jazz *) xH,
     {| f_info := xO xH
      ; f_tyin := [(sword U128); (sword U128)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "key.280"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U128)
                         ; vname := "in.281"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U128)
                         ; vname := "out.282"  |}
                    ; v_info := dummy_var_info |}]
                (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U128)
                                   ; vname := "key.280"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U128)
                                    ; vname := "in.281"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U128)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U128)
                        ; vname := "out.282"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.
Defined.

(* use zify to use lia in a goal with ssr integers/naturals *)
(* install via opam: coq-mathcomp-zify *)
From mathcomp Require Import zify.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import micromega.Lia.
From mathcomp.word Require Import word.
From mathcomp.word Require Import ssrZ.
From JasminSSProve Require Import jasmin_utils.
Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

Require Import MSetGenTree.

Notation RCON := (xI (xI (xO (xO xH)))).
Notation KEY_COMBINE := (xO (xI (xI (xO xH)))).
Notation KEY_EXPAND := (xO (xI (xO (xO xH)))).
Notation KEYS_EXPAND := (xO (xO (xI xH))).

Infix "^" := wxor.
Definition ws_def : seq Z := [::].

Definition get_tr := get_translated_fun ssprove_jasmin_prog.

Definition pdisj (P : precond) (s_id : p_id) :=
  forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') ->  (P ((set_heap h1 l a), h2) <-> P (h1, h2)).

Ltac solve_in :=
  repeat match goal with
    | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
    | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
    end.

Fixpoint list_to_chtuple (l : list typed_chElement) : lchtuple [seq t.π1 | t <- l] :=
  match l as l0
  return lchtuple [seq t.π1 | t <- l0]
  with
  | [] => tt
  | tc' :: l' =>
    let rec := @list_to_chtuple l' in
    match l' as l'0
          return
          lchtuple [seq t.π1 | t <- l'0] ->
          lchtuple [seq t.π1 | t <- (tc'::l'0)]
    with
    | [] => fun _ => tc'.π2
    | tc'' :: l'' => fun rec => (tc'.π2, rec)
    end rec
  end.

Notation trp := (translate_prog' ssprove_jasmin_prog).1.
Notation trc := (fun fn i => translate_call ssprove_jasmin_prog fn trp i).

(* I use trc to be able to reuse statements about the function inside other functions where theyll appear as translate_calls (and not get_translated_funs).
     Furthermore, I think this is necessary to assure that all calls gets the complete list of translated functions.
     Otherwise result might depend on which buffer of translated functions gets passed to the call.
     In this construction we always use all of them, opposed to get_translated_fun which just uses the necessary ones (I believe).
 *)

Notation JRCON i j := (trc RCON i [('int ; j)]).
(* Notation JRCON  (j : Z) := (get_tr RCON i [('int ; j)]). *)

Notation JKEY_COMBINE i rkey temp1 temp2 := (trc KEY_COMBINE i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]).
(* Notation JKEY_COMBINE rkey temp1 temp2 := (get_tr KEY_COMBINE i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]). *)

Notation JKEY_EXPAND i rcon rkey temp2 := (trc KEY_EXPAND i [ ('int ; rcon) ; ('word U128 ; rkey) ; ('word U128 ; temp2) ]).
(* Notation JKEY_EXPAND rcon rkey temp2 := (get_tr KEY_EXPAND i [ ('int ; rcon) ; ('word U128 ; rkey) ; ('word U128 ; temp2) ]). *)

Notation JKEYS_EXPAND i rkey := (trc KEYS_EXPAND i [('word U128 ; rkey)]).
(* Notation JKEYS_EXPAND rkey := (get_tr KEYS_EXPAND i [('word U128 ; rkey)]). *)

Definition rcon (i : Z) : Z := nth 54%Z [:: 1; 2; 4; 8; 16; 32; 64; 128; 27; 54]%Z ((Z.to_nat i) - 1).

Definition key_expand (wn1 : u128) (rcon : u8) : 'word U128 :=
  let rcon := zero_extend U32 rcon (* W4u8 *) (* U32 4 *) (* [tuple rcon ; 0%R; 0%R; 0%R] *) (* [toword rcon; 0%Z; 0%Z; 0%Z] *) in
  let w0 := subword 0 U32 wn1 in
  let w1 := subword (1 * U32) U32 wn1 in
  let w2 := subword (2 * U32) U32 wn1 in
  let w3 := subword (3 * U32) U32 wn1 in
  let tmp := w3 in
  let tmp := substitute (wror tmp 1) ^ rcon in
  let w4 := w0 ^ tmp in
  let w5 := w1 ^ w4 in
  let w6 := w2 ^ w5 in
  let w7 := w3 ^ w6 in
  wcat [tuple w4; w5; w6; w7].

Lemma rcon_correct id0 pre i :
  (pdisj pre id0) ->
  (1 <= i < 10)%Z ->
  ⊢ ⦃ fun '(s0, s1) => pre (s0, s1) ⦄ JRCON id0 i
    ≈ ret ([('int ; rcon i)] : tchlist)
    ⦃ fun '(v0, s0) '(v1, s1) => pre (s0, s1) /\ v0 = v1 /\ v1 = ([('int ; rcon i)] : tchlist) ⦄.
Proof.
  unfold  get_tr, get_translated_fun.
  intros Hpdisj H.
  simpl_fun.
  repeat setjvars.
  repeat match goal with
         | |- context[(?a =? ?b)%Z] => let E := fresh in destruct (a =? b)%Z eqn:E; [rewrite ?Z.eqb_eq in E; subst|]
         (* | |- _ => eapply r_put_lhs with (pre := fun _ => True); ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K; eapply r_ret; easy *)
         | |- _ => simpl; ssprove_contract_put_get_lhs; rewrite !coerce_to_choice_type_K
         end.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros. unfold set_lhs in *.
      destruct H0 as [s0 []].
      exists (set_heap s0 c 1%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros; split.
      * destruct H0 as [s0 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros. unfold set_lhs in *.
      destruct H1 as [s0 []].
      exists (set_heap s0 c 2%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros; split.
      * destruct H1 as [s0 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 4%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 8%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 16%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 32%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 64%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 128%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - simpl. eapply r_put_lhs.
    ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K.
    eapply r_restore_lhs.
    + intros s0 s1 Hheap. unfold set_lhs in *.
      destruct Hheap as [s2 []].
      exists (set_heap s2 c 27%Z). subst. split.
      * eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * rewrite set_heap_commut. 1: reflexivity.
        apply injective_translate_var3. auto.
    + eapply r_ret.
      intros s0 s1 Hheap; split.
      * destruct Hheap as [s2 []]. subst.
        eapply Hpdisj. 1-2: reflexivity.
        assumption.
      * split. all: easy.
  - lia.
Qed.

(* copy of the easycrypt functional definition *)
Definition W4u8 : 4.-tuple u8 -> u32 := wcat.
Definition W4u32 : 4.-tuple u32 -> u128 := wcat.

Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.

Notation "m ⊕ k" := (@word.word.wxor _ m k) (at level 20).

Lemma lsr_word0 {ws1} a : @lsr ws1 word0 a = word0.
Proof.
  unfold lsr.
  rewrite Z.shiftr_0_l.
  apply val_inj.
  reflexivity.
Qed.

Lemma subword_word0 {ws1} a ws2 : @subword ws1 a ws2 word0 = word0.
Proof.
  unfold subword.
  rewrite lsr_word0.
  apply val_inj.
  reflexivity.
Qed.

Lemma wpshufd10 : forall w n, wpshufd1 w 0 n = zero_extend U32 w.
Proof.
  unfold wpshufd1.
  intros a n.
  rewrite subword_word0 Z.mul_0_r wshr0.
  change 32%nat with (nat_of_wsize U32).
  apply subword0.
Qed.

(* Lemma wpshufd_1280 : forall a,  wpshufd_128 a 0 = a. *)
(* Proof. *)
(*   intros a. *)
(*   unfold wpshufd_128. *)
(*   rewrite wrepr0. *)
(*   unfold iota, map. *)
(*   rewrite !wpshufd10. *)
(*   simpl. *)
(* Admitted. *)

Lemma wcat_eq ws p a t :
  (forall (i : 'I_p), subword (i * ws) ws a = tnth t i) -> a = wcat t.
Proof.
  intros.
  rewrite -[a]wcat_subwordK.
  apply f_equal. apply eq_from_tnth.
  intros i.
  rewrite -H tnth_map tnth_ord_tuple.
  reflexivity.
Qed.

Definition W4u32_eq : forall a t, (forall (i : 'I_4), subword (i * U32) U32 a = tnth t i) -> a = W4u32 t := wcat_eq U32 4.

Lemma wbit_subword {ws1} i ws2 (w : word ws1) j :
  (ws2 <= ws1)%nat ->
  (j < ws2)%nat ->
  wbit (subword i ws2 w) j = wbit w (i + j)%nat.
Proof.
  intros.
  unfold subword.
  simpl.
  unfold urepr.
  simpl.
  unfold wbit.
  simpl.
  unfold modulus.
  rewrite !two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_low.
  { rewrite Z.mod_pow2_bits_low. 2: lia.
    rewrite Z.shiftr_spec. 2: lia.
    f_equal. lia.
  }
  lia.
Qed.

Lemma subword_xor {n} i ws (a b : n.-word) :
  (* I don't know if the assumption is necessary *)
  (ws <= n)%nat ->
  subword i ws (a ⊕ b) = (subword i ws a) ⊕ (subword i ws b).
Proof.
  intros H.
  apply/eqP/eq_from_wbit.
  intros. rewrite !wbit_subword. 2,3: auto.
  rewrite !wxorE.
  rewrite !wbit_subword. 2-5: auto.
  reflexivity.
Qed.

Local Open Scope Z_scope.

Lemma wrepr_lsr (ws : wsize.wsize) a i :
  (0 <= a < modulus ws)%Z ->
  lsr (wrepr ws a) i = wrepr ws (Z.shiftr a (Z.of_nat i)).
Proof.
  intros H.
  unfold lsr.
  rewrite mkwordK.
  unfold wrepr.
  apply val_inj.
  simpl.
  rewrite [a mod _]Z.mod_small. 2: assumption.
  reflexivity.
Qed.

Lemma modulus_gt0' n : (0 < modulus n)%Z.
Proof.
  apply Z.ltb_lt.
  apply modulus_gt0.
Qed.

(* Lemma wcat_r_bound n (l : seq n.-word) : *)
(*   (0 <= wcat_r l < modulus (size l * n))%Z. *)
(* Proof. *)
(*   induction l. *)
(*   - simpl. *)
(*     split. *)
(*     + reflexivity. *)
(*     + apply Z.ltb_lt. *)
(*       apply modulus_gt0. *)
(*   - simpl. *)
(*     (* IHl implies that the wcat shifted is less than the modulus and then the lor is less than that *) *)
(* Admitted. *)

(* following two lemmas are from fiat crypto, consider importing *)
Lemma mod_pow_same_base_larger a b n m :
  0 <= n <= m -> 0 < b ->
  (a mod (b^n)) mod (b^m) = a mod b^n.
Proof.
  intros.
  pose proof Z.mod_pos_bound a (b^n) ltac:(auto with zarith).
  assert (b^n <= b^m).
  { eapply Z.pow_le_mono_r; lia. }
  apply Z.mod_small. auto with zarith.
Qed.

Lemma mod_pow_same_base_smaller a b n m :
  0 <= m <= n -> 0 < b ->
  (a mod (b^n)) mod (b^m) = a mod b^m.
Proof.
  intros. replace n with (m+(n-m)) by lia.
  rewrite -> Z.pow_add_r, Z.rem_mul_r by auto with zarith.
  rewrite <- Zplus_mod_idemp_r.
  rewrite <- Zmult_mod_idemp_l.
  rewrite Z.mod_same. 2: eapply Z.pow_nonzero ; lia.
  rewrite Z.mul_0_l.
  rewrite Z.mod_0_l. 2: eapply Z.pow_nonzero ; lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod. 2: eapply Z.pow_nonzero ; lia.
  reflexivity.
Qed.

Lemma larger_modulus a n m :
  (n <= m)%nat ->
  (a mod modulus n) mod modulus m = a mod modulus n.
Proof.
  intros H.
  rewrite !modulusZE.
  apply mod_pow_same_base_larger. 2: lia.
  zify. simpl. lia.
Qed.

Lemma smaller_modulus a n m :
  (m <= n)%nat ->
  (a mod modulus n) mod modulus m = a mod modulus m.
Proof.
  intros H.
  rewrite !modulusZE.
  apply mod_pow_same_base_smaller. 2: lia.
  zify. simpl. lia.
Qed.

Lemma nat_of_wsize_m ws : (wsize_size_minus_1 ws).+1 = nat_of_wsize ws.
Proof. destruct ws; reflexivity. Qed.
Lemma modulus_ne0 : forall n, modulus n <> 0.
Proof.
  intros n.
  pose proof modulus_gt0 n.
  zify. lia.
Qed.

Lemma enum0 :
  enum ('I_0) = [].
Proof.
  assert (size (enum 'I_0) = 0%nat).
  { apply size_enum_ord. }
  apply size0nil. assumption.
Qed.

Lemma nth_aux {T} (a : T) l :
  [seq nth a l (val i) | i <- enum 'I_(size l)] = l.
Proof.
  replace [seq nth a l (val i) | i <- enum 'I_(size l)] with [seq nth a l i | i <- [seq val i | i <- enum 'I_(size l)]].
  2: { rewrite -map_comp. reflexivity. }
  rewrite val_enum_ord.
  rewrite map_nth_iota0. 2: lia.
  rewrite take_size. reflexivity.
Qed.

Lemma make_vec_wcat {ws1} (l : seq (word.word ws1)) :
  wcat_r l = wcat [tuple nth word0 l i | i < size l].
Proof.
  unfold wcat.
  simpl.
  rewrite nth_aux.
  reflexivity.
Qed.
Lemma wbit_wrepr (ws : wsize.wsize) a i :
  (i < ws)%nat ->
  wbit (urepr (wrepr ws a)) i = wbit a i.
Proof.
  intros H.
  unfold wbit.
  unfold wrepr.
  unfold urepr.
  simpl. unfold modulus.
  rewrite two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_low.
  2:{ unfold nat_of_wsize in *. lia. }
  reflexivity.
Qed.

Lemma wbit_make_vec {ws1} (ws2 : wsize.wsize) (l : seq (word.word ws1)) i :
  (i < ws2)%nat ->
  wbit (urepr (make_vec ws2 l)) i = wbit (nth word0 l (i %/ ws1)) (i %% ws1).
Proof.
  intros H.
  unfold make_vec.
  rewrite make_vec_wcat.
  rewrite wbit_wrepr. 2: assumption.
  rewrite wcat_wbitE.
  unfold urepr.
  simpl.
  repeat f_equal.
  apply nth_aux.
Qed.

Lemma divn_aux j i n :
  (j < n)%nat ->
  (n <= j %% n + i %% n)%nat = false ->
  (j + i) %/ n = i %/ n.
Proof.
  intros H1 H2.
  rewrite divnD. 2: lia.
  rewrite H2.
  rewrite divn_small. all: lia.
Qed.

Lemma modn_aux j i n :
  (j < n)%nat ->
  (n <= j %% n + i %% n)%nat = false ->
  (j + i) %% n = (j + i %% n)%nat.
Proof.
  intros H1 H2.
  rewrite modnD. 2: lia.
  rewrite H2.
  rewrite modn_small. all: lia.
Qed.

Lemma subword_make_vec1 {ws1} i ws2 (ws3 : wsize.wsize) (l : seq (word.word ws1)) :
  (* i + ws2 does 'reach across' a single word in the list *)
  (ws2 <= ws1)%nat ->
  (i + ws2 <= ws3)%nat ->
  (ws1 <= (ws2 - 1) %% ws1 + i %% ws1)%nat = false ->
  (* i think this condition is equivalent, but the others fit with other lemmas *)
  (* ((i + ws2 - 1) / ws1)%nat = (i / ws1)%nat -> *)
  subword i ws2 (make_vec ws3 l) = subword (i %% ws1) ws2 (nth word0 l (i %/ ws1)%nat).
Proof.
  intros H1 H2 H3.
  rewrite !subwordE.
  f_equal.
  apply eq_mktuple.
  intros j.
  destruct j. simpl.
  rewrite wbit_make_vec. 2: lia.
  f_equal.
  - f_equal. f_equal.
    apply divn_aux. 1:{ simpl. lia. }
    rewrite modn_small in H3. 2: lia.
    rewrite modn_small. 2: lia.
    lia.
  - apply modn_aux. 1: lia.
    rewrite modn_small in H3. 2: lia.
    rewrite modn_small. 1: lia.
    lia.
Qed.

Lemma make_vec_ws ws (l : seq (word.word ws)) :
  make_vec ws l = nth word0 l 0.
Proof.
  apply/eqP.
  apply/eq_from_wbit.
  intros [i].
  rewrite wbit_make_vec.
  simpl.
  rewrite divn_small.
  rewrite modn_small.
  reflexivity.
  unfold nat_of_wsize. lia.
  unfold nat_of_wsize. lia.
  unfold nat_of_wsize. simpl. lia.
Qed.

Lemma subword_0_128 (l : seq u128) :
  subword 0 0 (make_vec U128 l) = subword 0 0 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_0_32_128 (l : seq u128) :
  subword 0 U32 (make_vec U128 l) = subword 0 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_1_32_128 (l : seq u128) :
  subword 1 U32 (make_vec U128 l) = subword 1 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_2_32_128 (l : seq u128) :
  subword 2 U32 (make_vec U128 l) = subword 2 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.

Lemma subword_3_32_128 (l : seq u128) :
  subword 3 U32 (make_vec U128 l) = subword 3 U32 (nth word0 l 0).
Proof.
  by rewrite make_vec_ws.
Qed.


Lemma subword_make_vec {ws1} i (ws2 : wsize.wsize) (l : seq (word.word ws1)) :
  (ws1 <= ws2)%nat ->
  ((i + 1) * ws1 < ws2)%nat ->
  subword (i * ws1) ws1 (make_vec ws2 l) = nth word0 l i.
Proof.
  intros H1 H2.
  apply/eqP.
  apply /eq_from_wbit.
  intros [i0]. simpl.
  rewrite wbit_subword.
  rewrite wbit_make_vec.
  rewrite addnC.
  rewrite divn_aux.
  rewrite mulnK.
  rewrite modn_aux.
  rewrite modnMl.
  rewrite addn0.
  reflexivity. all: try lia.
  rewrite modnMl. lia.
  rewrite modnMl. lia.
  unfold nat_of_ord in *. unfold nat_of_wsize in *. lia.
Qed.

Lemma subword_u {ws} (w : word.word ws) : subword 0 ws w = w.
Proof. by rewrite subword0 zero_extend_u. Qed.

Lemma nth_map2 {A B C} (a : A) (b : B) (c : C) la lb f n :
  (n < Nat.min (size la) (size lb))%nat -> nth c (map2 f la lb) n = f (nth a la n) (nth b lb n).
Proof.
  revert la lb.
  induction n; intros.
  - destruct la.
    + simpl in H; zify; lia.
    + destruct lb.
      * simpl in H; zify; lia.
      * reflexivity.
  - destruct la.
    + simpl in H; zify; lia.
    + destruct lb.
      * simpl in H; zify; lia.
      * simpl.
        eapply IHn.
        simpl in H.
        zify; lia.
Qed.

Lemma subword_make_vec_32_0_32_128 (l : seq u32) : subword 0 U32 (make_vec U128 l) = nth word0 l 0.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_1_32_128 (l : seq u32) : subword U32 U32 (make_vec U128 l) = nth word0 l 1.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_2_32_128 (l : seq u32) : subword (2 * U32) U32 (make_vec U128 l) = nth word0 l 2.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

Lemma subword_make_vec_32_3_32_128 (l : seq u32) : subword (3 * U32) U32 (make_vec U128 l) = nth word0 l 3.
Proof.
  rewrite subword_make_vec1.
  rewrite subword_u.
  all: auto.
Qed.

(* Lemma subword_wshufps_0_32_128 o s1 s2 : subword 0 U32 (wshufps_128 o s1 s2) = wpshufd1 s1 o 0. *)
(* Proof. *)
(*   unfold wshufps_128. *)
(*   rewrite subword_make_vec1. *)
(*   rewrite subword_u. *)
(*   reflexivity. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma subword_wshufps_128 o s1 s2 : subword 0 U32 (wshufps_128 o s1 s2) = *)
(*                               wpshufd1 s1 o 0. *)
(* Proof. *)
(*   unfold wshufps_128. *)
(*   rewrite subword_make_vec1. *)
(*   rewrite subword_u. *)
(*   reflexivity. *)
(*   reflexivity. *)
(* Qed.   *)

Arguments nat_of_wsize : simpl never.
Arguments wsize_size_minus_1 : simpl never.

Lemma make_vec_single {ws1} ws2 (a : word.word ws1) :
  make_vec ws2 [:: a] = zero_extend ws2 a.
Proof.
  unfold make_vec. cbn -[Z.of_nat].
  by rewrite Z.shiftl_0_l Z.lor_0_r.
Qed.

Lemma wshr_word0 {ws} i : @wshr ws 0 i = word0.
Proof.
  unfold wshr.
  by rewrite lsr_word0.
Qed.

Lemma wxor_0_r {n} (a : n.-word) : wxor a word0 = a.
Proof.
  unfold wxor.
  apply val_inj. simpl.
  by rewrite Z.lxor_0_r.
Qed.

Lemma wxor_0_l {n} (a : n.-word) : wxor word0 a = a.
Proof.
  apply val_inj.
  reflexivity.
Qed.

(* Lemma lsr_add_r {n} (w : n.-word) i j : lsr (lsr w i) j = lsr w (i + j). *)
(* Proof. *)
(*   unfold lsr. *)
(*   rewrite urepr_word; simpl. *)
(*   apply val_inj. *)
(*   simpl. *)

(* from fiat crypto, but proof is more involved *)
Lemma mod_pull_div a b c
  : 0 <= c -> (a / b) mod c = a mod (c * b) / b.
Admitted.

Lemma shiftr_shiftr_mod w ws1 ws2 i j :
  (ws2 + j <= ws1)%nat ->
  Z.shiftr (Z.shiftr w (Z.of_nat i) mod modulus ws1) (Z.of_nat j) mod modulus ws2 =
    Z.shiftr w (Z.of_nat (i + j)) mod modulus ws2.
Proof.
  intros H.
  rewrite modulusZE.
  simpl.
  rewrite !modulusZE.
  rewrite !Z.shiftr_div_pow2.
  rewrite !mod_pull_div.
  simpl.
  rewrite -!Z.pow_add_r.
  rewrite mod_pow_same_base_smaller.
  rewrite Z.div_div.
  rewrite -Z.pow_add_r.
  rewrite Nat2Z.inj_add.
  f_equal. f_equal. f_equal.
  all: try lia.
Qed.

Lemma subword_wshr {ws1} i j ws2 (w : ws1.-word) :
  (ws2 + i <= ws1)%nat ->
  subword i ws2 (lsr w j) = subword (j + i) ws2 w.
Proof.
  intros H.
  unfold subword; simpl.
  apply val_inj; simpl.
  rewrite urepr_word.
  unfold lsr.
  simpl.
  rewrite urepr_word.
  rewrite !smaller_modulus.
  rewrite shiftr_shiftr_mod.
  reflexivity.
  all: lia.
Qed.

Lemma wxor_involutive {n} : forall k : word n, k ⊕ k = word0.
Proof.
  intros k.
  apply/eqP/eq_from_wbit=> i.
  rewrite !wxorE addbb.
  unfold wbit.
  rewrite Z.testbit_0_l.
  reflexivity.
Qed.

(* Lemma wxorC : ∀ m k : word, (m ⊕ k) = (k ⊕ m). *)
(* Proof. *)
(*   intros m k. *)
(*   apply/eqP/eq_from_wbit=> i. *)
(*   by rewrite !wxorE addbC. *)
(* Qed. *)

Lemma wxorA {n} : forall m k l : word n, ((m ⊕ k) ⊕ l) = (m ⊕ (k ⊕ l)).
Proof.
  intros m k l.
  apply/eqP/eq_from_wbit=> i.
  by rewrite !wxorE addbA.
Qed.

Lemma wror_substitute {n} (w : word.word n) k : wror (substitute w) k = substitute (wror w k).
Proof.
  (* I would like to case on w, but not sure how to do this most efficiently? *)
Admitted.

Notation pr T l n := (coerce_to_choice_type T (nth (T ; chCanonical T) l n).π2).
Lemma wxorC {n} (a b : word n) : wxor a b = wxor b a.
Proof.
  apply/eqP/eq_from_wbit=> i. rewrite !wxorE.
  rewrite addbC. reflexivity.
Qed.

Lemma wreprI ws (a : word.word ws) : wrepr ws (toword a) = a.

Proof.
  apply val_inj. simpl. destruct a. rewrite Z.mod_small. reflexivity.
  simpl in *. lia.
Qed.

Lemma key_expand_aux rcon rkey temp2 rcon_ :
  toword rcon_ = rcon ->
  subword 0 U32 temp2 = word0 ->
  ((rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
     (rkey ⊕ lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)) ⊕ wpshufd_128 (wAESKEYGENASSIST rkey (wrepr U8 rcon)) (wunsigned (wpack U8 2 [3; 3; 3; 3])) =
    key_expand rkey rcon_.
Proof.
  intros.
  subst.
  unfold key_expand.
  apply W4u32_eq.
  intros [[ | [ | [ | [ | i]]]] j]; simpl; unfold tnth; simpl.
  - rewrite !subword_xor.
    rewrite mul0n.
    unfold lift2_vec.
    rewrite !subword_0_32_128.
    simpl.
    rewrite mul0n.
    rewrite !make_vec_ws.
    rewrite !subword_u.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpack.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !wshr0.
    rewrite !subword_make_vec_32_0_32_128.
    simpl.
    unfold wAESKEYGENASSIST.
    rewrite subword_wshr.
    rewrite subword_make_vec_32_3_32_128.
    simpl.
    rewrite !wxorA.
    f_equal.
    unfold wpshufd1.
    simpl.
    rewrite wshr0.
    rewrite -wxorA.
    rewrite wxor_involutive.

    rewrite wxor_0_l.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
    all: auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_1_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    rewrite subword_wshr.
    simpl.
    rewrite addn0.
    rewrite !wxorA.
    f_equal.
    rewrite H0.
    rewrite wxor_0_l.
    f_equal.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
    all: try auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_2_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_0_32_128.
    unfold wpshufd1.
    rewrite subword_wshr.
    simpl.
    rewrite addn0.
    rewrite !wxorA.
    f_equal.
    rewrite H0.
    rewrite wxor_0_l.
    f_equal.
    f_equal.
    rewrite wror_substitute.
    unfold word.wxor.
    f_equal.
    rewrite wreprI.
    reflexivity.
    all: try auto.
  - simpl.
    unfold lift2_vec.
    rewrite !make_vec_ws.
    rewrite mul1n.
    unfold wpack.
    simpl.
    rewrite mul0n.
    rewrite !subword_u.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    unfold wpshufd1.
    simpl.
    rewrite !subword_wshr.
    rewrite !addn0.
    rewrite !subword_xor.
    rewrite !subword_make_vec_32_3_32_128.
    simpl.
    rewrite !subword_make_vec_32_2_32_128.
    unfold wpshufd1.
    rewrite subword_wshr.
    simpl.
    rewrite !wxorA.
    f_equal.
    rewrite wxorC.
    rewrite !wxorA.
    f_equal.
    rewrite subword_wshr.
    rewrite addn0.
    f_equal.
    rewrite wror_substitute.
    rewrite wxorC.
    rewrite wxorA.
    f_equal.
    f_equal.
    rewrite wreprI.
    reflexivity.
    all: auto.
  - lia.
Qed.

Lemma key_expand_aux2 rkey temp2 :
  subword 0 U32 temp2 = word0 ->
  subword 0 U32
    (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 3; 0; 2])) U128 (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey)
       (word.wxor rkey (lift2_vec U128 (wshufps_128 (wpack U8 2 [0; 0; 1; 0])) U128 temp2 rkey))) = word0.
Proof.
  intros.
  rewrite subword_0_32_128. simpl.
  rewrite subword_make_vec_32_0_32_128. simpl.
  unfold wpshufd1. simpl.
  rewrite subword_wshr. simpl.
  rewrite addn0.
  rewrite subword_u.
  rewrite subword_0_32_128. simpl.
  rewrite subword_make_vec_32_0_32_128. simpl.
  rewrite subword_u.
  unfold wpshufd1. simpl.
  rewrite subword_wshr.
  rewrite add0n.
  assumption.
  auto. auto.
Qed.


Ltac pdisj_apply h :=
  lazymatch goal with
  | |- ?pre (set_heap _ _ _, _) =>
      eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
  | |- _ => try assumption
  end.

Lemma key_expandP pre id0 rcon rkey temp2 rcon_ :
  pdisj pre (JKEY_EXPAND_vars id0) →
  toword rcon_ = rcon →
  subword 0 U32 temp2 = word0 →
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
    JKEY_EXPAND id0 rcon rkey temp2
    ≈ ret tt
  ⦃ λ '(v0, s0) '(v1, s1),
    pre (s0, s1) ∧
    ∃ o1 o2,
      v0 = [ ('word U128 ; o1) ; ('word U128 ; o2) ] ∧
      o1 = key_expand rkey rcon_ ∧
      subword 0 U32 o2 = word0
  ⦄.
Proof.
  intros disj Hrcon Htemp2.
  tvars disj.
  simpl_fun.
  repeat setjvars.
  repeat clear_get.

  unfold sopn_sem.
  unfold tr_app_sopn_tuple.
  unfold tr_app_sopn_single.

  simpl.

  rewrite !zero_extend_u.
  rewrite !coerce_to_choice_type_K.

  repeat eapply r_put_lhs.
  eapply r_ret.
  intros s0 s1 Hpre.
  repeat
    match goal with
    | [ H : set_lhs _ _ _ _ |- _ ] =>
      let sn := fresh in
      let Hsn := fresh in
      destruct H as [sn [Hsn]]
    end.
  split.
  (* Goal: prove pre is preserved by using disj; this should be automated *)
  - subst.
    pdisj_apply disj.
    (* TODO: Fix how the variable set is computed: It needs to include the called functions variables as well *)
    all: admit.
  - eexists _, _. intuition eauto.
    (* this is key_expand_correct1 *)
    + apply key_expand_aux. all: assumption.
    + apply key_expand_aux2. assumption.
Admitted.

Definition getmd {T S} m d i := match @getm T S m i with Some a => a | _ => d end.

Local Open Scope Z_scope.

Fixpoint for_list (c : Z → raw_code 'unit) (vs : seq Z) : raw_code 'unit :=
  match vs with
  | [::] => ret tt
  | v :: vs => c v ;; for_list c vs
  end.

Definition for_loop' (c : Z -> raw_code 'unit) lo hi := for_list c (wrange UpTo lo hi).

Definition to_arr ws len (a : 'array) :=
  mkfmapf (fun i => chArray_get ws a i (wsize_size ws)) (ziota 0 len).

Notation " 'arr ws " := (chMap 'int ('word ws)) (at level 2) : package_scope.

Definition rkeys : Location := ( 'arr U128 ; 0%nat ).

Definition keyExpansion (key : u128) : raw_code ('arr U128) :=
  #put rkeys := @emptym Z_ordType u128 ;;
                rkeys0 ← get rkeys ;;
                #put rkeys := setm rkeys0 0 key ;;
                              for_loop' (fun i => rkeys0 ← get rkeys ;; #put rkeys := setm rkeys0 i (key_expand (zero_extend _ (getmd rkeys0 word0 (i - 1))) (wrepr U8 (rcon i))) ;; ret tt) 1 11 ;;
                              rkeys0 ← get rkeys ;;
                              ret rkeys0.

Lemma iota_aux {A} k c n (f : nat -> A) g :
  (forall a, a \in (iota k n) -> f a = g (a + c)%nat) ->
  [seq f i | i <- iota k n] = [seq g i | i <- iota (k + c) n].
Proof.
  revert k c.
  induction n.
  - reflexivity.
  - intros k c ex.
    simpl. rewrite -addSn.
    rewrite <- IHn.
    f_equal.
    apply ex.
    simpl.
    rewrite in_cons.

    apply/orP. left. apply/eqP. reflexivity.
    intros a ain. apply ex.
    simpl. rewrite in_cons.
    apply/orP. right. assumption.
Qed.

Lemma for_loop'_rule I c₀ c₁ lo hi :
  lo <= hi ->
  (∀ i, (lo <= i < hi)%Z -> ⊢ ⦃ λ '(s₀, s₁), I i (s₀, s₁) ⦄ c₀ i ≈ c₁ i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀, s₁), I lo (s₀, s₁) ⦄
    for_loop' c₀ lo hi ≈ for_loop' c₁ lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros hle h.
  remember (Z.to_nat (hi - lo)).
  revert hle h Heqn. revert lo hi.
  induction n as [| n ih]; intros.
  - simpl.
    assert (hi = lo).
    { zify. lia. }
    unfold for_loop'.
    simpl.
    rewrite -Heqn.
    simpl.
    subst.
    apply r_ret.
    easy.
  - unfold for_loop'.
    simpl. rewrite -Heqn. simpl. rewrite Z.add_0_r.
    eapply r_bind.
    + eapply h. lia.
    + intros a1 a2.
      replace [seq lo + Z.of_nat i | i <- iota 1 n] with [seq (Z.succ lo) + Z.of_nat i | i <- iota 0 n].
      replace n with (Z.to_nat (hi - Z.succ lo)).
      apply ih.
      * lia.
      * intros i hi2. apply h. lia.
      * lia.
      * lia.
      * replace (iota 1 n) with (iota (0 + 1) n). apply iota_aux.
        intros. lia.
        f_equal.
Qed.

Lemma translate_for_rule I lo hi (v : var_i) m_id s_id (body1 : p_id -> p_id * raw_code 'unit) body2 :
  lo <= hi ->
  (forall i s_id', (lo <= i <  hi) ->
              ⊢ ⦃ λ '(s₀, s₁), set_lhs (translate_var m_id v) (truncate_el (vtype v) (i : chInt)) (I i) (s₀, s₁) ⦄
                let (_, body1') := body1 s_id' in
                body1'
                  ≈ body2 i ⦃ λ '(_, s₀) '(_, s₁), I (Z.succ i) (s₀,s₁) ⦄) →
  ⊢ ⦃ λ '(s₀,s₁), I lo (s₀, s₁)⦄
    translate_for v (wrange UpTo lo hi) m_id body1 s_id
    ≈ for_loop' body2 lo hi
    ⦃ λ '(_,s₀) '(_,s₁), I hi (s₀,s₁) ⦄.
Proof.
  intros Hle ih.
  remember (Z.to_nat (hi - lo)).
  revert Heqn Hle ih. revert n lo hi s_id.
  induction n as [|n ih2]; intros.
  - assert (hi = lo). { zify. lia. }.
    subst.
    unfold translate_for, for_loop'. simpl.
    rewrite -Heqn.
    simpl.
    apply r_ret.
    easy.
  - unfold translate_for, for_loop'.
    unfold wrange.
    rewrite -Heqn.
    simpl.
    specialize (ih lo s_id) as ih''.
    destruct (body1 s_id).
    eapply r_put_lhs.
    eapply r_bind.
    eapply r_transL.
    2: rewrite Z.add_0_r; eapply ih''.
    eapply rreflexivity_rule. lia.
    intros a0 a1.
    replace (iota 1 n) with (iota (0 + 1) n) by f_equal.
    rewrite <- iota_aux with (f := fun i => Z.succ lo + Z.of_nat i).
    fold translate_for.
    replace n with (Z.to_nat (hi - Z.succ lo)) by lia.
    specialize (ih2 (Z.succ lo) hi p ltac:(lia) ltac:(lia)).
    eapply ih2.
    intros i s_id' ile.
    specialize (ih i s_id').
    destruct (body1 s_id'). apply ih. lia.
    intros a ain. lia.
Qed.

Opaque translate_for.
Notation hdtc res := (coerce_to_choice_type ('array) (hd ('word U64 ; chCanonical _) res).π2).
Notation call fn := (translate_call _ fn _).

From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
From Crypt Require Import Prelude Axioms ChoiceAsOrd.

Theorem rpre_hypothesis_rule' :
  ∀ {A₀ A₁ : ord_choiceType} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
    (pre : precond) post,
    (∀ s₀ s₁,
        pre (s₀, s₁) → ⊢ ⦃ λ '(s₀', s₁'), s₀' = s₀ ∧ s₁' = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
    ) →
    ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
Proof.
  intros A₀ A₁ p₀ p₁ pre post h.
  eapply rpre_hypothesis_rule.
  intros s0 s1 H. eapply rpre_weaken_rule.
  eapply h.
  eassumption.
  easy.
Qed.

Lemma wsize_size_aux (ws : wsize.wsize) :
  (ws %/ U8 + ws %% U8) = wsize_size ws.
Proof. destruct ws; reflexivity. Qed.

Lemma encode_aux {ws} (w : word.word ws) :
  LE.encode w = [seq subword ((Z.to_nat i0) * U8) U8 w | i0 <- ziota 0 (wsize_size ws)].
Proof.
  unfold LE.encode.
  unfold split_vec.
  unfold ziota.
  rewrite -wsize_size_aux.
  simpl.
  rewrite Z2Nat.inj_add.
  rewrite !Nat2Z.id.
  rewrite -map_comp.
  unfold comp.
  apply map_ext.
  intros a Ha.
  rewrite Nat2Z.id.
  reflexivity.
  apply Zle_0_nat.
  apply Zle_0_nat.
Qed.

Lemma wsize_size_bits ws:
  wsize_size ws < wsize_bits ws.
Proof.
  unfold wsize_size, wsize_bits.
  destruct ws; simpl; lia.
Qed.

Lemma chArray_get_set_eq ws a i w :
  (* (i * wsize_bits ws < wsize_size ws) -> *)
  chArray_get ws (chArray_set a AAscale i w) i (wsize_size ws) = w.
Proof.
  unfold chArray_get.
  unfold chArray_set.
  rewrite <- LE.decodeK.

  f_equal.
  rewrite encode_aux.
  apply map_ext.
  intros j Hj.
  unfold chArray_get8.
  rewrite chArray_write_get.
  assert ((0 <=? i * wsize_size ws + j - i * mk_scale AAscale ws) && (i * wsize_size ws + j - i * mk_scale AAscale ws <? wsize_size ws)).
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.  lia.
  rewrite H.
  unfold LE.wread8.
  unfold LE.encode.
  unfold split_vec.
  unshelve erewrite nth_map. exact 0%nat.
  simpl.
  rewrite nth_iota.
  simpl.
  f_equal.
  lia.
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)). lia.
  destruct ws; simpl; reflexivity.
  rewrite size_iota.
  simpl. move: Hj=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  replace (ws %/ U8 + ws %% U8)%nat with (Z.to_nat (wsize_size ws)). lia.
  destruct ws; simpl; reflexivity.
Qed.

Lemma chArray_get_set_neq ws a i j (w : 'word ws) :
  i <> j ->
  chArray_get ws (chArray_set a AAscale i w) j (wsize_size ws) = chArray_get ws a j (wsize_size ws).
Proof.
  intros H.
  unfold chArray_get.
  unfold chArray_set.
  f_equal.
  apply map_ext.
  intros a0 Ha0.
  unfold chArray_get8.
  rewrite chArray_write_get.
  assert ((0 <=? j * wsize_size ws + a0 - i * mk_scale AAscale ws) && (j * wsize_size ws + a0 - i * mk_scale AAscale ws <? wsize_size ws) = false).
  simpl. move: Ha0=>/InP. rewrite in_ziota=>/andP [] H1 h2.
  nia.
  rewrite H0.
  reflexivity.
Qed.

Lemma getm_to_arr' ws len a i :
  (len <= i) ->
  to_arr ws len a i = None.
Proof.
  intros. unfold to_arr.
  rewrite mkfmapfE.
Admitted.                  (* figure out a proof that is less stupid than the one for getm_to_arr *)

Lemma getm_to_arr ws len a i :
  (0 <= i < len) ->
  to_arr ws len a i = Some (chArray_get ws a i (wsize_size ws)).
Proof.
  unfold to_arr.
  rewrite mkfmapfE.
  intros H.
  (* this is a stupid proof and should be true by in_ziota, though for some reason the \in's resolve differently (one uses Z_eqType the other Z_ordType) *)
  assert (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota Z0 len)))).
  { assert (0 <= len) by lia. move: H. move: (Z.le_refl 0). replace len with (0 + len) at 1 by (now rewrite Z.add_0_l). generalize 0 at 2 3 4 5.
    change (∀ z : Z, 0 <= z -> z <= i < z + len →
                     (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota z len))))
           ) with ((fun len => ((forall z, 0 <= z -> z <= i < z + len ->
                                           (is_true (@in_mem (Ord.sort Z_ordType) i (@ssrbool.mem (Equality.sort (Ord.eqType Z_ordType)) (seq_predType (Ord.eqType Z_ordType)) (ziota z len))))
                   ))) len).
    apply natlike_ind.
    - intros z Hz Hz2. lia.
    - intros x Hx Ih z Hz Hz2. rewrite ziotaS_cons.
      destruct (Z.eq_dec z i).
      + rewrite in_cons. apply/orP. left. apply/eqP. easy.
      + rewrite in_cons. apply/orP. right. apply Ih. lia. lia.
      + lia.
    - assumption. }
  rewrite H0.
  reflexivity.
Qed.

Lemma to_arr_set_eq ws len a i w :
  (0 <= i < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) i = Some w.
Proof.
  intros H.
  rewrite getm_to_arr.
  rewrite chArray_get_set_eq.
  reflexivity.
  assumption.
Qed.

Lemma to_arr_set_neq' ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = Some (chArray_get ws a j (wsize_size ws)).
Proof.
  intros Hneq Hi.
  rewrite getm_to_arr.
  rewrite chArray_get_set_neq.
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma to_arr_set_neq ws len a i j (w : 'word ws) :
  (i <> j) ->
  (0 <= j < len) ->
  (to_arr ws len (chArray_set a AAscale i w)) j = (to_arr ws len a) j.
Proof.
  intros Hneq Hi.
  rewrite !getm_to_arr.
  rewrite chArray_get_set_neq.
  reflexivity.
  assumption.
  assumption.
  assumption.
Qed.

Lemma keyExpansionE pre id0 rkey :
  (pdisj pre (JKEYS_EXPAND_vars id0)) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    res ← JKEYS_EXPAND id0 rkey ;;
  ret (to_arr U128 11 (hdtc res))
    ≈
    keyExpansion rkey
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ v0 = v1 ⦄.
Proof.
  intros disj.
  (* unfold JKEYS_EXPAND. *)
  unfold call. (* get_tr, get_translated_fun, translate_prog', translate_funs. *)
  Opaque translate_call.
  Opaque wrange.
  simpl.

  simpl_fun.
  repeat setjvars.

  repeat clear_get.
  eapply r_put_lhs.
  eapply r_get_remember_lhs.
  intros v.
  eapply r_put_lhs.
  eapply r_put_lhs.
  unfold keyExpansion.
  eapply r_put_rhs.
  eapply r_get_remember_rhs.
  intros v0.
  Opaque for_loop'.
  eapply r_put_rhs.
  rewrite bind_assoc.

  rewrite bind_assoc.
  eapply r_bind.
  simpl.
  eapply rpre_weaken_rule.
  eapply translate_for_rule with (I := fun i => fun '(h0, h1) => pre (h0, h1) /\ (get_heap h0 key = chArray_get U128 (get_heap h0 rkeys) (i - 1) 16) /\ forall j, 0 <= j < i -> (to_arr U128 11 (get_heap h0 rkeys)) j = (get_heap h1 aes.rkeys) j). lia.
  intros i s_id ile.
  eapply r_get_remember_lhs.
  intros x.

  simpl.
  rewrite bind_assoc.
  eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).

  epose proof rcon_correct s_id~1 _ x _ _.
  eapply H.
  intros a0 a1.
  simpl.
  eapply rpre_hypothesis_rule'. intros s0 s1 [H1 [H2 H3]]. subst.

  destruct H1 as [[s6 []]].
  simpl in *.
  subst.

  simpl. repeat clear_get.
  eapply r_put_lhs with (pre := λ '(s0',s1'), _ ).
  eapply r_get_remember_lhs. intros x0.
  eapply r_get_remember_lhs. intros x1.
  rewrite bind_assoc.
  eapply r_bind with (m₁ := ret _) (f₁ := fun _ => _).
  epose proof key_expandP _ (s_id~0~1)%positive (rcon (get_heap (set_heap s6 round i) round)) x0 x1 (wrepr _ (rcon (get_heap (set_heap s6 round i) round))) _ _ _.
  rewrite !coerce_to_choice_type_K.
  eapply H0.
  intros a2 a3.

  eapply rpre_hypothesis_rule'.
  intros s2 s3 [H4 [o1 [o2 [H5 [H6 H7]]]]].
  subst.
  simpl in *.

  destruct H4 as [[[s7 [[]]]]].
  simpl in *.
  subst.

  rewrite !zero_extend_u.
  eapply r_put_lhs with (pre := λ '(s0',s1'), _).
  eapply r_put_lhs.

  eapply r_get_remember_lhs. intros x2.
  eapply r_get_remember_lhs. intros x3.
  eapply r_get_remember_lhs. intros x4.
  eapply r_put_lhs.
  eapply r_get_remember_rhs. intros x5.
  eapply r_put_rhs.
  eapply r_ret.
  intros s4 s5 H8.

  (* all this should be automated *)
  destruct H8 as [s7 [[[s8 [[[[[s9 [[s10 [[]]]]]]]]]]]]].
  simpl in *.
  subst.

  rewrite get_set_heap_eq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.

  rewrite !coerce_to_choice_type_K.
  rewrite !zero_extend_u.
  split; [|split].

  (* prove that pre is preserved in the inductive step *)
  tvars disj.
  apply disj. unfold rkeys.
  solve_in.
  apply disj. solve_in.
  apply disj. solve_in.
  apply disj. solve_in.
  apply disj. solve_in.
  (* what to do with the heap of the rhs? *) admit.

  (* prove the first invariant *)
  replace (Z.succ i - 1) with i by lia.
  rewrite chArray_get_set_eq.
  reflexivity.

  (* prove the second invariant *)
  intros j Hj.
  destruct (Z.eq_dec i j).

  (* i = j *)
  subst.
  rewrite to_arr_set_eq.
  rewrite setmE. rewrite eq_refl.
  destruct H as []. destruct H0. rewrite H0.
  f_equal. unfold getmd. rewrite -H1. rewrite getm_to_arr.
  f_equal. lia. lia. lia.

  (* i <> j *)
  rewrite to_arr_set_neq.
  rewrite setmE.
  assert (@eq bool (@eq_op Z_ordType j i) false). apply/eqP. auto.
  rewrite H0.
  apply H. lia. assumption. lia.

  (* trivial *)
  1-12: neq_loc_auto.

  (* prove base case *)
  intros s0 s1 H.
  destruct H as [s2 [[[s3 [[s4 [[s5 [[[s6 []]]]]]]]]]]].
  simpl in *; subst.

  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_neq.
  rewrite get_set_heap_eq.

  rewrite !coerce_to_choice_type_K.
  rewrite !zero_extend_u.
  split; [|split].

  (* prove that pre is preserved *) admit.

  (* first invariant *)
  rewrite chArray_get_set_eq. reflexivity.

  (* second invariant *)
  intros j Hj. assert (j = 0) by lia. subst.
  rewrite to_arr_set_eq. rewrite setmE. rewrite eq_refl. reflexivity.
  lia.
  1-4: neq_loc_auto.

  (* after for loop *)
  intros a0 a1.
  simpl.
  eapply r_get_remember_lhs with (pre := fun '(s0, s1) => _).
  intros x.
  eapply r_get_remember_rhs.
  intros x0.
  eapply r_ret.
  intros s0 s1 H.
  destruct H as [[[]]].
  destruct H0.
  simpl in *. subst.
  split. assumption.
  eapply eq_fmap.
  intros j.

  destruct ((0 <=? j) && (j <? 11)) eqn:E.
  rewrite !coerce_to_choice_type_K.
  apply H3. lia.

  rewrite getm_to_arr'.
  (* add this invariant to the rhs, or redefine the type of aes.rkeys. also generalize getm_to_arr' *)
  admit.
  admit.
Admitted.

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality.

Section Hacspec.
  Check key_combine.
  (* Check pack_eq_proof_statement _ _ _. *)
  Goal forall (key temp1 temp2 : u128), True.
    intros t1 t2 t3. destruct key_combine.
    (* pose (get_op_default pack_state). *)
    pose (get_op_default pack_state (KEY_COMBINE,
              (Hacspec_Lib_Pre.int128 '× Hacspec_Lib_Pre.int128 '× Hacspec_Lib_Pre.int128,
                Hacspec_Lib_Pre.int128 '× Hacspec_Lib_Pre.int128)) (t1, t2, t3)).
    Check opr.
    simpl. unfold IfToCEIf. simpl. apply/InP. apply -> LocationUtility.opsig_in_remove_fset. simpl. auto.
    simpl in c.
    reflexivity.
    KEY_COMBINE. []opr pack_state KEY_COMBINE.
    Lemma rxor_state : forall w1 w2,
        ⊢ ⦃ true_precond ⦄
          res ← Jkey_combine ;;
        ret (coerce_to_choice_type ('word U64) (hd ('word U64 ; chCanonical _) res).π2)
          ≈
          state_xor w1 w2
          ⦃ fun '(a, _) '(b, _) => (a = b) ⦄.
    Proof.
      intros w1 w2.
      unfold state_xor.
