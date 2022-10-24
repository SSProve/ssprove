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

From JasminSSProve Require Import jasmin_utils.

Import ListNotations.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

Definition get_tr := get_translated_fun ssprove_jasmin_prog.
Definition Jrcon (i : Z) := get_tr (xI (xI (xO (xO xH)))) 1%positive [('int ; i)].
Definition Jkey_combine rkey temp1 temp2 := get_tr (xO (xI (xI (xO xH)))) 1%positive [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)].
Definition Jkey_expand rcon rkey temp2 := get_tr (xO (xI (xO (xO xH)))) 1%positive [ ('int ; rcon) ; ('word U128 ; rkey) ; ('word U128 ; temp2) ].

Definition rcon (i : Z) := nth 54%Z [:: 1; 2; 4; 8; 16; 32; 64; 128; 27; 54]%Z ((Z.to_nat i) - 1).

Lemma rcon_correct :
  forall (i : Z), (1 <= i < 10)%Z ->
             ⊢ ⦃ fun _ => True ⦄ Jrcon i ⇓ [('int ; rcon i)] ⦃ fun _ => True ⦄.
Proof.
  unfold Jrcon, get_tr, get_translated_fun.
  intros i H.
  simpl_fun. repeat setjvars.
  repeat match goal with
         | |- context[(?a =? ?b)%Z] => let E := fresh in destruct (a =? b)%Z eqn:E; [rewrite ?Z.eqb_eq in E; subst|]
         | |- _ => eapply r_put_lhs with (pre := fun _ => True); ssprove_contract_put_get_lhs; eapply r_put_lhs; rewrite ?coerce_to_choice_type_K; eapply r_ret; easy
         | |- _ => simpl; ssprove_contract_put_get_lhs; rewrite !coerce_to_choice_type_K
         end.
  micromega.Lia.lia.
Qed.
From mathcomp.word Require Import word.

Infix "^" := wxor.

(* copy of the easycrypt functional definition *)
Definition key_expand (wn1 : u128) (rcon : u8) : 'word U128 :=
  let rcon := wpack U32 4 [toword rcon; 0%Z; 0%Z; 0%Z] in
  let w0 := subword 0 32 wn1 in
  let w1 := subword 1 32 wn1 in
  let w2 := subword 2 32 wn1 in
  let w3 := subword 3 32 wn1 in

  let tmp := w3 in
  let tmp := (rotr tmp 1) ^ rcon in
  let w4 := w0 ^ tmp in
  let w5 := w1 ^ w4 in
  let w6 := w2 ^ w5 in
  let w7 := w3 ^ w6 in
  wpack U128 4 [toword w4; toword w5; toword w6; toword w7].

Ltac neq_loc_auto ::= eapply injective_translate_var3; auto.

Notation "m ⊕ k" := (@word.wxor _ m k) (at level 70).

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

(* Lemma wcat_r_zero_extend : *)
  (* wcat_r [seq zero_extend a ] *)

Lemma wpshufd_1280 : forall a,  wpshufd_128 a 0 = a.
Proof.
  intros a.
  unfold wpshufd_128.
  rewrite wrepr0.
  unfold iota, map.
  rewrite !wpshufd10.
Admitted.

Lemma key_expand_correct rcon rkey temp2 rcon_ :
  toword rcon_ = rcon ->
  ⊢ ⦃ fun _ => True ⦄
    l ← (Jkey_expand rcon rkey temp2) ;;
  ret (nth ('word U128 ; word0) l 0%nat)
    ⇓ ('word U128 ; (key_expand rkey rcon_))
    ⦃ fun _ => True ⦄.
Proof.
  intros H.
  unfold Jkey_expand, get_tr, get_translated_fun.

  simpl_fun. repeat setjvars.
  rewrite !zero_extend_u.
  rewrite !coerce_to_choice_type_K.

  unfold eval_jdg.

  repeat clear_get.

  unfold sopn_sem.
  unfold tr_app_sopn_tuple.
  unfold tr_app_sopn_single.

  simpl.

  rewrite !zero_extend_u.
  rewrite !coerce_to_choice_type_K.

  repeat eapply u_put.
  eapply u_ret.

  split. easy.
  Admitted.
