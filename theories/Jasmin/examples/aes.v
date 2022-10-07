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
 [ ( (* RCON *) xI (xI (xO (xO xH))),
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
