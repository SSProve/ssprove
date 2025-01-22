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
 [ ( (* __bn_load *) xI (xO xH),
     {| f_info := xO (xI (xI (xO (xI (xI xH)))))
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "a.1377"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1379"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1380"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pload U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "a.1377"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1379"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "x.1378"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1379"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1380"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "x.1378"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_store *) xI xH,
     {| f_info := xI (xO (xI (xO (xI (xI xH)))))
      ; f_tyin := [(sword U64); (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "a.1373"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1374"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1375"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1376"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "b.1374"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1375"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lmem U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "a.1373"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1375"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1376"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* _bn2_load_ *) xI (xI (xO (xO (xI (xI xH))))),
     {| f_info := xO (xO (xI (xO (xI (xI xH)))))
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "a.1369"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1371"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                     (Pconst (Zpos (xI (xI xH))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1372"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pload U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "a.1369"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1371"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "x.1370"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1371"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1372"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "x.1370"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn2_store *) xI (xO (xI (xI xH))),
     {| f_info := xO (xI (xO (xO (xI (xI xH)))))
      ; f_tyin := [(sword U64); (sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "a.1365"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                  ; vname := "b.1366"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1367"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                     (Pconst (Zpos (xI (xI xH))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1368"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                        ; vname := "b.1366"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1367"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lmem U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "a.1365"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1367"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1368"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* __bn2_unpack *) xO (xO (xO (xO (xI (xI xH))))),
     {| f_info := xI (xO (xO (xO (xI (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "a.1359"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1362"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t1.1363"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                        ; vname := "a.1359"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1362"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t2.1364"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                         ; vname := "a.1359"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Oadd Op_int) (Pconst (Zpos (xI (xI xH))))
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.1362"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "lo.1361"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1362"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t1.1363"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "hi.1360"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1362"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t2.1364"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "hi.1360"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "lo.1361"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_pack2 *) xO (xI (xI (xI (xO (xI xH))))),
     {| f_info := xI (xI (xI (xI (xO (xI xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "lo.1354"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "hi.1355"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1357"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1358"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "lo.1354"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1357"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1356"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1357"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1358"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1357"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1358"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "hi.1355"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1357"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1356"  |}
                          ; v_info := dummy_var_info |}
                         (Papp2 (Oadd Op_int) (Pconst (Zpos (xI (xI xH))))
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "i.1357"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1358"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "r.1356"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_eq *) xO (xO (xI (xI (xO (xI xH))))),
     {| f_info := xI (xO (xI (xI (xO (xI xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1346"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1347"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.1348"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "are_equal.1349"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Zpos (xH))))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "acc.1350"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1351"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1352"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1346"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1351"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t.1352"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Olxor U64)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "t.1352"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pget AAscale U64
                             {| gv := {| v_var :=
                                           {| vtype :=
                                                (sarr (xO (xO (xO (xI (xI xH))))))
                                            ; vname := "b.1347"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.1351"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "acc.1350"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Olor U64)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "acc.1350"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "t.1352"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))))]);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var := {| vtype := sbool
                                 ; vname := "zf.1353"  |}
                     ; v_info := dummy_var_info |};
                  Lnone dummy_var_info (sword U64)]
                AT_keep (Oasm (* AND_64 *) (BaseOp (None, (AND U64))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "acc.1350"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "acc.1350"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.1348"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pif ((sword U64))
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := sbool
                                      ; vname := "zf.1353"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "are_equal.1349"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "res.1348"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res.1348"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_eq *) xO (xI (xO (xI (xO (xI xH))))),
     {| f_info := xI (xI (xO (xI (xO (xI xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1343"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1344"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1345"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO (xI (xI (xO (xI xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1343"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1344"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.1345"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_eq_ *) xI (xO (xO (xO (xI xH)))),
     {| f_info := xI (xO (xO (xI (xO (xI xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "_a.1338"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "_b.1339"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1341"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1338"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1342"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1339"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1340"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xO (xI (xO (xI xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1341"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1342"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1340"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "r.1340"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.1340"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_test0 *) xO (xI (xI (xI (xO xH)))),
     {| f_info := xO (xO (xO (xI (xO (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1332"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.1333"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "is_zero.1334"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Zpos (xH))))));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "acc.1335"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1332"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1336"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "acc.1335"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Papp2 (Olor U64)
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := (sword U64)
                                           ; vname := "acc.1335"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Pget AAscale U64
                            {| gv := {| v_var :=
                                          {| vtype :=
                                               (sarr (xO (xO (xO (xI (xI xH))))))
                                           ; vname := "a.1332"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "i.1336"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})))))]);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var := {| vtype := sbool
                                 ; vname := "zf.1337"  |}
                     ; v_info := dummy_var_info |};
                  Lnone dummy_var_info (sword U64)]
                AT_keep (Oasm (* AND_64 *) (BaseOp (None, (AND U64))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "acc.1335"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "acc.1335"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.1333"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pif ((sword U64))
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := sbool
                                      ; vname := "zf.1337"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "is_zero.1334"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "res.1333"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res.1333"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_test0 *) xO (xI (xI (xO (xO (xI xH))))),
     {| f_info := xI (xI (xI (xO (xO (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1330"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1331"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1330"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.1331"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_copy *) xI (xI (xO (xI (xO (xO xH))))),
     {| f_info := xI (xO (xI (xO (xO (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1326"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1328"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1329"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1326"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1328"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "r.1327"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1328"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1329"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1327"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_copy2 *) xI (xO (xO (xI (xI xH)))),
     {| f_info := xO (xO (xI (xO (xO (xI xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1322"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1323"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1324"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1325"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1322"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1324"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "r.1323"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1324"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1325"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1323"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_cmov *) xO (xI (xO (xI (xO (xO xH))))),
     {| f_info := xI (xI (xO (xO (xO (xI xH)))))
      ; f_tyin :=
          [sbool; (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cond.1317"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1318"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1319"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1320"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1321"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1318"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1320"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t.1321"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pif ((sword U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sbool
                                            ; vname := "cond.1317"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pget AAscale U64
                             {| gv := {| v_var :=
                                           {| vtype :=
                                                (sarr (xO (xO (xO (xI (xI xH))))))
                                            ; vname := "b.1319"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.1320"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |}))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "t.1321"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "a.1318"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1320"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1321"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1318"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_set0 *) xI (xO (xO (xO (xO (xI xH))))),
     {| f_info := xO (xI (xO (xO (xO (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1314"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t.1315"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1316"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Laset AAscale U64
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                              ; vname := "a.1314"  |}
                         ; v_info := dummy_var_info |}
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "i.1316"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |}))
                     AT_none ((sword U64))
                     ((Pvar
                         {| gv := {| v_var :=
                                       {| vtype := (sword U64)
                                        ; vname := "t.1315"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1314"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_add1c *) xI (xI (xI (xI (xI (xO xH))))),
     {| f_info := xO (xO (xO (xO (xO (xI xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH)))))); (sword U64)]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1310"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "b.1311"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1312"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1310"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1310"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b.1311"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1313"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Copn
                     [Lvar
                        {| v_var :=
                             {| vtype := sbool
                              ; vname := "cf.1312"  |}
                         ; v_info := dummy_var_info |};
                       Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "a.1310"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1313"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})]
                     AT_keep (Oaddcarry (U64))
                     [(Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1310"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1313"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}));
                       (Papp1 (Oword_of_int U64) (Pconst (Z0)));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sbool
                                         ; vname := "cf.1312"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})])]) ]
      ; f_tyout := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1312"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1310"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_addc *) xI (xI (xI (xO (xO xH)))),
     {| f_info := xO (xI (xI (xI (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1305"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1306"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t.1308"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "b.1306"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1307"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1305"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1305"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t.1308"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1309"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1308"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "b.1306"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1309"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lvar
                         {| v_var :=
                              {| vtype := sbool
                               ; vname := "cf.1307"  |}
                          ; v_info := dummy_var_info |};
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                                ; vname := "a.1305"  |}
                           ; v_info := dummy_var_info |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1309"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})]
                      AT_keep (Oaddcarry (U64))
                      [(Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1305"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1309"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}));
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t.1308"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sbool
                                          ; vname := "cf.1307"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})])]) ]
      ; f_tyout := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1307"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1305"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_addc *) xO (xO (xI (xI (xI (xO xH))))),
     {| f_info := xI (xO (xI (xI (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1302"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1303"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1304"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1302"  |}
                     ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1302"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1303"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1304"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1302"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_subc *) xO (xO (xI (xO (xO xH)))),
     {| f_info := xI (xI (xO (xI (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1297"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1298"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t.1300"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "b.1298"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1299"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1297"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Osubcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1297"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t.1300"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1301"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1300"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "b.1298"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1301"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lvar
                         {| v_var :=
                              {| vtype := sbool
                               ; vname := "cf.1299"  |}
                          ; v_info := dummy_var_info |};
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                                ; vname := "a.1297"  |}
                           ; v_info := dummy_var_info |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1301"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})]
                      AT_keep (Osubcarry (U64))
                      [(Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1297"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1301"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}));
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t.1300"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sbool
                                          ; vname := "cf.1299"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})])]) ]
      ; f_tyout := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1299"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1297"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_subc *) xI (xO (xO (xI (xI (xO xH))))),
     {| f_info := xO (xI (xO (xI (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1294"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1295"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1296"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1294"  |}
                     ; v_info := dummy_var_info |}]
                (xO (xO (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1294"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1295"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1296"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1294"  |}
             ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __addacc3 *) xO (xO (xO (xO (xO (xO xH))))),
     {| f_info := xO (xO (xO (xI (xI (xO xH)))))
      ; f_tyin :=
          [(sword U64); (sword U64); (sarr (xO (xO (xO (xI xH))))); sint]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "b1.1289"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "b0.1290"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI xH)))))
                  ; vname := "a.1291"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "k.1292"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1293"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1291"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1292"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1291"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1292"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})
                       (Pconst (Zpos (xI xH)))));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b0.1290"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1293"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1291"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1292"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1291"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1292"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH)))));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b1.1289"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sbool
                                    ; vname := "cf.1293"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1293"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1291"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1292"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xO xH))))
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1291"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1292"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xO xH))))
                       (Pconst (Zpos (xI xH)))));
                  (Papp1 (Oword_of_int U64) (Pconst (Z0)));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sbool
                                    ; vname := "cf.1293"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI xH)))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI xH)))))
                 ; vname := "a.1291"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __muln_innerloop *) xI (xO (xO (xO (xO (xO xH))))),
     {| f_info := xI (xI (xI (xO (xI (xO xH)))))
      ; f_tyin :=
          [sint; sint; sint; (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI xH)))))]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "k.1279"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "istart.1280"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "iend.1281"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1282"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1283"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI xH)))))
                  ; vname := "x.1284"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1285"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo,
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sint
                                    ; vname := "istart.1280"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})),
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sint
                                    ; vname := "iend.1281"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var := {| vtype := sint
                                     ; vname := "j.1286"  |}
                         ; v_info := dummy_var_info |})
                     AT_inline (sint)
                     ((Papp2 (Osub Op_int)
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1279"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1285"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1287"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1282"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1285"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t1.1288"  |}
                          ; v_info := dummy_var_info |};
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "t0.1287"  |}
                           ; v_info := dummy_var_info |}]
                      AT_keep (Omulu (U64))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1287"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pget AAscale U64
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "b.1283"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |}
                           (Pvar
                              {| gv := {| v_var :=
                                            {| vtype := sint
                                             ; vname := "j.1286"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |}))]);
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1284"  |}
                          ; v_info := dummy_var_info |}]
                      (xO (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t1.1288"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t0.1287"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1284"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1279"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})])]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI xH)))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI xH)))))
                 ; vname := "x.1284"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_muln *) xI (xO (xO (xO (xO xH)))),
     {| f_info := xO (xI (xI (xO (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1272"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1273"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                  ; vname := "r.1274"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t0.1275"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1272"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t1.1276"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "t0.1275"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Omulu (U64))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t0.1275"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pget AAscale U64
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1273"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}
                     (Pconst (Z0)))]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1274"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Z0)))
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t0.1275"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI xH)))))
                         ; vname := "x.1277"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Zpos (xH))))
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t1.1276"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1277"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Zpos (xO xH)))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1277"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1278"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI xH)))))
                              ; vname := "x.1277"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xO (xO (xO (xO (xO xH))))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "k.1278"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pconst (Z0));
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1278"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xH))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1272"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "b.1273"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1277"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1275"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1277"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1278"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                ; vname := "x.1277"  |}
                           ; v_info := dummy_var_info |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1278"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))]
                      AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64)))
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1274"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1278"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1275"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1278"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xI (xI xH))))),
                  (Papp2 (Osub Op_int)
                     (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                        (Pconst (Zpos (xI (xI xH)))))
                     (Pconst (Zpos (xH)))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI xH)))))
                              ; vname := "x.1277"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xO (xO (xO (xO (xO xH))))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "k.1278"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Papp2 (Oadd Op_int)
                          (Papp2 (Osub Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1278"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))));
                       (Pconst (Zpos (xI (xI xH))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1272"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "b.1273"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1277"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1275"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1277"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1278"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                ; vname := "x.1277"  |}
                           ; v_info := dummy_var_info |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1278"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))]
                      AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64)))
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1274"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1278"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1275"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1274"  |}
                    ; v_info := dummy_var_info |}
                   (Papp2 (Osub Op_int)
                      (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                         (Pconst (Zpos (xI (xI xH)))))
                      (Pconst (Zpos (xH)))))
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "x.1277"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Osub Op_int)
                          (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH))))))) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "r.1274"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_muln *) xO (xO (xI (xO (xI (xO xH))))),
     {| f_info := xI (xO (xI (xO (xI (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1269"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1270"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                  ; vname := "r.1271"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1271"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1269"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1270"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1271"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "r.1271"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __addacc3x2 *) xO (xI (xO (xO (xI (xO xH))))),
     {| f_info := xI (xI (xO (xO (xI (xO xH)))))
      ; f_tyin :=
          [(sword U64); (sword U64); (sarr (xO (xO (xO (xI xH))))); sint]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "x.1260"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "y.1261"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI xH)))))
                  ; vname := "a.1262"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "k.1263"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "b1.1264"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "b0.1265"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Omulu (U64))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "x.1260"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "y.1261"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t.1266"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "b0.1265"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "b0.1265"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp2 (Olsl (Op_w U64))
                    (Pvar
                       {| gv := {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "b0.1265"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                    (Papp1 (Oword_of_int U8) (Pconst (Zpos (xH)))))));
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var := {| vtype := sbool
                                 ; vname := "cf.1267"  |}
                     ; v_info := dummy_var_info |};
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "b1.1264"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* SHLD_64 *) (BaseOp (None, (SHLD U64))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "b1.1264"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t.1266"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Papp1 (Oword_of_int U8) (Pconst (Zpos (xH))))]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "b2.1268"  |}
                    ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* MOV_64 *) (BaseOp (None, (MOV U64))))
                [(Papp1 (Oword_of_int U64) (Pconst (Z0)))]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1267"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "b2.1268"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Oaddcarry (U64))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "b2.1268"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b2.1268"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sbool
                                    ; vname := "cf.1267"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1267"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1262"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1263"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1262"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1263"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})
                       (Pconst (Zpos (xI xH)))));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b0.1265"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pbool false)]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1267"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1262"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1263"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1262"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1263"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH)))));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b1.1264"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sbool
                                    ; vname := "cf.1267"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1267"  |}
                    ; v_info := dummy_var_info |};
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "a.1262"  |}
                     ; v_info := dummy_var_info |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1263"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xO xH))))
                       (Pconst (Zpos (xI xH))))]
                AT_keep (Oaddcarry (U64))
                [(Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "a.1262"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Oadd Op_int)
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1263"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pconst (Zpos (xO xH))))
                       (Pconst (Zpos (xI xH)))));
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "b2.1268"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sbool
                                    ; vname := "cf.1267"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI xH)))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI xH)))))
                 ; vname := "a.1262"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __sqrn_innerloop *) xO (xO (xO (xO (xI (xO xH))))),
     {| f_info := xI (xO (xO (xO (xI (xO xH)))))
      ; f_tyin :=
          [sint; sint; sint; (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI xH)))))]
      ; f_params :=
          [{| v_var := {| vtype := sint
                        ; vname := "k.1251"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "istart.1252"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := sint
                         ; vname := "iend.1253"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "a.1254"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI xH)))))
                  ; vname := "x.1255"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1256"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo,
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sint
                                    ; vname := "istart.1252"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})),
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := sint
                                    ; vname := "iend.1253"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |}))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var := {| vtype := sint
                                     ; vname := "j.1257"  |}
                         ; v_info := dummy_var_info |})
                     AT_inline (sint)
                     ((Papp2 (Osub Op_int)
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1251"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |})
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1256"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "ti.1258"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1254"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "i.1256"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "tj.1259"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1254"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "j.1257"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1255"  |}
                          ; v_info := dummy_var_info |}]
                      (xO (xI (xO (xO (xI (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "ti.1258"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "tj.1259"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1255"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1251"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})])]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI xH)))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI xH)))))
                 ; vname := "x.1255"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __bn_sqrn *) xO (xI (xI (xI xH))),
     {| f_info := xI (xI (xI (xI (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1245"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                  ; vname := "r.1246"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t0.1247"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1245"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t1.1248"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "t0.1247"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Omulu (U64))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t0.1247"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t0.1247"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1246"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Z0)))
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t0.1247"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI xH)))))
                         ; vname := "x.1249"  |}
                    ; v_info := dummy_var_info |}
                   (Pconst (Zpos (xH))))
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "t1.1248"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1249"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Zpos (xO xH)))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1249"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1250"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xH)))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI xH)))))
                              ; vname := "x.1249"  |}
                         ; v_info := dummy_var_info |}]
                     (xO (xO (xO (xO (xI (xO xH))))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "k.1250"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pconst (Z0));
                       (Papp2 (Odiv Cmp_int)
                          (Papp2 (Oadd Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xH))))
                          (Pconst (Zpos (xO xH))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1245"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1249"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cif
                      (Papp2 (Oeq Op_int)
                         (Papp2 (Omod Cmp_int)
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "k.1250"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            (Pconst (Zpos (xO xH))))
                         (Pconst (Z0)))
                      [MkI InstrInfo.witness
                        (Cassgn
                           (Lvar
                              {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t0.1247"  |}
                               ; v_info := dummy_var_info |})
                           AT_none ((sword U64))
                           ((Pget AAscale U64
                               {| gv := {| v_var :=
                                             {| vtype :=
                                                  (sarr (xO (xO (xO (xI (xI xH))))))
                                              ; vname := "a.1245"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |}
                               (Papp2 (Odiv Cmp_int)
                                  (Pvar
                                     {| gv := {| v_var :=
                                                   {| vtype := sint
                                                    ; vname := "k.1250"  |}
                                               ; v_info := dummy_var_info |} ; gs := Slocal |})
                                  (Pconst (Zpos (xO xH)))))));
                        MkI InstrInfo.witness
                         (Copn
                            [Lvar
                               {| v_var :=
                                    {| vtype := (sword U64)
                                     ; vname := "t1.1248"  |}
                                ; v_info := dummy_var_info |};
                              Lvar
                                {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "t0.1247"  |}
                                 ; v_info := dummy_var_info |}]
                            AT_keep (Omulu (U64))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "t0.1247"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := (sword U64)
                                                ; vname := "t0.1247"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                        MkI InstrInfo.witness
                         (Ccall InlineFun
                            [Lvar
                               {| v_var :=
                                    {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                     ; vname := "x.1249"  |}
                                ; v_info := dummy_var_info |}]
                            (xO (xO (xO (xO (xO (xO xH))))))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "t1.1248"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := (sword U64)
                                                ; vname := "t0.1247"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype :=
                                                    (sarr (xO (xO (xO (xI xH)))))
                                                ; vname := "x.1249"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "k.1250"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})])]
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1247"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1249"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                ; vname := "x.1249"  |}
                           ; v_info := dummy_var_info |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))]
                      AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64)))
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1246"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1250"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1247"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1250"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xI (xI xH))))),
                  (Papp2 (Osub Op_int)
                     (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                        (Pconst (Zpos (xI (xI xH)))))
                     (Pconst (Zpos (xH)))))
                [MkI InstrInfo.witness
                  (Ccall InlineFun
                     [Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI xH)))))
                              ; vname := "x.1249"  |}
                         ; v_info := dummy_var_info |}]
                     (xO (xO (xO (xO (xI (xO xH))))))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype := sint
                                        ; vname := "k.1250"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Papp2 (Oadd Op_int)
                          (Papp2 (Osub Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))));
                       (Papp2 (Odiv Cmp_int)
                          (Papp2 (Oadd Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xH))))
                          (Pconst (Zpos (xO xH))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "a.1245"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1249"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cif
                      (Papp2 (Oeq Op_int)
                         (Papp2 (Omod Cmp_int)
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "k.1250"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            (Pconst (Zpos (xO xH))))
                         (Pconst (Z0)))
                      [MkI InstrInfo.witness
                        (Cassgn
                           (Lvar
                              {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "t0.1247"  |}
                               ; v_info := dummy_var_info |})
                           AT_none ((sword U64))
                           ((Pget AAscale U64
                               {| gv := {| v_var :=
                                             {| vtype :=
                                                  (sarr (xO (xO (xO (xI (xI xH))))))
                                              ; vname := "a.1245"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |}
                               (Papp2 (Odiv Cmp_int)
                                  (Pvar
                                     {| gv := {| v_var :=
                                                   {| vtype := sint
                                                    ; vname := "k.1250"  |}
                                               ; v_info := dummy_var_info |} ; gs := Slocal |})
                                  (Pconst (Zpos (xO xH)))))));
                        MkI InstrInfo.witness
                         (Copn
                            [Lvar
                               {| v_var :=
                                    {| vtype := (sword U64)
                                     ; vname := "t1.1248"  |}
                                ; v_info := dummy_var_info |};
                              Lvar
                                {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "t0.1247"  |}
                                 ; v_info := dummy_var_info |}]
                            AT_keep (Omulu (U64))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "t0.1247"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := (sword U64)
                                                ; vname := "t0.1247"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                        MkI InstrInfo.witness
                         (Ccall InlineFun
                            [Lvar
                               {| v_var :=
                                    {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                     ; vname := "x.1249"  |}
                                ; v_info := dummy_var_info |}]
                            (xO (xO (xO (xO (xO (xO xH))))))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "t1.1248"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := (sword U64)
                                                ; vname := "t0.1247"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype :=
                                                    (sarr (xO (xO (xO (xI xH)))))
                                                ; vname := "x.1249"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "k.1250"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})])]
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1247"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1249"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                ; vname := "x.1249"  |}
                           ; v_info := dummy_var_info |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1250"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))]
                      AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64)))
                      []);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "r.1246"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1250"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1247"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1246"  |}
                    ; v_info := dummy_var_info |}
                   (Papp2 (Osub Op_int)
                      (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                         (Pconst (Zpos (xI (xI xH)))))
                      (Pconst (Zpos (xH)))))
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "x.1249"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Osub Op_int)
                          (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH))))))) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "r.1246"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _bn_sqrn *) xI (xO (xI (xI (xO (xO xH))))),
     {| f_info := xO (xI (xI (xI (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1243"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                  ; vname := "r.1244"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1244"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1243"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1244"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xI xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "r.1244"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_caddP *) xI (xO (xI (xO (xO (xO xH))))),
     {| f_info := xO (xO (xI (xI (xO (xO xH)))))
      ; f_tyin := [sbool; (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var := {| vtype := sbool
                        ; vname := "cf.1235"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "x.1236"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "glob_pp.1237"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_p.1070"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_tmp.1238"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO (xI (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_pp.1237"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "t0.1239"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1240"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1241"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "_tmp.1238"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1240"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t.1241"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pif ((sword U64))
                          (Papp1 Onot
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sbool
                                               ; vname := "cf.1235"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |}))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "t0.1239"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "t.1241"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "_tmp.1238"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1240"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1241"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "tmp.1242"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_tmp.1238"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "x.1236"  |}
                     ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "x.1236"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "tmp.1242"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "x.1236"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_cminusP *) xI (xI (xI (xI (xI xH)))),
     {| f_info := xI (xO (xO (xI (xO (xO xH)))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "x.1230"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_tmp.1231"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO (xI (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "x.1230"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "tmp.1232"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_tmp.1231"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "glob_mpp.1233"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_mp.1069"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "_cf.1234"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "tmp.1232"  |}
                     ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "tmp.1232"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "glob_mpp.1233"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "x.1230"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xO (xI (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := sbool
                                   ; vname := "_cf.1234"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "x.1230"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "tmp.1232"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "x.1230"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_add *) xI (xI (xI (xO (xO (xO xH))))),
     {| f_info := xO (xO (xO (xI (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1228"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1229"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1228"  |}
                     ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1228"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1229"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1228"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xI (xI (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1228"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1228"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_add *) xO (xI (xO (xI xH))),
     {| f_info := xO (xI (xI (xO (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1226"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1227"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1226"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1226"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1226"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1226"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1227"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1226"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_sub *) xI (xI (xO (xO (xO (xO xH))))),
     {| f_info := xO (xO (xI (xO (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1223"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1224"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var := {| vtype := sbool
                                ; vname := "cf.1225"  |}
                    ; v_info := dummy_var_info |};
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1223"  |}
                     ; v_info := dummy_var_info |}]
                (xO (xO (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1223"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1224"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1223"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := sbool
                                   ; vname := "cf.1225"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1223"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1223"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_sub *) xI (xI (xI (xO xH))),
     {| f_info := xO (xI (xO (xO (xO (xO xH)))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1221"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1222"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1221"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1221"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1221"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO (xO (xO (xO xH))))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1221"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1222"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1221"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_rdcn *) xI (xO (xI (xO (xI xH)))),
     {| f_info := xO (xI (xI (xI (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xI (xI xH)))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                 ; vname := "a.1211"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1212"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sword U64)
                          ; vname := "zero.1213"  |}
                     ; v_info := dummy_var_info |}]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "u0r.1214"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "glob_u0.1067"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "p0.1215"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_p.1070"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |}
                    (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1216"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Z0))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1216"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Zpos (xH)))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Copn
                [Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool; Lnone dummy_var_info sbool;
                  Lnone dummy_var_info sbool;
                  Laset AAscale U64
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI xH)))))
                          ; vname := "x.1216"  |}
                     ; v_info := dummy_var_info |}
                    (Pconst (Zpos (xO xH)))]
                AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64))) []);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1218"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                              ; vname := "glob_pp.1217"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                     ((Pvar
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "glob_p.1070"  |}
                                   ; v_info := dummy_var_info |} ; gs := Sglob |})));
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1216"  |}
                          ; v_info := dummy_var_info |}]
                      (xI (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1218"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pconst (Z0));
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1218"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "r.1212"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "glob_pp.1217"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1216"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1219"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                         ; vname := "a.1211"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1218"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1216"  |}
                          ; v_info := dummy_var_info |}]
                      (xO (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "zero.1213"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t0.1219"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1216"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1218"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1219"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1216"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1218"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info (sword U64);
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "t0.1219"  |}
                           ; v_info := dummy_var_info |}]
                      AT_keep (Omulu (U64))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1219"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "u0r.1214"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "r.1212"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "k.1218"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1219"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Copn
                      [Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t1.1220"  |}
                          ; v_info := dummy_var_info |};
                        Lvar
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "t0.1219"  |}
                           ; v_info := dummy_var_info |}]
                      AT_keep (Omulu (U64))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1219"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "p0.1215"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1216"  |}
                          ; v_info := dummy_var_info |}]
                      (xO (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t1.1220"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t0.1219"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1216"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1218"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})])]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "k.1218"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Zpos (xI (xI xH))))),
                  (Papp2 (Osub Op_int)
                     (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                        (Pconst (Zpos (xI (xI xH)))))
                     (Pconst (Zpos (xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                              ; vname := "glob_pp.1217"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                     ((Pvar
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "glob_p.1070"  |}
                                   ; v_info := dummy_var_info |} ; gs := Sglob |})));
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1216"  |}
                          ; v_info := dummy_var_info |}]
                      (xI (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := sint
                                         ; vname := "k.1218"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Papp2 (Oadd Op_int)
                           (Papp2 (Osub Op_int)
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "k.1218"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |})
                              (Pconst (Zpos (xI (xI xH)))))
                           (Pconst (Zpos (xH))));
                        (Pconst (Zpos (xI (xI xH))));
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "r.1212"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "glob_pp.1217"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1216"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1219"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                         ; vname := "a.1211"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "k.1218"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Ccall InlineFun
                      [Lvar
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI xH)))))
                               ; vname := "x.1216"  |}
                          ; v_info := dummy_var_info |}]
                      (xO (xO (xO (xO (xO (xO xH))))))
                      [(Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "zero.1213"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := (sword U64)
                                          ; vname := "t0.1219"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI xH)))))
                                          ; vname := "x.1216"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |});
                        (Pvar
                           {| gv := {| v_var :=
                                         {| vtype := sint
                                          ; vname := "k.1218"  |}
                                     ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t0.1219"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI xH)))))
                                         ; vname := "x.1216"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1218"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH)))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                               ; vname := "r.1212"  |}
                          ; v_info := dummy_var_info |}
                         (Papp2 (Osub Op_int)
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "k.1218"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            (Pconst (Zpos (xI (xI xH))))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t0.1219"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Copn
                      [Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Lnone dummy_var_info sbool;
                        Laset AAscale U64
                          {| v_var :=
                               {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                ; vname := "x.1216"  |}
                           ; v_info := dummy_var_info |}
                          (Papp2 (Omod Cmp_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "k.1218"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xI xH))))]
                      AT_keep (Oasm (* set0_64 *) (ExtOp (Oset0 U64)))
                      [])]);
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI xH)))))
                         ; vname := "x.1216"  |}
                    ; v_info := dummy_var_info |}
                   (Papp2 (Omod Cmp_int)
                      (Papp2 (Osub Op_int)
                         (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                            (Pconst (Zpos (xI (xI xH)))))
                         (Pconst (Zpos (xH))))
                      (Pconst (Zpos (xI xH)))))
                AT_none ((sword U64))
                ((Papp2 (Oadd (Op_w U64))
                    (Pget AAscale U64
                       {| gv := {| v_var :=
                                     {| vtype :=
                                          (sarr (xO (xO (xO (xI xH)))))
                                      ; vname := "x.1216"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |}
                       (Papp2 (Omod Cmp_int)
                          (Papp2 (Osub Op_int)
                             (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                                (Pconst (Zpos (xI (xI xH)))))
                             (Pconst (Zpos (xH))))
                          (Pconst (Zpos (xI xH)))))
                    (Pget AAscale U64
                       {| gv := {| v_var :=
                                     {| vtype :=
                                          (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                      ; vname := "a.1211"  |}
                                 ; v_info := dummy_var_info |} ; gs := Slocal |}
                       (Papp2 (Osub Op_int)
                          (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))))))));
            MkI InstrInfo.witness
             (Cassgn
                (Laset AAscale U64
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1212"  |}
                    ; v_info := dummy_var_info |}
                   (Papp2 (Osub Op_int) (Pconst (Zpos (xI (xI xH))))
                      (Pconst (Zpos (xH)))))
                AT_none ((sword U64))
                ((Pget AAscale U64
                    {| gv := {| v_var :=
                                  {| vtype := (sarr (xO (xO (xO (xI xH)))))
                                   ; vname := "x.1216"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}
                    (Papp2 (Omod Cmp_int)
                       (Papp2 (Osub Op_int)
                          (Papp2 (Omul Op_int) (Pconst (Zpos (xO xH)))
                             (Pconst (Zpos (xI (xI xH)))))
                          (Pconst (Zpos (xH))))
                       (Pconst (Zpos (xI xH)))))));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1212"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xI (xI (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "r.1212"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1212"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_mul *) xO (xO (xI (xO xH))),
     {| f_info := xI (xO (xI (xI (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1206"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1207"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1208"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1208"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "r.1208"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1210"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_tmp.1209"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1210"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1206"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1207"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "tmp.1210"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1208"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "tmp.1210"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1208"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1208"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_mulU *) xI (xI (xO (xO (xI xH)))),
     {| f_info := xO (xO (xI (xI (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1202"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "b.1203"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1202"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1202"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1205"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_tmp.1204"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1205"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1202"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1203"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "tmp.1205"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1202"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "tmp.1205"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1202"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1202"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_sqr *) xI (xO (xO (xO xH))),
     {| f_info := xI (xI (xO (xI (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1198"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1199"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1199"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "r.1199"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1201"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_tmp.1200"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1201"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1198"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "tmp.1201"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1199"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "tmp.1201"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1199"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1199"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_sqrU *) xO (xO (xO (xI (xI xH)))),
     {| f_info := xO (xI (xO (xI (xI xH))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1195"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1195"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1195"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1197"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_tmp.1196"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1197"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1195"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "tmp.1197"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1195"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "tmp.1197"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1195"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1195"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_exp *) xO (xI (xI xH)),
     {| f_info := xI (xI (xI (xO (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1181"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "_b.1182"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1183"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "x.1185"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_x.1184"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "glob_oneMp.1186"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_oneM.1066"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "x.1185"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xI (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1181"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "x.1185"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1183"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xI (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_oneMp.1186"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1183"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_x.1184"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "x.1185"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "bb.1187"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1182"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "rr.1188"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "r.1183"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "j.1190"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                              ; vname := "b.1189"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                     ((Pvar
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "bb.1187"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "t.1191"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pget AAscale U64
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xI (xI xH))))))
                                         ; vname := "b.1189"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := sint
                                            ; vname := "j.1190"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "k.1192"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp1 (Oword_of_int U64)
                          (Pconst (Zpos (xO (xO (xO (xO (xO (xO xH)))))))))));
                  MkI InstrInfo.witness
                   (Cwhile NoAlign []
                      ((Papp2 (Oneq (Op_w U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "k.1192"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Papp1 (Oword_of_int U64) (Pconst (Z0)))))
                      [MkI InstrInfo.witness
                        (Cassgn
                           (Lvar
                              {| v_var :=
                                   {| vtype := (sword U64)
                                    ; vname := "ss.1193"  |}
                               ; v_info := dummy_var_info |})
                           AT_none ((sword U64))
                           ((Pvar
                               {| gv := {| v_var :=
                                             {| vtype := (sword U64)
                                              ; vname := "k.1192"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})));
                        MkI InstrInfo.witness
                         (Copn
                            [Lnone dummy_var_info sbool;
                              Lvar
                                {| v_var :=
                                     {| vtype := sbool
                                      ; vname := "cf.1194"  |}
                                 ; v_info := dummy_var_info |};
                              Lnone dummy_var_info sbool;
                              Lnone dummy_var_info sbool;
                              Lnone dummy_var_info sbool;
                              Lvar
                                {| v_var :=
                                     {| vtype := (sword U64)
                                      ; vname := "t.1191"  |}
                                 ; v_info := dummy_var_info |}]
                            AT_keep
                            (Oasm (* SHR_64 *) (BaseOp (None, (SHR U64))))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "t.1191"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |});
                              (Papp1 (Oword_of_int U8) (Pconst (Zpos (xH))))]);
                        MkI InstrInfo.witness
                         (Cif
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sbool
                                              ; vname := "cf.1194"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            [MkI InstrInfo.witness
                              (Cassgn
                                 (Lvar
                                    {| v_var :=
                                         {| vtype :=
                                              (sarr (xO (xO (xO (xI (xI xH))))))
                                          ; vname := "r.1183"  |}
                                     ; v_info := dummy_var_info |})
                                 AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                                 ((Pvar
                                     {| gv := {| v_var :=
                                                   {| vtype :=
                                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                                    ; vname := "rr.1188"  |}
                                               ; v_info := dummy_var_info |} ; gs := Slocal |})));
                              MkI InstrInfo.witness
                               (Cassgn
                                  (Lvar
                                     {| v_var :=
                                          {| vtype :=
                                               (sarr (xO (xO (xO (xI (xI xH))))))
                                           ; vname := "x.1185"  |}
                                      ; v_info := dummy_var_info |})
                                  AT_none
                                  ((sarr (xO (xO (xO (xI (xI xH)))))))
                                  ((Pvar
                                      {| gv := {| v_var :=
                                                    {| vtype :=
                                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                                     ; vname := "_x.1184"  |}
                                                ; v_info := dummy_var_info |} ; gs := Slocal |})));
                              MkI InstrInfo.witness
                               (Ccall DoNotInline
                                  [Lvar
                                     {| v_var :=
                                          {| vtype :=
                                               (sarr (xO (xO (xO (xI (xI xH))))))
                                           ; vname := "r.1183"  |}
                                      ; v_info := dummy_var_info |}]
                                  (xI (xI (xO (xO (xI xH)))))
                                  [(Pvar
                                      {| gv := {| v_var :=
                                                    {| vtype :=
                                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                                     ; vname := "r.1183"  |}
                                                ; v_info := dummy_var_info |} ; gs := Slocal |});
                                    (Pvar
                                       {| gv := {| v_var :=
                                                     {| vtype :=
                                                          (sarr (xO (xO (xO (xI (xI xH))))))
                                                      ; vname := "x.1185"  |}
                                                 ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                              MkI InstrInfo.witness
                               (Cassgn
                                  (Lvar
                                     {| v_var :=
                                          {| vtype :=
                                               (sarr (xO (xO (xO (xI (xI xH))))))
                                           ; vname := "_x.1184"  |}
                                      ; v_info := dummy_var_info |})
                                  AT_none
                                  ((sarr (xO (xO (xO (xI (xI xH)))))))
                                  ((Pvar
                                      {| gv := {| v_var :=
                                                    {| vtype :=
                                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                                     ; vname := "x.1185"  |}
                                                ; v_info := dummy_var_info |} ; gs := Slocal |})));
                              MkI InstrInfo.witness
                               (Cassgn
                                  (Lvar
                                     {| v_var :=
                                          {| vtype :=
                                               (sarr (xO (xO (xO (xI (xI xH))))))
                                           ; vname := "rr.1188"  |}
                                      ; v_info := dummy_var_info |})
                                  AT_none
                                  ((sarr (xO (xO (xO (xI (xI xH)))))))
                                  ((Pvar
                                      {| gv := {| v_var :=
                                                    {| vtype :=
                                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                                     ; vname := "r.1183"  |}
                                                ; v_info := dummy_var_info |} ; gs := Slocal |})))]
                            []);
                        MkI InstrInfo.witness
                         (Cassgn
                            (Lvar
                               {| v_var :=
                                    {| vtype :=
                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                     ; vname := "x.1185"  |}
                                ; v_info := dummy_var_info |})
                            AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                            ((Pvar
                                {| gv := {| v_var :=
                                              {| vtype :=
                                                   (sarr (xO (xO (xO (xI (xI xH))))))
                                               ; vname := "_x.1184"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})));
                        MkI InstrInfo.witness
                         (Ccall DoNotInline
                            [Lvar
                               {| v_var :=
                                    {| vtype :=
                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                     ; vname := "x.1185"  |}
                                ; v_info := dummy_var_info |}]
                            (xO (xO (xO (xI (xI xH)))))
                            [(Pvar
                                {| gv := {| v_var :=
                                              {| vtype :=
                                                   (sarr (xO (xO (xO (xI (xI xH))))))
                                               ; vname := "x.1185"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                        MkI InstrInfo.witness
                         (Cassgn
                            (Lvar
                               {| v_var :=
                                    {| vtype :=
                                         (sarr (xO (xO (xO (xI (xI xH))))))
                                     ; vname := "_x.1184"  |}
                                ; v_info := dummy_var_info |})
                            AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                            ((Pvar
                                {| gv := {| v_var :=
                                              {| vtype :=
                                                   (sarr (xO (xO (xO (xI (xI xH))))))
                                               ; vname := "x.1185"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})));
                        MkI InstrInfo.witness
                         (Cassgn
                            (Lvar
                               {| v_var :=
                                    {| vtype := (sword U64)
                                     ; vname := "k.1192"  |}
                                ; v_info := dummy_var_info |})
                            AT_none ((sword U64))
                            ((Pvar
                                {| gv := {| v_var :=
                                              {| vtype := (sword U64)
                                               ; vname := "ss.1193"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})));
                        MkI InstrInfo.witness
                         (Cassgn
                            (Lvar
                               {| v_var :=
                                    {| vtype := (sword U64)
                                     ; vname := "k.1192"  |}
                                ; v_info := dummy_var_info |})
                            AT_none ((sword U64))
                            ((Papp2 (Osub (Op_w U64))
                                (Pvar
                                   {| gv := {| v_var :=
                                                 {| vtype := (sword U64)
                                                  ; vname := "k.1192"  |}
                                             ; v_info := dummy_var_info |} ; gs := Slocal |})
                                (Papp1 (Oword_of_int U64)
                                   (Pconst (Zpos (xH)))))))])]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1183"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "rr.1188"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}))) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1183"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* __fp_inv *) xI (xI (xO xH)),
     {| f_info := xO (xI (xI (xO (xI xH))))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xI (xI xH))))));
            (sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1178"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                  ; vname := "r.1179"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "glob_pm2p.1180"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_pm2.1068"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1179"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1178"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "glob_pm2p.1180"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1179"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "r.1179"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_fromM *) xO (xO xH),
     {| f_info := xO (xO (xI (xO (xI xH))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1173"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1173"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1173"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1174"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Laset AAscale U64
                        {| v_var :=
                             {| vtype :=
                                  (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                              ; vname := "_tmp.1175"  |}
                         ; v_info := dummy_var_info |}
                        (Papp2 (Oadd Op_int) (Pconst (Zpos (xI (xI xH))))
                           (Pvar
                              {| gv := {| v_var :=
                                            {| vtype := sint
                                             ; vname := "i.1174"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |})))
                     AT_none ((sword U64))
                     ((Papp1 (Oword_of_int U64) (Pconst (Z0)))))]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1174"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1176"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xI (xI xH))))))
                                        ; vname := "a.1173"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1174"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                               ; vname := "_tmp.1175"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.1174"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1176"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "tmp.1177"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_tmp.1175"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1173"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xI (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "tmp.1177"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1173"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1173"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* _fp_toM *) xO (xO (xO xH)),
     {| f_info := xO (xI (xO (xO (xI xH))))
      ; f_tyin := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1171"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1171"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1171"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "glob_rMp.1172"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "glob_rM.1065"  |}
                              ; v_info := dummy_var_info |} ; gs := Sglob |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1171"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1171"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "glob_rMp.1172"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xI (xI xH))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                 ; vname := "a.1171"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* bn_eq *) xI (xI (xI (xI (xO xH)))),
     {| f_info := xO (xO (xO (xO (xI xH))))
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "ap.1164"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1165"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1167"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1164"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1168"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1167"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1169"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1165"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1170"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1169"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1166"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO (xI xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1168"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1170"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.1166"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* bn_test0 *) xO (xO (xI (xI (xO xH)))),
     {| f_info := xI (xO (xI (xI (xO xH))))
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "ap.1160"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1162"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1160"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1163"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1162"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1161"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1163"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "r.1161"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "r.1161"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |}))) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "r.1161"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* bn_copy *) xO (xI (xO (xI (xO xH)))),
     {| f_info := xI (xI (xO (xI (xO xH))))
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1156"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1157"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1158"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "t.1159"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pload U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "ap.1157"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1158"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lmem U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "rp.1156"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.1158"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "t.1159"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* bn_set0 *) xO (xO (xO (xI (xO xH)))),
     {| f_info := xI (xO (xO (xI (xO xH))))
      ; f_tyin := [(sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1154"  |}
            ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.1155"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xI (xI xH)))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lmem U64
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "rp.1154"  |}
                         ; v_info := dummy_var_info |}
                        (Papp1 (Oword_of_int U64)
                           (Papp2 (Omul Op_int)
                              (Pconst (Zpos (xO (xO (xO xH)))))
                              (Pvar
                                 {| gv := {| v_var :=
                                               {| vtype := sint
                                                ; vname := "i.1155"  |}
                                           ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                     AT_none ((sword U64))
                     ((Papp1 (Oword_of_int U64) (Pconst (Z0)))))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* bn_addn *) xI (xO (xI (xO (xO xH)))),
     {| f_info := xO (xI (xI (xO (xO xH))))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1147"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1148"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1149"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1150"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1148"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1151"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1150"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1152"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1149"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1153"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1152"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1151"  |}
                     ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1151"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1153"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1147"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1151"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* bn_subn *) xO (xI (xO (xO (xO xH)))),
     {| f_info := xI (xI (xO (xO (xO xH))))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1140"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1141"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1142"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1143"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1141"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1144"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1143"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1145"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1142"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1146"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1145"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lnone dummy_var_info sbool;
                  Lvar
                    {| v_var :=
                         {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                          ; vname := "a.1144"  |}
                     ; v_info := dummy_var_info |}]
                (xO (xO (xI (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1144"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1146"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1140"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1144"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* bn_muln *) xI (xI (xI (xI xH))),
     {| f_info := xO (xO (xO (xO (xO xH))))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1131"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1132"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1133"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1134"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1132"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1135"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1134"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1136"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1133"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1137"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1136"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1139"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_r.1138"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1139"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO (xO xH)))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1135"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1137"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1139"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI (xO (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1131"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1139"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* bn_sqrn *) xI (xI (xO (xI xH))),
     {| f_info := xO (xO (xI (xI xH)))
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1125"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1126"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1127"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1126"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1128"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1127"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1130"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xO (xI (xI xH))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                   ; vname := "_r.1129"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                         ; vname := "r.1130"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1128"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1130"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI (xO (xI (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1125"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xI (xI xH)))))))
                                    ; vname := "r.1130"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_add *) xO (xO (xO (xI xH))),
     {| f_info := xI (xO (xO (xI xH)))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1118"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1119"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1120"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1121"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1119"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1122"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1121"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1123"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1120"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1124"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1123"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1122"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xO (xI xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1122"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1124"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1118"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1122"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_sub *) xI (xO (xI (xO xH))),
     {| f_info := xO (xI (xI (xO xH)))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1111"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1112"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1113"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1114"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1112"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1115"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1114"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1116"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1113"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1117"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1116"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1115"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xI (xO xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1115"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1117"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1111"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1115"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_mul *) xO (xI (xO (xO xH))),
     {| f_info := xI (xI (xO (xO xH)))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1102"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1103"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1104"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1105"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1103"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1106"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1105"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1107"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1104"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1108"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1107"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1110"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_r.1109"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1110"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO (xI (xO xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1106"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1108"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1110"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1102"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1110"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_sqr *) xI (xI (xI xH)),
     {| f_info := xO (xO (xO (xO xH)))
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1096"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1097"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1098"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1097"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1099"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1098"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1101"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_r.1100"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1101"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO (xO (xO xH))))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1099"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1101"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1096"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1101"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_expm_noct *) xO (xO (xI xH)),
     {| f_info := xI (xO (xI xH))
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1086"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1087"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "bp.1088"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "_rp.1089"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1086"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1090"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1087"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1091"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1090"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_b.1092"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "bp.1088"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "b.1093"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_b.1092"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1095"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_r.1094"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1095"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xI (xI xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1091"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "b.1093"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1095"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "rp.1086"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "_rp.1089"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1086"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1095"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_inv *) xI (xO (xO xH)),
     {| f_info := xO (xI (xO xH))
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1079"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1080"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "_rp.1081"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1079"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1082"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1080"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1083"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1082"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1085"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_r.1084"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "r.1085"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xI (xO xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1083"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1085"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "rp.1079"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "_rp.1081"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1079"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "r.1085"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_toM *) xO (xI xH),
     {| f_info := xI (xI xH)
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1075"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1076"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1077"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1076"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1078"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1077"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1078"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO (xO xH)))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1078"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1075"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1078"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* fp_fromM *) xH,
     {| f_info := xO xH
      ; f_tyin := [(sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "rp.1071"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "ap.1072"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Ccall InlineFun
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "_a.1073"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "ap.1072"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1074"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sarr (xO (xO (xO (xI (xI xH)))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "_a.1073"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                         ; vname := "a.1074"  |}
                    ; v_info := dummy_var_info |}]
                (xO (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xI (xI xH))))))
                                   ; vname := "a.1074"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Ccall InlineFun [] (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "rp.1071"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xI (xI xH))))))
                                    ; vname := "a.1074"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [({| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                ; vname := "glob_rM.1065"  |},
                (@Garr (xO (xO (xO (xI (xI xH))))) (* TODO: pp_gd *) _))
                ; ({| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                    ; vname := "glob_oneM.1066"  |},
                    (@Garr (xO (xO (xO (xI (xI xH))))) (* TODO: pp_gd *) _))
                ; ({| vtype := (sword U64)
                    ; vname := "glob_u0.1067"  |},
                    (@Gword U64 (* TODO: pp_gd *) _))
                ; ({| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                    ; vname := "glob_pm2.1068"  |},
                    (@Garr (xO (xO (xO (xI (xI xH))))) (* TODO: pp_gd *) _))
                ; ({| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                    ; vname := "glob_mp.1069"  |},
                    (@Garr (xO (xO (xO (xI (xI xH))))) (* TODO: pp_gd *) _))
                ; ({| vtype := (sarr (xO (xO (xO (xI (xI xH))))))
                    ; vname := "glob_p.1070"  |},
                    (@Garr (xO (xO (xO (xI (xI xH))))) (* TODO: pp_gd *) _))] ;
           p_extra := tt |}.

  set rMZ := [48 ; 155 ; 214 ; 220 ; 101 ; 91 ; 229 ; 40 ; 194 ; 152 ; 135 ; 118 ; 103 ; 115 ; 236 ; 172 ; 141 ; 104 ; 17 ; 131 ; 63 ; 151 ; 39 ; 171 ; 11 ; 124 ; 108 ; 141 ; 175 ; 198 ; 92 ; 23 ; 126 ; 52 ; 222 ; 45 ; 191 ; 146 ; 205 ; 171 ; 154 ; 109 ; 104 ; 199 ; 97 ; 106 ; 225 ; 105 ; 42 ; 209 ; 205 ; 155 ; 168 ; 37 ; 0 ; 0]%Z.
  set rM := WArray.fill 56 [seq word.mkword U8 i | i <- rMZ].
  destruct rM as [rM|]; [ exact rM | exact (WArray.empty 56) ].

  set oneMZ := [44 ; 116 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 252 ; 4 ; 244 ; 15 ; 185 ; 212 ; 172 ; 159 ; 85 ; 251 ; 164 ; 1 ; 216 ; 12 ; 65 ; 119 ; 95 ; 84 ; 84 ; 50 ; 233 ; 218 ; 46 ; 189 ; 167 ; 238 ; 236 ; 0 ; 0]%Z.
  set oneM := WArray.fill 56 [seq word.mkword U8 i | i <- oneMZ].
  destruct oneM as [oneM|]; [ exact oneM | exact (WArray.empty 56) ].

  set u0 := (word.mkword U64 1 : u64).
  exact u0.

  set pm2Z := [253 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 226 ; 122 ; 118 ; 193 ; 253 ; 163 ; 174 ; 88 ; 49 ; 120 ; 92 ; 198 ; 123 ; 86 ; 32 ; 197 ; 129 ; 214 ; 95 ; 252 ; 108 ; 68 ; 115 ; 23 ; 39 ; 31 ; 52 ; 2 ; 0]%Z.
  set pm2 := WArray.fill 56 [seq word.mkword U8 i | i <- pm2Z].
  destruct pm2 as [pm2|]; [ exact pm2 | exact (WArray.empty 56) ].

  set mpZ := [ (Zpos 1) (* FIXME: 1 *) ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 0 ; 29 ; 133 ; 137 ; 62 ; 2 ; 92 ; 81 ; 167 ; 206 ; 135 ; 163 ; 57 ; 132 ; 169 ; 223 ; 58 ; 126 ; 41 ; 160 ; 3 ; 147 ; 187 ; 140 ; 232 ; 216 ; 224 ; 203 ; 253 ; 255]%Z.
  set mp := WArray.fill 56 [seq word.mkword U8 i | i <- mpZ].
  destruct mp as [mp|]; [ exact mp | exact (WArray.empty 56) ].


  set pZ := [255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 255 ; 226 ; 122 ; 118 ; 193 ; 253 ; 163 ; 174 ; 88 ; 49 ; 120 ; 92 ; 198 ; 123 ; 86 ; 32 ; 197 ; 129 ; 214 ; 95 ; 252 ; 108 ; 68 ; 115 ; 23 ; 39 ; 31 ; 52 ; 2 ; 0]%Z.
  set p := WArray.fill 56 [seq word.mkword U8 i | i <- pZ].
  destruct p as [p|]; [ exact p | exact (WArray.empty 56) ].
Defined.
