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
 [ ( (* productMM *) xH,
     {| f_info := FunInfo.witness
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "x.216"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "y.217"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "z.218"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.219"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO (xI (xO xH)))))
                     (Pconst (Zpos (xO (xI (xO xH)))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.220"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pload U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "x.216"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.219"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                               ; vname := "mx.221"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.219"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.220"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "tmp.220"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pload U64
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "y.217"  |}
                           ; v_info := dummy_var_info |}
                          (Papp1 (Oword_of_int U64)
                             (Papp2 (Omul Op_int)
                                (Pconst (Zpos (xO (xO (xO xH)))))
                                (Pvar
                                   {| gv := {| v_var :=
                                                 {| vtype := sint
                                                  ; vname := "i.219"  |}
                                             ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                               ; vname := "my.222"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.219"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.220"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "mz.223"  |}
                    ; v_info := dummy_var_info |}]
                (xO xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "mx.221"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "my.222"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "mz.223"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.219"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO (xI (xO xH)))))
                     (Pconst (Zpos (xO (xI (xO xH)))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.220"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "mz.223"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.219"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lmem U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "z.218"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.219"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.220"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} )
 ; ( (* product_matrix_matrix *) xO xH,
     {| f_info := FunInfo.witness
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m1.224"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "m2.225"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "res.226"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "pres.227"  |}
                    ; v_info := dummy_var_info |})
                AT_none
                ((sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH)))))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "res.226"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "m2t.228"  |}
                    ; v_info := dummy_var_info |}]
                (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "m2.225"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "m2t.228"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.229"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall DoNotInline
                     [Lasub AAscale U64 (xO (xI (xO xH)))
                        {| v_var :=
                             {| vtype :=
                                  (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                              ; vname := "rest.230"  |}
                         ; v_info := dummy_var_info |}
                        (Papp2 (Omul Op_int)
                           (Pvar
                              {| gv := {| v_var :=
                                            {| vtype := sint
                                             ; vname := "i.229"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |})
                           (Pconst (Zpos (xO (xI (xO xH))))))]
                     (xO (xO xH))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "m1.224"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Psub AAscale U64 (xO (xI (xO xH)))
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                         ; vname := "m2t.228"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omul Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.229"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xO (xI (xO xH)))))));
                       (Psub AAscale U64 (xO (xI (xO xH)))
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                         ; vname := "rest.230"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omul Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.229"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xO (xI (xO xH)))))))])]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "res.226"  |}
                    ; v_info := dummy_var_info |})
                AT_none
                ((sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH)))))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "pres.227"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "res.226"  |}
                    ; v_info := dummy_var_info |}]
                (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "rest.230"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "res.226"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "res.226"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* transpose *) xI xH,
     {| f_info := FunInfo.witness
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m.231"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "res.232"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.233"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Cfor
                     ({| v_var := {| vtype := sint
                                   ; vname := "j.234"  |}
                       ; v_info := dummy_var_info |})
                     ((UpTo, (Pconst (Z0))),
                       (Pconst (Zpos (xO (xI (xO xH))))))
                     [MkI InstrInfo.witness
                       (Cassgn
                          (Lvar
                             {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "tmp.235"  |}
                              ; v_info := dummy_var_info |})
                          AT_none ((sword U64))
                          ((Pget AAscale U64
                              {| gv := {| v_var :=
                                            {| vtype :=
                                                 (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                             ; vname := "m.231"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |}
                              (Papp2 (Oadd Op_int)
                                 (Pvar
                                    {| gv := {| v_var :=
                                                  {| vtype := sint
                                                   ; vname := "j.234"  |}
                                              ; v_info := dummy_var_info |} ; gs := Slocal |})
                                 (Papp2 (Omul Op_int)
                                    (Pvar
                                       {| gv := {| v_var :=
                                                     {| vtype := sint
                                                      ; vname := "i.233"  |}
                                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                                    (Pconst (Zpos (xO (xI (xO xH))))))))));
                       MkI InstrInfo.witness
                        (Cassgn
                           (Laset AAscale U64
                              {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "res.232"  |}
                               ; v_info := dummy_var_info |}
                              (Papp2 (Oadd Op_int)
                                 (Pvar
                                    {| gv := {| v_var :=
                                                  {| vtype := sint
                                                   ; vname := "i.233"  |}
                                              ; v_info := dummy_var_info |} ; gs := Slocal |})
                                 (Papp2 (Omul Op_int)
                                    (Pvar
                                       {| gv := {| v_var :=
                                                     {| vtype := sint
                                                      ; vname := "j.234"  |}
                                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                                    (Pconst (Zpos (xO (xI (xO xH))))))))
                           AT_none ((sword U64))
                           ((Pvar
                               {| gv := {| v_var :=
                                             {| vtype := (sword U64)
                                              ; vname := "tmp.235"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})))])]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "res.232"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* product_matrix_vector *) xO (xO xH),
     {| f_info := FunInfo.witness
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m.236"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "v.237"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "res.238"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.239"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall DoNotInline
                     [Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.240"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xO xH))
                     [(Psub AAscale U64 (xO (xI (xO xH)))
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "m.236"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Papp2 (Omul Op_int)
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "i.239"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            (Pconst (Zpos (xO (xI (xO xH)))))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                         ; vname := "v.237"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                               ; vname := "res.238"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.239"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.240"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                 ; vname := "res.238"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* dot_product *) xI (xO xH),
     {| f_info := FunInfo.witness
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xI (xO xH)))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                 ; vname := "v1.241"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "v2.242"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.243"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.244"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.245"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                        ; vname := "v1.241"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.244"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "tmp.245"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Omul (Op_w U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "tmp.245"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pget AAscale U64
                             {| gv := {| v_var :=
                                           {| vtype :=
                                                (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                            ; vname := "v2.242"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.244"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "res.243"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Oadd (Op_w U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "res.243"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "tmp.245"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))))]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res.243"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.

Defined.
Notation PRODUCTMM := ( xH ).
Notation PRODUCT_MATRIX_MATRIX := ( xO xH ).
Notation TRANSPOSE := ( xI xH ).
Notation PRODUCT_MATRIX_VECTOR := ( xO (xO xH) ).
Notation DOT_PRODUCT := ( xI (xO xH) ).