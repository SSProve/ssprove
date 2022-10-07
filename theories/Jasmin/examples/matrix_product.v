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
 [ ( (* dot_product *) xI (xO (xO xH)),
     {| f_info := xO (xI (xO xH))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xI (xO xH)))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                 ; vname := "v1.243"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "v2.244"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype := (sword U64)
                         ; vname := "res.245"  |}
                    ; v_info := dummy_var_info |})
                AT_none ((sword U64))
                ((Papp1 (Oword_of_int U64) (Pconst (Z0)))));
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.246"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.247"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                        ; vname := "v1.243"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.246"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "tmp.247"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Omul (Op_w U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "tmp.247"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pget AAscale U64
                             {| gv := {| v_var :=
                                           {| vtype :=
                                                (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                            ; vname := "v2.244"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.246"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "res.245"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Papp2 (Oadd (Op_w U64))
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "res.245"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |})
                          (Pvar
                             {| gv := {| v_var :=
                                           {| vtype := (sword U64)
                                            ; vname := "tmp.247"  |}
                                       ; v_info := dummy_var_info |} ; gs := Slocal |}))))]) ]
      ; f_tyout := [(sword U64)]
      ; f_res :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "res.245"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* product_matrix_vector *) xO (xI xH),
     {| f_info := xO (xO (xO xH))
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))));
            (sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m.238"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "v.239"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                  ; vname := "res.240"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.241"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall DoNotInline
                     [Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.242"  |}
                         ; v_info := dummy_var_info |}]
                     (xI (xO (xO xH)))
                     [(Psub AAscale U64 (xO (xI (xO xH)))
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "m.238"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Papp2 (Omul Op_int)
                            (Pvar
                               {| gv := {| v_var :=
                                             {| vtype := sint
                                              ; vname := "i.241"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})
                            (Pconst (Zpos (xO (xI (xO xH)))))));
                       (Pvar
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                                         ; vname := "v.239"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})]);
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                               ; vname := "res.240"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.241"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.242"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xI (xO xH)))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype := (sarr (xO (xO (xO (xO (xI (xO xH)))))))
                 ; vname := "res.240"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* transpose *) xI (xO xH),
     {| f_info := xI (xI xH)
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m.233"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "res.234"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.235"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Cfor
                     ({| v_var := {| vtype := sint
                                   ; vname := "j.236"  |}
                       ; v_info := dummy_var_info |})
                     ((UpTo, (Pconst (Z0))),
                       (Pconst (Zpos (xO (xI (xO xH))))))
                     [MkI InstrInfo.witness
                       (Cassgn
                          (Lvar
                             {| v_var :=
                                  {| vtype := (sword U64)
                                   ; vname := "tmp.237"  |}
                              ; v_info := dummy_var_info |})
                          AT_none ((sword U64))
                          ((Pget AAscale U64
                              {| gv := {| v_var :=
                                            {| vtype :=
                                                 (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                             ; vname := "m.233"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |}
                              (Papp2 (Oadd Op_int)
                                 (Pvar
                                    {| gv := {| v_var :=
                                                  {| vtype := sint
                                                   ; vname := "j.236"  |}
                                              ; v_info := dummy_var_info |} ; gs := Slocal |})
                                 (Papp2 (Omul Op_int)
                                    (Pvar
                                       {| gv := {| v_var :=
                                                     {| vtype := sint
                                                      ; vname := "i.235"  |}
                                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                                    (Pconst (Zpos (xO (xI (xO xH))))))))));
                       MkI InstrInfo.witness
                        (Cassgn
                           (Laset AAscale U64
                              {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "res.234"  |}
                               ; v_info := dummy_var_info |}
                              (Papp2 (Oadd Op_int)
                                 (Pvar
                                    {| gv := {| v_var :=
                                                  {| vtype := sint
                                                   ; vname := "i.235"  |}
                                              ; v_info := dummy_var_info |} ; gs := Slocal |})
                                 (Papp2 (Omul Op_int)
                                    (Pvar
                                       {| gv := {| v_var :=
                                                     {| vtype := sint
                                                      ; vname := "j.236"  |}
                                                 ; v_info := dummy_var_info |} ; gs := Slocal |})
                                    (Pconst (Zpos (xO (xI (xO xH))))))))
                           AT_none ((sword U64))
                           ((Pvar
                               {| gv := {| v_var :=
                                             {| vtype := (sword U64)
                                              ; vname := "tmp.237"  |}
                                         ; v_info := dummy_var_info |} ; gs := Slocal |})))])]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "res.234"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* product_matrix_matrix *) xI xH,
     {| f_info := xO (xO xH)
      ; f_tyin :=
          [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))));
            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_params :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "m1.226"  |}
            ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "m2.227"  |}
             ; v_info := dummy_var_info |};
            {| v_var :=
                 {| vtype :=
                      (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                  ; vname := "res.228"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "pres.229"  |}
                    ; v_info := dummy_var_info |})
                AT_none
                ((sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH)))))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "res.228"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "m2t.230"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "m2.227"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "m2t.230"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.231"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))), (Pconst (Zpos (xO (xI (xO xH))))))
                [MkI InstrInfo.witness
                  (Ccall DoNotInline
                     [Lasub AAscale U64 (xO (xI (xO xH)))
                        {| v_var :=
                             {| vtype :=
                                  (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                              ; vname := "rest.232"  |}
                         ; v_info := dummy_var_info |}
                        (Papp2 (Omul Op_int)
                           (Pvar
                              {| gv := {| v_var :=
                                            {| vtype := sint
                                             ; vname := "i.231"  |}
                                        ; v_info := dummy_var_info |} ; gs := Slocal |})
                           (Pconst (Zpos (xO (xI (xO xH))))))]
                     (xO (xI xH))
                     [(Pvar
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "m1.226"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |});
                       (Psub AAscale U64 (xO (xI (xO xH)))
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                         ; vname := "m2t.230"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omul Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.231"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xO (xI (xO xH)))))));
                       (Psub AAscale U64 (xO (xI (xO xH)))
                          {| gv := {| v_var :=
                                        {| vtype :=
                                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                         ; vname := "rest.232"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |}
                          (Papp2 (Omul Op_int)
                             (Pvar
                                {| gv := {| v_var :=
                                              {| vtype := sint
                                               ; vname := "i.231"  |}
                                          ; v_info := dummy_var_info |} ; gs := Slocal |})
                             (Pconst (Zpos (xO (xI (xO xH)))))))])]);
            MkI InstrInfo.witness
             (Cassgn
                (Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "res.228"  |}
                    ; v_info := dummy_var_info |})
                AT_none
                ((sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH)))))))))))
                ((Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "pres.229"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |})));
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "res.228"  |}
                    ; v_info := dummy_var_info |}]
                (xI (xO xH))
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "rest.232"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "res.228"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]) ]
      ; f_tyout := [(sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))]
      ; f_res :=
          [{| v_var :=
                {| vtype :=
                     (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                 ; vname := "res.228"  |}
            ; v_info := dummy_var_info |}]
      ; f_extra := tt
      ; |} )
 ; ( (* productMM *) xH,
     {| f_info := xO xH
      ; f_tyin := [(sword U64); (sword U64); (sword U64)]
      ; f_params :=
          [{| v_var := {| vtype := (sword U64)
                        ; vname := "x.218"  |}
            ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "y.219"  |}
             ; v_info := dummy_var_info |};
            {| v_var := {| vtype := (sword U64)
                         ; vname := "z.220"  |}
             ; v_info := dummy_var_info |}]
      ; f_body :=
          [ MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.221"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO (xI (xO xH)))))
                     (Pconst (Zpos (xO (xI (xO xH)))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.222"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pload U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "x.218"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.221"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                               ; vname := "mx.223"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.221"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.222"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lvar
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "tmp.222"  |}
                          ; v_info := dummy_var_info |})
                      AT_none ((sword U64))
                      ((Pload U64
                          {| v_var :=
                               {| vtype := (sword U64)
                                ; vname := "y.219"  |}
                           ; v_info := dummy_var_info |}
                          (Papp1 (Oword_of_int U64)
                             (Papp2 (Omul Op_int)
                                (Pconst (Zpos (xO (xO (xO xH)))))
                                (Pvar
                                   {| gv := {| v_var :=
                                                 {| vtype := sint
                                                  ; vname := "i.221"  |}
                                             ; v_info := dummy_var_info |} ; gs := Slocal |}))))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Laset AAscale U64
                         {| v_var :=
                              {| vtype :=
                                   (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                               ; vname := "my.224"  |}
                          ; v_info := dummy_var_info |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.221"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.222"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]);
            MkI InstrInfo.witness
             (Ccall DoNotInline
                [Lvar
                   {| v_var :=
                        {| vtype :=
                             (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                         ; vname := "mz.225"  |}
                    ; v_info := dummy_var_info |}]
                (xI xH)
                [(Pvar
                    {| gv := {| v_var :=
                                  {| vtype :=
                                       (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                   ; vname := "mx.223"  |}
                              ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "my.224"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |});
                  (Pvar
                     {| gv := {| v_var :=
                                   {| vtype :=
                                        (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                    ; vname := "mz.225"  |}
                               ; v_info := dummy_var_info |} ; gs := Slocal |})]);
            MkI InstrInfo.witness
             (Cfor
                ({| v_var := {| vtype := sint
                              ; vname := "i.221"  |}
                  ; v_info := dummy_var_info |})
                ((UpTo, (Pconst (Z0))),
                  (Papp2 (Omul Op_int) (Pconst (Zpos (xO (xI (xO xH)))))
                     (Pconst (Zpos (xO (xI (xO xH)))))))
                [MkI InstrInfo.witness
                  (Cassgn
                     (Lvar
                        {| v_var :=
                             {| vtype := (sword U64)
                              ; vname := "tmp.222"  |}
                         ; v_info := dummy_var_info |})
                     AT_none ((sword U64))
                     ((Pget AAscale U64
                         {| gv := {| v_var :=
                                       {| vtype :=
                                            (sarr (xO (xO (xO (xO (xO (xI (xO (xO (xI xH))))))))))
                                        ; vname := "mz.225"  |}
                                   ; v_info := dummy_var_info |} ; gs := Slocal |}
                         (Pvar
                            {| gv := {| v_var :=
                                          {| vtype := sint
                                           ; vname := "i.221"  |}
                                      ; v_info := dummy_var_info |} ; gs := Slocal |}))));
                  MkI InstrInfo.witness
                   (Cassgn
                      (Lmem U64
                         {| v_var :=
                              {| vtype := (sword U64)
                               ; vname := "z.220"  |}
                          ; v_info := dummy_var_info |}
                         (Papp1 (Oword_of_int U64)
                            (Papp2 (Omul Op_int)
                               (Pconst (Zpos (xO (xO (xO xH)))))
                               (Pvar
                                  {| gv := {| v_var :=
                                                {| vtype := sint
                                                 ; vname := "i.221"  |}
                                            ; v_info := dummy_var_info |} ; gs := Slocal |}))))
                      AT_none ((sword U64))
                      ((Pvar
                          {| gv := {| v_var :=
                                        {| vtype := (sword U64)
                                         ; vname := "tmp.222"  |}
                                    ; v_info := dummy_var_info |} ; gs := Slocal |})))]) ]
      ; f_tyout := []
      ; f_res := []
      ; f_extra := tt
      ; |} ) ] ;
  p_globs := [] ;
  p_extra := tt |}.
Defined.
