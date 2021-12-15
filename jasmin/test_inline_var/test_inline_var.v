Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition test_inline_var :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r1.135" |};
          v_info :=
           xO
            (xO xH) |}];
       f_body :=
        [MkI
          (xI
            (xI
              (xI xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.136" |};
              v_info :=
               xI
                (xO
                  (xO
                    (xO xH))) |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "r1.135" |};
               v_info :=
                xO
                 (xO
                   (xO
                     (xO xH))) |};
             gs := Slocal |}));
         MkI
          (xO
            (xO
              (xI xH)))
          (Ccall (InlineFun)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.136" |};
              v_info :=
               xO
                (xI
                  (xI xH)) |}])
           (xI
            (xI xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.136" |};
                v_info :=
                 xI
                  (xO
                    (xI xH)) |};
              gs := Slocal |};
            Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xO
                  (xI xH))))]));
         MkI
          (xI
            (xO
              (xO xH)))
          (Ccall (InlineFun)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.136" |};
              v_info :=
               xI
                (xI
                  (xO xH)) |}])
           (xI
            (xI xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.136" |};
                v_info :=
                 xO
                  (xI
                    (xO xH)) |};
              gs := Slocal |};
            Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xI xH)))]));
         MkI
          (xI
            (xO xH))
          (Ccall (InlineFun)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.136" |};
              v_info :=
               xO
                (xO
                  (xO xH)) |}])
           (xI
            (xI xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.136" |};
                v_info :=
                 xO
                  (xI xH) |};
              gs := Slocal |};
            Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xI
                  (xO xH))))]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.136" |};
          v_info :=
           xO
            (xI
              (xO
                (xO xH))) |}];
       f_extra := tt |});
     (xI (xI xH),
      {| f_info :=
        xI
         (xI
           (xO
             (xO xH)));
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.137" |};
          v_info :=
           xO
            (xO
              (xI
                (xO xH))) |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "n.138" |};
          v_info :=
           xI
            (xO
              (xI
                (xO xH))) |}];
       f_body :=
        [MkI
          (xI
            (xI
              (xO
                (xI xH))))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.137" |};
              v_info :=
               xO
                (xI
                  (xI
                    (xI xH))) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.137" |};
                v_info :=
                 xI
                  (xO
                    (xI
                      (xI xH))) |};
              gs := Slocal |})
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "n.138" |};
                v_info :=
                 xO
                  (xO
                    (xI
                      (xI xH))) |};
              gs := Slocal |})));
         MkI
          (xO
            (xI
              (xI
                (xO xH))))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.137" |};
              v_info :=
               xO
                (xI
                  (xO
                    (xI xH))) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.137" |};
                v_info :=
                 xI
                  (xO
                    (xO
                      (xI xH))) |};
              gs := Slocal |})
            (Papp2
             (Oadd (Op_w U64))
             (Pvar
              {| gv :=
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "n.138" |};
                 v_info :=
                  xO
                   (xO
                     (xO
                       (xI xH))) |};
               gs := Slocal |})
             (Pvar
              {| gv :=
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "n.138" |};
                 v_info :=
                  xI
                   (xI
                     (xI
                       (xO xH))) |};
               gs := Slocal |}))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.137" |};
          v_info :=
           xI
            (xI
              (xI
                (xI xH))) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.