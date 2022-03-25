Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition ex :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.133" |};
          v_info :=
           xO
            (xO xH) |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "y.134" |};
          v_info :=
           xI
            (xO xH) |}];
       f_body :=
        [MkI
          (xI
            (xI
              (xO xH)))
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.135" |};
               v_info :=
                xO
                 (xI
                   (xI xH)) |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "x.133" |};
               v_info :=
                xI
                 (xI
                   (xI xH)) |}])
           (AT_none) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.133" |};
                v_info :=
                 xO
                  (xO
                    (xI xH)) |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.134" |};
                v_info :=
                 xI
                  (xO
                    (xI xH)) |};
              gs := Slocal |};
            Pbool false]));
         MkI
          (xO
            (xI xH))
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.135" |};
               v_info :=
                xI
                 (xO
                   (xO xH)) |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "y.134" |};
               v_info :=
                xO
                 (xI
                   (xO xH)) |}])
           (AT_none) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.134" |};
                v_info :=
                 xI
                  (xI xH) |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.133" |};
                v_info :=
                 xO
                  (xO
                    (xO xH)) |};
              gs := Slocal |};
            Pbool false]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.134" |};
          v_info :=
           xO
            (xO
              (xO
                (xO xH))) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.