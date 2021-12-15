Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition add1 :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "arg.130" |};
          v_info :=
           xO
            (xO xH) |}];
       f_body :=
        [MkI
          (xO
            (xO
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.131" |};
              v_info :=
               xO
                (xI
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "arg.130" |};
               v_info :=
                xI
                 (xO
                   (xO xH)) |};
             gs := Slocal |}));
         MkI
          (xI
            (xO xH))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.131" |};
              v_info :=
               xI
                (xI xH) |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.131" |};
                v_info :=
                 xO
                  (xI xH) |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.131" |};
          v_info :=
           xI
            (xI
              (xO xH)) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.