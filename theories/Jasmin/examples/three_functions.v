Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition three_functions :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.159" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.159" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.159" |};
                v_info := dummy_var_info |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO
                      (xI
                        (xO xH))))))))));
         MkI
          (dummy_instr_info)
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := res_"z.160" |};
              v_info := dummy_var_info |}])
           (xI xH)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.159" |};
                v_info := dummy_var_info |};
              gs := Slocal |}]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := res_"z.160" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI xH,
      {| f_info :=
        xO (xO xH);
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.161" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := res_"y.162" |};
              v_info := dummy_var_info |}])
           (xI
            (xO xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.161" |};
                v_info := dummy_var_info |};
              gs := Slocal |}]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := res_"y.162" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI (xO xH),
      {| f_info :=
        xO (xI xH);
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.163" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := res_"x.164" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.163" |};
                v_info := dummy_var_info |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := res_"x.164" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.