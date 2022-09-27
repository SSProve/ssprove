Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition add1 :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "arg.141" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.142" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "arg.141" |};
               v_info := dummy_var_info |};
             gs := Slocal |}));
         MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.142" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "z.142" |};
                v_info := dummy_var_info |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.142" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.