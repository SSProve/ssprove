Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition ex :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.144" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "y.145" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.146" |};
               v_info := dummy_var_info |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "x.144" |};
               v_info := dummy_var_info |}])
           (AT_keep) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.144" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.145" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pbool false]));
         MkI
          (dummy_instr_info)
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.146" |};
               v_info := dummy_var_info |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "y.145" |};
               v_info := dummy_var_info |}])
           (AT_keep) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.145" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.144" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pbool false]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.145" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.