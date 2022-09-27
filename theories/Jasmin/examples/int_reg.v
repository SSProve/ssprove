Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition int_reg :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := [sint];
       f_params :=
        [{| v_var :=
           {| vtype := sint; vname := "k.141" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype := sint; vname := "x.142" |};
              v_info := dummy_var_info |})
           (AT_none) (sint)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype := sint; vname := "k.141" |};
               v_info := dummy_var_info |};
             gs := Slocal |}))];
       f_tyout := [sint];
       f_res :=
        [{| v_var :=
           {| vtype := sint; vname := "x.142" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.