Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition retz :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := []; f_params := [];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.139" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pconst Z0)))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.139" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.