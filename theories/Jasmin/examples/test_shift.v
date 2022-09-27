Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition test_shift :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "a.142" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "u.143" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Papp2 (Osub Op_int)
             (Papp2 (Olsl Op_int)
              (Pconst (Zpos xH))
              (Pconst
               (Zpos
                 (xO
                   (xI
                     (xO
                       (xO xH)))))))
             (Pconst (Zpos xH)))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "u.143" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.