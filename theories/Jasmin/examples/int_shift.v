Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition int_shift :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := []; f_params := [];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Ccall (InlineFun)
           ([Lvar
             {| v_var :=
               {| vtype := sint; vname := "x.151" |};
              v_info := dummy_var_info |}])
           (xI xH)
           ([Pconst Z0]));
         MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "y.150" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype := sint;
                  vname := "x.151" |};
                v_info := dummy_var_info |};
              gs := Slocal |})))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "y.150" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI xH,
      {| f_info :=
        xO (xO xH);
       f_tyin := [sint];
       f_params :=
        [{| v_var :=
           {| vtype := sint; vname := "n.152" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype := sint; vname := "m.153" |};
              v_info := dummy_var_info |})
           (AT_inline) (sint)
           (Papp2 (Olsl Op_int)
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype := sint;
                  vname := "n.152" |};
                v_info := dummy_var_info |};
              gs := Slocal |})
            (Pconst
             (Zpos
               (xI
                 (xO
                   (xO
                     (xO
                       (xO
                         (xO xH))))))))))];
       f_tyout := [sint];
       f_res :=
        [{| v_var :=
           {| vtype := sint; vname := "m.153" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.