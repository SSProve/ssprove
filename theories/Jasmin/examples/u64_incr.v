Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition u64_incr :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := []; f_params := [];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Ccall (InlineFun)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "x.148" |};
              v_info := dummy_var_info |}])
           (xI xH)
           ([Papp1 (Oword_of_int U64)
             (Pconst Z0)]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.148" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI xH,
      {| f_info :=
        xO (xO xH);
       f_tyin := [sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "n.149" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "m.150" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp2
            (Oadd (Op_w U64))
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "n.149" |};
                v_info := dummy_var_info |};
              gs := Slocal |})
            (Papp1 (Oword_of_int U64)
             (Pconst
              (Zpos
                (xO xH))))))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "m.150" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.