Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition test_for :=  {| p_funcs :=
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
                vname := "r.141" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pconst Z0)));
         MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.142" |};
             v_info := dummy_var_info |})
           (((DownTo, Pconst Z0),
            Pconst
             (Zpos
               (xI xH))))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "r.141" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Papp2
               (Oadd (Op_w U64))
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "r.141" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
               (Papp1 (Oword_of_int U64)
                (Pconst
                 (Zpos xH)))))]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.141" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.