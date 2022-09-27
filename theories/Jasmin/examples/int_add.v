Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition int_add :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin := [sint; sint];
       f_params :=
        [{| v_var :=
           {| vtype := sint; vname := "n.154" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype := sint; vname := "m.155" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.156" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype := sint;
                  vname := "n.154" |};
                v_info := dummy_var_info |};
              gs := Slocal |}))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype := sint;
                   vname := "m.155" |};
                 v_info := dummy_var_info |})
              (AT_inline) (sint)
              (Papp2 (Oadd Op_int)
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "m.155" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
               (Pconst (Zpos xH))))]))];
       f_tyout := [sint];
       f_res :=
        [{| v_var :=
           {| vtype := sint; vname := "m.155" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI xH,
      {| f_info :=
        xO (xO xH);
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "n.157" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "m.158" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.159" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Papp1 (Oint_of_word U64)
             (Pvar
              {| gv :=
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "n.157" |};
                 v_info := dummy_var_info |};
               gs := Slocal |})))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "m.158" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Papp2
               (Oadd (Op_w U64))
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "m.158" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
               (Papp1 (Oword_of_int U64)
                (Pconst
                 (Zpos xH)))))]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "m.158" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.