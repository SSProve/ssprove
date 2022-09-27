Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition bigadd :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO xH)))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xO xH)))))];
       f_params :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO xH)))));
            vname := "x.151" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO xH)))));
            vname := "y.152" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "xr.154" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Pget (AAscale) (U64)
            ({| gv :=
              {| v_var :=
                {| vtype :=
                  sarr
                   (xO
                     (xO
                       (xO
                         (xO
                           (xO xH)))));
                 vname := "x.151" |};
               v_info := dummy_var_info |};
             gs := Slocal |})
            (Pconst Z0)));
         MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "yr.155" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Pget (AAscale) (U64)
            ({| gv :=
              {| v_var :=
                {| vtype :=
                  sarr
                   (xO
                     (xO
                       (xO
                         (xO
                           (xO xH)))));
                 vname := "y.152" |};
               v_info := dummy_var_info |};
             gs := Slocal |})
            (Pconst Z0)));
         MkI
          (dummy_instr_info)
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.156" |};
               v_info := dummy_var_info |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "xr.154" |};
               v_info := dummy_var_info |}])
           (AT_keep) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "xr.154" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "yr.155" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pbool false]));
         MkI
          (dummy_instr_info)
          (Cassgn
           (Laset (AAscale) (U64)
             ({| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO xH)))));
                vname := "res.153" |};
              v_info := dummy_var_info |})
             (Pconst Z0))
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "xr.154" |};
               v_info := dummy_var_info |};
             gs := Slocal |}));
         MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.157" |};
             v_info := dummy_var_info |})
           (((UpTo,
             Pconst (Zpos xH)),
            Pconst
             (Zpos
               (xO
                 (xO xH)))))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "xr.154" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pget (AAscale) (U64)
               ({| gv :=
                 {| v_var :=
                   {| vtype :=
                     sarr
                      (xO
                        (xO
                          (xO
                            (xO
                              (xO xH)))));
                    vname := "x.151" |};
                  v_info := dummy_var_info |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.157" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "yr.155" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pget (AAscale) (U64)
               ({| gv :=
                 {| v_var :=
                   {| vtype :=
                     sarr
                      (xO
                        (xO
                          (xO
                            (xO
                              (xO xH)))));
                    vname := "y.152" |};
                  v_info := dummy_var_info |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.157" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})));
            MkI
             (dummy_instr_info)
             (Copn
              ([Lvar
                 {| v_var :=
                   {| vtype := sbool;
                    vname := "cf.156" |};
                  v_info := dummy_var_info |};
                Lvar
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "xr.154" |};
                  v_info := dummy_var_info |}])
              (AT_keep) (Oaddcarry U64)
              ([Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "xr.154" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |};
               Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "yr.155" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |};
               Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sbool;
                     vname := "cf.156" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |}]));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Laset (AAscale) (U64)
                ({| v_var :=
                  {| vtype :=
                    sarr
                     (xO
                       (xO
                         (xO
                           (xO
                             (xO xH)))));
                   vname := "res.153" |};
                 v_info := dummy_var_info |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.157" |};
                    v_info := dummy_var_info |};
                  gs := Slocal |}))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "xr.154" |};
                  v_info := dummy_var_info |};
                gs := Slocal |}))]))];
       f_tyout :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO xH)))))];
       f_res :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO xH)))));
            vname := "res.153" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.