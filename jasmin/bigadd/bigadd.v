Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition bigadd :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
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
            vname := "x.140" |};
          v_info :=
           xO
            (xO xH) |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO xH)))));
            vname := "y.141" |};
          v_info :=
           xI
            (xO xH) |}];
       f_body :=
        [MkI
          (xI
            (xO
              (xI
                (xO
                  (xO xH)))))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "xr.143" |};
              v_info :=
               xI
                (xI
                  (xI
                    (xO
                      (xO xH)))) |})
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
                 vname := "x.140" |};
               v_info :=
                xO
                 (xI
                   (xI
                     (xO
                       (xO xH)))) |};
             gs := Slocal |})
            (Pconst Z0)));
         MkI
          (xO
            (xI
              (xO
                (xO
                  (xO xH)))))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "yr.144" |};
              v_info :=
               xO
                (xO
                  (xI
                    (xO
                      (xO xH)))) |})
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
                 vname := "y.141" |};
               v_info :=
                xI
                 (xI
                   (xO
                     (xO
                       (xO xH)))) |};
             gs := Slocal |})
            (Pconst Z0)));
         MkI
          (xI
            (xO
              (xI
                (xI xH))))
          (Copn
           ([Lvar
              {| v_var :=
                {| vtype := sbool;
                 vname := "cf.145" |};
               v_info :=
                xO
                 (xO
                   (xO
                     (xO
                       (xO xH)))) |};
             Lvar
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "xr.143" |};
               v_info :=
                xI
                 (xO
                   (xO
                     (xO
                       (xO xH)))) |}])
           (AT_none) (Oaddcarry U64)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "xr.143" |};
                v_info :=
                 xO
                  (xI
                    (xI
                      (xI xH))) |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "yr.144" |};
                v_info :=
                 xI
                  (xI
                    (xI
                      (xI xH))) |};
              gs := Slocal |};
            Pbool false]));
         MkI
          (xO
            (xI
              (xO
                (xI xH))))
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
                vname := "res.142" |};
              v_info :=
               xO
                (xO
                  (xI
                    (xI xH))) |})
             (Pconst Z0))
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "xr.143" |};
               v_info :=
                xI
                 (xI
                   (xO
                     (xI xH))) |};
             gs := Slocal |}));
         MkI
          (xO
            (xI xH))
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.146" |};
             v_info :=
              xI
               (xI xH) |})
           (((UpTo,
             Pconst (Zpos xH)),
            Pconst
             (Zpos
               (xO
                 (xO xH)))))
           ([MkI
             (xO
               (xI
                 (xI
                   (xO xH))))
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "xr.143" |};
                 v_info :=
                  xI
                   (xO
                     (xO
                       (xI xH))) |})
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
                    vname := "x.140" |};
                  v_info :=
                   xO
                    (xO
                      (xO
                        (xI xH))) |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.146" |};
                   v_info :=
                    xI
                     (xI
                       (xI
                         (xO xH))) |};
                 gs := Slocal |})));
            MkI
             (xO
               (xI
                 (xO
                   (xO xH))))
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "yr.144" |};
                 v_info :=
                  xI
                   (xO
                     (xI
                       (xO xH))) |})
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
                    vname := "y.141" |};
                  v_info :=
                   xO
                    (xO
                      (xI
                        (xO xH))) |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.146" |};
                   v_info :=
                    xI
                     (xI
                       (xO
                         (xO xH))) |};
                 gs := Slocal |})));
            MkI
             (xO
               (xO
                 (xI xH)))
             (Copn
              ([Lvar
                 {| v_var :=
                   {| vtype := sbool;
                    vname := "cf.145" |};
                  v_info :=
                   xO
                    (xO
                      (xO
                        (xO xH))) |};
                Lvar
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "xr.143" |};
                  v_info :=
                   xI
                    (xO
                      (xO
                        (xO xH))) |}])
              (AT_none) (Oaddcarry U64)
              ([Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "xr.143" |};
                   v_info :=
                    xI
                     (xO
                       (xI xH)) |};
                 gs := Slocal |};
               Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "yr.144" |};
                   v_info :=
                    xO
                     (xI
                       (xI xH)) |};
                 gs := Slocal |};
               Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sbool;
                     vname := "cf.145" |};
                   v_info :=
                    xI
                     (xI
                       (xI xH)) |};
                 gs := Slocal |}]));
            MkI
             (xO
               (xO
                 (xO xH)))
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
                   vname := "res.142" |};
                 v_info :=
                  xI
                   (xI
                     (xO xH)) |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.146" |};
                    v_info :=
                     xO
                      (xI
                        (xO xH)) |};
                  gs := Slocal |}))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "xr.143" |};
                  v_info :=
                   xI
                    (xO
                      (xO xH)) |};
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
            vname := "res.142" |};
          v_info :=
           xO
            (xO
              (xO
                (xI
                  (xO xH)))) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.