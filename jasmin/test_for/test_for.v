Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition test_for :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := []; f_params := [];
       f_body :=
        [MkI
          (xI
            (xO
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.130" |};
              v_info :=
               xO
                (xI
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pconst Z0)));
         MkI
          (xO
            (xO xH))
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.131" |};
             v_info :=
              xI
               (xO xH) |})
           (((DownTo, Pconst Z0),
            Pconst
             (Zpos
               (xI xH))))
           ([MkI
             (xO
               (xI xH))
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "r.130" |};
                 v_info :=
                  xO
                   (xO
                     (xO xH)) |})
              (AT_none) (sword U64)
              (Papp2
               (Oadd (Op_w U64))
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "r.130" |};
                   v_info :=
                    xI
                     (xI xH) |};
                 gs := Slocal |})
               (Papp1 (Oword_of_int U64)
                (Pconst
                 (Zpos xH)))))]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.130" |};
          v_info :=
           xI
            (xI
              (xO xH)) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.