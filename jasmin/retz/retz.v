Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition retz :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin := []; f_params := [];
       f_body :=
        [MkI
          (xO
            (xO xH))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "z.128" |};
              v_info :=
               xI
                (xO xH) |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pconst Z0)))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "z.128" |};
          v_info :=
           xO
            (xI xH) |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.