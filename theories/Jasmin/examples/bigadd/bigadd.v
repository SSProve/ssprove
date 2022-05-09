Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
From Jasmin Require Import expr.
(* From Jasmin Require Import x86_extra. *)
From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Context (f : funname).

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


Import PackageNotation.
Notation coe_cht := coerce_to_choice_type.
Notation coe_tyc := coerce_typed_code.
Notation " 'array " := (chMap 'int ('word U8)) (at level 2) : package_scope.
Notation " 'array " := (chMap 'int ('word U8)) (in custom pack_type at level 2).
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (at level 2) : package_scope.
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (in custom pack_type at level 2).
Notation " ⸨ ws ⸩ a .[ ptr * scale ] " := (chArray_get ws a ptr scale)
    (format " ⸨ ws ⸩  a .[ ptr * scale ] ").
Notation " a [ w / p ] " :=
  (chArray_set a AAscale p w)
    (at level 99, no associativity,
      format " a [ w / p ] ").

From Equations Require Import Equations.
Set Equations With UIP.
Set Equations Transparent.

From extructures Require Import ord fset fmap.

Definition empty_ufun_decl := (1%positive, {| f_info := 1%positive; f_tyin := [::]; f_params := [::]; f_body := [::]; f_tyout := [::]; f_res := [::]; f_extra := tt |}) : _ufun_decl.
Definition translate_simple_prog P := translate_fundef P emptym (List.nth_default empty_ufun_decl P.(p_funcs) 0).

Definition fn_bigadd := Eval simpl in ((ffun (translate_simple_prog bigadd).2).π2).π2.

Lemma eq_rect_K :
  forall (A : eqType) (x : A) (P : A -> Type) h e,
    @eq_rect A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

From CoqWord Require Import word.

Notation "$ i" := (_ ; nat_of_fun_var _ {| vtype := _; vname := i |})
                    (at level 99, format "$ i").

Notation "$$ i" := ({| v_var := {| vtype := _; vname := i |}; v_info := _ |})
                    (at level 99,
                      format "$$ i").

Notation "'for var ∈ seq" := (translate_for _ ($$var) seq)
                                      (at level 99).

Ltac prog_unfold := unfold translate_write_var, translate_instr, translate_var, coerce_chtuple_to_list, bind_list', bind_list_trunc_aux, wsize_size.
Hint Rewrite coerce_typed_code_K eq_rect_K eq_rect_r_K : prog_rewrite.

Opaque translate_for.
Ltac simpl_fun :=
  repeat (match goal with
         | _ => progress autorewrite with prog_rewrite
         | _ => prog_unfold; simpl
         end).

Goal forall aa goal, fn_bigadd aa = goal.
  intros [a1 a2] goal.
  unfold fn_bigadd.
  simpl_fun.

  (* BSH: the setoid_rewrites takes forever if we do not 'set' these names first *)
  set (array32 := sarr 32%positive).
  set (x := $"x.140").
  set (xr := $"xr.143").
  set (y := $"y.141").
  set (yr := $"yr.144").
  set (cf := $"cf.145").
  set (i := $"i.146").
  set (res := $"res.142").

  setoid_rewrite coerce_to_choice_type_K.
  setoid_rewrite coerce_to_choice_type_K.
  time repeat setoid_rewrite (@zero_extend_u U64).
Admitted.
