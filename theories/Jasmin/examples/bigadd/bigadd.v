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

Definition tr_bigadd := translate_prog bigadd.
Definition f_bigadd : ('array * 'array) -> raw_code 'array.
Proof.
  pose tr_bigadd. unfold tr_bigadd in s. unfold translate_prog in s.
  simpl in s.
  destruct s eqn:E.
  - unfold s in E. discriminate.
  - pose (ffun p.2).π2.π2.
    simpl in r.
    unfold s in E.
    noconf E.
    (* simpl in r. *)
    exact r.
Defined.

Lemma eq_rect_K :
  forall (A : eqType) (x : A) (P : A -> Type) h e,
    @eq_rect A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

Eval cbn in tr_bigadd.
Goal forall aa, f_bigadd aa = f_bigadd aa.

  intros [a1 a2].
  unfold f_bigadd at 2.
  unfold apply_noConfusion.
  simpl.
  unfold translate_write_var. simpl.
  unfold translate_instr. simpl.
  Opaque translate_for.
  (* unfold translate_for. simpl. *)
  rewrite !coerce_typed_code_K.
  simpl.
  unfold translate_var. simpl.
  (* set (TODO := ('unit; distr.dnull)). *)
  set (array32 := sarr 32%positive).
  set (fn := 2%positive).
  set (x := ('array; nat_of_fun_ident fn "x.140")).
  set (xr := ('word U64; nat_of_fun_ident fn "xr.143")).
  set (y := ('array; nat_of_fun_ident fn "y.141")).
  set (yr := ('word U64; nat_of_fun_ident fn "yr.144")).
  set (cf := ('bool; nat_of_fun_ident fn "cf.145")).
  set (i := ('int; nat_of_fun_ident fn "i.146")).

  set (x_ := {| v_var := {| vtype := array32; vname := "x.140" |};
               v_info := (fn~0)%positive |}).
  set (y_ := {| v_var := {| vtype := array32; vname := "y.141" |};
               v_info := (fn~1)%positive |}).

  unfold coerce_chtuple_to_list; simpl.
  rewrite eq_rect_r_K.
  simpl.
  fold x y.

  unfold bind_list'. simpl.
  unfold bind_list_trunc_aux. simpl.
  rewrite eq_rect_K.

  unfold translate_var. simpl.
  set (res := ('array; nat_of_fun_ident fn "res.142")).

  time repeat setoid_rewrite (@zero_extend_u U64).
  unfold wsize_size.
  rewrite !coerce_to_choice_type_K.
  setoid_rewrite coerce_to_choice_type_K.
  setoid_rewrite coerce_to_choice_type_K.

  (* Strangely, some instances of coe_cht don't get simplified away here. *)
