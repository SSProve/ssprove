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

Definition xor :=
  {| p_funcs :=
    [(xO xH,
      {| f_info := xI xH;
       f_tyin :=
        [sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.131" |};
          v_info :=
           xO
            (xO xH) |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "y.132" |};
          v_info :=
           xI
            (xO xH) |}];
       f_body :=
        [MkI
          (xO
            (xI
              (xO xH)))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.133" |};
              v_info :=
               xO
                (xO
                  (xI xH)) |})
           (AT_none) (sword U64)
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sword U64;
                 vname := "x.131" |};
               v_info :=
                xI
                 (xI
                   (xO xH)) |};
             gs := Slocal |}));
         MkI
          (xO
            (xI xH))
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "r.133" |};
              v_info :=
               xI
                (xO
                  (xO xH)) |})
           (AT_none) (sword U64)
           (Papp2 (Olxor U64)
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "r.133" |};
                v_info :=
                 xO
                  (xO
                    (xO xH)) |};
              gs := Slocal |})
            (Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.132" |};
                v_info :=
                 xI
                  (xI xH) |};
              gs := Slocal |})))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "r.133" |};
          v_info :=
           xI
            (xO
              (xI xH)) |}];
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

Definition tr_xor := translate_prog xor.
Definition f_xor : 'word U64 × 'word U64 -> raw_code ('word U64).
Proof.
  pose tr_xor. unfold tr_xor in s. unfold translate_prog in s.
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


Eval cbn in tr_xor.
Goal forall w, f_xor w = f_xor w.
  intros [w1 w2].
  unfold f_xor at 2.
  unfold apply_noConfusion.
  simpl.
  unfold translate_write_var. simpl.
  unfold translate_var. simpl.
  set (fn := 2%positive).
  set (x := ('word U64; nat_of_fun_ident fn "x.131")).
  set (r := ('word U64; nat_of_fun_ident fn "r.133")).
  set (y := ('word U64; nat_of_fun_ident fn "y.132")).
  set (r_ := {| vtype := sword64; vname := "r.133" |}).
  set (x_ := {| v_var := {| vtype := sword64; vname := "x.131" |};
               v_info := (fn~0)%positive |}).
  set (y_ := {| v_var := {| vtype := sword64; vname := "y.132" |};
               v_info := (fn~1)%positive |}).

  unfold coerce_chtuple_to_list; simpl.
  rewrite eq_rect_r_K.
  simpl.
  fold x y.

  unfold bind_list'. simpl.
  unfold bind_list_trunc_aux. simpl.
  rewrite eq_rect_K.
  time repeat setoid_rewrite (@zero_extend_u U64).
  unfold translate_var. simpl. fold r.
