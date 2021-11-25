(**

  translating simple functions/packages between Jasmin and SSProve

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms chUniverse Package Prelude.

From extructures Require Import ord fset.

Import PackageNotation.

From CoqWord Require Import word.

Module Type Param.

  (* Parameter nbits : nat. *)
  Definition chWord : chUniverse := chWord 64.

End Param.

Module Identity (param : Param).

  Import param.

  Notation " 'word " :=
    chWord
      (in custom pack_type at level 2).

  Definition x : Location := (chWord ; 1%N).

  Local Open Scope package_scope.

  Definition IdentityLOC := fset [:: x].

  (* Definition IdentityCode {L : {fset Location}} (i : chWord) : *)
  (*   code L [interface] chWord := *)
  (*   {code *)
  (*      y ← i ;; *)
  (*      ret y *)
  (*   }. *)

  Definition IdentityPackage :
    package IdentityLOC
            [interface]
            [interface val #[10] : 'word → 'word ] :=
    [package
       def #[10] (r : 'word) : 'word
       {
         put x := r ;;
         r ← get x ;;
         ret r
       }
    ].

End Identity.

Require Import List.
From Jasmin Require Import expr.
From Crypt Require Import pkg_core_definition.

Import ListNotations.

Local Open Scope positive.
Local Open Scope string.

Notation jas_prog := expr.prog.     (* jasmin program *)

Definition identity : jas_prog :=
  {| p_globs := [];
     p_funcs :=
       [(1,
         {|
           f_iinfo := 2;
           f_tyin := [sword U64];
           f_params := [{|v_var := {|
                                    vtype := sword U64;
                                    vname := "x.121"
                                  |};
                          v_info := xI xH|}];
           f_body := [MkI
                        (xO (xO xH))
                        (Cassgn
                           (Lvar
                              {| v_var :=
                                  {| vtype := sword U64;
                                     vname := "x.???" |}; (* fixme *)
                                 v_info := xO (xI xH)|})
                           AT_none
                           (sword U64)
                           (Pvar
                              {|v_var :=
                                  {| vtype := sword U64;
                                     vname := "x.???" |}; (* fixme *)
                                v_info := xI (xO xH)|}))];
           f_tyout := [sword U64];
           f_res := [{|v_var :=
                         {| vtype := sword U64;
                            vname := "x.???"|}; (* fixme *)
                       v_info := xI (xI xH) |}]
         |})]
  |}.

(** original ocaml prog  **)

(* cprog: Jasmin.Expr.prog = *)
(*   {Jasmin.Expr.p_globs = []; *)
(*    p_funcs = *)
(*     [(Jasmin.BinNums.Coq_xH, *)
(*       {Jasmin.Expr.f_iinfo = Jasmin.BinNums.Coq_xO Jasmin.BinNums.Coq_xH; *)
(*        f_tyin = [Jasmin.Type.Coq_sword Jasmin.Wsize.U64]; *)
(*        f_params = *)
(*      [{Jasmin.Expr.v_var = *)
(*         {Jasmin.Var0.Var.vtype = Jasmin.Type.Coq_sword Jasmin.Wsize.U64; *)
(*          vname = <abstr>}; *)
(*        v_info = Jasmin.BinNums.Coq_xI Jasmin.BinNums.Coq_xH}]; *)
(*        f_body = *)
(*      [Jasmin.Expr.MkI *)
(*        (Jasmin.BinNums.Coq_xO *)
(*          (Jasmin.BinNums.Coq_xO Jasmin.BinNums.Coq_xH), *)
(*        Jasmin.Expr.Cassgn *)
(*         (Jasmin.Expr.Lvar *)
(*           {Jasmin.Expr.v_var = *)
(*             {Jasmin.Var0.Var.vtype = *)
(*               Jasmin.Type.Coq_sword Jasmin.Wsize.U64; *)
(*              vname = <abstr>}; *)
(*            v_info = *)
(*             Jasmin.BinNums.Coq_xO *)
(*              (Jasmin.BinNums.Coq_xI Jasmin.BinNums.Coq_xH)}, *)
(*         Jasmin.Expr.AT_none, Jasmin.Type.Coq_sword Jasmin.Wsize.U64, *)
(*         Jasmin.Expr.Pvar *)
(*          {Jasmin.Expr.v_var = *)
(*            {Jasmin.Var0.Var.vtype = Jasmin.Type.Coq_sword Jasmin.Wsize.U64; *)
(*             vname = <abstr>}; *)
(*           v_info = *)
(*            Jasmin.BinNums.Coq_xI *)
(*             (Jasmin.BinNums.Coq_xO Jasmin.BinNums.Coq_xH)}))]; *)
(*        f_tyout = [Jasmin.Type.Coq_sword Jasmin.Wsize.U64]; *)
(*        f_res = *)
(*      [{Jasmin.Expr.v_var = *)
(*         {Jasmin.Var0.Var.vtype = Jasmin.Type.Coq_sword Jasmin.Wsize.U64; *)
(*          vname = <abstr>}; *)
(*        v_info = *)
(*         Jasmin.BinNums.Coq_xI *)
(*          (Jasmin.BinNums.Coq_xI Jasmin.BinNums.Coq_xH)}]})]} *)

(** ec translation *)

(* module M = { *)
(*   proc identity (x:W64.t) : W64.t = { *)
(*     var r:W64.t; *)
(*     r <- x; *)
(*     return (r); *)
(*   } *)
(* }. *)

(* todo: prove that these two have the same semantics *)
