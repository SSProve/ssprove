Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.

From Jasmin Require Import expr compiler_util values sem.

From Coq Require Import Utf8.

From Crypt Require Import Prelude Package.
Import PackageNotation.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Section Section.

Context `{asmop:asmOp}.
Context (fresh_counter: Ident.ident).

Context {T} {pT:progT T}.


Context {Loc : {fset Location}}.
Context {import : Interface}.

Context {pd: PointerData}.

Variable P:uprog.

Notation gd := (p_globs P).

Context {encode : stype -> choice_type}.
Context (embed : forall t, sem_t t -> encode t).

Definition tr_var : (gvar -> Location).
  intros X. destruct X.
           destruct gv.
           destruct v_var.
           constructor.
           - apply encode.
             exact vtype0.
           - assert (Ident.ident -> nat) as db_of_ident.
             { intros id.
               induction id.
               - exact 1.
               - exact (256 * IHid + (Ascii.nat_of_ascii a))%nat.
             }
             exact (db_of_ident vname0).
Defined.

Definition typed_code := ∑ (a : choice_type), raw_code a.
Local Definition unsupported : typed_code.
Proof.
  exists chUnit.
  exact (pkg_distr.assert false).
Defined.

Fixpoint translate_pexpr (e : pexpr) : typed_code.
Proof.
  destruct e.
  - exact unsupported.
  - exists chBool. exact (ret b).
  - (* Parr_init only gets produced by ArrayInit() in jasmin source; the EC
       export asserts false on it, so we don't support it for now. *)
    exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
  - exact unsupported.
Defined.

(* FIXME: actually perform the truncation *)
Definition truncate_code (s : stype) (c : typed_code) : typed_code := c.

Definition ssprove_write_lval (l : lval) (tr_p : typed_code)
  : raw_code chUnit
  := projT2 unsupported
.

Definition translate_instr (i : instr) : raw_code chUnit.
Proof.
  destruct i as [iinfo i]. destruct i.
  - (* Cassgn *)
    (* l :a=_s p *)
    pose (translate_pexpr p) as tr_p.
    pose (truncate_code s tr_p) as tr_p'.
    exact (ssprove_write_lval l tr_p').
  - exact (projT2 unsupported). (* Copn *)
  - exact (projT2 unsupported). (* Cif *)
  - exact (projT2 unsupported). (* Cfor *)
  - exact (projT2 unsupported). (* Cwhile *)
  - (* Ccall i l f l0 *)
    (* translate arguments *)
    pose (map translate_pexpr l0) as tr_l0.
    (* "perform" the call via `opr` *)
    (* probably we'd look up the function signature in the current ambient program *)

    (* write_lvals the result of the call into lvals `l` *)

    exact (projT2 unsupported).
Defined.

Definition translate_cmd (c : cmd) : raw_code chUnit.
Proof.
  (* fold bind translate_instr *)
  exact (projT2 unsupported).
Defined.

Record fdef := { _ : typed_raw_function ; _ : {fset Location} ; _ : Interface ; _ : Interface }.

Definition translate_fundef (fd : _fun_decl extra_fun_t) : funname * fdef.
Proof.
  destruct fd. destruct _f.
  split. 1: exact f.
  constructor.
  - exists chUnit. exists chUnit.
    intros u.
    (* TODO: store function arguments in their locations *)
    exact (translate_cmd f_body).
    (* TODO: read return values from their locations *)
  - exact fset0.
  - exact [interface].
  - exact [interface].
Defined.

Fixpoint satisfies_globs (globs : glob_decls) : heap -> Prop.
Proof.
  exact (fun x => False).
Defined.

Fixpoint collect_globs (globs : glob_decls) : seq Location.
Proof.
  exact nil.
Defined.

Definition ssprove_prog {T} := seq (funname * T).

Definition translate_prog (p:expr.prog) : ssprove_prog :=
  let globs := collect_globs (p_globs p) in
  let fds := map translate_fundef (p_funcs p) in
  fds.

(* Theorem translate_correct entries (p : prog) (fn : funname) m va m' vr rf : *)
(*   fn \in entries → *)
(*   sem.sem_call p m fn va m' vr → *)
(*   let sp := (translate_prog p) in *)
(*   get_fundef fn sp = Some rf → *)
(*   { satisfies_globs (p_globs p) } rf (fix_types rf (translate_values va)) ~ ret vr *)
(*                                   { λ (v1,s1) (v2,s2), v1 = v2} *)
(* Proof. *)

End Section.
