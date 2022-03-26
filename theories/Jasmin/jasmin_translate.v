Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.

From Jasmin Require Import expr compiler_util values sem.
From Jasmin Require Import expr_facts.

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

Definition encode (t : stype) : choice_type :=
  match t with
  | sbool => chBool
  | sint => chInt
  | sarr n => chMap chInt (chWord 8)
  | sword n => chWord n
  end.

Context (embed : forall t, sem_t t -> encode t).

Definition nat_of_ident (id : Ident.ident) : nat.
Proof.
  induction id.
  - exact 1.
  - exact (256 * IHid + (Ascii.nat_of_ascii a))%nat.
Defined.

(* injection *)
Definition nat_of_fun_ident (f : funname) (id : Ident.ident) : nat.
Proof.
  exact (3^(nat_of_pos f) * 2^(nat_of_ident id))%nat.
Defined.

Definition translate_var (f : funname) (x : var) : Location.
  destruct x.
  constructor.
  - apply encode.
    exact vtype0.
  - exact (nat_of_fun_ident f vname0).
Defined.

Definition translate_gvar (f : funname) (gv : gvar) : Location.
  destruct gv.
  destruct gv.
  now apply translate_var.
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

Definition cast_typed_code (ty : choice_type) (tc : typed_code) : raw_code ty.
Proof.
  destruct tc as [t c].
  destruct (t == ty) eqn:E.
  - move : E => /eqP E. subst; exact c.
  - apply ret. apply chCanonical.
Defined.

Definition ssprove_write_lval (fn : funname) (l : lval) (tc : typed_code)
  : raw_code chUnit
  :=
  match l with
  | Lnone _ ty => ret tt
  | Lvar x =>
      (* write_var x v s *)
      let l := translate_var fn (v_var x) in
      let c := cast_typed_code l tc in
      (x ← c ;; #put l := x ;; ret tt)%pack
  | _ => projT2 unsupported
  (* | Lmem sz x e => *)
  (*   Let vx := get_var (evm s) x >>= to_pointer in *)
  (*   Let ve := sem_pexpr s e >>= to_pointer in *)
  (*   let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *) *)
  (*   Let w := to_word sz v in *)
  (*   Let m :=  write s.(emem) p w in *)
  (*   ok {| emem := m;  evm := s.(evm) |} *)
  (* | Laset aa ws x i => *)
  (*   Let (n,t) := s.[x] in *)
  (*   Let i := sem_pexpr s i >>= to_int in *)
  (*   Let v := to_word ws v in *)
  (*   Let t := WArray.set t aa i v in *)
  (*   write_var x (@to_val (sarr n) t) s *)
  (* | Lasub aa ws len x i => *)
  (*   Let (n,t) := s.[x] in *)
  (*   Let i := sem_pexpr s i >>= to_int in *)
  (*   Let t' := to_arr (Z.to_pos (arr_size ws len)) v in  *)
  (*   Let t := @WArray.set_sub n aa ws len t i t' in *)
  (*   write_var x (@to_val (sarr n) t) s *)
  end.

Definition translate_instr_r (fn : funname) (i : instr_r) : raw_code chUnit.
Proof.
  destruct i.
  - (* Cassgn *)
    (* l :a=_s p *)
    pose (translate_pexpr p) as tr_p.
    pose (truncate_code s tr_p) as tr_p'.
    exact (ssprove_write_lval fn l tr_p').
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

Record fdef := { ffun : typed_raw_function ; locs : {fset Location} ; imp : Interface ; exp : Interface }.

Definition translate_fundef (fd : _ufun_decl (* extra_fun_t *)) : funname * fdef.
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

Fixpoint satisfies_globs (globs : glob_decls) : heap * heap -> Prop.
Proof.
  exact (fun '(x, y) => False).
Defined.

Fixpoint collect_globs (globs : glob_decls) : seq Location.
Proof.
  exact nil.
Defined.

Definition ssprove_prog := seq (funname * fdef).

Definition translate_prog (p:uprog) : ssprove_prog :=
  let globs := collect_globs (p_globs p) in
  let fds := map translate_fundef (p_funcs p) in
  fds.
Print typed_raw_function.
Check Interface.
About rel_jdg.
About package.
Check value.

Definition choice_type_of_val (val : value) : choice_type := encode (type_of_val val).

Fixpoint lchtuple (ts:seq choice_type) : choice_type :=
  match ts with
  | [::]   => chUnit
  | [::t1] => t1
  | t1::ts => chProd t1 (lchtuple ts)
  end.

Definition get_fundef_ssp (sp : seq (funname * fdef)) (fn : funname) (dom cod : choice_type) : option (dom -> raw_code cod).
Proof.
  exact None.
Defined.

Definition typed_chElement := ∑ (T: choice_type), T.

Definition translate_value (v : value) : choice_type_of_val v.
Proof.
  destruct v as [b | z | size a | size wd | undef_ty].
  - exact b.
  - exact z.
  - destruct a as [arr_data].
    eapply Mz.fold with (2 := arr_data) (3 := emptym).
    intros k v m.
    exact (setm m k v).
  - exact wd.
  - apply chCanonical.
    (* It shouldn't matter which value we pick, because when coercing an undef
       value at type ty back to ty via to_{bool,int,word,arr} (defined in
       values.v), all of these functions raise an error on Vundef. *)
Defined.


Fixpoint type_of_values vs : choice_type :=
  match vs with
  | [::]   => chUnit
  | [::v] => choice_type_of_val v
  | hd::tl => chProd (choice_type_of_val hd) (type_of_values tl)
  end.

(* lchtuple (map choice_type_of_val vs) *)

Definition translate_values (vs : seq value) : lchtuple (map choice_type_of_val vs).
Proof.
  induction vs as [|v vs tr_vs].
  - exact tt.
  - destruct vs as [|v' vs'].
    + exact (translate_value v).
    + exact (translate_value v, tr_vs).
Defined.

(* Definition seq_prod ls := *)
(*   map translate_value ls *)
(*   foldr chProd ls *)

Definition translate_ptr (ptr : pointer) : Location := (chWord Uptr ; Z.to_nat (wunsigned ptr)).

Definition coerce_to_choice_type (t : choice_type) {tv : choice_type} (v : tv) : t.
  destruct (tv == t) eqn:E.
  - move: E => /eqP E.
    subst. exact v.
  - apply chCanonical.
Defined.

Definition rel_mem (m : mem) (h : heap) :=
  forall ptr sz v, read m ptr sz = ok v -> get_heap h (translate_ptr ptr) = coerce_to_choice_type _ (translate_value (@to_val (sword sz) v)).

From Jasmin Require Import expr.
Local Open Scope vmap_scope.

Definition rel_vmap (vm : vmap) (h : heap) (fn : funname) :=
  forall (i : var) v, vm.[i] = ok v
    -> get_heap h (translate_var fn i) = coerce_to_choice_type _ (embed v).


Definition rel_estate (s : estate) (h : heap) (fn : funname) :=
  rel_mem s.(emem) h /\ rel_vmap s.(evm) h fn.

Definition instr_d (i : instr) : instr_r := match i with | MkI _ i => i end.

Theorem translate_correct (p : expr.uprog) (fn : funname) m va m' vr f :
  sem.sem_call p m fn va m' vr →
  let sp := (translate_prog p) in
  let dom := lchtuple (map choice_type_of_val va) in
  let cod := lchtuple (map choice_type_of_val vr) in
  get_fundef_ssp sp fn dom cod = Some f →
  (* satisfies_globs (p_globs p) (translate_mem m, translate_mem m') -> *)
  ⊢ ⦃ satisfies_globs (p_globs p) ⦄ f (translate_values va) ≈ ret (translate_values vr) ⦃ λ '(v1, s1) '(v2,s2), v1 = v2 ⦄.
Proof.
  (* intros H H1 H2 H3 H4. *)
  (* unshelve eapply sem_call_Ind. *)
  (* all: shelve_unifiable. *)
  intros H.
  set (Pfun :=
         λ (m : mem) (fn : funname) (va : seq value)  (m' : mem) (vr : seq value),
         forall f,
         let sp := translate_prog p in
         let dom := lchtuple [seq choice_type_of_val i | i <- va] in
         let cod := lchtuple [seq choice_type_of_val i | i <- vr] in
         get_fundef_ssp sp fn dom cod = Some f ->
         (* satisfies_globs (p_globs p) (translate_mem m, translate_mem m') → *)
         ⊢ ⦃ satisfies_globs (p_globs p) ⦄ f (translate_values va) ≈
     ret (translate_values vr) ⦃ λ '(v1, _) '(v2, _), v1 = v2 ⦄
      ).

  set (Pi_r :=
         λ (s1 : estate) (i : instr_r) (s2 : estate),
         ⊢ ⦃ λ '(h1,h2), False ⦄ translate_instr_r fn i ≈ ret tt ⦃ λ '(v1, _) '(v2, _), True ⦄
      ).

  set (Pi := λ s1 i s2, (Pi_r s1 (instr_d i) s2)).
  set (Pc :=
         λ (s1 : estate) (c : cmd) (s2 : estate),
         ⊢ ⦃ λ '(h1,h2), False ⦄ translate_cmd c ≈ ret tt ⦃ λ '(v1, _) '(v2, _), True ⦄
      ).

  (* FIXME *)
  set (Pfor := λ (v : var_i) (ls : seq Z) (s1 : estate) (c : cmd) (s2 : estate),
         ⊢ ⦃ λ '(h1,h2), False ⦄ (* ssprove_for *) translate_cmd c ≈ ret tt ⦃ λ '(v1, _) '(v2, _), True ⦄).


  unshelve eapply (@sem_call_Ind _ _ _ _ Pc Pi_r Pi Pfor Pfun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  - red. intros.
    red. unfold translate_cmd. simpl.
    admit.
  - red. intros.
    red. unfold translate_cmd. simpl.
    admit.
  - red. intros.
    apply H1.
  - red. intros.
    red.
    unfold translate_instr_r.
    destruct x.
    + simpl. admit.
    + simpl.
      eapply r_transL.
      * eapply r_bind with (mid := eq).
        -- instantiate (1 := ret (coerce_to_choice_type _
                         (translate_value v'))).
           admit.               (* by H0: sem_pexpr e = ok v *)
        -- intros.
           eapply rpre_hypothesis_rule.
           intros ? ? E. From Equations Require Import Equations.
           noconf E.
           eapply rpre_weaken_rule.
           1: refine (rreflexivity_rule _).
           simpl.
           intros. by intuition subst.
      * simpl.
        eapply r_put_lhs with (pre := (λ '(_, _), False)).
        apply r_ret.
        intros.
        admit.
    + admit.
    + admit.
    + admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    red.
    unfold translate_cmd.
    admit.
  - red. intros.
    red.
    unfold translate_instr_r.
    admit.
  - red. intros.
    unfold Pfun. intros.
    unfold get_fundef_ssp in H7.
    admit.
Admitted.

End Section.
