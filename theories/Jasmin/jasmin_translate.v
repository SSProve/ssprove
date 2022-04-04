Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From Jasmin Require Import expr compiler_util values sem.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.
From Jasmin Require Import expr_facts.

From Coq Require Import Utf8.

From Crypt Require Import Prelude Package.
Import PackageNotation.

From Equations Require Import Equations.
Set Equations With UIP.
Set Equations Transparent.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Derive NoConfusion for result.
Derive NoConfusion for value.
Derive NoConfusion for wsize.
Derive NoConfusion for CoqWord.word.word.
Derive EqDec for wsize.

Section Translation.

Context `{asmop : asmOp}.

Context {T} {pT : progT T}.

Context {pd : PointerData}.

Context (P : uprog).

Notation gd := (p_globs P).

(* Tactic to deal with Let _ := _ in _ = ok _ in assumption h *)
(* x and hx are introduced names for the value and its property *)
Ltac jbind h x hx :=
  eapply rbindP ; [| exact h ] ;
  clear h ; intros x hx h ;
  cbn beta in h.

Notation " 'array " := (chMap 'int ('word U8)) (at level 2) : package_scope.
Notation " 'array " := (chMap 'int ('word U8)) (in custom pack_type at level 2).
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (at level 2) : package_scope.
Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (in custom pack_type at level 2).

Parameter mem_index : nat.
Definition mem_loc : Location := ('mem ; mem_index).

Definition encode (t : stype) : choice_type :=
  match t with
  | sbool => 'bool
  | sint => 'int
  | sarr n => 'array
  | sword n => 'word n
  end.

Definition embed {t} : sem_t t → encode t :=
  match t with
  | sbool => λ x, x
  | sint => λ x, x
  | sarr n => λ x, Mz.fold (λ k v m, setm m k v) x.(WArray.arr_data) emptym
  | sword n => λ x, x
  end.

Lemma elementsNIn :
  ∀ (T : Type) (k : Z) (v : T) (m : Mz.Map.t T),
    Mz.get m k = None →
    ~ List.In (k, v) (Mz.elements m).
Proof.
  intros S k v m H contra.
  apply Mz.elementsIn in contra.
  rewrite H in contra.
  discriminate.
Qed.

Lemma In_rcons {A} x y (l : seq A) :
  List.In x (rcons l y) →
  y = x ∨ List.In x l.
Proof.
  intro h.
  induction l in h |- *. all: simpl in *. all: intuition subst.
Qed.

Lemma NIn_rcons {A} x y (l : seq A) :
  ~ List.In x (rcons l y) →
  y ≠ x ∧ ~ List.In x l.
Proof.
  induction l; intros; simpl in *; intuition subst.
Qed.

Lemma foldl_In_uniq {S : eqType} (k : Mz.K.t) (v : S) (data : seq (Mz.K.t * S)) :
  List.In (k, v) data →
  @uniq Mz.K.t [seq i.1 | i <- data] →
  foldl (λ (a : {fmap Mz.K.t → S}) (kv : Mz.K.t * S), setm a kv.1 kv.2) emptym data k = Some v.
Proof.
  intros.
  replace data with (rev (rev data)) in * by apply revK.
  set (data' := rev data) in *.
  induction data'.
  - easy.
  - rewrite rev_cons.
    rewrite rev_cons in H.
    apply In_rcons in H.
    rewrite foldl_rcons.
    destruct H.
    + subst. simpl.
      rewrite setmE.
      rewrite eq_refl.
      reflexivity.
    + rewrite rev_cons in H0.
      rewrite map_rcons in H0.
      rewrite rcons_uniq in H0.
      move: H0 => /andP [H1 H2].
      move: H1 => /in_map H3.
      assert (negb (@eq_op Z_ordType k a.1)). {
        apply /eqP => contra; case: H3; exists (a.1, v); by move: contra <-.
      }
      rewrite setmE.
      rewrite <- negbK.
      rewrite H0.
      simpl.
      apply IHdata'; assumption.
Qed.

Lemma foldl_NIn {S : eqType} (k : Mz.K.t) (data : seq (Mz.K.t * S)) :
  (∀ w, ~ List.In (k, w) data) →
  foldl (λ (a : {fmap Mz.K.t → S}) (kv : Mz.K.t * S), setm a kv.1 kv.2) emptym data k = None.
Proof.
  intros.
  replace data with (rev (rev data)) in * by apply revK.
  set (data' := rev data) in *.
  induction data'.
  - easy.
  - rewrite rev_cons.
    rewrite rev_cons in H.
    specialize (H a.2) as H0.
    rewrite foldl_rcons.
    apply NIn_rcons in H0 as [H1].
    assert (negb (@eq_op Z_ordType k a.1)). {
      apply /eqP => contra. apply H1. move: contra ->. apply surjective_pairing. }
    rewrite setmE.
    rewrite <- negbK.
    rewrite H2.
    simpl.
    apply IHdata'.
    intros.
    specialize (H w).
    apply NIn_rcons in H. easy.
Qed.

Lemma fold_get {S : eqType} (data : Mz.Map.t S) i :
  Mz.fold (λ k v m, setm m k v) data emptym i = Mz.get data i.
Proof.
  rewrite Mz.foldP.
  destruct Mz.get eqn:E.
  - set (kv := (i, s)).
    replace i with kv.1 in * by reflexivity.
    replace s with kv.2 in * by reflexivity.
    apply Mz.elementsIn in E. subst kv.
    apply foldl_In_uniq.
    + assumption.
    + apply Mz.elementsU.
  - apply foldl_NIn.
    intros.
    apply elementsNIn.
    assumption.
Qed.

Definition unembed {t : stype} : encode t → sem_t t :=
  match t return encode t → sem_t t with
  | sbool => λ x, x
  | sint => λ x, x
  | sarr n => λ x,
    match
      foldr
        (λ kv m, Let m' := m in WArray.set m' AAscale kv.1 kv.2)
        (Ok _ (WArray.empty _)) x
    with
    | Ok ar => ar
    | _ => WArray.empty _
    end
  | sword n => λ x, x
  end.

Fixpoint nat_of_ident (id : Ident.ident) : nat :=
  match id with
  | EmptyString => 1
  | String a s => 256 * nat_of_ident s + (Ascii.nat_of_ascii a)
  end.

(* injection *)
Definition nat_of_fun_ident (f : funname) (id : Ident.ident) : nat :=
  3^(nat_of_pos f) * 2^(nat_of_ident id).

Definition translate_var (f : funname) (x : var) : Location :=
  (encode x.(vtype) ; nat_of_fun_ident f x.(vname)).

Definition typed_code :=
  ∑ (a : choice_type), raw_code a.

#[local] Definition unsupported : typed_code :=
  ('unit ; assert false).

Lemma truncate_val_type :
  ∀ ty v v',
    truncate_val ty v = ok v' →
    type_of_val v' = ty.
Proof.
  intros ty v v' e.
  unfold truncate_val in e.
  jbind e x ev. noconf e.
  apply type_of_to_val.
Qed.

(* from pkg_invariants *)
Definition cast_ct_val {t t' : choice_type} (e : t = t') (v : t) : t'.
Proof.
  subst. auto.
Defined.

Lemma cast_ct_val_K :
  ∀ t e v,
    @cast_ct_val t t e v = v.
Proof.
  intros t e v.
  assert (e = erefl).
  { apply eq_irrelevance. }
  subst. reflexivity.
Qed.

Equations? coerce_to_choice_type (t : choice_type) {tv : choice_type} (v : tv) : t :=
  @coerce_to_choice_type t tv v with inspect (tv == t) := {
    | @exist true e => cast_ct_val _ v
    | @exist false e => chCanonical t
    }.
Proof.
  symmetry in e.
  move: e => /eqP e. subst. reflexivity.
Qed.

Definition truncate_chWord {t : choice_type} (n : wsize) : t → 'word n :=
  match t with
  | chWord m =>
      λ w,
        match truncate_word n w with
        | Ok w' => w'
        | _ => chCanonical _
        end
  | _ => λ x, chCanonical _
  end.

Definition truncate_el {t : choice_type} (s : stype) : t → encode s :=
  match s return t → encode s with
  | sbool => λ b, coerce_to_choice_type 'bool b
  | sint => λ i, coerce_to_choice_type 'int i
  | sarr n =>
      (* Here we do not perform the check on the length of the array as
        performed by to_arr n.
      *)
      λ a, coerce_to_choice_type 'array a
  | sword n =>
      λ w, truncate_chWord n w
  end.

Definition translate_to_pointer {t : choice_type} (c : t) : 'word Uptr :=
  truncate_el (sword Uptr) c.

Definition truncate_code (s : stype) (c : typed_code) : typed_code :=
  (encode s ; x ← c.π2 ;; ret (truncate_el s x)).

Definition cast_typed_code (t' : choice_type) (c : typed_code) (e : c.π1 = t') :
  raw_code t'.
Proof.
  subst. exact (projT2 c).
Defined.

Lemma cast_typed_code_K :
  ∀ t c e,
    @cast_typed_code t (t ; c) e = c.
Proof.
  intros t c e.
  assert (e = erefl).
  { apply eq_irrelevance. }
  subst. reflexivity.
Qed.

Equations? coerce_typed_code (ty : choice_type) (tc : typed_code) : raw_code ty :=
  @coerce_typed_code ty tc with inspect (tc.π1 == ty) := {
    | @exist true e => @cast_typed_code ty tc _
    | @exist false e => ret (chCanonical ty)
    }.
Proof.
  symmetry in e.
  move: e => /eqP e. subst. reflexivity.
Qed.

Lemma coerce_typed_code_neq :
  ∀ (ty ty' : choice_type) c,
    ty ≠ ty' →
    coerce_typed_code ty' (ty ; c) = ret (chCanonical _).
Proof.
  intros ty ty' c ne.
  funelim (coerce_typed_code ty' (ty ; c)).
  1:{
    clear - e ne. symmetry in e. move: e => /eqP e. simpl in e. contradiction.
  }
  symmetry. assumption.
Qed.

Lemma coerce_typed_code_K :
  ∀ (ty : choice_type) c,
    coerce_typed_code ty (ty ; c) = c.
Proof.
  intros ty c.
  funelim (coerce_typed_code ty (ty ; c)).
  2:{
    clear - e. symmetry in e. move: e => /eqP e. simpl in e. contradiction.
  }
  rewrite <- Heqcall.
  apply cast_typed_code_K.
Qed.

Definition typed_chElement :=
  pointed_value.

Definition choice_type_of_val (val : value) : choice_type :=
  encode (type_of_val val).

Definition translate_value (v : value) : choice_type_of_val v.
Proof.
  destruct v as [b | z | size a | size wd | undef_ty].
  - apply embed. exact b.
  - apply embed. exact z.
  - apply embed. exact a.
  - apply embed. exact wd.
  - apply chCanonical.
    (* It shouldn't matter which value we pick, because when coercing an undef
       value at type ty back to ty via to_{bool,int,word,arr} (defined in
       values.v), all of these functions raise an error on Vundef. *)
Defined.

Definition translate_write_var (fn : funname) (x : var_i) (v : typed_code) :=
  let l := translate_var fn (v_var x) in
  x ← (truncate_code x.(vtype) v).π2 ;;
  #put l := x ;;
  ret tt.

Definition translate_get_var (f : funname) (x : var) : raw_code (encode x.(vtype)) :=
  x ← get (translate_var f x) ;; ret x.

(* TW: We can remove it right? *)
Fixpoint satisfies_globs (globs : glob_decls) : heap * heap → Prop.
Proof.
  exact (λ '(x, y), False). (* TODO *)
Defined.

(* Fixpoint collect_globs (globs : glob_decls) : seq Location.
Proof.
  exact [::]. (* TODO *)
Defined. *)

Definition translate_gvar (f : funname) (x : gvar) : raw_code (encode x.(gv).(vtype)) :=
  if is_lvar x
  then translate_get_var f x.(gv).(v_var)
  else
    match get_global gd x.(gv).(v_var) with
    | Ok v => ret (coerce_to_choice_type _ (translate_value v))
    | _ => ret (chCanonical _)
    end.

Definition chArray_get ws (a : 'array) ptr scale :=
  (* Jasmin fails if ptr is not aligned; we may not need it. *)
  (* if negb (is_align ptr sz) then chCanonical ws else *)
  let f k :=
    match a (ptr * scale + k)%Z with (* BSH: maybe abstract this matchee with chArray_get8? *)
    | None => chCanonical ('word U8)
    | Some x => x
    end
  in
  let l := map f (ziota 0 (wsize_size ws)) in
  Jasmin.memory_model.LE.decode ws l.

Definition chArray_get_sub ws len (a : 'array) ptr scale :=
  let size := arr_size ws len in
  let start := (ptr * scale)%Z in
  if (0 <=? start)%Z (* && (start + size <=? ) *)
  then (
    foldr (λ (i : Z) (data : 'array),
      match assoc a (start + i)%Z with
      | Some w => setm data i w
      | None => data
      end
    ) emptym (ziota 0 size)
  )
  else chCanonical 'array.

Definition totc (ty : choice_type) (c : raw_code ty) : typed_code :=
  (ty ; c).

Definition chRead ptr ws : raw_code ('word ws) :=
  (* memory as array *)
  mem ← get mem_loc ;;
  let f k :=
    match mem (ptr + (wrepr Uptr k))%R with
    | None => chCanonical ('word U8)
    | Some x => x
    end
  in
  let l := map f (ziota 0 (wsize_size ws)) in
  ret (Jasmin.memory_model.LE.decode ws l).

(* Following sem_pexpr *)
Fixpoint translate_pexpr (fn : funname) (e : pexpr) {struct e} : typed_code :=
  match e with
  | Pconst z => totc 'int (@ret 'int z) (* Why do we need to give 'int twice? *)
  | Pbool b => totc 'bool (ret b)
  | Parr_init n =>
    (* Parr_init only gets produced by ArrayInit() in jasmin source. *)
    (* The EC export asserts false on it. *)
    totc 'array (ret emptym)
  | Pvar v => totc _ (translate_gvar fn v)
  | Pget aa ws x e =>
    totc ('word ws) (
      arr ← translate_gvar fn x ;; (* Performs the lookup in gd *)
      let a := coerce_to_choice_type 'array arr in
      i ← (truncate_code sint (translate_pexpr fn e)).π2 ;; (* to_int *)
      let scale := mk_scale aa ws in
      ret (chArray_get ws a i scale)
    )
  | Psub aa ws len x e =>
    totc 'array (
      arr ← translate_gvar fn x ;; (* Performs the lookup in gd *)
      let a := coerce_to_choice_type 'array arr in
      i ← (truncate_code sint (translate_pexpr fn e)).π2 ;; (* to_int *)
      let scale := mk_scale aa ws in
      ret (chArray_get_sub ws len a i scale)
    )
  | Pload sz x e =>
    totc ('word sz) (
      w ← translate_get_var fn x ;;
      let w1 : word _ := truncate_el (sword Uptr) w in
      w2 ← (truncate_code (sword Uptr) (translate_pexpr fn e)).π2 ;;
      ww ← chRead (w1 + w2)%R sz ;;
      ret (truncate_el (sword sz) ww)
    )
  | Papp1 o e =>
    totc _ (
      (* We truncate and call sem_sop1_typed instead of calling sem_sop1
        which does the truncation and then calls sem_sop1_typed.
      *)
      x ← (truncate_code (type_of_op1 o).1 (translate_pexpr fn e)).π2 ;;
      ret (embed (sem_sop1_typed o (unembed x)))
    )
  | Papp2 o e1 e2 =>
    totc _ (
      (* Same here *)
      r1 ← (truncate_code (type_of_op2 o).1.1 (translate_pexpr fn e1)).π2 ;;
      r2 ← (truncate_code (type_of_op2 o).1.2 (translate_pexpr fn e2)).π2 ;;
      ret match sem_sop2_typed o (unembed r1) (unembed r2) with
      | Ok y => embed y
      | _ => chCanonical _
      end
    )
  | PappN op es => unsupported
  | Pif t eb e1 e2 =>
    totc _ (
      b ← (truncate_code sbool (translate_pexpr fn eb)).π2 ;; (* to_bool *)
      if b
      then (truncate_code t (translate_pexpr fn e1)).π2
      else (truncate_code t (translate_pexpr fn e2)).π2
    )
  end.

(*   (* | Pget aa ws x e => *)
    exists 'word ws.
    (* Look up x amongst the evm part of the estate and the globals gd. Monadic
       Let because we might find None. If (Some val) is found, fail with type
       error unless (val = Varr n t). We obtain (n: positive) and (t: array n). *)
  (*     Let (n, t) := gd, s.[x] in *)

    pose (x' := translate_gvar fn x).
    pose (arr := y ← x'.π2 ;; @ret _ (coerce_to_choice_type 'array y)).

  (* Evaluate the indexing expression `e` and coerce it to Z. *)
  (*     Let i := sem_pexpr s e >>= to_int in *)
    pose (i := coerce_typed_code 'int (translate_pexpr fn e)).

  (* The actual array look-up, where
       WArray.get aa ws t i = CoreMem.read t a (i * (mk_scale aa ws)) ws
     and
       mk_scale = (if aa == AAscale then (ws/8) else 1) *)

  (*     Let w := WArray.get aa ws t i in *)
    pose (scale := mk_scale aa ws).

    exact (a ← arr ;; ptr ← i ;; ret (chArray_get ws a ptr scale)). *)

  (* | PappN op es => *)
    (*   Let vs := mapM (sem_pexpr s) es in *)
    (*   sem_opN op vs *)
    (* pose (vs := map (translate_pexpr fn) l).
    pose proof (sem_opN_typed o) as f. simpl in f. *)

(* Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T := *)
(*   match ts return sem_prod ts (exec T) → values → exec T with *)
(*   | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error *)
(*   | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values), *)
(*     if vs is v :: vs *)
(*     then Let v := of_val t v in app_sopn (o v) vs *)
(*     else type_error *)
(*   end. *)

    (* pose (vs' := fold (fun x => y ← x ;; unembed y) f vs). *)

Definition translate_write {n} (p : word Uptr) (w : word n) : raw_code 'unit :=
  (* For now we do not worry about alignment *)
  unsupported.π2. (* Do we really have to slice the word into 8bit parts? *)

Definition translate_write_lval (fn : funname) (l : lval) (v : typed_code)
  : raw_code 'unit
  :=
  match l with
  | Lnone _ ty => ret tt
  | Lvar x => translate_write_var fn x v
  | Lmem sz x e =>
    vx' ← translate_get_var fn x ;;
    let vx : word _ := translate_to_pointer vx' in
    ve' ← (translate_pexpr fn e).π2 ;;
    let ve := translate_to_pointer ve' in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *) (* Is it from us or them? *)
    v ← v.π2 ;;
    let w := truncate_chWord sz v in
    translate_write p w
  | Laset aa ws x i =>
    (* Let (n,t) := s.[x] in is a notation calling on_arr_varr on get_var *)
    (* We just cast it since we do not track lengths *)
    t' ← translate_get_var fn x ;;
    let t := coerce_to_choice_type 'array t' in
    i ← (truncate_code sint (translate_pexpr fn i)).π2 ;; (* to_int *)
    v ← v.π2 ;;
    let v := truncate_chWord ws v in
    (* let t := setm t i v in *) (* WArray.set also calls write *)
    unsupported.π2
  | Lasub aa ws len x i =>
    (* Same observation as Laset *)
    t' ← translate_get_var fn x ;;
    let t := coerce_to_choice_type 'array t' in
    (* Again, we ignore the length *)
    (* Let t' := to_arr (Z.to_pos (arr_size ws len)) v in *)
    unsupported.π2
  (* | Laset aa ws x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t aa i v in
    write_var x (@to_val (sarr n) t) s *)
  (* | Lasub aa ws len x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in
    Let t := @WArray.set_sub n aa ws len t i t' in
    write_var x (@to_val (sarr n) t) s *)
  end.

Definition instr_d (i : instr) : instr_r :=
  match i with MkI _ i => i end.

Fixpoint translate_instr_r (fn : funname) (i : instr_r) {struct i} : raw_code 'unit
with translate_instr (fn : funname) (i : instr) {struct i} : raw_code 'unit.
Proof.
  (* translate_instr_r *)
  {
    pose proof (translate_cmd :=
            (fix translate_cmd (fn : funname) (c : cmd) : raw_code 'unit :=
               match c with
               | [::] => ret tt
               | i :: c => translate_instr fn i ;; translate_cmd fn c
               end)).

    destruct i as [ | | e c1 c2 | | | ].
    - (* Cassgn *)
      (* l :a=_s p *)
      pose (translate_pexpr fn p) as tr_p.
      pose (truncate_code s tr_p) as tr_p'.
      exact (translate_write_lval fn l tr_p').
    - exact (unsupported.π2). (* Copn *)
    - (* Cif e c1 c2 *)
      pose (e' := translate_pexpr fn e).
      pose (c1' := translate_cmd fn c1).
      pose (c2' := translate_cmd fn c2).
      pose (rb := coerce_typed_code 'bool e').
      exact (b ← rb ;; if b then c1' else c2').
    - exact (unsupported.π2). (* Cfor *)
    - exact (unsupported.π2). (* Cwhile *)
    - (* Ccall i l f l0 *)
      (* translate arguments *)
      pose (map (translate_pexpr fn) l0) as tr_l0.
      (* "perform" the call via `opr` *)
      (* probably we'd look up the function signature in the current ambient program *)

      (* write_lvals the result of the call into lvals `l` *)

      exact (unsupported.π2).
  }
  (* translate_instr *)
  {
    exact (translate_instr_r fn (instr_d i)).
  }
Defined.

Fixpoint translate_cmd (fn : funname) (c : cmd) : raw_code 'unit :=
  match c with
  | [::] => ret tt
  | i :: c => translate_instr fn i ;; translate_cmd fn c
  end.

Record fdef := {
  ffun : typed_raw_function ;
  locs : {fset Location} ;
  imp : Interface ;
  exp : Interface
}.

Definition translate_fundef (fd : _ufun_decl (* extra_fun_t *)) : funname * fdef.
Proof.
  destruct fd. destruct _f.
  split. 1: exact f.
  constructor.
  - exists chUnit. exists chUnit.
    intros u.
    (* TODO: store function arguments in their locations *)
    exact (translate_cmd f f_body).
    (* TODO: read return values from their locations *)
  - exact fset0.
  - exact [interface].
  - exact [interface].
Defined.

Definition ssprove_prog := seq (funname * fdef).

Definition translate_prog (p : uprog) : ssprove_prog :=
  (* let globs := collect_globs (p_globs p) in *)
  let fds := map translate_fundef (p_funcs p) in
  fds.

Fixpoint lchtuple (ts : seq choice_type) : choice_type :=
  match ts with
  | [::] => 'unit
  | [:: t1 ] => t1
  | t1 :: ts => t1 × (lchtuple ts)
  end.

Definition get_fundef_ssp (sp : seq (funname * fdef)) (fn : funname) (dom cod : choice_type) :
  option (dom → raw_code cod).
Proof.
  exact None. (* TODO *)
Defined.

Lemma eq_rect_r_K :
  ∀ (A : eqType) (x : A) (P : A → Type) h e,
    @eq_rect_r A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

Lemma translate_value_to_val :
  ∀ (s : stype) (v : sem_t s),
    translate_value (to_val v) = eq_rect_r encode (embed v) (type_of_to_val v).
Proof.
  intros s v.
  destruct s as [| | size | size].
  all: simpl ; rewrite eq_rect_r_K ; reflexivity.
Qed.

Fixpoint type_of_values vs : choice_type :=
  match vs with
  | [::] => 'unit
  | [:: v ] => choice_type_of_val v
  | hd :: tl => choice_type_of_val hd × type_of_values tl
  end.

(* lchtuple (map choice_type_of_val vs) *)

Definition translate_values (vs : seq value) :
  lchtuple (map choice_type_of_val vs).
Proof.
  induction vs as [| v vs tr_vs].
  - exact tt.
  - destruct vs as [| v' vs'].
    + exact (translate_value v).
    + exact (translate_value v, tr_vs).
Defined.

Definition translate_ptr (ptr : pointer) : Location :=
  ('word U8 ; (5 ^ Z.to_nat (wunsigned ptr))%nat).

Definition rel_mem (m : mem) (h : heap) :=
  ∀ ptr v,
    (* mem as array model: *)
    read m ptr U8 = ok v →
    (get_heap h mem_loc) ptr = Some v.
    (* mem as locations model: *)
    (* get_heap h (translate_ptr ptr) = *)
    (* coerce_to_choice_type _ (translate_value (@to_val (sword U8) v)). *)

#[local] Open Scope vmap_scope.

Definition rel_vmap (vm : vmap) (fn : funname) (h : heap) :=
  ∀ (i : var) v,
    vm.[i] = ok v →
    get_heap h (translate_var fn i) = coerce_to_choice_type _ (embed v).

Definition rel_estate (s : estate) (fn : funname) (h : heap) :=
  rel_mem s.(emem) h ∧ rel_vmap s.(evm) fn h.

Lemma coerce_cast_code (ty vty : choice_type) (v : vty) :
  ret (coerce_to_choice_type ty v) = coerce_typed_code ty (vty ; ret v).
Proof.
  simpl.
  funelim (coerce_to_choice_type ty v) ;
  funelim (coerce_typed_code t (tv ; ret v)).
  - rewrite <- Heqcall, <- Heqcall0.
    pose proof e as e'. symmetry in e'.
    move: e' => /eqP e'. subst.
    rewrite cast_ct_val_K.
    rewrite cast_typed_code_K. reflexivity.
  - simpl in *. congruence.
  - simpl in *. congruence.
  - rewrite <- Heqcall, <- Heqcall0.
    reflexivity.
Qed.

Lemma coerce_to_choice_type_neq :
  ∀ (ty ty' : choice_type) (v : ty),
    ty ≠ ty' →
    coerce_to_choice_type ty' v = chCanonical _.
Proof.
  intros ty ty' v ne.
  funelim (coerce_to_choice_type ty' v).
  1:{
    clear - e ne. symmetry in e. move: e => /eqP e. simpl in e. contradiction.
  }
  symmetry. assumption.
Qed.

Lemma coerce_to_choice_type_K :
  ∀ (t : choice_type) (v : t),
    coerce_to_choice_type t v = v.
Proof.
  intros t v.
  funelim (coerce_to_choice_type t v).
  2:{ clear - e. rewrite eqxx in e. discriminate. }
  rewrite <- Heqcall.
  apply cast_ct_val_K.
Qed.

(* Unary judgment concluding on evaluation of program *)

Definition eval_jdg {A : choiceType}
  (pre : heap → Prop) (post : heap → Prop)
  (c : raw_code A) (v : A) :=
  ⊢ ⦃ λ '(h₀, h₁), pre h₀ ⦄
    c ≈ ret v
  ⦃ λ '(a₀, h₀) '(a₁, h₁), post h₀ ∧ a₀ = a₁ ∧ a₁ = v ⦄.

Notation "⊢ ⦃ pre ⦄ c ⇓ v ⦃ post ⦄" :=
  (eval_jdg pre post c v)
  (format "⊢  ⦃  pre  ⦄ '/  '  '[' c  ']' '/' ⇓ '/  '  '[' v  ']' '/' ⦃  post  ⦄")
  : package_scope.

Lemma u_ret :
  ∀ {A : choiceType} (v v' : A) (p q : heap → Prop),
    (∀ hp, p hp → q hp ∧ v = v') →
    ⊢ ⦃ p ⦄ ret v ⇓ v' ⦃ q ⦄.
Proof.
  intros A v v' p q h.
  unfold eval_jdg.
  apply r_ret.
  intros hp hp' hhp.
  specialize (h hp).
  intuition eauto.
Qed.

Lemma u_ret_eq :
  ∀ {A : choiceType} (v : A) (p q : heap → Prop),
    (∀ hp, p hp → q hp) →
    ⊢ ⦃ p ⦄ ret v ⇓ v ⦃ q ⦄.
Proof.
  intros A v p q h.
  apply u_ret. intuition eauto.
Qed.

Lemma u_bind :
  ∀ {A B : choiceType} m f v₁ v₂ (p q r : heap → Prop),
    ⊢ ⦃ p ⦄ m ⇓ v₁ ⦃ q ⦄ →
    ⊢ ⦃ q ⦄ f v₁ ⇓ v₂ ⦃ r ⦄ →
    ⊢ ⦃ p ⦄ @bind A B m f ⇓ v₂ ⦃ r ⦄.
Proof.
  intros A B m f v₁ v₂ p q r hm hf.
  unfold eval_jdg.
  change (ret v₂) with (ret v₁ ;; ret v₂).
  eapply r_bind.
  - exact hm.
  - intros a₀ a₁.
    eapply rpre_hypothesis_rule.
    intuition subst.
    eapply rpre_weaken_rule.
    1: apply hf.
    simpl. intuition subst. assumption.
Qed.

(* Unary variant of set_lhs *)
Definition u_set_pre (ℓ : Location) (v : ℓ) (pre : heap → Prop): heap → Prop :=
  λ m, ∃ m', pre m' ∧ m = set_heap m' ℓ v.

Lemma u_put :
  ∀ {A : choiceType} (ℓ : Location) (v : ℓ) (r : raw_code A) (v' : A) p q,
    ⊢ ⦃ u_set_pre ℓ v p ⦄ r ⇓ v' ⦃ q ⦄ →
    ⊢ ⦃ p ⦄ #put ℓ := v ;; r ⇓ v' ⦃ q ⦄.
Proof.
  intros A ℓ v r v' p q h.
  eapply r_put_lhs with (pre := λ '(_,_), _).
  eapply rpre_weaken_rule. 1: eapply h.
  intros m₀ m₁ hm. simpl.
  destruct hm as [m' hm].
  exists m'. exact hm.
Qed.

(* Unary variant of inv_conj (⋊) *)
Definition u_pre_conj (p q : heap → Prop) : heap → Prop :=
  λ m, p m ∧ q m.

Notation "p ≪ q" :=
  (u_pre_conj p q) (at level 19, left associativity) : package_scope.

(* Unary variant of rem_lhs *)
Definition u_get (ℓ : Location) (v : ℓ) : heap → Prop :=
  λ m, get_heap m ℓ = v.

Lemma u_get_remember :
  ∀ (A : choiceType) (ℓ : Location) (k : ℓ → raw_code A) (v : A) p q,
    (∀ x, ⊢ ⦃ p ≪ u_get ℓ x ⦄ k x ⇓ v ⦃ q ⦄) →
    ⊢ ⦃ p ⦄ x ← get ℓ ;; k x ⇓ v ⦃ q ⦄.
Proof.
  intros A ℓ k v p q h.
  eapply r_get_remember_lhs with (pre := λ '(_,_), _).
  intro x.
  eapply rpre_weaken_rule. 1: eapply h.
  simpl. intuition eauto.
Qed.

(* Unary rpre_weaken_rule *)
Lemma upre_weaken_rule :
  ∀ A (r : raw_code A) v (p1 p2 : heap → Prop) q,
    ⊢ ⦃ p1 ⦄ r ⇓ v ⦃ q ⦄ →
    (∀ h, p2 h → p1 h) →
    ⊢ ⦃ p2 ⦄ r ⇓ v ⦃ q ⦄.
Proof.
  intros A r v p1 p2 q h hp.
  eapply rpre_weaken_rule.
  - eapply h.
  - intros. apply hp. assumption.
Qed.

(* Unary rpost_weaken_rule *)
Lemma upost_weaken_rule :
  ∀ A (r : raw_code A) v p (q1 q2 : heap → Prop),
    ⊢ ⦃ p ⦄ r ⇓ v ⦃ q1 ⦄ →
    (∀ h, q1 h → q2 h) →
    ⊢ ⦃ p ⦄ r ⇓ v ⦃ q2 ⦄.
Proof.
  intros A r v p q1 q2 h hq.
  eapply rpost_weaken_rule.
  - eapply h.
  - intros [] []. intuition eauto.
Qed.

Lemma coerce_to_choice_type_translate_value_to_val :
  ∀ ty (v : sem_t ty),
    coerce_to_choice_type (encode ty) (translate_value (to_val v)) =
    embed v.
Proof.
  intros ty v.
  destruct ty.
  all: simpl. all: rewrite coerce_to_choice_type_K. all: reflexivity.
Qed.

Lemma translate_get_var_correct :
  ∀ fn x s v (cond : heap → Prop),
    get_var (evm s) x = ok v →
    (∀ m, cond m → rel_estate s fn m) →
    ⊢ ⦃ cond ⦄
      translate_get_var fn x ⇓ coerce_to_choice_type _ (translate_value v)
    ⦃ cond ⦄.
Proof.
  intros fn x s v cond ev hcond.
  unfold translate_get_var.
  eapply u_get_remember. intros vx.
  eapply u_ret. intros m [hm hx].
  split. 1: assumption.
  unfold u_get in hx. unfold get_var in ev.
  eapply on_vuP. 3: exact ev. 2: discriminate.
  intros sx esx esv.
  eapply hcond in hm. eapply hm in esx. subst.
  rewrite coerce_to_choice_type_translate_value_to_val.
  rewrite esx. rewrite coerce_to_choice_type_K. reflexivity.
Qed.

Lemma translate_gvar_correct (f : funname) (x : gvar) (v : value) s (cond : heap → Prop) :
  get_gvar gd (evm s) x = ok v →
  (∀ m, cond m → rel_estate s f m) →
  ⊢ ⦃ cond ⦄
    translate_gvar f x ⇓ coerce_to_choice_type _ (translate_value v)
  ⦃ cond ⦄.
Proof.
  intros ev hcond.
  unfold translate_gvar.
  unfold get_gvar in ev.
  destruct is_lvar.
  - eapply translate_get_var_correct. all: eassumption.
  - rewrite ev.
    apply u_ret. intros m hm.
    split. 1: assumption.
    reflexivity.
Qed.

Lemma translate_of_val :
  ∀ ty v v',
    of_val ty v = ok v' →
    truncate_el ty (translate_value v) =
    coerce_to_choice_type (encode ty) (translate_value (to_val v')).
Proof.
  intros ty v v' e.
  destruct ty, v. all: simpl in e. all: try discriminate.
  all: try solve [
    lazymatch type of e with
    | match ?t with _ => _ end = _ => destruct t ; discriminate
    end
  ].
  - noconf e. simpl. rewrite !coerce_to_choice_type_K. reflexivity.
  - noconf e. simpl. rewrite !coerce_to_choice_type_K. reflexivity.
  - simpl. rewrite !coerce_to_choice_type_K.
    unfold WArray.cast in e. destruct (_ <=? _)%Z. 2: discriminate.
    noconf e. simpl. reflexivity.
  - simpl. rewrite !coerce_to_choice_type_K.
    rewrite e. reflexivity.
Qed.

Lemma translate_truncate_val :
  ∀ ty v v',
    truncate_val ty v = ok v' →
    truncate_el ty (translate_value v) =
    coerce_to_choice_type (encode ty) (translate_value v').
Proof.
  intros ty v v' h.
  unfold truncate_val in h.
  jbind h vx e. noconf h.
  apply translate_of_val. assumption.
Qed.

Lemma translate_to_bool :
  ∀ v b,
    to_bool v = ok b →
    coerce_to_choice_type 'bool (translate_value v) = b.
Proof.
  intros v b e.
  destruct v as [| | | | t]. all: try discriminate.
  2:{ destruct t. all: discriminate. }
  simpl in e. noconf e.
  rewrite coerce_to_choice_type_K. reflexivity.
Qed.

Lemma translate_to_int :
  ∀ v z,
    to_int v = ok z →
    coerce_to_choice_type 'int (translate_value v) = z.
Proof.
  intros v z e.
  destruct v as [| | | | t]. all: try discriminate.
  2:{ destruct t. all: discriminate. }
  simpl in e. noconf e.
  rewrite coerce_to_choice_type_K. reflexivity.
Qed.

Lemma translate_truncate_code :
  ∀ (c : typed_code) (ty : stype) v v' p q,
    truncate_val ty v =  ok v' →
    c.π1 = choice_type_of_val v →
    ⊢ ⦃ p ⦄ c.π2 ⇓ coerce_to_choice_type _ (translate_value v) ⦃ q ⦄ →
    ⊢ ⦃ p ⦄ (truncate_code ty c).π2 ⇓ coerce_to_choice_type _ (translate_value v') ⦃ q ⦄.
Proof.
  intros c ty v v' p q hv e h.
  destruct c as [ty' c]. simpl in *. subst.
  eapply u_bind. 1: eapply h.
  eapply u_ret. intros m hm.
  split. 1: assumption.
  rewrite coerce_to_choice_type_K.
  apply translate_truncate_val. assumption.
Qed.

Lemma translate_pexpr_type fn s₁ e v :
  sem_pexpr gd s₁ e = ok v →
  (translate_pexpr fn e).π1 = choice_type_of_val v.
Proof with try discriminate; simpl in *.
  intros.
  revert v H.
  destruct e; intros; simpl in *.
  1-3: noconf H; reflexivity.
  - eapply type_of_get_gvar in H.
    unfold choice_type_of_val.
    rewrite H.
    unfold translate_gvar.
    reflexivity.
  - simpl in H.
    destruct get_gvar...
    + destruct v0...
      destruct sem_pexpr...
      destruct v0...
      * destruct WArray.get...
        noconf H.
        reflexivity.
      * destruct t...
  - destruct get_gvar...
    destruct v0...
    destruct sem_pexpr...
    destruct v0...
    * destruct WArray.get_sub...
      noconf H.
      reflexivity.
    * destruct t...
  - destruct get_var...
    destruct to_pointer...
    destruct sem_pexpr...
    destruct to_pointer...
    destruct read...
    noconf H. reflexivity.
  - destruct sem_pexpr...
    apply sem_sop1I in H as [].
    rewrite H0.
    unfold choice_type_of_val.
    rewrite type_of_to_val.
    reflexivity.
  - destruct (sem_pexpr _ _ e1)...
    destruct sem_pexpr...
    apply sem_sop2I in H as [? [? [? []]]].
    unfold choice_type_of_val. subst.
    by rewrite type_of_to_val.
  - admit.
  - destruct (sem_pexpr _ _ e1)...
    destruct to_bool...
    destruct (sem_pexpr _ _ e2)...
    destruct truncate_val eqn:E...
    destruct sem_pexpr...
    destruct (truncate_val s v3) eqn:E2...
    unfold truncate_val in *.
    repeat destruct of_val...
    noconf E. noconf E2.
    unfold choice_type_of_val.
    destruct b; noconf H; by rewrite type_of_to_val.
Admitted.

Lemma mapM_nil {eT aT bT} f l :
  @mapM eT aT bT f l = ok [::] →
  l = [::].
Proof.
  intro h.
  induction l in h |- *.
  - reflexivity.
  - simpl in h.
    jbind h y hy. jbind h ys hys. noconf h.
Qed.

Lemma chArray_get_correct (len : BinNums.positive) (a : WArray.array len) (z : Z) ws aa s :
  WArray.get aa ws a z = ok s →
  chArray_get ws (translate_value (Varr a)) z (mk_scale aa ws) = translate_value (Vword s).
Proof.
  intros H.
  simpl in *.
  unfold WArray.get, read in H.
  destruct is_align. 2: discriminate.
  simpl in H.
  jbind H l E. noconf H.
  unfold chArray_get.
  f_equal.
  revert l E.
  apply ziota_ind.
  - intros l E. noconf E. reflexivity.
  - intros i l E IH l0 H.
    destruct l0.
    { apply mapM_nil in H. discriminate. }
    apply mapM_cons in H as [H H0].
    simpl.
    rewrite (IH l0). 2: assumption.
    apply f_equal2. 2: reflexivity.
    unfold WArray.get8 in H.
    destruct WArray.in_bound. 2: discriminate.
    destruct WArray.is_init. 2: discriminate.
    noconf H.
    unfold odflt, oapp.
    rewrite <- fold_get.
    reflexivity.
Qed.

Lemma translate_pexpr_correct :
  ∀ fn (e : pexpr) s₁ v (cond : heap → Prop),
    sem_pexpr gd s₁ e = ok v →
    (∀ m, cond m → rel_estate s₁ fn m) →
    ⊢ ⦃ cond ⦄
      (translate_pexpr fn e).π2 ⇓
      coerce_to_choice_type _ (translate_value v)
    ⦃ cond ⦄.
Proof.
  intros fn e s1 v cond h1 hcond.
  induction e as [z|b| |x|aa ws x e| | | | | | ] in s1, v, h1, cond, hcond |- *.
  - simpl in h1. noconf h1.
    rewrite coerce_to_choice_type_K.
    apply u_ret_eq. auto.
  - simpl in h1. noconf h1.
    rewrite coerce_to_choice_type_K.
    apply u_ret_eq. auto.
  - simpl in h1. noconf h1.
    rewrite coerce_to_choice_type_K.
    apply u_ret_eq. auto.
  - simpl in h1.
    apply type_of_get_gvar in h1 as es.
    unfold translate_pexpr.
    unfold translate_gvar. unfold translate_var.
    unfold get_gvar in h1.
    destruct is_lvar eqn:hlvar.
    + destruct x as [gx gs]. simpl in *.
      unfold is_lvar in hlvar. simpl in hlvar. move: hlvar => /eqP hlvar. subst.
      unfold get_var in h1.
      unfold on_vu in h1. destruct Fv.get as [sx | e] eqn:e1.
      2:{ destruct e. all: discriminate. }
      noconf h1.
      eapply u_get_remember. simpl.
      intro v. apply u_ret.
      intros m [hm e]. unfold u_get in e. subst.
      split. 1: assumption.
      apply hcond in hm. destruct hm as [hm hv].
      apply hv in e1. rewrite e1.
      simpl. rewrite coerce_to_choice_type_K.
      rewrite coerce_to_choice_type_translate_value_to_val.
      reflexivity.
    + simpl.
      rewrite h1.
      apply u_ret. auto.
  - simpl in *.
    jbind h1 nt ent. destruct nt. all: try discriminate.
    jbind h1 i ei. jbind ei i' ei'.
    jbind h1 w ew. noconf h1.
    rewrite coerce_to_choice_type_K.
    eapply u_bind.
    + eapply translate_gvar_correct. all: eassumption.
    + rewrite !bind_assoc.
      eapply u_bind.
      * eapply IHe. all: eassumption.
      * eapply u_ret.
        intros m hm.
        split. 1: assumption.
        erewrite translate_pexpr_type. 2: eassumption.
        rewrite coerce_to_choice_type_K.
        eapply type_of_get_gvar in ent as ety. rewrite <- ety.
        rewrite !coerce_to_choice_type_K.
        erewrite translate_to_int. 2: eassumption.
        apply chArray_get_correct. assumption.
  - (* Psub *) admit.
  - (* Pload *) admit.
  - (* Papp1 *)
    simpl in *.
    jbind h1 v' h2.
    rewrite bind_assoc. simpl.
    eapply u_bind.
    + eapply IHe; eauto.
    + apply u_ret.
      intros.
      split. 1: assumption.
      unfold sem_sop1 in h1.
      jbind h1 v'' h3.
      noconf h1.
      rewrite coerce_to_choice_type_translate_value_to_val.
      apply translate_pexpr_type with (fn:=fn) in h2.
      rewrite h2.
      rewrite !coerce_to_choice_type_K.
      erewrite translate_of_val.
      2: exact h3.
      rewrite coerce_to_choice_type_translate_value_to_val.
      destruct op.
      all: try reflexivity.
      destruct o.
      all: try reflexivity.
  - (* Papp2 *) admit.
  - (* PappN TODO *) admit.
  - (* Pif *)
    simpl in h1. jbind h1 b eb. jbind eb b' eb'.
    jbind h1 v1 ev1. jbind ev1 v1' ev1'.
    jbind h1 v2 ev2. jbind ev2 v2' ev2'.
    noconf h1.
    simpl. rewrite bind_assoc.
    eapply u_bind.
    1:{ eapply IHe1. all: eauto. }
    simpl. erewrite translate_pexpr_type. 2: eassumption.
    rewrite coerce_to_choice_type_K.
    erewrite translate_to_bool. 2: eassumption.
    destruct b.
    + eapply u_bind.
      1:{ eapply IHe2. all: eauto. }
      simpl. eapply u_ret. intros m hm.
      split. 1: assumption.
      erewrite translate_pexpr_type. 2: eassumption.
      rewrite coerce_to_choice_type_K.
      apply translate_truncate_val. assumption.
    + eapply u_bind.
      1:{ eapply IHe3. all: eauto. }
      simpl. eapply u_ret. intros m hm.
      split. 1: assumption.
      erewrite translate_pexpr_type. 2: eassumption.
      rewrite coerce_to_choice_type_K.
      apply translate_truncate_val. assumption.
Admitted.

Lemma ptr_var_neq (ptr : pointer) (fn : funname) (v : var) :
  translate_ptr ptr != translate_var fn v.
Proof.
  unfold translate_ptr.
  unfold translate_var.
  unfold nat_of_fun_ident.
  apply /eqP. intro e.
  noconf e.
  apply (f_equal (λ n, n %% 3)) in H0.
Admitted.

Notation coe_cht := coerce_to_choice_type.
Notation coe_tyc := coerce_typed_code.

(* TODO MOVE *)
(* Lemma u_coerce_typed_code :
  ∀ (c : typed_code) (ty : choice_type) (v : ty) p q,
    ⊢ ⦃ p ⦄ c.π2 ⇓ coerce_to_choice_type c.π1 v ⦃ q ⦄ →
    ⊢ ⦃ p ⦄ coerce_typed_code ty c ⇓ v ⦃ q ⦄.
Proof.
  intros c ty v p q h.
  destruct c as [ty' c]. simpl in h.
  destruct (ty' == ty) eqn:e.
  all: move: e => /eqP e.
  - subst. rewrite coerce_typed_code_K. rewrite coerce_to_choice_type_K in h.
    assumption.
  - rewrite coerce_typed_code_neq. 2: assumption.
    rewrite coerce_to_choice_type_neq in h. 2: eauto.
    WRONG, should just have coercion in the conclusions, including the value
Abort. *)

Lemma injective_translate_var :
  ∀ fn, injective (translate_var fn).
Proof.
Admitted.

(* TODO Make fixpoint too! *)
Lemma translate_instr_r_correct :
  ∀ (fn : funname) (i : instr_r) (s₁ s₂ : estate),
  sem_i P s₁ i s₂ →
  ⊢ ⦃ rel_estate s₁ fn ⦄
    translate_instr_r fn i ⇓ tt
  ⦃ rel_estate s₂ fn ⦄.
Proof.
  intros fn i s₁ s₂ h.
  induction h as [es₁ es₂ y tag sty e v v' sem_e trunc hw | | | | | | |].
  - simpl. destruct y as [ | yl | | | ] eqn:case_lval.
    + simpl. apply u_ret_eq. intros hp hr.
      simpl in hw. unfold write_none in hw.
      destruct is_sbool eqn:eb.
      * unfold on_vu in hw. destruct of_val as [| []].
        all: noconf hw. all: assumption.
      * unfold on_vu in hw. destruct of_val as [| []].
        all: noconf hw. assumption.
    + simpl. unfold translate_write_var. simpl in hw. unfold write_var in hw.
      jbind hw vm eset. noconf hw.
      simpl. rewrite !bind_assoc. simpl.
      eapply u_bind.
      * eapply translate_pexpr_correct. all: eauto.
      * {
        erewrite translate_pexpr_type. 2: eassumption.
        clear sem_e tag e.
        eapply u_put.
        apply u_ret_eq.
        intros m' [m [hm e]]. subst.
        destruct hm as [hm hv].
        split.
        - unfold rel_mem.
          admit.
          (* intros ptr sz w hrw. *)
          (* rewrite get_set_heap_neq. 2: apply ptr_var_neq. *)
          (* apply hm. assumption. *)
        - simpl. unfold rel_vmap.
          intros i vi ei.
          simpl. rewrite !coerce_to_choice_type_K.
          eapply set_varP. 3: exact eset. (* all: clear eset. *)
          + intros v₁ hv₁ eyl. subst.
            destruct (i == yl) eqn:evar.
            all: move: evar => /eqP evar.
            * subst.
              rewrite Fv.setP_eq in ei. noconf ei.
              rewrite get_set_heap_eq.
              apply truncate_val_type in trunc as ety. subst.
              eapply translate_truncate_val in trunc.
              eapply translate_of_val in hv₁.
              rewrite trunc. rewrite coerce_to_choice_type_K.
              rewrite hv₁. apply coerce_to_choice_type_translate_value_to_val.
            * rewrite Fv.setP_neq in ei.
              2:{ apply /eqP. eauto. }
              rewrite get_set_heap_neq.
              2:{
                apply /eqP. intro e.
                apply injective_translate_var in e.
                contradiction.
              }
              eapply hv in ei. rewrite ei.
              rewrite coerce_to_choice_type_K. reflexivity.
          + intros hbo hyl hset.
            subst.
            destruct (i == yl) eqn:evar.
            all: move: evar => /eqP evar.
            * exfalso. subst. rewrite Fv.setP_eq in ei.
              clear - ei hbo. destruct (vtype yl). all: discriminate.
            * rewrite Fv.setP_neq in ei.
              2:{ apply /eqP. eauto. }
              rewrite get_set_heap_neq.
              2:{
                apply /eqP. intro e.
                apply injective_translate_var in e.
                contradiction.
              }
              eapply hv in ei. rewrite ei.
              rewrite coerce_to_choice_type_K. reflexivity.
      }
    + simpl. simpl in hw.
      jbind hw vx hvx. jbind hvx vx' hvx'. jbind hw ve hve.
      jbind hve ve' hve'. jbind hw w hw'. jbind hw m hm.
      noconf hw.
      eapply u_get_remember. intros tv.
      eapply u_bind.
      1:{
        eapply translate_pexpr_correct.
        - eassumption.
        - intros ? []. assumption.
      }
      rewrite bind_assoc.
      eapply u_bind.
      1:{
        eapply translate_pexpr_correct.
        - eassumption.
        - intros ? []. assumption.
      }
      simpl. admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem translate_prog_correct (p : expr.uprog) (fn : funname) m va m' vr f :
  sem.sem_call p m fn va m' vr →
  let sp := (translate_prog p) in
  let dom := lchtuple (map choice_type_of_val va) in
  let cod := lchtuple (map choice_type_of_val vr) in
  get_fundef_ssp sp fn dom cod = Some f →
  (* satisfies_globs (p_globs p) (translate_mem m, translate_mem m') -> *)
  ⊢ ⦃ satisfies_globs (p_globs p) ⦄
    f (translate_values va) ≈ ret (translate_values vr)
  ⦃ λ '(v1, s1) '(v2,s2), v1 = v2 ⦄.
Proof.
  (* intros H H1 H2 H3 H4. *)
  (* unshelve eapply sem_call_Ind. *)
  (* all: shelve_unifiable. *)
  intros H.
  set (Pfun :=
    λ (m : mem) (fn : funname) (va : seq value) (m' : mem) (vr : seq value),
      ∀ f,
        let sp := translate_prog p in
        let dom := lchtuple [seq choice_type_of_val i | i <- va] in
        let cod := lchtuple [seq choice_type_of_val i | i <- vr] in
        get_fundef_ssp sp fn dom cod = Some f ->
        (* satisfies_globs (p_globs p) (translate_mem m, translate_mem m') → *)
        ⊢ ⦃ satisfies_globs (p_globs p) ⦄
          f (translate_values va) ≈
          ret (translate_values vr)
        ⦃ λ '(v1, _) '(v2, _), v1 = v2 ⦄
  ).
  set (Pi_r :=
    λ (s1 : estate) (i : instr_r) (s2 : estate),
      ⊢ ⦃ λ '(h1,h2), False ⦄
        translate_instr_r fn i ≈ ret tt
      ⦃ λ '(v1, _) '(v2, _), True ⦄
  ).
  set (Pi := λ s1 i s2, (Pi_r s1 (instr_d i) s2)).
  set (Pc :=
    λ (s1 : estate) (c : cmd) (s2 : estate),
      ⊢ ⦃ λ '(h1,h2), False ⦄ translate_cmd fn c ≈ ret tt ⦃ λ '(v1, _) '(v2, _), True ⦄
  ).
  (* FIXME *)
  set (Pfor :=
    λ (v : var_i) (ls : seq Z) (s1 : estate) (c : cmd) (s2 : estate),
      ⊢ ⦃ λ '(h1,h2), False ⦄
        (* ssprove_for *) translate_cmd fn c ≈
        ret tt
      ⦃ λ '(v1, _) '(v2, _), True ⦄
  ).
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
           (* by eapply translate_pexpr_sound. *)
           admit.               (* by H0: sem_pexpr e = ok v *)
        -- intros.
           eapply rpre_hypothesis_rule.
           intros ? ? E.
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

End Translation.
