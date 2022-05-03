Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From Jasmin Require Import expr compiler_util values sem.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.
From Jasmin Require Import expr_facts.

From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From CoqWord Require Import ssrZ.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

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
Lemma u_pre_weaken_rule :
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
Lemma u_post_weaken_rule :
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

Definition mem_index : nat := 0.
Definition mem_loc : Location := ('mem ; mem_index).

Definition encode (t : stype) : choice_type :=
  match t with
  | sbool => 'bool
  | sint => 'int
  | sarr n => 'array
  | sword n => 'word n
  end.

Definition embed_array {len} (a : WArray.array len) : 'array :=
  Mz.fold (λ k v m, setm m k v) a.(WArray.arr_data) emptym.

Definition embed {t} : sem_t t → encode t :=
  match t with
  | sbool => λ x, x
  | sint => λ x, x
  | sarr n => embed_array
  | sword n => λ x, x
  end.

Lemma elementsNIn :
  ∀ (T : Type) (k : Z) (v : T) (m : Mz.Map.t T),
    Mz.get m k = None →
    ¬ List.In (k, v) (Mz.elements m).
Proof.
  intros S k v m H contra.
  apply Mz.elementsIn in contra.
  rewrite H in contra.
  discriminate.
Qed.

Lemma foldl_In_uniq {S : eqType} (k : Mz.K.t) (v : S) (data : seq (Mz.K.t * S)) :
  List.In (k, v) data →
  @uniq Mz.K.t [seq i.1 | i <- data] →
  foldr (λ (kv : Mz.K.t * S) (a : {fmap Mz.K.t → S}), setm a kv.1 kv.2) emptym data k = Some v.
Proof.
  intros.
  induction data.
  - easy.
  - simpl in H.
    simpl.
    destruct H.
    + subst. simpl.
      rewrite setmE.
      rewrite eq_refl.
      reflexivity.
    + move: H0 => /andP [H1 H2].
      move: H1 => /in_map H3.
      assert (negb (@eq_op Z_ordType k a.1)). {
        apply /eqP => contra; case: H3; exists (a.1, v); by move: contra <-.
      }
      rewrite setmE.
      rewrite <- negbK.
      rewrite H0.
      simpl.
      apply IHdata; assumption.
Qed.

Lemma foldl_NIn {S : eqType} (k : Mz.K.t) (data : seq (Mz.K.t * S)) :
  (∀ w, ¬ List.In (k, w) data) →
  foldr (λ (kv : Mz.K.t * S) (a : {fmap Mz.K.t → S}), setm a kv.1 kv.2) emptym data k = None.
Proof.
  intros.
  induction data.
  - easy.
  - specialize (H a.2) as H0.
    simpl. apply List.not_in_cons in H0 as [H0 H1].
    assert (negb (@eq_op Z_ordType k a.1)). {
      apply /eqP => contra. apply H0. move: contra ->. symmetry. apply surjective_pairing. }
    rewrite setmE.
    rewrite <- negbK.
    rewrite H2.
    simpl.
    apply IHdata.
    intros.
    specialize (H w).
    apply List.not_in_cons in H. easy.
Qed.

Lemma rev_list_rev {S} :
  ∀ (l : seq S), List.rev l = rev l.
Proof.
  induction l; intuition subst; simpl.
  rewrite rev_cons. rewrite IHl. rewrite <- cats1. reflexivity.
Qed.

Lemma fold_get {S : eqType} (data : Mz.Map.t S) i :
  Mz.fold (λ k v m, setm m k v) data emptym i = Mz.get data i.
Proof.
  rewrite Mz.foldP.
  replace (Mz.elements data) with (rev (rev (Mz.elements data))). 2: by rewrite revK.
  rewrite foldl_rev.
  destruct Mz.get eqn:E.
  - set (kv := (i, s)).
    replace i with kv.1 in * by reflexivity.
    replace s with kv.2 in * by reflexivity.
    apply Mz.elementsIn in E. subst kv.
    apply foldl_In_uniq.
    + rewrite <- rev_list_rev. apply -> List.in_rev. assumption.
    + rewrite map_rev. rewrite rev_uniq. apply Mz.elementsU.
  - apply foldl_NIn.
    intros.
    rewrite <- rev_list_rev.
    rewrite <- List.in_rev.
    apply elementsNIn.
    assumption.
Qed.

Lemma embed_array_get :
  ∀ len (a : WArray.array len) (k : Z),
    embed_array a k = Mz.get a.(WArray.arr_data) k.
Proof.
  intros len a k.
  unfold embed_array.
  rewrite fold_get. reflexivity.
Qed.

Lemma eq_op_MzK :
  ∀ (k x : Z_ordType),
    @eq_op Mz.K.t k x = (k == x).
Proof.
  intros k x.
  destruct (k == x) eqn: e.
  - apply /eqP. move: e => /eqP. auto.
  - apply /eqP. move: e => /eqP. auto.
Qed.

Lemma fold_set {S : eqType} (data : Mz.Map.t S) k v :
  setm (Mz.fold (λ (k : Mz.Map.key) (v : S) (m : {fmap Z → S}), setm m k v) data emptym) k v =
  Mz.fold (λ (k : Mz.Map.key) (v : S) (m : {fmap Z → S}), setm m k v) (Mz.set data k v) emptym.
Proof.
  apply eq_fmap.
  intros x.
  rewrite fold_get.
  rewrite setmE Mz.setP.
  rewrite eq_sym.
  rewrite eq_op_MzK.
  destruct (k == x).
  - reflexivity.
  - rewrite fold_get. reflexivity.
Qed.

Lemma embed_array_set :
  ∀ len (a : WArray.array len) (k : Z) v,
    setm (embed_array a) k v =
    embed_array (WArray.Build_array len (Mz.set a.(WArray.arr_data) k v)).
Proof.
  intros len a k v.
  unfold embed_array.
  rewrite fold_set. reflexivity.
Qed.

Lemma fold_rem {S : eqType} (data : Mz.Map.t S) k :
  remm (Mz.fold (λ (k : Mz.Map.key) (v : S) (m : {fmap Z → S}), setm m k v) data emptym) k =
  Mz.fold (λ (k : Mz.Map.key) (v : S) (m : {fmap Z → S}), setm m k v) (Mz.remove data k) emptym.
Proof.
  apply eq_fmap.
  intros x.
  rewrite fold_get.
  rewrite remmE Mz.removeP.
  rewrite eq_sym.
  rewrite eq_op_MzK.
  destruct (k == x).
  - reflexivity.
  - rewrite fold_get. reflexivity.
Qed.

Lemma embed_array_rem :
  ∀ len (a : WArray.array len) (k : Z),
    remm (embed_array a) k =
    embed_array (WArray.Build_array len (Mz.remove a.(WArray.arr_data) k)).
Proof.
  intros len a k.
  unfold embed_array.
  rewrite fold_rem. reflexivity.
Qed.

Definition unembed {t : stype} : encode t → sem_t t :=
  match t return encode t → sem_t t with
  | sbool => λ x, x
  | sint => λ x, x
  | sarr n => λ x,
    foldr (λ kv m,
      {| WArray.arr_data := Mz.set m.(WArray.arr_data) kv.1 kv.2 |}
    ) (WArray.empty _) x
  (* (λ kv m, Let m' := m in WArray.set8 m' kv.1 kv.2) *)
  (* (Ok _ (WArray.empty _)) x *)
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

Definition translate_write_var (fn : funname) (x : var_i) (v : typed_chElement) :=
  let l := translate_var fn (v_var x) in
  #put l := truncate_el x.(vtype) v.π2 ;;
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

Definition chArray_get8 (a : 'array) ptr :=
  match a ptr with
  | None => chCanonical ('word U8)
  | Some x => x
  end.

Lemma chArray_get8_correct len (a : WArray.array len) s ptr :
  WArray.get8 a ptr = ok s →
  chArray_get8 (embed_array a) ptr = translate_value (Vword s).
Proof.
  intros H. simpl.
  unfold WArray.get8 in H.
  jbind H x Hx.
  jbind H y Hy.
  noconf H.
  unfold chArray_get8, odflt, oapp, embed_array.
  rewrite fold_get.
  reflexivity.
Qed.

Definition chArray_get ws (a : 'array) ptr scale :=
  (* Jasmin fails if ptr is not aligned; we may not need it. *)
  (* if negb (is_align ptr sz) then chCanonical ws else *)
  let f k := chArray_get8 a (ptr * scale + k)%Z in
  let l := map f (ziota 0 (wsize_size ws)) in
  Jasmin.memory_model.LE.decode ws l.

Definition chArray_get_sub ws len (a : 'array) ptr scale :=
  let size := arr_size ws len in
  let start := (ptr * scale)%Z in
  if (0 <=? start)%Z (* && (start + size <=? ) *)
  then (
    foldr (λ (i : Z) (data : 'array),
      match a (start + i)%Z with
      | Some w => setm data i w
      | None => remm data i      (* BSH: this should maybe not be done; I added it to simplify the proof of equivalence *)
      end
    ) emptym (ziota 0 size)
  )
  else chCanonical 'array.

Definition totc (ty : choice_type) (c : raw_code ty) : typed_code :=
  (ty ; c).

(* Almost chArray_get but with a different key type *)
Definition read_mem (m : 'mem) ptr ws : 'word ws :=
  let f k :=
    match m (ptr + (wrepr Uptr k))%R with
    | None => chCanonical ('word U8)
    | Some x => x
    end
  in
  let l := map f (ziota 0 (wsize_size ws)) in
  Jasmin.memory_model.LE.decode ws l.

Definition chRead ptr ws : raw_code ('word ws) :=
  (* memory as array *)
  mem ← get mem_loc ;;
  ret (read_mem mem ptr ws).

Definition chArray_set8 (a : 'array) ptr w :=
  setm a ptr w.

Lemma chArray_set8_correct {len} (a : WArray.array len) ptr w s :
  WArray.set8 a ptr w = ok s →
  chArray_set8 (embed_array a) ptr w = embed_array s.
Proof.
  intros H. simpl.
  unfold WArray.set8 in H.
  jbind H x Hx.
  noconf H.
  unfold chArray_set8, embed_array.
  simpl.
  rewrite <- fold_set.
  reflexivity.
Qed.

(* Jasmin's write on 'array *)
Definition chArray_write {sz} (a : 'array) ptr (w : word sz) : 'array :=
  (* For now we do not worry about alignment *)
  foldr (λ (k : Z) (a' : 'array),
    chArray_set8 a' (ptr + k)%Z (LE.wread8 w k)
  ) a (ziota 0 (wsize_size sz)).

Definition chArray_write_foldl {sz} (a : 'array) ptr (w : word sz) : 'array :=
  foldl (λ (a' : 'array) (k : Z),
    chArray_set8 a' (ptr + k)%Z (LE.wread8 w k)
  ) a (ziota 0 (wsize_size sz)).

Lemma foldr_set_not_eq {K : ordType} {K' : eqType} {V : eqType} m f g (k : K) (v : V) (l : seq K') :
  (forall k', k' \in l -> k <> f k') ->
  setm (foldr (λ k m, setm m (f k) (g k)) m l) k v = foldr (λ k m, setm m (f k) (g k)) (setm m k v) l.
Proof.
  intros.
  apply eq_fmap.
  intros z. revert z.
  induction l.
  - reflexivity.
  - simpl.
    intros.
    assert (k <> f a).
    { apply H. unfold in_mem. simpl. rewrite eq_refl. auto. }
    rewrite !setmE.
    destruct (_ == _) eqn:E.
    + move: E => /eqP. intros. subst.
      assert (k == f a = false).
      { apply /eqP. assumption. }
      rewrite H1. rewrite <- IHl.
      {
        rewrite setmE.
        rewrite eq_refl.
        reflexivity.
      }
      intros. apply H.
      rewrite in_cons.
      rewrite H2.
      rewrite Bool.orb_true_r. auto.
    +
      destruct (_ == f a). 1: reflexivity.
      rewrite <- IHl.
      { rewrite setmE.
        rewrite E.
        reflexivity.
      }
      intros.
      apply H.
      rewrite in_cons.
      rewrite H1.
      rewrite Bool.orb_true_r. auto.
Qed.

Lemma foldl_set_not_eq {K : ordType} {K' : eqType} {V : eqType} m f g (k : K) (v : V) (l : seq K') :
  (∀ k', k' \in l -> k ≠ f k') →
  setm (foldl (λ m k, setm m (f k) (g k)) m l) k v = foldl (λ m k, setm m (f k) (g k)) (setm m k v) l.
Proof.
  intros h.
  rewrite <- revK.
  rewrite !foldl_rev.
  apply foldr_set_not_eq.
  intros k' hk'.
  rewrite <- rev_list_rev in hk'.
  move: hk' => /InP hk'.
  apply List.in_rev in hk'.
  apply h.
  apply /InP. assumption.
Qed.

Lemma foldl_foldr_setm
  {K : ordType} {K' : eqType} {V : eqType} m (f : K' → K) (g : K' → V) (l : seq K') :
  uniq [seq f i | i <- l] →
  foldl (λ m k, setm m (f k) (g k)) m l = foldr (λ k m, setm m (f k) (g k)) m l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- foldl_set_not_eq.
    1: rewrite IHl.
    1: reflexivity.
    { intros. simpl in H. move: H => /andP. easy. }
    { intros. simpl in H. move: H => /andP [] H _.
      clear -H0 H.
      induction l.
      { simpl in *. inversion H0. }
      { simpl in *. rewrite in_cons in H0.
        rewrite notin_cons in H.
        move: H => /andP [] H1 H2.
        move: H0 => /orP [/eqP -> | H0 ].
        { apply /eqP. assumption. }
        { apply IHl; assumption. } } }
Qed.

Lemma chArray_write_aux {sz} (a : 'array) ptr (w : word sz) :
  chArray_write a ptr w = chArray_write_foldl a ptr w.
Proof.
  unfold chArray_write_foldl, chArray_write, chArray_set8.
  rewrite foldl_foldr_setm. 1: reflexivity.
  rewrite map_inj_uniq.
  - unfold ziota.
    rewrite map_inj_uniq.
    + apply iota_uniq.
    + intros n m H.
      micromega.Lia.lia.
  - intros n m H.
    micromega.Lia.lia.
Qed.

(* From WArray.set *)
Definition chArray_set {ws} (a : 'array) (aa : arr_access) (p : Z) (w : word ws) :=
  chArray_write a (p * mk_scale aa ws)%Z w.

(* Jasmin's write on 'mem *)
Definition write_mem {sz} (m : 'mem) (ptr : word Uptr) (w : word sz) : 'mem :=
  (* For now we do not worry about alignment *)
  foldr (λ (k : Z) (m' : 'mem),
    setm m' (ptr + (wrepr Uptr k))%R (LE.wread8 w k)
  ) m (ziota 0 (wsize_size sz)).

Definition translate_write {sz} (p : word Uptr) (w : word sz) : raw_code 'unit :=
  m ← get mem_loc ;; #put mem_loc := write_mem m p w ;; ret tt.

Fixpoint lchtuple (ts : seq choice_type) : choice_type :=
  match ts with
  | [::] => 'unit
  | [:: t1 ] => t1
  | t1 :: ts => t1 × (lchtuple ts)
  end.

(* Unpack `t : lchtuple stys` into a list `xs` s.t. `nth i xs = (nth i sty, t.i)`. *)
Definition coerce_chtuple_to_list (ty : choice_type) (stys : seq stype) (t : ty)
  : list typed_chElement.
Proof.
  pose (lchtuple (map encode stys)) as ty'.
  destruct (ty == ty') eqn:E.
  2: exact [::].
  move: E. move /eqP => E.
  subst. unfold ty' in t. clear ty'.
  move: t. induction stys.
  - move => _. exact [::].
  - intros.
    destruct stys in IHstys, t |- *.
    + simpl in *. apply cons. 2: exact [::].
      econstructor. exact t.
    + destruct t as [t1 ts].
      pose (IHstys ts) as tl.
      pose ((encode a; t1) : typed_chElement) as hd.
      exact (hd :: tl).
Defined.

Definition to_typed_chElement {t : choice_type} (v : t) : typed_chElement := (t ; v).

Fixpoint bind_list (cs : list typed_code) {struct cs} : raw_code ([choiceType of list typed_chElement]) :=
  match cs with
  | [::] => ret [::]
  | c :: cs =>
      v ← c.π2 ;;
      vs ← bind_list cs ;;
      ret (to_typed_chElement v :: vs)
  end.

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

Fixpoint app_sopn_list {S} (ts : list stype) :=
  match ts as ts0
  return (sem_prod ts0 (exec (sem_t S)) → [choiceType of list typed_chElement] → encode S)
  with
  | [::] =>
    λ (o : exec (sem_t S)) (vs : list typed_chElement),
      match vs with
      | [::] =>
        match o with
        | Ok o => embed o
        | _ => chCanonical _
        end
      | _ :: _ => chCanonical _
      end
  | t :: ts0 =>
    λ (o : sem_t t → sem_prod ts0 (exec (sem_t S))) (vs : list typed_chElement),
      match vs with
      | [::] => chCanonical _
      | v :: vs0 => app_sopn_list ts0 (o (unembed (truncate_el t v.π2))) vs0
      end
  end.

Section bind_list_alt.

  Definition bind_typed_list (cs : list typed_code)
    : raw_code (lchtuple ([seq tc.π1 | tc <- cs])).
  Proof.
    induction cs as [| c cs bind_cs].
    - exact (ret tt).
    - destruct cs as [|c' cs'].
      + exact c.π2.
      + exact ( vs ← bind_cs ;;
                v ← c.π2 ;;
                ret (v, vs) ).
  Defined.

  Definition bind_list_truncate (l : list (stype * typed_code))
    : raw_code (lchtuple ([seq encode ttc.1 | ttc <- l])).
  Proof.
    induction l as [| [t c] tcs bind_tcs].
    - exact (ret tt).
    - destruct tcs as [| [t' c'] tcs'].
      + pose (truncate_code t c) as c'.
        exact c'.π2.
      + exact ( vs ← bind_tcs ;;
                v ← (truncate_code t c).π2 ;;
                ret (v, vs) ).
  Defined.

  Lemma map_fst {A B C} (xs : seq A) (ys : seq B) (f : A -> C) (H : size xs = size ys)
    : [seq f xy.1 | xy <- zip xs ys] = [seq f x | x <- xs].
  Proof.
    set (f' := fun xy => f (fst xy)).
    assert ([seq f' i | i <- zip xs ys] = map f (unzip1 (zip xs ys))) as mc by apply map_comp.
    rewrite mc.
    rewrite unzip1_zip.
    1: reflexivity.
    now rewrite H.
  Qed.

  Definition bind_list_trunc_aux (ts : list stype) (cs : list typed_code)
             (H : size ts = size cs)
    : raw_code (lchtuple ([seq encode t | t <- ts])).
  Proof.
    erewrite <- map_fst.
    1: exact (bind_list_truncate (zip ts cs)).
    assumption.
  Defined.

  Definition bind_list' (ts : list stype) (cs : list typed_code)
    : raw_code (lchtuple ([seq encode t | t <- ts])).
  Proof.
    destruct (size ts == size cs) eqn:e.
    - eapply bind_list_trunc_aux.
      apply: eqP e.
    - exact (ret (chCanonical _)).
  Defined.

End bind_list_alt.

Notation totce := to_typed_chElement.


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
      chRead (w1 + w2)%R sz
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
  | PappN op es =>
      (* note that this is sligtly different from Papp2 and Papp1, in that
         we don't truncate when we bind, but when we apply (in app_sopn_list).
         This made the proof easier, but is also more faithful(maybe?) to
         how it is done in jasmin. Maybe we should change Papp1/2.
       *)
    totc _ (
      vs ← bind_list [seq translate_pexpr fn e | e <- es] ;;
      ret (app_sopn_list (type_of_opN op).1 (sem_opN_typed op) vs)
    )
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

Definition translate_write_lval (fn : funname) (l : lval) (v : typed_chElement)
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
    let w := truncate_chWord sz v.π2 in
    translate_write p w
  | Laset aa ws x i =>
    (* Let (n,t) := s.[x] in is a notation calling on_arr_varr on get_var *)
    (* We just cast it since we do not track lengths *)
    t' ← translate_get_var fn x ;;
    let t := coerce_to_choice_type 'array t' in
    i ← (truncate_code sint (translate_pexpr fn i)).π2 ;; (* to_int *)
    let v := truncate_chWord ws v.π2 in
    let t := chArray_set t aa i v in
    translate_write_var fn x (totce t)
  | Lasub aa ws len x i =>
    (* Same observation as Laset *)
    t' ← translate_get_var fn x ;;
    let t := coerce_to_choice_type 'array t' in
    (* Again, we ignore the length *)
    (* Let t' := to_arr (Z.to_pos (arr_size ws len)) v in *)
    unsupported.π2

  (* | Lasub aa ws len x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in
    Let t := @WArray.set_sub n aa ws len t i t' in
    write_var x (@to_val (sarr n) t) s *)
  end.

Definition instr_d (i : instr) : instr_r :=
  match i with MkI _ i => i end.

(* Note c is translated from cmd, in the case ws = [], sem_for does not
  guarantee it is well-formed.
  Also note, it feels odd to get a var_i when I should translate before calling.
  The problem comes from translate_write_var which expects var_i instead of
  Location.
*)
Fixpoint translate_for fn (i : var_i) (ws : seq Z) (c : raw_code 'unit) : raw_code 'unit :=
  match ws with
  | [::] => ret tt
  | w :: ws =>
    translate_write_var fn i (totce (translate_value w)) ;;
    c ;;
    translate_for fn i ws c
  end.
(* sem_i *)
(* Fixpoint translate_instr_r (fn : funname) (i : instr_r) {struct i} : raw_code 'unit *)
(* with translate_instr (fn : funname) (i : instr) {struct i} : raw_code 'unit. *)
(* Proof. *)
(*   (* translate_instr_r *) *)
(*   { *)
(*     pose proof (translate_cmd := *)
(*             (fix translate_cmd (fn : funname) (c : cmd) : raw_code 'unit := *)
(*                match c with *)
(*                | [::] => ret tt *)
(*                | i :: c => translate_instr fn i ;; translate_cmd fn c *)
(*                end)). *)

(*     destruct i as [ | | e c1 c2 | | | ]. *)
(*     - (* Cassgn *) *)
(*       (* l :a=_s p *) *)
(*       pose (translate_pexpr fn p) as tr_p. *)
(*       pose (truncate_code s tr_p) as tr_p'. *)
(*       eapply bind. 1: exact tr_p'.π2. intros. *)
(*       exact (translate_write_lval fn l (totce X)). *)
(*     - exact (unsupported.π2). (* Copn *) *)
(*     - (* Cif e c1 c2 *) *)
(*       pose (e' := translate_pexpr fn e). *)
(*       pose (c1' := translate_cmd fn c1). *)
(*       pose (c2' := translate_cmd fn c2). *)
(*       pose (rb := coerce_typed_code 'bool e'). *)
(*       exact (b ← rb ;; if b then c1' else c2'). *)
(*     - exact (unsupported.π2). (* Cfor *) *)
(*     - exact (unsupported.π2). (* Cwhile *) *)
(*     - (* Ccall i l f l0 *) *)
(*       (* translate arguments *) *)
(*       pose (map (translate_pexpr fn) l0) as tr_l0. *)
(*       (* "perform" the call via `opr` *) *)
(*       (* probably we'd look up the function signature in the current ambient program *) *)

(*       (* write_lvals the result of the call into lvals `l` *) *)

Definition embed_ot {t} : sem_ot t → encode t :=
  match t with
  (* BSH: I'm not sure this will be correct? In jasmin this is an Option bool, perhaps because you don't have to specify all output flags *)
  | sbool => λ x, match x with
                 | Some b => b
                 | None => false
                 end
  | sint => λ x, x
  | sarr n => embed_array
  | sword n => λ x, x
  end.

(* takes a tuple of jasmin values and embeds each component *)
Fixpoint embed_tuple {ts} : sem_tuple ts → lchtuple [seq encode t | t <- ts] :=
  match ts as ts0
  return sem_tuple ts0 -> lchtuple [seq encode t | t <- ts0]
  with
  | [::] => λ (_ : unit), tt
  | t' :: ts' =>
    let rec := @embed_tuple ts' in
    match ts' as ts'0
    return
      (sem_tuple ts'0 -> lchtuple [seq encode t | t <- ts'0]) →
      sem_tuple (t'::ts'0) -> lchtuple [seq encode t | t <- (t'::ts'0)]
    with
    | [::] => λ _ (v : sem_ot t'), embed_ot v
    | t'' :: ts'' => λ rec (p : (sem_ot t') * (sem_tuple (t''::ts''))), (embed_ot p.1, rec p.2)
    end rec
  end.

(* this correcsponds to app_sopn, in the case where applied function can have several return values,
   as opposed to app_sopn_list which is used in the case where there is only one return value
   (e.g. in expressions). In jasmin they manage to only have one function (app_sopn) for these two
   use cases; i'm unsure if we can do the same
 *)
Fixpoint app_sopn_list_tuple {ts_out : list stype} (ts_in  : list stype) :=
  match ts_in as ts0
  return
    (sem_prod ts0 (exec (sem_tuple ts_out))) →
    [choiceType of list typed_chElement] →
    lchtuple ([seq encode t | t <- ts_out])
  with
  | [::] =>
    λ (o : exec (sem_tuple ts_out)) (vs : list typed_chElement),
      match vs, o with
      | [::], Ok o => embed_tuple o
      | _, _ => chCanonical _
      end
  | t :: ts0 =>
    λ (o : sem_t t → sem_prod ts0 (exec (sem_tuple ts_out))) (vs : list typed_chElement),
      match vs with
      | [::] => chCanonical _
      | v :: vs0 => app_sopn_list_tuple ts0 (o (unembed (truncate_el t v.π2))) vs0
      end
  end.

(* list_ltuple *)
Fixpoint list_lchtuple {ts} : lchtuple ([seq encode t | t <- ts]) → [choiceType of list typed_chElement] :=
  match ts as ts0
  return
    lchtuple ([seq encode t | t <- ts0]) →
    [choiceType of list typed_chElement]
  with
  | [::] => λ _, [::]
  | t' :: ts' =>
    let rec := @list_lchtuple ts' in
    match ts' as ts'0
    return
      (lchtuple ([seq encode t | t <- ts'0]) →
      [choiceType of list typed_chElement]) →
      lchtuple [seq encode t | t <- (t'::ts'0)] →
      [choiceType of list typed_chElement]
    with
    | [::] => λ _ (v : encode t'), [:: totce v]
    | t'' :: ts'' => λ rec (p : (encode t') × (lchtuple [seq encode t | t <- (t''::ts'')])), totce p.1 :: rec p.2
    end rec
  end.

(* corresponds to exec_sopn *)
Definition translate_exec_sopn (o : sopn) (vs : seq typed_chElement) :=
  list_lchtuple (app_sopn_list_tuple _ (sopn_sem o) vs).

Fixpoint foldl2 {A B R} (f : R -> A -> B -> R) (la : seq A) (lb : seq B) r :=
  match la with
  | [::] => r
  | a :: la0 => match lb with
              | [::] => r
              | b :: lb0 => foldl2 f la0 lb0 (f r a b)
              end
  end.

Fixpoint foldr2 {A B R} (f : A -> B -> R -> R) (la : seq A) (lb : seq B) r :=
  match la with
  | [::] => r
  | a :: la0 => match lb with
              | [::] => r
              | b :: lb0 => f a b (foldr2 f la0 lb0 r)
              end
  end.

Definition translate_write_lvals fn ls vs :=
  (* foldl2 (λ c l v, translate_write_lval fn l v ;; c) ls vs (ret tt). *)
  foldr2 (λ l v c, translate_write_lval fn l v ;; c) ls vs (ret tt).

Fixpoint translate_instr_r (prog_exports : {fmap funname -> opsig}) (fn : funname) (i : instr_r) {struct i} : raw_code 'unit

with translate_instr (prog_exports : {fmap funname -> opsig}) (fn : funname) (i : instr) {struct i} : raw_code 'unit :=
  translate_instr_r prog_exports fn (instr_d i).
Proof.
  pose proof (translate_cmd :=
    (fix translate_cmd (fn : funname) (c : cmd) : raw_code 'unit :=
      match c with
      | [::] => ret tt
      | i :: c =>
        translate_instr prog_exports fn i ;;
        translate_cmd fn c
      end
    )
  ).

  destruct i as [ | ls _ o es | e c1 c2 | i [[d lo] hi] c | | ii xs f args ].
  - (* Cassgn *)
    (* l :a=_s p *)
    pose (translate_pexpr fn p) as tr_p.
    eapply bind. 1: exact (tr_p.π2).
    intros v. pose (truncate_el s v) as tr_v.
    exact (translate_write_lval fn l (totce tr_v)).
  - (* Copn *)
    pose (cs := [seq (translate_pexpr fn e) | e <- es]).
    pose (vs := bind_list cs).
    eapply bind. 1: exact vs. intros bvs.
    pose (out := translate_exec_sopn o bvs).
    exact (translate_write_lvals fn ls out). (* BSH: I'm not sure if the outputs should be truncated? *)
  - (* Cif e c1 c2 *)
    pose (e' := translate_pexpr fn e).
    pose (c1' := translate_cmd fn c1).
    pose (c2' := translate_cmd fn c2).
    pose (rb := coerce_typed_code 'bool e').
    exact (b ← rb ;; if b then c1' else c2').
  - (* Cfor i (d, lo, hi) c *)
    (* pose (iᵗ := translate_var fn i). *) (* Weird not to do it *)
    pose (loᵗ := coerce_typed_code 'int (translate_pexpr fn lo)).
    pose (hiᵗ := coerce_typed_code 'int (translate_pexpr fn hi)).
    pose (cᵗ := translate_cmd fn c).
    exact (
      vlo ← loᵗ ;;
      vhi ← hiᵗ ;;
      translate_for fn i (wrange d vlo vhi) cᵗ
    ).
  - exact (unsupported.π2). (* Cwhile *)
  - (* Ccall ii xs f args *)
    (* Translate arguments. *)
    pose (map (translate_pexpr f) args) as tr_args.

    (* We need some typing about the translated and original f, let's look it
        up. *)
    destruct (prog_exports f) as [f_sg|].
    2: {
      (* The function `f` wasn't found in the exports. This should mean that
          the Jasmin semantics also failed at `sem_call` where
          `get_fundef (p_funcs P) f = Some f'` is expected. *)
      exact (unsupported.π2).
    }
    destruct (get_fundef (p_funcs P) f) eqn:E.
    2: exact (unsupported.π2).

    (* Evaluate & truncate arguments according to the Jasmin typing of `f`. *)
    (* Note that in Ecall we do not need to truncate, as sem_call does not
        enforce any relation between the types of the function and the
        arguments. But we need the types to match. sem_call, however, does
        truncate as soon as the type of `f` is looked up. *)
    pose (bind_list' _f.(f_tyin) tr_args) as vargs'.
    (* pose (bind_list [seq translate_pexpr fn e | e <- args]) as vargs'. *)
    (* Bind the values. *)
    apply (bind vargs'). intros vargs.
    (* Now "perform" the call via `opr`. *)
    apply (opr f_sg).
    + exact (coerce_to_choice_type (chsrc f_sg) vargs).
    + intros vs.

      (* Unpack `vs : tgt f_sg` into a list in order to write `xs`. *)
      pose (f_tyout _f) as f_tyout.
      apply (coerce_chtuple_to_list _ f_tyout) in vs.
      pose (zip f_tyout vs) as vs_f.

      (* We coerce rather than truncating here. The truncation should happen
          in sem_call; the coercion should never fail on well-translated
          functions. Presumably these results just got truncated in sem_call,
          so we could also truncate instead of coercing if convenient. *)
      pose (map (λ '(ty,c),
                  let ty' := encode ty in
                            (totce (coerce_to_choice_type ty' c.π2)) : typed_chElement) vs_f)
        as vres'.
      (* pose (map (λ '(ty,c), (truncate_code ty (totc c.π1 (ret c.π2)))) l0) as vres'. *)

      pose (map (λ '(x,v), translate_write_lval fn x v) (zip xs vres')) as vres''.
      exact (foldl (λ c k, c ;; k) (ret tt) vres'').
Defined.

(* translate_instr is blocked because it is a fixpoint *)
Lemma translate_instr_unfold :
  ∀ ep fn i,
    translate_instr ep fn i = translate_instr_r ep fn (instr_d i).
Proof.
  intros ep fn i.
  destruct i. reflexivity.
Qed.

(* Trick to have it expand to the same as the translate_cmd above *)
Section TranslateCMD.

Context (prog_exports : {fmap funname -> opsig}).

Fixpoint translate_cmd (fn : funname) (c : cmd) : raw_code 'unit :=
  match c with
  | [::] => ret tt
  | i :: c => translate_instr prog_exports fn i ;; translate_cmd fn c
  end.

End TranslateCMD.

Record fdef := {
  ffun : typed_raw_function ;
  locs : {fset Location} ;
  imp : Interface ;
}.

#[local] Definition ty_in fd := (ffun fd).π1.
#[local] Definition ty_out fd := ((ffun fd).π2).π1.

Definition translate_fundef (prog_exports : {fmap funname -> opsig})
           (fd : _ufun_decl (* extra_fun_t *)) : funname * fdef.
Proof.
  destruct fd. destruct _f.
  split. 1: exact f.
  constructor.
  - pose (lchtuple (map encode f_tyin)) as tyin'.
    pose (lchtuple (map encode f_tyout)) as tyout'.
    exists tyin', tyout'. intros vargs'.

    (* NB: We coerce rather than truncating here, i.e. we expect the arguments
       provided to us to be of the correct type. This differs slightly from
       Jasmin where the truncation is performed in `sem_call`. However, as
       explained in the translation of `Ccall` in `translate_instr_r`, we need
       the types of the arguments to match the function in order to write the
       function application, so we truncate at the caller side. We thus expect
       the arguments to already be of the type `f_tyin` prescribed by the
       function `f`. *)
    apply (coerce_chtuple_to_list _ f_tyin) in vargs'.

    (* Write the arguments to their locations. *)
    pose (map (λ '(x, (ty; v)), translate_write_var f x (totce v))
              (zip f_params vargs'))
      as cargs.
    apply (foldl (λ c k, c ;; k) (ret tt)) in cargs.
    apply (bind cargs) => _.

    (* Perform the function body. *)
    apply (bind (translate_cmd prog_exports f f_body)) => _.

    (* Look up the results in their locations and return them. *)
    pose (map (λ x, totc _ (translate_get_var f (v_var x))) f_res) as cres.
    exact (bind_list' f_tyout cres).
  - exact fset0.
  - exact [interface].
Defined.

(* Apply cast_fun or return default value, like lookup_op *)
Equations? cast_typed_raw_function {dom cod : choice_type} (rf : typed_raw_function) : dom → raw_code cod :=
  cast_typed_raw_function rf with inspect ((dom == rf.π1) && (cod == rf.π2.π1)) := {
  | @exist true e => pkg_composition.cast_fun _ _ rf.π2.π2 ;
  | @exist false e => λ _, ret (chCanonical _)
  }.
Proof.
  all: symmetry in e.
  all: move: e => /andP [/eqP e1 /eqP e2].
  all: eauto.
Defined.

Definition get_fundef_ssp (sp : seq (funname * fdef)) (fn : funname) (dom cod : choice_type) :
  option (dom → raw_code cod) :=
  match assoc sp fn with
  | Some fd => Some (cast_typed_raw_function fd.(ffun))
  | None => None
  end.

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

Lemma translate_read :
  ∀ s ptr sz w m,
    rel_mem s m →
    read s ptr sz = ok w →
    read_mem (get_heap m mem_loc) ptr sz = w.
Proof.
  intros s ptr sz w m hm h.
  rewrite readE in h.
  jbind h _u eb. apply assertP in eb.
  jbind h l hl. noconf h.
  unfold read_mem. f_equal.
  revert l hl. apply ziota_ind.
  - simpl. intros l h. noconf h. reflexivity.
  - simpl. intros i l' hi ih l h.
    jbind h y hy. jbind h ys hys. noconf h.
    erewrite ih. 2: exact hys.
    eapply hm in hy. rewrite hy. reflexivity.
Qed.

Lemma get_mem_read8 :
  ∀ m p,
    read_mem m p U8 =
    match m p with
    | Some w => w
    | None => chCanonical _
    end.
Proof.
  intros m p.
  unfold read_mem. simpl.
  rewrite <- addE.
  rewrite add_0.
  destruct (m p) eqn:E.
  all: rewrite E; rewrite <- LE.encode8E; apply LE.decodeK.
Qed.

Lemma write_mem_get ws m p (w : word ws) p' :
  write_mem m p w p' =
  if (0 <=? sub p' p)%Z && (sub p' p <? wsize_size ws)%Z
  then Some (LE.wread8 w (sub p' p))
  else m p'.
Proof.
  unfold write_mem.
  rewrite -in_ziota. unfold wsize_size.
  apply ziota_ind.
  - auto.
  - intros i l h Ih.
    rewrite (@in_cons ssrZ.Z_eqType).
    simpl.
    rewrite <- addE.
    destruct (_ == _) eqn:eb.
    + move: eb => /eqP <-.
      rewrite setmE.
      rewrite add_sub.
      rewrite !eq_refl.
      reflexivity.
    + move: eb => /eqP.
      rewrite setmE.
      destruct (p' == add p i) eqn:E.
      * rewrite E.
        move: E => /eqP E eb.
        rewrite E in eb.
        rewrite sub_add in eb.
        2:{ destruct ws. all: unfold wsize_size. all: micromega.Lia.lia. }
        contradiction.
      * rewrite E. intros. apply Ih.
Qed.

(* Copy of write_read8 *)
(* BSH: i don't know if we need this any more (see write_mem_get) *)
Lemma write_read_mem8 :
  ∀ m p ws w p',
    read_mem (write_mem (sz := ws) m p w) p' U8 =
    (let i := sub p' p in
    if (0 <=? i)%Z && (i <? wsize_size ws)%Z
    then LE.wread8 w i
    else read_mem m p' U8
    ).
Proof.
  intros m p ws w p'.
  simpl.
  rewrite !get_mem_read8.
  rewrite write_mem_get.
  destruct (_ : bool) eqn:eb.
  all: reflexivity.
Qed.

Lemma translate_write_mem_correct :
  ∀ sz cm cm' ptr w m,
    write cm ptr (sz := sz) w = ok cm' →
    rel_mem cm m →
    rel_mem cm' (set_heap m mem_loc (write_mem (get_heap m mem_loc) ptr w)).
Proof.
  intros sz cm cm' ptr w m hw hr.
  intros ptr' v ev.
  rewrite get_set_heap_eq.
  rewrite write_mem_get.
  erewrite write_read8 in ev. 2: exact hw.
  simpl in ev.
  destruct (_ : bool).
  - noconf ev. reflexivity.
  - apply hr. assumption.
Qed.

#[local] Open Scope vmap_scope.

Definition rel_vmap (vm : vmap) (fn : funname) (h : heap) :=
  ∀ (i : var) v,
    vm.[i] = ok v →
    get_heap h (translate_var fn i) = coerce_to_choice_type _ (embed v).

Definition rel_estate (s : estate) (fn : funname) (h : heap) :=
  rel_mem s.(emem) h ∧ rel_vmap s.(evm) fn h.

Lemma translate_read_estate :
  ∀ fn s ptr sz w m,
    rel_estate s fn m →
    read (emem s) ptr sz = ok w →
    read_mem (get_heap m mem_loc) ptr sz = w.
Proof.
  intros fn s ptr sz w m [] h.
  eapply translate_read. all: eassumption.
Qed.

Lemma mem_loc_translate_var_neq :
  ∀ fn x,
    mem_loc != translate_var fn x.
Proof.
Admitted.

Lemma translate_write_estate :
  ∀ fn sz s cm ptr w m,
    write s.(emem) ptr (sz := sz) w = ok cm →
    rel_estate s fn m →
    rel_estate {| emem := cm ; evm := s.(evm) |} fn (set_heap m mem_loc (write_mem (get_heap m mem_loc) ptr w)).
Proof.
  intros fn sz s cm ptr w m hw [hrm hvm].
  split.
  - simpl. eapply translate_write_mem_correct. all: eassumption.
  - simpl. intros i v ev.
    rewrite get_set_heap_neq.
    2:{ rewrite eq_sym. apply mem_loc_translate_var_neq. }
    apply hvm. assumption.
Qed.

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

Lemma coerce_to_choice_type_translate_value_to_val :
  ∀ ty (v : sem_t ty),
    coerce_to_choice_type (encode ty) (translate_value (to_val v)) =
    embed v.
Proof.
  intros ty v.
  destruct ty.
  all: simpl. all: rewrite coerce_to_choice_type_K. all: reflexivity.
Qed.

Lemma totce_coerce t (tv : choice_type) (v : tv) :
  t = tv →
  totce (coerce_to_choice_type t v) = totce v.
Proof.
  intro e.
  rewrite e. rewrite coerce_to_choice_type_K.
  reflexivity.
Qed.

Section bind_list_test.

  (* Quick test to see that the definition-via-tactics of bind_list' computes
     as expected. *)
  Definition cs : list typed_code :=
    [:: ('bool; (ret false)) ; ('bool; (ret true)) ; ('nat; (ret 666))].
  Definition ts := [:: sbool; sbool; sint; sint].
  Goal bind_list' ts cs = bind_list' ts cs.
    unfold bind_list' at 2.
    unfold bind_list_trunc_aux.
    simpl.
    (* rewrite !coerce_to_choice_type_K. *)
    simp coerce_to_choice_type.
    cbn.
  Abort.
End bind_list_test.


Lemma get_var_get_heap :
  ∀ fn x s v m,
    get_var (evm s) x = ok v →
    rel_estate s fn m →
    get_heap m (translate_var fn x) =
    coerce_to_choice_type _ (translate_value v).
Proof.
  intros fn x s v m ev hm.
  unfold get_var in ev.
  eapply on_vuP. 3: exact ev. 2: discriminate.
  intros sx esx esv.
  eapply hm in esx. subst.
  rewrite coerce_to_choice_type_translate_value_to_val.
  rewrite esx. rewrite coerce_to_choice_type_K. reflexivity.
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
  unfold u_get in hx. subst.
  eapply get_var_get_heap.
  - eassumption.
  - eapply hcond. assumption.
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

Lemma totce_truncate_translate :
  ∀ ty v v',
    truncate_val ty v = ok v' →
    totce (truncate_el ty (translate_value v)) = totce (translate_value v').
Proof.
  intros ty v v' h.
  erewrite translate_truncate_val by eassumption.
  apply totce_coerce.
  unfold choice_type_of_val.
  erewrite truncate_val_type by eassumption.
  reflexivity.
Qed.

Lemma bind_list_correct cond cs vs :
  [seq c.π1 | c <- cs] = [seq choice_type_of_val v | v <- vs] →
  List.Forall2 (λ c v, ⊢ ⦃ cond ⦄ c.π2 ⇓ coerce_to_choice_type _ (translate_value v) ⦃ cond ⦄) cs vs →
  ⊢ ⦃ cond ⦄ bind_list cs ⇓ [seq to_typed_chElement (translate_value v) | v <- vs ] ⦃ cond ⦄.
Proof.
  revert vs.
  induction cs; intros.
  - destruct vs.
    2: inversion H.
    apply u_ret.
    intros; auto.
  - simpl.
    destruct vs.
    1: inversion H0.
    inversion H0; subst.
    inversion H; subst.
    eapply u_bind.
    1: eassumption.
    eapply u_bind.
    + apply IHcs; eassumption.
    + apply u_ret.
      intros; split; auto.
      simpl.
      rewrite H2.
      rewrite coerce_to_choice_type_K.
      reflexivity.
Qed.

Lemma translate_truncate_word :
  ∀ sz sz' (w : word sz) (w' : word sz'),
    truncate_word sz' w = ok w' →
    truncate_chWord sz' (@embed (sword _) w) = w'.
Proof.
  intros sz sz' w w' h.
  simpl. rewrite h. reflexivity.
Qed.

Lemma translate_to_word :
  ∀ sz v w,
    to_word sz v = ok w →
    truncate_chWord sz (translate_value v) = w.
Proof.
  intros sz v w h.
  destruct v as [| | | sz' w' | []]. all: try discriminate.
  simpl in h.
  unfold translate_value.
  apply translate_truncate_word. assumption.
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
Proof.
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
    jbind H x h1.
    destruct x. all: try discriminate.
    jbind H x h2.
    jbind H y h3.
    noconf H.
    reflexivity.
  - jbind H x h1.
    destruct x. all: try discriminate.
    jbind H x h2.
    jbind H y h3.
    noconf H.
    reflexivity.
  - jbind H x h1.
    jbind H y h2.
    jbind H z h3.
    noconf H.
    reflexivity.
  - jbind H x h1.
    jbind H y h2.
    noconf H.
    unfold choice_type_of_val.
    rewrite type_of_to_val.
    reflexivity.
  - jbind H v1 h1.
    jbind H v2 h2.
    jbind H v3 h3.
    jbind H v4 h4.
    jbind H v5 h5.
    noconf H.
    unfold choice_type_of_val.
    rewrite type_of_to_val.
    reflexivity.
  - jbind H v1 h1.
    jbind H v2 h2.
    noconf H.
    unfold choice_type_of_val.
    rewrite type_of_to_val.
    reflexivity.
  - jbind H v1 h1.
    jbind H v2 h2.
    jbind H v3 h3.
    noconf H.
    jbind h2 v4 h4.
    jbind h3 v5 h5.
    unfold choice_type_of_val.
    destruct v1.
    all: erewrite truncate_val_type. 1,3: reflexivity. 1,2: eassumption.
Qed.

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
  simpl.
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
    apply chArray_get8_correct.
    assumption.
Qed.

Lemma chArray_write_correct :
  ∀ ws len (a : WArray.array len) i (w : word ws) t,
    write a i w = ok t →
    chArray_write (translate_value (Varr a)) i w = translate_value (Varr t).
Proof.
  intros.
  unfold write in H.
  jbind H x Hx.
  rewrite chArray_write_aux.
  unfold chArray_write_foldl.
  revert a H.
  apply ziota_ind.
  - intros.
    simpl in *.
    noconf H.
    reflexivity.
  - intros.
    simpl in *.
    jbind H1 y Hy.
    apply chArray_set8_correct in Hy.
    rewrite Hy.
    eapply H0.
    assumption.
Qed.

Lemma chArray_get_sub_correct (lena len : BinNums.positive) a aa sz i t :
  WArray.get_sub aa sz len a i = ok t ->
  chArray_get_sub sz len (translate_value (@Varr lena a)) i (mk_scale aa sz) = translate_value (Varr t).
Proof.
  intros H.
  unfold WArray.get_sub in H.
  destruct (_ && _) eqn:E. 2: discriminate.
  noconf H.
  unfold chArray_get_sub.
  unfold WArray.get_sub_data.
  move: E => /andP []-> h2.
  rewrite <- !foldl_rev.
  apply ziota_ind.
  - reflexivity.
  - intros.
    rewrite rev_cons.
    rewrite !foldl_rcons.
    rewrite H0.
    rewrite fold_get.
    destruct (Mz.get (WArray.arr_data a) (i * mk_scale aa sz + i0)%Z) eqn:E.
    + rewrite E.
      rewrite fold_set.
      reflexivity.
    + rewrite E.
      rewrite fold_rem.
      reflexivity.
Qed.

(* Like write_mem_get *)
Lemma chArray_write_get :
  ∀ ws (a : 'array) (w : word ws) (i j : Z),
    chArray_write a i w j =
    if (0 <=? j - i)%Z && (j - i <? wsize_size ws)%Z
    then Some (LE.wread8 w (j - i))
    else a j.
Proof.
  intros ws a w i j.
  unfold chArray_write. rewrite -in_ziota. unfold wsize_size.
  apply ziota_ind.
  - simpl. reflexivity.
  - simpl. intros k l h ih.
    rewrite (@in_cons ssrZ.Z_eqType).
    destruct (_ == _) eqn:eb.
    + simpl. move: eb => /eqP eb. subst.
      unfold chArray_set8.
      rewrite setmE.
      replace (i + (j - i))%Z with j by micromega.Lia.lia.
      rewrite eq_refl.
      reflexivity.
    + simpl. move: eb => /eqP eb.
      rewrite setmE.
      destruct (_ == _) eqn: e.
      1:{ move: e => /eqP e. subst. micromega.Lia.lia. }
      apply ih.
Qed.

Lemma embed_read8 :
  ∀ len (a : WArray.array len) (z : Z) v,
    read a z U8 = ok v →
    chArray_get U8 (embed_array a) z 1 = translate_value (Vword v).
Proof.
  intros len a z v h.
  unfold read in h. jbind h _u hb. jbind h l hl. noconf h.
  simpl in hl. jbind hl y hy. noconf hl.
  unfold WArray.get8 in hy. jbind hy _u1 hb1. jbind hy _u2 hb2. noconf hy.
  unfold odflt, oapp. rewrite <- embed_array_get. rewrite add_0.
  simpl.
  unfold chArray_get. simpl.
  replace (z * 1 + 0)%Z with z by micromega.Lia.lia.
  reflexivity.
Qed.

Lemma chArray_set_correct :
  ∀ ws len (a : WArray.array len) aa i (w : word ws) t,
    WArray.set a aa i w = ok t →
    chArray_set (translate_value (Varr a)) aa i w = translate_value (Varr t).
Proof.
  intros ws len a aa i w t h.
  unfold WArray.set in h.
  unfold chArray_set.
  apply chArray_write_correct. assumption.
Qed.

Lemma sop1_unembed_embed op v :
  sem_sop1_typed op (unembed (embed v)) = sem_sop1_typed op v.
Proof.
  destruct op as [| | | | | | o]. 1-6: reflexivity.
  destruct o. all: reflexivity.
Qed.

Lemma sop2_unembed_embed op v1 v2 :
  sem_sop2_typed op (unembed (embed v1)) (unembed (embed v2)) =
  sem_sop2_typed op v1 v2.
Proof.
  destruct op.
  all: try reflexivity.
  all: try destruct o.
  all: try destruct c.
  all: reflexivity.
Qed.

Lemma translate_pexprs_types fn s1 es vs :
  mapM (sem_pexpr gd s1) es = ok vs →
  [seq (translate_pexpr fn e).π1 | e <- es] = [seq choice_type_of_val v | v <- vs].
Proof.
  revert vs. induction es; intros.
  - destruct vs. 2: discriminate.
    reflexivity.
  - inversion H.
    jbind H1 v Hv.
    jbind H1 vs' Hvs'.
    noconf H1.
    simpl.
    erewrite IHes by eassumption.
    erewrite translate_pexpr_type by eassumption.
    reflexivity.
Qed.

(* jbind with fresh names *)
Ltac jbind_fresh h :=
  eapply rbindP ; [| exact h ] ;
  let x := fresh in
  let hx := fresh in
  clear h ; intros x hx h ;
  cbn beta in h.

Lemma app_sopn_nil_ok_size :
  ∀ T ts (f : sem_prod ts (exec T)) vs v,
    app_sopn ts f vs = ok v →
    size ts = size vs.
Proof.
  intros A ts f vs v h.
  induction ts as [| t ts ih] in f, vs, v, h |- *.
  - destruct vs. 2: discriminate.
    reflexivity.
  - destruct vs as [| v' vs]. 1: discriminate.
    simpl in *.
    jbind h v1 hv.
    f_equal. eapply ih. eassumption.
Qed.

Definition WArray_ext_eq {len} (a b : WArray.array len) :=
  ∀ i, Mz.get a.(WArray.arr_data) i = Mz.get b.(WArray.arr_data) i.

Notation "a =ₑ b" := (WArray_ext_eq a b) (at level 90).
Notation "(=ₑ)" := WArray_ext_eq (only parsing).

Instance WArray_ext_eq_equiv {len} : Equivalence (@WArray_ext_eq len).
Proof.
  split.
  - intros x.
    unfold WArray_ext_eq.
    intros.
    reflexivity.
  - intros x y H.
    unfold WArray_ext_eq.
    intros.
    rewrite H.
    reflexivity.
  - intros x y z H1 H2.
    unfold WArray_ext_eq.
    intros.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Lemma embed_unembed {t} (a : encode t) :
  embed (unembed a) = a.
Proof.
  destruct t. 1,2,4: reflexivity.
  apply eq_fmap.
  intros x.
  unfold embed, embed_array, unembed.
  rewrite fold_get.
  simpl in *.
  destruct a.
  cbn.
  induction fmval; intros; simpl in *.
  - rewrite Mz.get0. reflexivity.
  - rewrite Mz.setP.
    rewrite eq_sym.
    destruct (_ == _)%B eqn:E.
    + move: E => /eqP ->.
      rewrite eq_refl.
      reflexivity.
    + destruct (@eq_op (Ord.eqType Z_ordType) _ _)%B eqn:E2.
      { move: E2 E => /eqP ->. rewrite eq_refl. easy. }
      apply IHfmval.
      eapply path_sorted.
      eassumption.
Qed.

Lemma unembed_embed {len} (a : sem_t (sarr len)) :
  unembed (embed a) =ₑ a.
Proof.
  intros x.
  rewrite <- embed_array_get.
  change (embed_array (unembed (embed a))) with (embed (unembed (embed a))).
  rewrite embed_unembed.
  unfold embed, embed_array.
  rewrite fold_get.
  reflexivity.
Qed.

Instance unembed_embed_Proper {len} : Proper ((=ₑ) ==> (=ₑ)) (λ (a : sem_t (sarr len)), unembed (embed a)).
Proof.
  intros x y H.
  rewrite !unembed_embed.
  assumption.
Qed.

Instance WArray_get8_Proper {len} : Proper ((=ₑ) ==> eq ==> eq) (@WArray.get8 len).
  intros a b H ? ? Hi.
  unfold WArray.get8, WArray.in_bound, WArray.is_init.
  rewrite H Hi.
  reflexivity.
Qed.

Instance WArray_get_Proper {len ws} : Proper ((=ₑ) ==> eq ==> eq) (@WArray.get len AAscale ws).
Proof.
  intros a b H i j Hij.
  unfold WArray.get, read.
  rewrite Hij.
  destruct is_align. 2: reflexivity.
  simpl. f_equal.
  apply eq_mapM. intros.
  rewrite H.
  reflexivity.
Qed.

(* this should be moved to the jasmin repo *)
Lemma in_rcons_r {S : eqType} (a : S) l :
  a \in rcons l a.
Proof.
  induction l.
  - apply mem_head.
  - simpl.
    rewrite in_cons IHl.
    by apply /orP; right.
Qed.

Lemma in_rcons_l {S : eqType} (a b : S) l :
  a \in l → a \in rcons l b.
Proof.
  induction l.
  - easy.
  - intros.
    rewrite in_cons in H.
    move: H => /orP [].
    + move=> /eqP ->.
      rewrite rcons_cons.
      rewrite in_cons.
      by apply /orP; left.
    + move=> H.
      rewrite rcons_cons.
      rewrite in_cons.
      apply /orP; right.
      apply IHl; assumption.
Qed.

Lemma foldM_rcons eT (aT: eqType) bT (f: aT → bT → result eT bT) (a:aT) (b:bT) (l:list aT) :
  foldM f b (rcons l a) = Let b' := foldM f b l in f a b'.
Proof.
  induction l as [| c l ih] in a, b |- *.
  - simpl. destruct (f a b). all: reflexivity.
  - simpl.
    destruct (f c b).
    + simpl. rewrite ih. reflexivity.
    + reflexivity.
Qed.

Lemma eq_foldM eT (aT: eqType) bT (f1 f2: aT → bT → result eT bT) (b:bT) (l:list aT) :
  (∀ a b, a \in l → f1 a b = f2 a b) →
  foldM f1 b l = foldM f2 b l.
Proof.
  replace l with (rev (rev l)) by (apply revK).
  set (l' := rev l).
  induction l'; intros.
  - reflexivity.
  - rewrite rev_cons.
    rewrite !foldM_rcons.
    rewrite IHl'.
    + destruct (foldM f2 b (rev l')). 2: reflexivity.
      apply H.
      rewrite rev_cons.
      apply in_rcons_r.
    + intros. apply H.
      rewrite rev_cons.
      apply in_rcons_l.
      assumption.
Qed.

Instance WArray_copy_Proper {ws p} : Proper ((=ₑ) ==> eq) (@WArray.copy ws p).
Proof.
  intros a b H.
  unfold WArray.copy, WArray.fcopy.
  apply eq_foldM.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma app_sopn_list_tuple_correct o vs vs' :
  app_sopn _ (sopn_sem o) vs = ok vs' →
  app_sopn_list_tuple
    _
    (sopn_sem o)
    [seq to_typed_chElement (translate_value v) | v <- vs]
  =
  embed_tuple vs'.
Proof.
  intro H.
  destruct o as [ ws p | | | | | ].
  - apply app_sopn_nil_ok_size in H as Hs.
    simpl in Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 2: inversion Hs.
    cbn -[wsize_size app_sopn_list_tuple].
    cbn [app_sopn_list_tuple].

    jbind H vs'' Hv''.
    simpl in H.
    unfold sopn_sem in H.

    cbn -[wsize_size WArray.copy unembed truncate_el].
    erewrite translate_of_val by eassumption.
    rewrite coerce_to_choice_type_K.
    rewrite translate_value_to_val.
    rewrite eq_rect_r_K.
    cbn -[wsize_size ziota] in H.
    rewrite unembed_embed.
    rewrite H.
    reflexivity.
  - simpl; destruct map; reflexivity.
  - apply app_sopn_nil_ok_size in H as Hs.
    simpl in Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 2: inversion Hs.

    simpl in *.
    jbind H v' Hv'.
    jbind H v'' Hv''.
    erewrite translate_to_word by eassumption.
    erewrite translate_to_word by eassumption.

    unfold sopn_sem in H.
    simpl in H.
    noconf H.

    reflexivity.
  - apply app_sopn_nil_ok_size in H as Hs.
    simpl in Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 2: inversion Hs.

    simpl in *.
    jbind H v' Hv'.
    jbind H v'' Hv''.
    jbind H v''' Hv'''.
    erewrite translate_to_word by eassumption.
    erewrite translate_to_word by eassumption.
    erewrite translate_to_bool by eassumption.

    unfold sopn_sem in H.
    simpl in H.
    noconf H.

    reflexivity.
  - apply app_sopn_nil_ok_size in H as Hs.
    simpl in Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 1: inversion Hs.
    destruct vs. 2: inversion Hs.

    simpl in *.
    jbind H v' Hv'.
    jbind H v'' Hv''.
    jbind H v''' Hv'''.
    erewrite translate_to_word by eassumption.
    erewrite translate_to_word by eassumption.
    erewrite translate_to_bool by eassumption.

    unfold sopn_sem in H.
    simpl in H.
    noconf H.

    reflexivity.
  (* assume this case is correct wrt to the chosen set of assemnly operations *)
  - Admitted.

Lemma list_tuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p : sem_tuple (t1 :: t2 :: ts)) :
  list_ltuple p = (oto_val p.1) :: (list_ltuple (p.2 : sem_tuple (t2 :: ts))).
Proof. reflexivity. Qed.

Lemma embed_tuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p : sem_tuple (t1 :: t2 :: ts)) :
  embed_tuple p = (embed_ot p.1, embed_tuple (p.2 : sem_tuple (t2 :: ts))).
Proof. reflexivity. Qed.

Lemma list_lchtuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p1 : encode t1) (p2 : lchtuple [seq encode t | t <- (t2 :: ts)]) :
  list_lchtuple ((p1, p2) : lchtuple [seq encode t | t <- (t1 :: t2 :: ts)]) = (totce p1) :: (list_lchtuple p2).
Proof. reflexivity. Qed.

Lemma translate_exec_sopn_correct (o : sopn) (ins outs : values) :
  exec_sopn o ins = ok outs ->
  translate_exec_sopn o [seq totce (translate_value v) | v <- ins] = [seq totce (translate_value v) | v <- outs].
Proof.
  intros.
  unfold translate_exec_sopn.
  jbind H vs Hvs.
  noconf H.
  erewrite app_sopn_list_tuple_correct by eassumption.
  clear Hvs.
  induction tout.
  - reflexivity.
  - destruct l.
    + destruct a; destruct vs; reflexivity.
    + rewrite list_tuple_cons_cons.
      rewrite embed_tuple_cons_cons.
      rewrite list_lchtuple_cons_cons.
      rewrite map_cons.
      rewrite IHl.
      f_equal.
      destruct vs; simpl.
      destruct a.
      * destruct s0; reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
Qed.

Lemma app_sopn_list_correct (op : opN) (v : sem_t (type_of_opN op).2) (vs : values) :
  app_sopn (type_of_opN op).1 (sem_opN_typed op) vs = ok v →
  app_sopn_list
    (type_of_opN op).1
    (sem_opN_typed op)
    [seq to_typed_chElement (translate_value v) | v <- vs]
  =
  embed v.
Proof.
  intro H.
  destruct op as [w p | c].
  - simpl in *.
    apply app_sopn_nil_ok_size in H as hl.
    rewrite size_nseq in hl. rewrite hl.
    rewrite hl in H.
    set (f := curry _ _) in *. clearbody f.
    induction vs as [| v' vs ih] in v, w, f, H |- *.
    + simpl in *. rewrite H. reflexivity.
    + simpl in *. jbind H v1 hv1.
      eapply ih. eapply translate_to_int in hv1.
      rewrite hv1. assumption.
  - simpl in *.
    repeat (destruct vs; [repeat jbind_fresh H; discriminate|]).
    destruct vs. 2: repeat jbind_fresh H; discriminate.
    repeat jbind_fresh H.
    inversion H.
    destruct (cf_tbl c) as [[] []].
    all: simpl in *; erewrite translate_to_bool; [|eassumption]; try reflexivity.
    all: erewrite translate_to_bool; [|eassumption]; try reflexivity.
    all: erewrite translate_to_bool; [|eassumption]; try reflexivity.
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
  - (* Psub *)
    simpl. simpl in h1.
    jbind h1 nt hnt. destruct nt. all: try discriminate.
    jbind h1 i hi. jbind hi i' hi'. jbind h1 t ht. noconf h1.
    eapply u_bind.
    1:{ eapply translate_gvar_correct. all: eauto. }
    rewrite bind_assoc.
    eapply u_bind.
    1:{ eapply IHe. all: eauto. }
    eapply u_ret. intros m hm.
    split. 1: assumption.
    rewrite coerce_to_choice_type_K.
    erewrite translate_pexpr_type. 2: eassumption.
    rewrite coerce_to_choice_type_K.
    erewrite translate_to_int. 2: eassumption.
    apply type_of_get_gvar in hnt. rewrite <- hnt.
    rewrite !coerce_to_choice_type_K.
    apply chArray_get_sub_correct.
    assumption.
  - (* Pload *)
    simpl in h1. jbind h1 w1 hw1. jbind hw1 vx hvx.
    jbind h1 w2 hw2. jbind hw2 v2 hv2. jbind h1 w hw. noconf h1.
    simpl.
    eapply u_get_remember. simpl. intros x'.
    rewrite bind_assoc.
    eapply u_bind.
    1:{
      eapply IHe. 1: eassumption.
      intros ? []. eauto.
    }
    simpl.
    eapply u_get_remember. intros mem.
    eapply u_ret. unfold u_get. intros m [[hm e1] e2].
    split. 1: assumption.
    subst.
    rewrite coerce_to_choice_type_K.
    erewrite translate_pexpr_type. 2: eassumption.
    rewrite coerce_to_choice_type_K.
    erewrite translate_to_word. 2: eassumption.
    eapply hcond in hm.
    erewrite get_var_get_heap. 2-3: eassumption.
    simpl. erewrite <- type_of_get_var. 2: eassumption.
    rewrite coerce_to_choice_type_K.
    eapply translate_to_word in hw1 as e1. rewrite e1. clear e1.
    eapply translate_read_estate. all: eassumption.
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
      f_equal.
      apply sop1_unembed_embed.
  - (* Papp2 *)
    simpl in *.
    jbind h1 v' h2.
    jbind h1 v'' h3.
    rewrite bind_assoc. simpl.
    eapply u_bind.
    1: eapply IHe1; eauto.
    rewrite bind_assoc. simpl.
    eapply u_bind.
    1: eapply IHe2; eauto.
    apply u_ret.
    intuition subst.
    unfold sem_sop2 in h1.
    jbind h1 v''' h4.
    jbind h1 v'''' h5.
    jbind h1 v''''' h6.
    noconf h1.
    rewrite coerce_to_choice_type_translate_value_to_val.
    apply translate_pexpr_type with (fn:=fn) in h2.
    apply translate_pexpr_type with (fn:=fn) in h3.
    rewrite h2 h3.
    rewrite !coerce_to_choice_type_K.
    erewrite translate_of_val.
    2: exact h4.
    erewrite translate_of_val.
    2: exact h5.
    rewrite coerce_to_choice_type_translate_value_to_val.
    rewrite coerce_to_choice_type_translate_value_to_val.
    rewrite sop2_unembed_embed.
    rewrite h6.
    reflexivity.
  - (* PappN *)
    simpl in *.
    jbind h1 v' h2.
    jbind h1 v'' h3.
    noconf h1.
    (* jbind h3 v''' h4. *)
    eapply u_bind.
    + eapply bind_list_correct with (vs := v').
      * rewrite <- map_comp.
        unfold comp.
        eapply translate_pexprs_types.
        eassumption.
      (* this should maybe be a lemma or the condition in bind_list_correct should be rewrote to match H *)
      * clear -h2 H hcond.
        revert v' h2 H.
        induction es; intros.
        ** inversion h2.
           constructor.
        ** inversion h2.
           jbind H1 x Hx.
           jbind H1 y Hy.
           noconf H1.
           constructor.
           *** eapply H.
               1: apply mem_head.
               1: eassumption.
               assumption.
           *** eapply IHes.
               1: assumption.
               intros.
               eapply H.
               { rewrite in_cons. rewrite H0. by apply /orP; right. }
               1: eassumption.
               assumption.
    + apply u_ret.
      intros; split; auto.
      rewrite coerce_to_choice_type_translate_value_to_val.
      apply app_sopn_list_correct.
      assumption.
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
Qed.

Lemma translate_pexprs_correct fn s vs es :
  sem_pexprs gd s es = ok vs ->
  List.Forall2 (λ c v, ⊢ ⦃ rel_estate s fn ⦄ c.π2 ⇓ coerce_to_choice_type _ (translate_value v) ⦃ rel_estate s fn ⦄) [seq translate_pexpr fn e | e <- es] vs.
Proof.
  revert vs. induction es; intros vs hvs.
  - destruct vs.
    + constructor.
    + inversion hvs.
  - destruct vs.
    + inversion hvs.
      jbind H0 vs' hvs'.
      jbind H0 vs'' hvs''.
      noconf H0.
    + inversion hvs.
      jbind H0 vs' hvs'.
      jbind H0 vs'' hvs''.
      noconf H0.
      rewrite map_cons.
      constructor.
      * eapply translate_pexpr_correct.
        1: eassumption.
        easy.
      * eapply IHes.
        assumption.
Qed.

Corollary translate_pexpr_correct_cast :
  ∀ fn (e : pexpr) s₁ v (cond : heap → Prop),
    sem_pexpr gd s₁ e = ok v →
    (∀ m, cond m → rel_estate s₁ fn m) →
    ⊢ ⦃ cond ⦄
      coerce_typed_code _ (translate_pexpr fn e) ⇓
      translate_value v
    ⦃ cond ⦄.
Proof.
  intros fn e s v cond he hcond.
  eapply translate_pexpr_correct with (fn := fn) in he as h. 2: exact hcond.
  eapply translate_pexpr_type with (fn := fn) in he.
  unfold choice_type_of_val in he.
  destruct (translate_pexpr) as [? exp] eqn:?. simpl in *. subst.
  rewrite coerce_to_choice_type_K in h.
  rewrite coerce_typed_code_K. assumption.
Qed.

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

Lemma injective_translate_var :
  ∀ fn, injective (translate_var fn).
Proof.
Admitted.

Lemma translate_write_correct :
  ∀ fn sz s p (w : word sz) cm (cond : heap → Prop),
    (∀ m, cond m → write s.(emem) p w = ok cm ∧ rel_estate s fn m) →
    ⊢ ⦃ cond ⦄ translate_write p w ⇓ tt ⦃ rel_estate {| emem := cm ; evm := s.(evm) |} fn ⦄.
Proof.
  intros fn sz s p w cm cond h.
  unfold translate_write.
  eapply u_get_remember. intros m.
  eapply u_put.
  eapply u_ret_eq.
  intros ? [m' [[h1 h2] ?]]. subst.
  unfold u_get in h2. subst.
  eapply h in h1. destruct h1.
  eapply translate_write_estate. all: assumption.
Qed.

Lemma translate_write_var_estate :
  ∀ fn i v s1 s2 m,
    write_var i v s1 = ok s2 →
    rel_estate s1 fn m →
    rel_estate s2 fn (set_heap m (translate_var fn i) (truncate_el i.(vtype) (translate_value v))).
Proof.
  intros fn i v s1 s2 m hw [h1 h2].
  unfold write_var in hw. jbind hw vm hvm. noconf hw.
  split. all: simpl.
  - intros ptr v' er.
    eapply h1 in er.
    rewrite get_set_heap_neq. 2: apply mem_loc_translate_var_neq.
    assumption.
  - intros vi v' ev.
    eapply set_varP. 3: exact hvm.
    + intros v₁ hv₁ eyl. subst.
      destruct (vi == i) eqn:evar.
      all: move: evar => /eqP evar.
      * subst. rewrite Fv.setP_eq in ev. noconf ev.
        rewrite get_set_heap_eq. rewrite coerce_to_choice_type_K.
        eapply translate_of_val in hv₁ as e.
        rewrite e. apply coerce_to_choice_type_translate_value_to_val.
      * rewrite Fv.setP_neq in ev.
        2:{ apply /eqP. eauto. }
        rewrite get_set_heap_neq.
        2:{
          apply /eqP. intro ee.
          apply injective_translate_var in ee.
          contradiction.
        }
        eapply h2 in ev. assumption.
    + intros hbo hyl hset. subst.
      destruct (vi == i) eqn:evar.
      all: move: evar => /eqP evar.
      1:{
        exfalso. subst. rewrite Fv.setP_eq in ev.
        clear - ev hbo. destruct (vtype i). all: discriminate.
      }
      rewrite Fv.setP_neq in ev.
      2:{ apply /eqP. eauto. }
      rewrite get_set_heap_neq.
      2:{
        apply /eqP. intro ee.
        apply injective_translate_var in ee.
        contradiction.
      }
      eapply h2 in ev. assumption.
Qed.

Lemma translate_write_lval_correct :
  ∀ es₁ es₂ fn y v,
    write_lval gd y v es₁ = ok es₂ →
    ⊢ ⦃ rel_estate es₁ fn ⦄
      translate_write_lval fn y (totce (translate_value v))
      ⇓ tt
    ⦃ rel_estate es₂ fn ⦄.
Proof.
  intros es₁ es₂ fn y v hw.
  destruct y as [ | yl | | aa ws x ei | ] eqn:case_lval.
  - simpl. apply u_ret_eq.
    intros hp hr.
    simpl in hw. unfold write_none in hw.
    destruct is_sbool eqn:eb.
    + unfold on_vu in hw. destruct of_val as [| []].
      all: noconf hw. all: assumption.
    + unfold on_vu in hw. destruct of_val as [| []].
      all: noconf hw. assumption.
  - simpl. unfold translate_write_var. simpl in hw.
    simpl.
    eapply u_put.
    apply u_ret_eq.
    intros m' [m [hm e]]. subst.
    eapply translate_write_var_estate. all: eassumption.
  - simpl. simpl in hw.
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
    simpl.
    eapply translate_write_correct. intros m' [hm' em'].
    unfold u_get in em'. subst.
    split. 2: assumption.
    erewrite translate_pexpr_type. 2: eassumption.
    rewrite !coerce_to_choice_type_K.
    eapply translate_to_word in hw' as ew. rewrite ew. clear ew.
    unfold translate_to_pointer. simpl.
    eapply translate_to_word in hve as ew. rewrite ew. clear ew.
    erewrite get_var_get_heap. 2,3: eassumption.
    simpl. erewrite <- type_of_get_var. 2: eassumption.
    rewrite coerce_to_choice_type_K.
    eapply translate_to_word in hvx as ew. rewrite ew. clear ew.
    assumption.
  - simpl. simpl in hw.
    jbind hw nt hnt. destruct nt. all: try discriminate.
    jbind hw i hi. jbind hi i' hi'.
    jbind hw w ew. jbind hw t ht.
    eapply u_get_remember. simpl. intros vx.
    rewrite !bind_assoc. simpl.
    eapply u_bind.
    1:{
      eapply translate_pexpr_correct.
      - eassumption.
      - intros ? []. assumption.
    }
    simpl. unfold translate_write_var. simpl.
    eapply u_put.
    eapply u_ret_eq.
    intros ? [m [[hs hm] ?]]. subst.
    unfold u_get in hm. subst.
    erewrite translate_pexpr_type. 2: eassumption.
    rewrite !coerce_to_choice_type_K.
    eapply translate_to_word in ew. rewrite ew.
    erewrite translate_to_int. 2: eassumption.
    erewrite get_var_get_heap. 2,3: eassumption.
    Opaque translate_value. simpl. Transparent translate_value.
    eapply type_of_get_var in hnt as ety. simpl in ety.
    apply (f_equal encode) in ety. simpl in ety.
    rewrite -ety. rewrite !coerce_to_choice_type_K.
    erewrite chArray_set_correct. 2: eassumption.
    eapply translate_write_var_estate in hs. 2: eassumption.
    assumption.
  - admit.
Admitted.

Lemma translate_write_lvals_cons fn l ls v vs :
  translate_write_lvals fn (l :: ls) (v :: vs) = (translate_write_lval fn l v ;; translate_write_lvals fn ls vs).
Proof. reflexivity. Qed.

Lemma translate_write_lvals_correct fn s1 ls vs s2 :
  write_lvals gd s1 ls vs = ok s2 ->
  ⊢ ⦃ rel_estate s1 fn ⦄
     translate_write_lvals fn ls [seq totce (translate_value v) | v <- vs]
  ⇓
     tt
  ⦃ rel_estate s2 fn ⦄.
Proof.
  intros.
  revert s1 vs H.
  induction ls as [| l ls]; intros s1 vs H.
  - destruct vs. 2: discriminate.
    noconf H.
    apply u_ret_eq.
    easy.
  - destruct vs. 1: inversion H.
    inversion H.
    jbind H1 s3 Hs3.
    rewrite map_cons.
    rewrite translate_write_lvals_cons.
    eapply u_bind.
    + eapply translate_write_lval_correct.
      eassumption.
    + apply IHls.
      assumption.
Qed.

Definition ssprove_prog := seq (funname * fdef).

Definition exports_of_prog (p : ssprove_prog) : {fmap funname -> opsig} :=
  foldl (λ m f, setm m f.1 (nat_of_pos f.1, (ty_in f.2, ty_out f.2)))
        emptym p.

Definition translate_prog : ssprove_prog :=
  foldl (λ p f,
    let f' := translate_fundef (exports_of_prog p) f in
    f' :: p
  ) [::] P.(p_funcs).

(** Handled programs

  This predicate eliminates programs that are currently not supported by the
  translation. This is mainly used to disallow while loops.
*)

Fixpoint handled_instr (i : instr) :=
  match i with
  | MkI ii i => handled_instr_r i
  end

with handled_instr_r (i : instr_r) :=
  match i with
  | Cassgn l tag sty e => true
  | Copn l tag o es => true
  | Cif e c₁ c₂ => List.forallb handled_instr c₁ && List.forallb handled_instr c₂
  | Cfor i r c => List.forallb handled_instr c
  | Cwhile al cb e c => false
  | Ccall ii l fn es => true
  end.

Definition handled_cmd (c : cmd) :=
  List.forallb handled_instr c.

Definition handled_fundecl (f : _ufun_decl) :=
  handled_cmd f.2.(f_body).

Definition handled_program :=
  List.forallb handled_fundecl P.(p_funcs).

Theorem translate_prog_correct (fn : funname) m va m' vr f :
  handled_program →
  sem.sem_call P m fn va m' vr →
  let sp := translate_prog in
  let dom := lchtuple (map choice_type_of_val va) in
  let cod := lchtuple (map choice_type_of_val vr) in
  get_fundef_ssp sp fn dom cod = Some f →
  ⊢ ⦃ λ m, True ⦄
    f (translate_values va) ⇓ translate_values vr
  ⦃ λ m, True ⦄.
Proof.
  intros hP H.
  set (Pfun :=
    λ (m : mem) (fn : funname) (va : seq value) (m' : mem) (vr : seq value),
      ∀ f,
        handled_program →
        let sp := translate_prog in
        let dom := lchtuple [seq choice_type_of_val i | i <- va] in
        let cod := lchtuple [seq choice_type_of_val i | i <- vr] in
        get_fundef_ssp sp fn dom cod = Some f →
        ⊢ ⦃ λ m, True ⦄
          f (translate_values va) ⇓ translate_values vr
        ⦃ λ m, True ⦄
  ).
  set (ep := exports_of_prog translate_prog).
  set (Pi_r :=
    λ (s1 : estate) (i : instr_r) (s2 : estate),
      handled_instr_r i →
      ⊢ ⦃ rel_estate s1 fn ⦄
        translate_instr_r ep fn i ⇓ tt
      ⦃ rel_estate s2 fn ⦄
  ).
  set (Pi := λ s1 i s2, Pi_r s1 (instr_d i) s2).
  set (Pc :=
    λ (s1 : estate) (c : cmd) (s2 : estate),
      handled_cmd c →
      ⊢ ⦃ rel_estate s1 fn ⦄ translate_cmd ep fn c ⇓ tt ⦃ rel_estate s2 fn ⦄
  ).
  set (Pfor :=
    λ (v : var_i) (ws : seq Z) (s1 : estate) (c : cmd) (s2 : estate),
      handled_cmd c →
      ⊢ ⦃ rel_estate s1 fn ⦄
        translate_for fn v ws (translate_cmd ep fn c) ⇓ tt
      ⦃ rel_estate s2 fn ⦄
  ).
  unshelve eapply (@sem_call_Ind _ _ _ _ Pc Pi_r Pi Pfor Pfun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  - (* nil *)
    red. intros s.
    red. simpl. intros _.
    eapply u_ret_eq. auto.
  - (* cons *)
    red. intros s1 s2 s3 i c hi ihi hc ihc.
    red. simpl. move /andP => [hdi hdc].
    eapply u_bind.
    + rewrite translate_instr_unfold. eapply ihi.
      destruct i. apply hdi.
    + apply ihc. assumption.
  - (* mkI *)
    red. intros ii i s1 s2 hi ihi.
    apply ihi.
  - (* assgn *)
    red. intros s₁ s₂ x tag ty e v v' he hv hw.
    red. simpl. intros _.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct. all: eauto. }
    erewrite translate_pexpr_type by eassumption.
    rewrite coerce_to_choice_type_K.
    erewrite totce_truncate_translate by eassumption.
    eapply translate_write_lval_correct. all: eauto.
  - (* opn *)
    red. intros s1 s2 tag o xs es ho _.
    red. simpl.
    jbind ho vs hv.
    jbind hv vs' hv'.
    eapply u_bind.
    + eapply bind_list_correct.
      * rewrite <- map_comp. unfold comp.
        eapply translate_pexprs_types.
        eassumption.
      * apply translate_pexprs_correct.
        assumption.
    + erewrite translate_exec_sopn_correct by eassumption.
      apply translate_write_lvals_correct.
      assumption.
  - (* if_true *)
    red. intros s1 s2 e c1 c2 he hc1 ihc1.
    red. simpl. move /andP => [hdc1 hdc2].
    lazymatch goal with
    | |- context [ if _ then ?f ?fn ?c else _ ] =>
      change (f fn c) with (translate_cmd ep fn c)
    end.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in he. all: eauto. }
    simpl. apply ihc1. assumption.
  - (* if_false *)
    red. intros s1 s2 e c1 c2 he hc2 ihc2.
    red. simpl. move /andP => [hdc1 hdc2].
    (* lazymatch goal with
    | |- context [ if _ then _ else (?f ?fn ?c) ] =>
      change (f fn c) with (translate_cmd ep fn c)
    end. *)
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in he. all: eauto. }
    simpl. apply ihc2. assumption.
  - (* while_true *)
    red. intros s1 s2 s3 s4 a c e c' hc ihc he hc' ihc' h ih.
    red. simpl. discriminate.
  - (* while_false *)
    red. intros s1 s2 a c e c' hc ihc he.
    red. simpl. discriminate.
  - (* for *)
    red. intros s1 s2 i d lo hi c vlo vhi hlo hhi hfor ihfor.
    red. simpl. intros hdc.
    lazymatch goal with
    | |- context [ translate_for _ _ _ (?f ?fn ?c) ] =>
      change (f fn c) with (translate_cmd ep fn c)
    end.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in hlo. all: eauto. }
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in hhi. all: eauto. }
    apply ihfor. assumption.
  - (* for_nil *)
    red. intros. red. intros hdc.
    simpl. apply u_ret_eq. auto.
  - (* for_cons *)
    red. intros s1 s1' s2 s3 i w ws c hw hc ihc hfor ihfor.
    red. simpl. intros hdc.
    eapply u_put.
    eapply u_bind.
    1:{
      red in ihc. eapply u_pre_weaken_rule.
      1: eapply ihc. 1: assumption.
      intros ? [me [hme ?]]. subst.
      eapply translate_write_var_estate. all: eassumption.
    }
    apply ihfor. assumption.
  - (* call *)
    red. intros s1 m2 s2 ii xs gn args vargs vs hargs hvs ihvs hw.
    red. simpl. intros _.
    admit.
  - red. intros m1 m2 gn g vs vs' s1 vm2 vrs vrs'.
    intros hg hvs ?????.
    unfold Pfun. intros f' hdp hf'.
    (* Maybe have a dedicated lemma linking to hg? *)
    unfold get_fundef_ssp in hf'.
    admit.
Admitted.

End Translation.
