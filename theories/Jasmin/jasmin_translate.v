Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import expr compiler_util values sem.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths".
(* Silencing the following warning: *)
(* New coercion path [Pbool] : bool >-> pexpr is ambiguous with existing  *)
(* [nat_of_bool; Posz; int_to_Z; Pconst] : bool >-> pexpr. *)
From Jasmin Require Import expr_facts.
Set Warnings "ambiguous-paths".

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
Set Default Proof Using "Type".

Derive NoConfusion for result.
Derive NoConfusion for value.
Derive NoConfusion for wsize.
(* Derive NoConfusion for (word wsize). *)
Derive EqDec for wsize.

Local Open Scope positive_scope.

Notation p_id := BinNums.positive.

Lemma nat_of_pos_nonzero :
  ∀ p,
    nat_of_pos p ≠ 0%nat.
Proof.
  intros p. induction p as [p ih | p ih |].
  - simpl. micromega.Lia.lia.
  - simpl. rewrite NatTrec.doubleE.
    move => /eqP. rewrite double_eq0. move /eqP. assumption.
  - simpl. micromega.Lia.lia.
Qed.

Lemma injective_nat_of_pos :
  forall p1 p2, nat_of_pos p1 = nat_of_pos p2 -> p1 = p2.
Proof.
  intros p1. induction p1 as [p1 ih | p1 ih |]; intros.
  - destruct p2.
    + inversion H.
      f_equal. apply ih.
      apply double_inj.
      rewrite -!NatTrec.doubleE.
      assumption.
    + inversion H.
      rewrite !NatTrec.doubleE in H1.
      apply f_equal with (f:=odd) in H1.
      simpl in H1.
      rewrite !odd_double in H1.
      easy.
    + inversion H.
      move: H1 => /eqP.
      rewrite NatTrec.doubleE double_eq0 => /eqP H1.
      apply nat_of_pos_nonzero in H1 as [].
  - destruct p2.
    + inversion H.
      rewrite !NatTrec.doubleE in H1.
      apply f_equal with (f:=odd) in H1.
      simpl in H1.
      rewrite !odd_double in H1.
      easy.
    + inversion H.
      f_equal. apply ih.
      apply double_inj.
      rewrite -!NatTrec.doubleE.
      assumption.
    + inversion H.
      rewrite !NatTrec.doubleE in H1.
      apply f_equal with (f:=odd) in H1.
      simpl in H1.
      rewrite !odd_double in H1.
      easy.
  - destruct p2.
    + inversion H.
      move: H1 => /eqP.
      rewrite eq_sym NatTrec.doubleE double_eq0 => /eqP H1.
      apply nat_of_pos_nonzero in H1 as [].
    + inversion H.
      rewrite !NatTrec.doubleE in H1.
      apply f_equal with (f:=odd) in H1.
      simpl in H1.
      rewrite !odd_double in H1.
      easy.
    + reflexivity.
Qed.

Definition nat_of_p_id : p_id -> nat := nat_of_pos.
Definition nat_of_p_id_nonzero : forall p, nat_of_p_id p <> 0%nat := nat_of_pos_nonzero.
Definition nat_of_p_id_injective : injective nat_of_p_id := injective_nat_of_pos.

Inductive preceq : p_id -> p_id -> Prop :=
| preceqEq : forall i, preceq i i
| preceqI : forall i1 i2, preceq i1 i2 -> preceq i1 i2~1
| preceqO : forall i1 i2, preceq i1 i2 -> preceq i1 i2~0.
Infix "⪯" := preceq (at level 70).

Definition prec i1 i2 := i1 ⪯ i2 /\ i1 <> i2.
Infix "≺" := prec (at level 70).

#[export] Instance preceq_trans : Transitive preceq.
Proof.
  intros i1 i2 i3 hi1 hi2.
  induction hi2.
  - assumption.
  - constructor.
    apply IHhi2.
    assumption.
  - constructor.
    apply IHhi2.
    assumption.
Qed.

#[export] Instance preceq_refl : Reflexive preceq.
Proof.
  intros i. induction i; constructor; assumption.
Qed.

Lemma preceq_size :
  forall i j, i ⪯ j -> Pos.size i <= Pos.size j.
Proof.
  intros i j h.
  induction h.
  - reflexivity.
  - simpl; micromega.Lia.lia.
  - simpl; micromega.Lia.lia.
Qed.

Lemma preceq_I :
  forall i, i ⪯ i~1.
Proof.
  intros. constructor. reflexivity.
Qed.

Lemma preceq_O :
  forall i, i ⪯ i~0.
Proof.
  intros. constructor. reflexivity.
Qed.

Lemma xO_neq :
  forall i, i~0 <> i.
Proof.
  induction i; congruence.
Qed.

Lemma xI_neq :
  forall i, i~1 <> i.
Proof.
  induction i; congruence.
Qed.

Lemma precneq_O :
  forall i, ~ i~0 ⪯ i.
Proof.
  intros i contra.
  apply preceq_size in contra.
  simpl in contra.
  micromega.Lia.lia.
Qed.

Lemma precneq_I :
  forall i, ~ i~1 ⪯ i.
Proof.
  intros i contra.
  apply preceq_size in contra.
  simpl in contra.
  micromega.Lia.lia.
Qed.

Lemma size_1 :
  forall i, Pos.size i = 1 -> i = 1.
Proof.
  intros i h.
  induction i.
  - simpl in *.
    micromega.Lia.lia.
  - simpl in *.
    micromega.Lia.lia.
  - reflexivity.
Qed.

Lemma preceq_size_eq_eq :
  forall i j, Pos.size i = Pos.size j -> i ⪯ j -> i = j.
Proof.
  intros i j; revert i; induction j; intros i hsize hprec.
  - simpl in *.
    inversion hprec; subst.
    + reflexivity.
    + destruct i.
      * simpl in *.
        apply Pos.succ_inj in hsize.
        apply IHj in hsize.
        1: subst; auto.
        etransitivity.
        1: eapply preceq_I.
        assumption.
      * simpl in *.
        apply Pos.succ_inj in hsize.
        apply IHj in hsize.
        1: subst; auto.
        1: apply precneq_O in H1; easy.
        etransitivity.
        1: eapply preceq_O.
        assumption.
      * simpl in hsize.
        micromega.Lia.lia.
  - simpl in *.
    inversion hprec; subst.
    + reflexivity.
    + destruct i.
      * simpl in *.
        apply Pos.succ_inj in hsize.
        apply IHj in hsize.
        1: subst; auto.
        1: apply precneq_I in H1; easy.
        etransitivity.
        1: eapply preceq_I.
        assumption.
      * simpl in *.
        apply Pos.succ_inj in hsize.
        apply IHj in hsize.
        1: subst; auto.
        etransitivity.
        1: eapply preceq_O.
        assumption.
      * simpl in hsize.
        micromega.Lia.lia.
  - simpl in hsize.
    apply size_1.
    assumption.
Qed.

#[export] Instance preceq_antisym : Antisymmetric _ _ preceq.
Proof.
  intros i1 i2 h1 h2.
  apply preceq_size in h1 as hsize1.
  apply preceq_size in h2 as hsize2.
  apply preceq_size_eq_eq.
  1: micromega.Lia.lia.
  assumption.
Qed.

Lemma preceq_prefix : forall i1 i2 i3, i1 ⪯ i3 -> i2 ⪯ i3 -> i1 ⪯ i2 \/ i2 ⪯ i1.
Proof.
  intros i1 i2 i3.  revert i1 i2.
  induction i3; intros.
  - inversion H; subst.
    + right. assumption.
    + inversion H0; subst.
      * left; assumption.
      * apply IHi3; assumption.
  - inversion H; subst.
    + right. assumption.
    + inversion H0; subst.
      * left; assumption.
      * apply IHi3; assumption.
  - inversion H; subst.
    inversion H0; subst.
    left; constructor.
Qed.

Definition fresh_id i :=
  (i~0, i~1).

Lemma prec_neq p fp : p ≺ fp -> p <> fp.
Proof. unfold prec. easy. Qed.

Lemma prec_precneq i1 i2 : i1 ≺ i2 -> ~ i2 ⪯ i1.
Proof.
  intros H contra.
  eapply prec_neq.
  1: exact H.
  apply antisymmetry; auto.
  apply H.
Qed.

#[export] Instance prec_trans : Transitive prec.
Proof.
  intros i1 i2 i3.
  intros [hpre1 hneq1] [hpre2 hneq2].
  split.
  - etransitivity; eauto.
  - intro contra; subst.
    apply hneq2.
    apply antisymmetry; assumption.
Qed.

Lemma fresh1 i : i ≺ (fresh_id i).1.
Proof.
  simpl; split.
  - apply preceq_O.
  - apply nesym. apply xO_neq.
Qed.

Lemma fresh2 i : i ≺ (fresh_id i).2.
Proof.
  simpl; split.
  - apply preceq_I.
  - apply nesym. apply xI_neq.
Qed.

Lemma preceq_prec_trans : forall p1 p2 p3, p1 ⪯ p2 -> p2 ≺ p3 -> p1 ≺ p3.
Proof.
  intros p1 p2 p3 h1 [h2 h3].
  split.
  - etransitivity; eauto.
  - intros contra; subst.
    apply h3. apply antisymmetry; assumption.
Qed.

Lemma prec_preceq_trans : forall p1 p2 p3, p1 ≺ p2 -> p2 ⪯ p3 -> p1 ≺ p3.
Proof.
  intros p1 p2 p3 [h1 h2] h3.
  split.
  - etransitivity; eauto.
  - intros contra; subst.
    apply h2. apply antisymmetry; assumption.
Qed.

Lemma fresh1_weak s_id : s_id ⪯ s_id~0.
Proof. apply fresh1. Qed.

Lemma fresh2_weak s_id : s_id ⪯ s_id~1.
Proof. apply fresh2. Qed.

Definition disj i1 i2 :=
  forall i3, i1 ⪯ i3 -> ~ i2 ⪯ i3.

Lemma disj_antirefl i : ~ disj i i.
Proof.
  intros contra.
  unfold disj in contra.
  specialize (contra i ltac:(reflexivity)).
  apply contra. reflexivity.
Qed.

#[export] Instance disj_sym : Symmetric disj.
Proof.
  intros i1 i2 hi1 i3 hi2.
  intros contra.
  apply hi1 in contra.
  contradiction.
Qed.

Lemma fresh_disj i :
  disj (fresh_id i).1 (fresh_id i).2.
Proof.
  intros i' h contra.
  simpl in *.
  pose proof preceq_prefix i~0 i~1 i' h contra.
  destruct H.
  - inversion H; subst.
    eapply precneq_O; eassumption.
  - inversion H; subst.
    eapply precneq_I; eassumption.
Qed.

Lemma disj_prec_l : forall id1 id2 id3, id1 ⪯ id2 -> disj id1 id3 -> disj id2 id3.
Proof.
  intros id1 id2 id3 hpre hdisj.
  intros id' hprec.
  apply hdisj.
  etransitivity; eauto.
Qed.

Lemma disj_prec_r : forall id1 id2 id3, id1 ⪯ id2 -> disj id3 id1 -> disj id3 id2.
Proof.
  intros id1 id2 id3 hpre hdisj.
  apply disj_sym.
  eapply disj_prec_l; eauto.
  apply disj_sym; assumption.
Qed.

Lemma disj_prec : forall id1 id2 id3 id4, id1 ⪯ id2 -> id3 ⪯ id4 -> disj id1 id3 -> disj id2 id4.
Proof.
  intros.
  eapply disj_prec_l; eauto.
  eapply disj_prec_r; eauto.
Qed.

#[export] Hint Resolve fresh1 fresh2 fresh1_weak fresh2_weak preceq_refl preceq_trans prec_trans : prefix.

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

Definition typed_chElement :=
  pointed_value.

Definition to_typed_chElement {t : choice_type} (v : t) : typed_chElement :=
  (t ; v).

Definition typed_code :=
  ∑ (a : choice_type), raw_code a.

Definition encode (t : stype) : choice_type :=
  match t with
  | sbool => 'bool
  | sint => 'int
  | sarr n => (chMap 'int ('word U8))
  | sword n => 'word n
  end.

Definition embed_array {len} (a : WArray.array len) : (chMap 'int ('word U8)) :=
  Mz.fold (λ k v m, setm m k v) a.(WArray.arr_data) emptym.

Definition embed {t} : sem_t t → encode t :=
  match t with
  | sbool => λ x, x
  | sint => λ x, x
  | sarr n => embed_array
  | sword n => λ x, x
  end.

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

Definition choice_type_of_val (val : value) : choice_type :=
  encode (type_of_val val).

(* Tactic to deal with Let _ := _ in _ = ok _ in assumption h *)
(* x and hx are introduced names for the value and its property *)
Ltac jbind h x hx :=
  eapply rbindP ; [| exact h ] ;
  clear h ; intros x hx h ;
  cbn beta in h.

Module JasminNotation.
  Notation " 'array " := (chMap 'int ('word U8)) (at level 2) : package_scope.
  Notation " 'array " := (chMap 'int ('word U8)) (in custom pack_type at level 2).
  Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (at level 2) : package_scope.
  Notation " 'mem " := (chMap ('word Uptr) ('word U8)) (in custom pack_type at level 2).
  Notation totce := to_typed_chElement.
  Notation coe_cht := coerce_to_choice_type.
  Notation coe_tyc := coerce_typed_code.

End JasminNotation.

Import JasminNotation.

Section Translation.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context (gd : glob_decls).
Context `{sc_sem : syscall_sem }.

Definition mem_index : nat := 0.
Definition mem_loc : Location := ('mem ; mem_index).

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

Definition nat_of_stype t : nat :=
  match t with
  | sbool => 5
  | sint => 7
  | sarr len => 11 ^ (Pos.to_nat len)
  | sword ws => 13 ^ ws
  end.

(* injection *)
Definition nat_of_p_id_ident (p : p_id) (id : Ident.ident) : nat :=
  3^(nat_of_p_id p) * 2^(nat_of_ident id).

Definition nat_of_p_id_var (p : p_id) (x : var) : nat :=
  (nat_of_stype x.(vtype) * (nat_of_p_id_ident p x.(vname)))%coq_nat.

Definition translate_var (p : p_id) (x : var) : Location :=
  (encode x.(vtype) ; nat_of_p_id_var p x).

Lemma Natpow_expn :
  ∀ (n m : nat),
    (n ^ m)%nat = expn n m.
Proof.
  intros n m.
  induction m as [| m ih] in n |- *.
  - cbn. reflexivity.
  - simpl. rewrite expnS. rewrite -ih. reflexivity.
Qed.

Lemma Mpowmodn :
  ∀ d n,
    n ≠ 0%nat →
    d ^ n %% d = 0%nat.
Proof.
  intros d n hn.
  destruct n as [| n]. 1: contradiction.
  simpl. apply modnMr.
Qed.

Lemma nat_of_ident_pos :
  ∀ x, (0 < nat_of_ident x)%coq_nat.
Proof.
  intros x. induction x as [| a s ih].
  - auto.
  - simpl.
    rewrite -mulP. rewrite -plusE.
    micromega.Lia.lia.
Qed.

Lemma injective_nat_of_ident :
  ∀ x y,
    nat_of_ident x = nat_of_ident y →
    x = y.
Proof.
  intros x y e.
  induction x as [| a x] in y, e |- *.
  all: destruct y as [| b y].
  all: simpl in e.
  - reflexivity.
  - rewrite -mulP in e. rewrite -plusE in e.
    pose proof (nat_of_ident_pos y).
    micromega.Lia.lia.
  - rewrite -mulP in e. rewrite -plusE in e.
    pose proof (nat_of_ident_pos x).
    micromega.Lia.lia.
  - apply (f_equal (λ a, Nat.modulo a 256)) in e as xy_eq.
    rewrite -Nat.add_mod_idemp_l in xy_eq. 2: micromega.Lia.lia.
    rewrite -Nat.mul_mod_idemp_l in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.mod_same in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.mul_0_l in xy_eq.
    rewrite Nat.mod_0_l in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.add_0_l in xy_eq.
    rewrite -Nat.add_mod_idemp_l in xy_eq. 2: micromega.Lia.lia.
    rewrite -Nat.mul_mod_idemp_l in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.mod_same in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.mul_0_l in xy_eq.
    rewrite Nat.mod_0_l in xy_eq. 2: micromega.Lia.lia.
    rewrite Nat.add_0_l in xy_eq.
    rewrite !Nat.mod_small in xy_eq. 2,3: apply Ascii.nat_ascii_bounded.
    apply OrderedTypeEx.String_as_OT.nat_of_ascii_inverse in xy_eq.
    subst. f_equal.
    apply IHx.
    rewrite -!addP in e.
    rewrite -!mulP in e.
    micromega.Lia.lia.
Qed.

Lemma injective_nat_of_p_id_ident :
  ∀ p x y,
    nat_of_p_id_ident p x = nat_of_p_id_ident p y →
    x = y.
Proof.
  intros p x y e.
  unfold nat_of_p_id_ident in e.
  apply Nat.mul_cancel_l in e. 2: apply Nat.pow_nonzero ; auto.
  eapply Nat.pow_inj_r in e. 2: auto.
  apply injective_nat_of_ident. assumption.
Qed.

Lemma coprime_mul_inj a b c d :
  coprime a d →
  coprime a b →
  coprime c b →
  coprime c d →
  (a * b = c * d)%nat →
  a = c ∧ b = d.
Proof.
  intros ad ab cb cd e.
  move: e => /eqP. rewrite eqn_dvd. move=> /andP [d1 d2].
  rewrite Gauss_dvd in d1. 2: assumption.
  rewrite Gauss_dvd in d2. 2: assumption.
  move: d1 d2 => /andP [d11 d12] /andP [d21 d22].
  rewrite Gauss_dvdl in d11. 2: assumption.
  rewrite Gauss_dvdr in d12. 2: rewrite coprime_sym; assumption.
  rewrite Gauss_dvdl in d21. 2: assumption.
  rewrite Gauss_dvdr in d22. 2: rewrite coprime_sym; assumption.
  split.
  - apply /eqP. rewrite eqn_dvd. by apply /andP.
  - apply /eqP. rewrite eqn_dvd. by apply /andP.
Qed.

Lemma coprime_nat_of_stype_nat_of_fun_ident t p v :
 coprime (nat_of_stype t) (nat_of_p_id_ident p v).
Proof.
  unfold nat_of_p_id_ident.
  unfold nat_of_stype.
  rewrite coprimeMr.
  apply /andP.
  destruct t.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpr.
    1: auto.
    1: apply /ltP; apply nat_of_ident_pos.
    1: apply /ltP; pose proof nat_of_p_id_nonzero p; micromega.Lia.lia.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpr.
    1: auto.
    1: apply /ltP; apply nat_of_ident_pos.
    1: apply /ltP; pose proof nat_of_p_id_nonzero p; micromega.Lia.lia.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2,3: apply/ltP; micromega.Lia.lia.
    rewrite !coprime_pexpr.
    1: auto.
    1: apply /ltP; apply nat_of_ident_pos.
    1: apply /ltP; pose proof nat_of_p_id_nonzero p; micromega.Lia.lia.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2,3: auto.
    rewrite !coprime_pexpr.
    1: auto.
    1: apply /ltP; apply nat_of_ident_pos.
    1: apply /ltP; pose proof nat_of_p_id_nonzero p; micromega.Lia.lia.
Qed.

Lemma nat_of_p_id_pos : forall p, (0 < nat_of_p_id p)%coq_nat.
Proof.
  intros. pose proof nat_of_p_id_nonzero p. micromega.Lia.lia.
Qed.

Lemma injective2_nat_of_p_id_ident :
  injective2 nat_of_p_id_ident.
Proof.
  intros p gn x y e.
  unfold nat_of_p_id_ident in e.
  apply coprime_mul_inj in e as [p1_p2 x_y].
  - apply Nat.pow_inj_r in p1_p2; [|micromega.Lia.lia].
    apply Nat.pow_inj_r in x_y; [|micromega.Lia.lia].
    split.
    + apply injective_nat_of_pos. assumption.
    + apply injective_nat_of_ident. assumption.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2: apply /ltP; apply nat_of_p_id_pos.
    rewrite !coprime_pexpr.
    2: apply /ltP; apply nat_of_ident_pos.
    reflexivity.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2: apply /ltP; apply nat_of_p_id_pos.
    rewrite !coprime_pexpr.
    2: apply /ltP; apply nat_of_ident_pos.
    reflexivity.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2: apply /ltP; apply nat_of_p_id_pos.
    rewrite !coprime_pexpr.
    2: apply /ltP; apply nat_of_ident_pos.
    reflexivity.
  - rewrite !Natpow_expn.
    rewrite !coprime_pexpl.
    2: apply /ltP; apply nat_of_p_id_pos.
    rewrite !coprime_pexpr.
    2: apply /ltP; apply nat_of_ident_pos.
    reflexivity.
Qed.

Lemma injective_translate_var :
  ∀ p, injective (translate_var p).
Proof.
  intros p u v e.
  unfold translate_var in e.
  destruct u as [uty u], v as [vty v].
  simpl in e. noconf e.
  unfold nat_of_p_id_var in H0.
  simpl in H0.
  apply coprime_mul_inj in H0 as [e1 e2].
  2,3,4,5: apply coprime_nat_of_stype_nat_of_fun_ident.
  f_equal.
  - destruct uty, vty; auto; try discriminate.
    + apply Nat.pow_inj_r in e1. 2: auto.
      2: micromega.Lia.lia.
      apply Pos2Nat.inj in e1.
      subst; reflexivity.
    + noconf H. reflexivity.
  - eapply injective_nat_of_p_id_ident.
    eassumption.
Qed.

Lemma injective_translate_var2 :
  forall (p1 p2 : p_id) v1 v2, p1 <> p2 -> translate_var p1 v1 != translate_var p2 v2.
Proof.
  intros.
  apply /eqP => contra.
  unfold translate_var in contra.
  noconf contra.
  unfold nat_of_p_id_var in H1.
  apply coprime_mul_inj in H1 as [e1 e2].
  2,3,4,5: apply coprime_nat_of_stype_nat_of_fun_ident.
  apply injective2_nat_of_p_id_ident in e2 as [p_gn _].
  easy.
Qed.

Lemma injective_translate_var3 :
  forall (p1 p2 : p_id) v1 v2, vname v1 != vname v2 -> translate_var p1 v1 != translate_var p2 v2.
Proof.
  intros.
  apply /eqP => contra.
  unfold translate_var in contra.
  noconf contra.
  unfold nat_of_p_id_var in H1.
  apply coprime_mul_inj in H1 as [e1 e2].
  2,3,4,5: apply coprime_nat_of_stype_nat_of_fun_ident.
  apply injective2_nat_of_p_id_ident in e2 as [p_gn ?].
  move: H => /eqP contra.
  easy.
Qed.

Lemma coprimenn n : (coprime n n) = (n == 1%nat).
Proof. by unfold coprime; rewrite gcdnn. Qed.

Lemma coprime_neq p q : p != 1%nat -> coprime p q -> p <> q.
Proof.
  intros.
  move=>contra; subst.
  move: H=>/eqP H; apply H; apply/eqP.
  by rewrite -coprimenn.
Qed.

Lemma nat_of_wsize_inj : injective nat_of_wsize.
Proof. intros ws1 ws2. by case ws1; case ws2. Qed.

Lemma nat_of_stype_injective : injective nat_of_stype.
Proof.
  intros s t.
  case s; case t; try by [].
  - intros p H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + reflexivity.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expr.
  - intros ws H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + reflexivity.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expr.
  - intros l H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + reflexivity.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expr.
  - intros ws H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + reflexivity.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expr.
  - intros l H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      all: micromega.Lia.lia.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expl.
  - intros l H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      all: micromega.Lia.lia.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expl.
  - intros l1 l2 H.
    destruct (l2 == l1) eqn:E.
    + by move: E=>/eqP ->.
    + exfalso.
      move: E=>/eqP=>contra; apply contra.
      eapply Pos2Nat.inj. eapply Nat.pow_inj_r.
      2: eapply H. micromega.Lia.lia.
  - intros ws l H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      all: micromega.Lia.lia.
    + unfold nat_of_stype. rewrite !Natpow_expn coprime_expl; auto.
      by rewrite coprime_expr.
  - intros ws H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      1: micromega.Lia.lia.
      apply/eqP. by case ws.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expl.
  - intros ws H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      1: micromega.Lia.lia.
      apply/eqP. by case ws.
    + unfold nat_of_stype. by rewrite Natpow_expn coprime_expl.
  - intros l ws H.
    exfalso.
    eapply coprime_neq.
    3: eapply H.
    + unfold nat_of_stype. apply/eqP. apply nesym. apply Nat.lt_neq.
      apply Nat.pow_gt_1.
      1: micromega.Lia.lia.
      apply/eqP. by case ws.
    + unfold nat_of_stype. rewrite !Natpow_expn coprime_expl; auto.
      by rewrite coprime_expr.
  - intros ws1 ws2 H.
    destruct (ws2 == ws1) eqn:E.
    + by move: E=>/eqP ->.
    + exfalso.
      move: E=>/eqP=>contra; apply contra.
      eapply nat_of_wsize_inj.
      eapply Nat.pow_inj_r.
      2: eapply H. micromega.Lia.lia.
Qed.

Lemma nat_of_p_id_var_injective2 :
  injective2 nat_of_p_id_var.
Proof.
  intros i1 i2 v1 v2.
  unfold nat_of_p_id_var.
  intros H.
  apply coprime_mul_inj in H as [].
  2,3,4,5: apply coprime_nat_of_stype_nat_of_fun_ident.
  apply nat_of_stype_injective in H.
  apply injective2_nat_of_p_id_ident in H0 as [? ?].
  destruct v1, v2. simpl in *; subst.
  easy.
Qed.

Lemma translate_var_injective2 :
  injective2 translate_var.
Proof.
  intros i1 i2 v1 v2.
  unfold translate_var.
  move=> H.
  noconf H.
  apply nat_of_p_id_var_injective2 in H0.
  assumption.
Qed.

Lemma translate_var_eq i1 i2 v1 v2 :
  (translate_var i1 v1 == translate_var i2 v2) = (i1 == i2) && (v1 == v2).
Proof.
  apply/eqP.
  destruct (_ && _) eqn:E.
  - by move: E=>/andP [] /eqP -> /eqP ->.
  - move=>contra.
    apply translate_var_injective2 in contra as [? ?].
    subst.
    move: E=>/andP []. split; by apply/eqP.
Qed.

Lemma mem_loc_translate_var_neq :
  ∀ p x,
    mem_loc != translate_var p x.
Proof.
  intros p x.
  unfold mem_loc, translate_var.
  apply /eqP. intro e.
  destruct x as [ty i]. simpl in e. noconf e.
  destruct ty. all: discriminate.
Qed.

#[local] Definition unsupported : typed_code :=
  ('unit ; ret (chCanonical 'unit)).

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

Definition translate_write_var (p : p_id) (x : var_i) (v : typed_chElement) :=
  let l := translate_var p (v_var x) in
  #put l := truncate_el x.(vtype) v.π2 ;;
  ret tt.

Definition translate_get_var (p : p_id) (x : var) : raw_code (encode x.(vtype)) :=
  x ← get (translate_var p x) ;; ret x.

Fixpoint satisfies_globs (globs : glob_decls) : heap * heap → Prop.
Proof.
  exact (λ '(x, y), False). (* TODO *)
Defined.

Definition translate_gvar (p : p_id) (x : gvar) : raw_code (encode x.(gv).(vtype)) :=
  if is_lvar x
  then translate_get_var p x.(gv).(v_var)
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
      | None => remm data i
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

(* WArray.set_sub *)
Definition chArray_set_sub (ws : wsize) (len : BinNums.positive) (aa : arr_access) (a : 'array) (p : Z) (b : 'array) : 'array :=
  let size := arr_size ws len in
  let start := (p * mk_scale aa ws)%Z in
  foldr (λ i data,
    match b i with
    | Some w => setm data (start + i)%Z w
    | None => remm data (start + i)%Z
    end
  ) a (ziota 0 size).

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

Fixpoint tr_app_sopn {S R} (can : R) (emb : S → R) (ts : list stype) :=
  match ts as ts'
  return (sem_prod ts' (exec S) → [choiceType of list typed_chElement] → R)
  with
  | [::] =>
    λ (o : exec S) (vs : list typed_chElement),
      match vs with
      | [::] =>
        match o with
        | Ok o => emb o
        | _ => can
        end
      | _ :: _ => can
      end
  | t :: ts' =>
    λ (o : sem_t t → sem_prod ts' (exec S)) (vs : list typed_chElement),
      match vs with
      | [::] => can
      | v :: vs' => tr_app_sopn can emb ts' (o (unembed (truncate_el t v.π2))) vs'
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
Context {fcp : FlagCombinationParams}.
Definition embed_ot {t} : sem_ot t → encode t :=
  match t with
  | sbool => λ x,
    match x with
    | Some b => b
    | None => false
    end
  | sint => λ x, x
  | sarr n => embed_array
  | sword n => λ x, x
  end.

Definition encode_tuple (ts : list stype) : choice_type :=
  lchtuple [seq encode t | t <- ts].

(* takes a tuple of jasmin values and embeds each component *)
Fixpoint embed_tuple {ts} : sem_tuple ts → encode_tuple ts :=
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

(* tr_app_sopn specialized to when there is only one return value *)
Definition tr_app_sopn_single {t} :=
  tr_app_sopn (chCanonical (encode t)) embed.

(* tr_app_sopn specialized to when there is several return values *)
Definition tr_app_sopn_tuple {ts} :=
  tr_app_sopn (chCanonical (encode_tuple ts)) embed_tuple.

(* Following sem_pexpr *)
Fixpoint translate_pexpr (p : p_id) (e : pexpr) {struct e} : typed_code :=
  match e with
  | Pconst z => totc 'int (@ret 'int z) (* Why do we need to give 'int twice? *)
  | Pbool b => totc 'bool (ret b)
  | Parr_init n =>
    (* Parr_init only gets produced by ArrayInit() in jasmin source. *)
    (* The EC export asserts false on it. *)
    totc 'array (ret emptym)
  | Pvar v => totc _ (translate_gvar p v)
  | Pget aa ws x e =>
    totc ('word ws) (
      arr ← translate_gvar p x ;; (* Performs the lookup in gd *)
      let a := coerce_to_choice_type 'array arr in
      i ← (truncate_code sint (translate_pexpr p e)).π2 ;; (* to_int *)
      let scale := mk_scale aa ws in
      ret (chArray_get ws a i scale)
    )
  | Psub aa ws len x e =>
    totc 'array (
      arr ← translate_gvar p x ;; (* Performs the lookup in gd *)
      let a := coerce_to_choice_type 'array arr in
      i ← (truncate_code sint (translate_pexpr p e)).π2 ;; (* to_int *)
      let scale := mk_scale aa ws in
      ret (chArray_get_sub ws len a i scale)
    )
  | Pload sz x e =>
    totc ('word sz) (
      w ← translate_get_var p x ;;
      let w1 : word _ := truncate_el (sword Uptr) w in
      w2 ← (truncate_code (sword Uptr) (translate_pexpr p e)).π2 ;;
      chRead (w1 + w2)%R sz
    )
  | Papp1 o e =>
    totc _ (
      (* We truncate and call sem_sop1_typed instead of calling sem_sop1
        which does the truncation and then calls sem_sop1_typed.
      *)
      x ← (truncate_code (type_of_op1 o).1 (translate_pexpr p e)).π2 ;;
      ret (embed (sem_sop1_typed o (unembed x)))
    )
  | Papp2 o e1 e2 =>
    totc _ (
      (* Same here *)
      r1 ← (truncate_code (type_of_op2 o).1.1 (translate_pexpr p e1)).π2 ;;
      r2 ← (truncate_code (type_of_op2 o).1.2 (translate_pexpr p e2)).π2 ;;
      ret match sem_sop2_typed o (unembed r1) (unembed r2) with
      | Ok y => embed y
      | _ => chCanonical _
      end
    )
  | PappN op es =>
      (* note that this is sligtly different from Papp2 and Papp1, in that
         we don't truncate when we bind, but when we apply (in app_sopn_list).
         This made the proof easier, but is also more faithful to
         how it is done in jasmin.
       *)
    totc _ (
      vs ← bind_list [seq translate_pexpr p e | e <- es] ;;
      ret (tr_app_sopn_single (type_of_opN op).1 (sem_opN_typed op) vs)
    )
  | Pif t eb e1 e2 =>
    totc _ (
      b ← (truncate_code sbool (translate_pexpr p eb)).π2 ;; (* to_bool *)
      if b
      then (truncate_code t (translate_pexpr p e1)).π2
      else (truncate_code t (translate_pexpr p e2)).π2
    )
  end.


Definition translate_write_lval (p : p_id) (l : lval) (v : typed_chElement)
  : raw_code 'unit
  :=
  match l with
  | Lnone _ ty => ret tt
  | Lvar x => translate_write_var p x v
  | Lmem sz x e =>
    vx' ← translate_get_var p x ;;
    let vx : word _ := translate_to_pointer vx' in
    ve' ← (translate_pexpr p e).π2 ;;
    let ve := translate_to_pointer ve' in
    let p := (vx + ve)%R in
    let w := truncate_chWord sz v.π2 in
    translate_write p w
  | Laset aa ws x i =>
    (* Let (n,t) := s.[x] in is a notation calling on_arr_varr on get_var *)
    (* We just cast it since we do not track lengths *)
    t' ← translate_get_var p x ;;
    let t := coerce_to_choice_type 'array t' in
    i ← (truncate_code sint (translate_pexpr p i)).π2 ;; (* to_int *)
    let v := truncate_chWord ws v.π2 in
    let t := chArray_set t aa i v in
    translate_write_var p x (totce t)
  | Lasub aa ws len x i =>
    (* Same observation as Laset *)
    t ← translate_get_var p x ;;
    let t := coerce_to_choice_type 'array t in
    i ← (truncate_code sint (translate_pexpr p i)).π2 ;; (* to_int *)
    let t' := truncate_el (sarr (Z.to_pos (arr_size ws len))) v.π2 in
    let t := chArray_set_sub ws len aa t i t' in
    translate_write_var p x (totce t)
  end.

(* the argument to c is its (valid) sub id, the return is the resulting (valid) sub id *)
Fixpoint translate_for (v : var_i) (ws : seq Z) (m_id : p_id) (c : p_id -> p_id * raw_code 'unit) (s_id : p_id) : raw_code 'unit :=
  match ws with
  | [::] => ret tt
  | w :: ws =>
      let (s_id', c') := c s_id in
      translate_write_var m_id v (totce (translate_value w)) ;;
      c' ;;
      translate_for v ws m_id c s_id'
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
  list_lchtuple (tr_app_sopn_tuple _ (sopn_sem o) vs).

Fixpoint foldl2 {A B R} (f : R → A → B → R) (la : seq A) (lb : seq B) r :=
  match la with
  | [::] => r
  | a :: la' =>
    match lb with
    | [::] => r
    | b :: lb' => foldl2 f la' lb' (f r a b)
    end
  end.

Fixpoint foldr2 {A B R} (f : A → B → R → R) (la : seq A) (lb : seq B) r :=
  match la with
  | [::] => r
  | a :: la' =>
    match lb with
    | [::] => r
    | b :: lb' => f a b (foldr2 f la' lb' r)
    end
  end.

Definition translate_write_lvals p ls vs :=
  foldr2 (λ l v c, translate_write_lval p l v ;; c) ls vs (ret tt).

Definition translate_write_vars p xs vs :=
  foldr2 (λ x v c, translate_write_var p x v ;; c) xs vs (ret tt).

Lemma eq_rect_K :
  ∀ (A : eqType) (x : A) (P : A -> Type) h e,
    @eq_rect A x P h x e = h.
Proof.
  intros A x P' h e.
  replace e with (@erefl A x) by apply eq_irrelevance.
  reflexivity.
Qed.

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

Definition nat_of_ptr (ptr : pointer) :=
  (7 ^ Z.to_nat (wunsigned ptr))%nat.

Definition translate_ptr (ptr : pointer) : Location :=
  ('word U8 ; nat_of_ptr ptr).

Lemma ptr_var_nat_neq (ptr : pointer) (p : p_id) (v : var) :
  nat_of_ptr ptr != nat_of_p_id_var p v.
Proof.
  unfold nat_of_ptr.
  unfold nat_of_p_id_var.
  apply /eqP. intro e.
  apply (f_equal (λ n, n %% 3)) in e.
  rewrite -modnMm in e.
  rewrite -(modnMm (3 ^ _)) in e.
  rewrite Mpowmodn in e. 2: apply nat_of_p_id_nonzero.
  rewrite mul0n in e.
  rewrite mod0n in e.
  rewrite muln0 in e.
  move: e => /eqP e. rewrite eqn_mod_dvd in e. 2: auto.
  rewrite subn0 in e.
  rewrite Natpow_expn in e. rewrite Euclid_dvdX in e. 2: auto.
  move: e => /andP [e _].
  rewrite dvdn_prime2 in e. 2,3: auto.
  move: e => /eqP e. micromega.Lia.lia.
Qed.

Lemma ptr_var_neq (ptr : pointer) (p : p_id) (v : var) :
  translate_ptr ptr != translate_var p v.
Proof.
  unfold translate_ptr.
  unfold translate_var.
  unfold nat_of_p_id_ident.
  apply /eqP. intro e.
  noconf e.
  move: (ptr_var_nat_neq ptr p v) => /eqP. contradiction.
Qed.

Definition rel_mem (m : mem) (h : heap) :=
  ∀ (ptr : pointer) (v : (word U8)),
    (* mem as array model: *)
    read m ptr U8 = ok v →
    (get_heap h mem_loc) ptr = Some v.

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

Definition rel_vmap (vm : vmap) (p : p_id) (h : heap) :=
  ∀ (i : var) (v : sem_t (vtype i)),
    vm.[i] = ok v →
    get_heap h (translate_var p i) = coerce_to_choice_type _ (embed v).

Lemma rel_vmap_set_heap_neq vm m_id m_id' i v h :
  m_id <> m_id' -> rel_vmap vm m_id h -> rel_vmap vm m_id (set_heap h (translate_var m_id' i) v).
Proof.
  intros hneq hrel i' v' H.
  rewrite get_set_heap_neq.
  1: apply hrel; auto.
  apply injective_translate_var2.
  assumption.
Qed.

(* empty stack/valid *)
Definition empty_stack stack h : Prop := forall i, get_heap h (translate_var stack i) = chCanonical _.

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

Lemma empty_stack_spec m_id :
  forall h, empty_stack m_id h -> rel_vmap vmap0  m_id h.
Proof.
  intros h emp i v hv.
  rewrite coerce_to_choice_type_K.
  rewrite Fv.get0 in hv.
  rewrite emp.
  unfold translate_var.
  destruct (vtype i); now inversion hv.
Qed.

Definition valid (sid : p_id) (h : heap) :=
  forall i, sid ≺ i -> empty_stack i h.

Lemma valid_prec : forall id1 id2 m, id1 ⪯ id2 -> valid id1 m -> valid id2 m.
Proof.
  intros id1 id2 m hpre hvalid.
  intros id' hprec.
  apply hvalid.
  eapply preceq_prec_trans; eauto.
Qed.

Lemma valid_set_heap_disj m_id s_id i v h :
  valid m_id h -> disj m_id s_id -> valid m_id (set_heap h (translate_var s_id i) v).
Proof.
  intros hvalid hdisj s_id' hpre i'.
  rewrite get_set_heap_neq.
  1: apply hvalid; assumption.
  apply injective_translate_var2.
  intros contra; subst.
  eapply disj_antirefl.
  eapply disj_prec_l.
  1: eapply hpre.
  assumption.
Qed.

Lemma valid_set_heap_prec m_id s_id i v h :
  valid s_id h -> m_id ⪯ s_id -> valid s_id (set_heap h (translate_var m_id i) v).
Proof.
  intros hvalid hpre s_id' hpre' i'.
  rewrite get_set_heap_neq.
  1: apply hvalid; auto.
  apply injective_translate_var2.
  apply nesym.
  apply prec_neq.
  eapply preceq_prec_trans; eauto.
Qed.

Hint Resolve valid_prec : prefix.

(* stack *)
Definition stack_frame := (vmap * p_id * p_id * list p_id)%type.

Definition stack := list stack_frame.

Definition stack_cons s_id (stf : stack_frame) : stack_frame :=
  (stf.1.1.1, stf.1.1.2, s_id, stf.1.2 :: stf.2).
Notation "s_id ⊔ stf" := (stack_cons s_id stf) (at level 60).

Definition stf_disjoint m_id s_id s_st := disj m_id s_id /\ forall s_id', List.In s_id' s_st -> disj m_id s_id'.

Definition valid_stack_frame '(vm, m_id, s_id, s_st) (h : heap) :=
  rel_vmap vm m_id h /\
  m_id ⪯ s_id /\
  valid s_id h /\
  ~ List.In s_id s_st /\
  List.NoDup s_st /\
  (forall s_id', List.In s_id' s_st -> valid s_id' h) /\
  (forall s_id', List.In s_id' s_st -> m_id ⪯ s_id') /\
  (forall s_id', List.In s_id' s_st -> disj s_id s_id') /\
  (forall s_id' s_id'', List.In s_id' s_st -> List.In s_id'' s_st -> s_id' <> s_id'' -> disj s_id' s_id'').

Inductive valid_stack' : stack -> heap -> Prop :=
| valid_stack'_nil : forall h, valid_stack' [::] h
| valid_stack'_cons :
  forall h stf st,
    valid_stack' st h ->
    (forall stf' : stack_frame, List.In stf' st -> stf_disjoint stf.1.1.2 stf'.1.2 stf'.2) ->
    valid_stack_frame stf h ->
    valid_stack' (stf :: st) h.

Inductive valid_stack : stack -> heap -> Prop :=
| valid_stack_nil : forall h, valid_stack [::] h
| valid_stack_new : forall st vm m_id s_id h,
    valid_stack st h ->
    rel_vmap vm m_id h ->
    m_id ⪯ s_id ->
    valid s_id h ->
    (forall stf, List.In stf st -> disj m_id stf.1.2 /\ forall s_id', List.In s_id' stf.2 -> disj m_id s_id') ->
    valid_stack ((vm, m_id, s_id, [::]) :: st) h
| valid_stack_sub : forall st vm m_id s_id s_id' s_st h,
    valid_stack ((vm, m_id, s_id, s_st) :: st) h ->
    m_id ⪯ s_id' ->
    valid s_id' h ->
    ~ List.In s_id' s_st ->
    disj s_id s_id' ->
    (forall s_id'', List.In s_id'' s_st -> disj s_id' s_id'') ->
    valid_stack ((vm, m_id, s_id', s_id :: s_st) :: st) h.

Lemma valid_stack_single vm m_id s_id s_st h :
  valid_stack_frame (vm, m_id, s_id, s_st) h ->
  valid_stack [::(vm, m_id, s_id, s_st)] h.
Proof.
  revert s_id.
  induction s_st; intros s_id [hrel [hpre1 [hvalid [hnin [hnodup [hvalid2 [hpre2 [hdisj1 hdisj2]]]]]]]].
  - constructor; auto.
    + constructor.
  - constructor; auto.
    + eapply IHs_st; repeat split; auto.
      * eapply hpre2; left; auto.
      * eapply hvalid2; left; auto.
      * inversion hnodup; auto.
      * inversion hnodup; auto.
      * intros s_id' s_in'.
        apply hvalid2; right; auto.
      * intros s_id' s_in'.
        apply hpre2; right; auto.
      * intros s_id' s_in'.
        apply hdisj2.
        ** left; auto.
        ** right; auto.
        ** inversion hnodup; subst.
           intros contra; subst.
           easy.
      * intros s_id' s_id'' s_in' s_in'' s_neq.
        apply hdisj2.
        ** right; auto.
        ** right; auto.
        ** assumption.
    + intros contra.
      apply hnin.
      right; auto.
    + apply disj_sym.
      apply hdisj1.
      left; auto.
    + intros s_id' s_in'.
      apply hdisj1.
      right; auto.
Qed.

Lemma valid_stack_cons vm m_id s_id s_st st h :
  valid_stack st h ->
  (forall stf, List.In stf st -> disj m_id stf.1.2 /\ forall s_id', List.In s_id' stf.2 -> disj m_id s_id') ->
  valid_stack_frame (vm, m_id, s_id, s_st) h ->
  valid_stack ((vm, m_id, s_id, s_st) :: st) h.
Proof.
  revert vm m_id s_id st h.
  intros vm m_id s_id st h hvs hdisj1 [hrel [hpre1 [hvalid1 [hnin [hnodup [hvalid2 [hpre2 [hdisj2 hdisj3]]]]]]]].
  revert s_id hpre1 hvalid1 hnin hdisj2. induction s_st.
  - constructor; auto.
  - constructor; auto.
    + eapply IHs_st.
      * inversion hnodup; auto.
      * intros s_id' s_in'.
        apply hvalid2; right; auto.
      * intros s_id' s_in'.
        apply hpre2; right; auto.
      * intros s_id' s_id'' s_in' s_in'' s_neq.
        eapply hdisj3.
        ** right; auto.
        ** right; auto.
        ** assumption.
      * apply hpre2.
        left; auto.
      * apply hvalid2.
        left; auto.
      * inversion hnodup.
        auto.
      *
        intros s_id' s_in'.
        apply hdisj3.
        ** left; auto.
        ** right; auto.
        ** inversion hnodup; subst.
           intros contra; subst.
           auto.
    + intros contra.
      apply hnin.
      right; auto.
    + apply disj_sym.
      apply hdisj2.
      left; auto.
    + intros s_id' s_in'.
      apply hdisj2.
      right; auto.
Qed.

Lemma valid_stack_valid_stack vm m_id s_id s_st st h : valid_stack ((vm, m_id, s_id, s_st) :: st) h -> valid_stack st h.
Proof.
  revert vm m_id s_id.
  induction s_st; intros.
  - inversion H; assumption.
  - inversion H.
    eapply IHs_st.
    eassumption.
Qed.

Lemma valid_stack_rel_vmap vm m_id s_id s_st st h : valid_stack ((vm, m_id, s_id, s_st) :: st) h -> rel_vmap vm m_id h.
Proof.
  revert vm m_id s_id.
  induction s_st; intros.
  - inversion H; assumption.
  - inversion H.
    eapply IHs_st.
    eassumption.
Qed.

Lemma valid_stack_disj vm m_id s_id s_st st h :
  valid_stack ((vm, m_id, s_id, s_st) :: st) h ->
  (forall stf, List.In stf st -> disj m_id stf.1.2 /\ forall s_id', List.In s_id' stf.2 -> disj m_id s_id').
  revert vm m_id s_id.
  induction s_st; intros vm m_id s_id H.
  - inversion H.
    assumption.
  - inversion H.
    eapply IHs_st.
    eassumption.
Qed.

Ltac split_and :=
  repeat lazymatch goal with
  | |- _ /\ _ => split
         end.

Lemma invert_valid_stack st vm m_id s_id s_st h :
  valid_stack ((vm, m_id, s_id, s_st) :: st) h ->
  valid_stack st h
  /\ (forall stf, List.In stf st -> disj m_id stf.1.2 /\ forall s_id', List.In s_id' stf.2 -> disj m_id s_id')
  /\  valid_stack_frame (vm, m_id, s_id, s_st) h.
Proof.
  intros H. unfold valid_stack_frame.
  split_and; subst; auto.
  - eapply valid_stack_valid_stack; eassumption.
  - revert s_id H.
    induction s_st.
    + intros.
      inversion H; subst.
      eapply H10; eauto.
    + intros s_id H stf.
      inversion H; subst.
      eapply IHs_st; eauto.
  - eapply valid_stack_rel_vmap; eassumption.
  - inversion H; auto.
  - inversion H; auto.
  - inversion H; subst; auto.
    intros [contra|contra]; subst.
    + eapply disj_antirefl; eauto.
    + easy.
  - revert s_id H. induction s_st.
    + constructor.
    + constructor.
      * inversion H; subst; auto.
        inversion H6; subst; auto.
        intros [contra|contra]; subst.
        **  eapply disj_antirefl; eauto.
        **  eapply disj_antirefl.
            eapply H17.
            assumption.
      * eapply IHs_st.
        inversion H; eauto.
  - revert s_id H. induction s_st.
    + easy.
    + intros s_id hvalid s_id' [|s_in']; subst.
      * inversion hvalid; subst.
        inversion H5; auto.
      * eapply IHs_st.
        ** inversion hvalid; eassumption.
        ** assumption.
  - revert s_id H. induction s_st.
    + easy.
    + intros s_id hvalid s_id' [|s_in']; subst.
      * inversion hvalid; subst.
        inversion H5; auto.
      * eapply IHs_st.
        ** inversion hvalid; eassumption.
        ** assumption.
  - inversion H; subst; auto.
    + easy.
    + intros s_id' [|s_in']; subst; auto.
      inversion H; subst; auto.
      apply disj_sym; auto.
  - revert s_id H. induction s_st.
    + easy.
    + intros s_id hvalid s_id' s_id'' [|s_in'] [|s_in''] hneq; subst; auto.
      * easy.
      * inversion hvalid; subst; auto.
        inversion H5; subst; auto.
        ** easy.
        ** destruct s_in'' as [|s_in'']; subst; auto.
           apply disj_sym; auto.
      * inversion hvalid; subst; auto.
        inversion H5; subst; auto.
        ** easy.
        ** destruct s_in' as [|s_in']; subst; auto.
           apply disj_sym; auto.
      * inversion hvalid; subst.
        eapply IHs_st; eauto.
Qed.

Lemma valid_stack'_spec st h :
  valid_stack' st h <-> valid_stack st h.
Proof.
  split.
  - intros.
    induction st.
    + constructor.
    + inversion H; subst.
    destruct a as [[[vm m_id] s_id] s_st].
    revert s_id H H3 H5.
    induction s_st; intros; destruct H5 as [h1 [h2 [h3 [h4 [h5 [h6 [h7 [h8]]]]]]]]; auto.
    * intros; constructor; auto; try easy.
    * assert (valid_stack_frame (vm, m_id, a, s_st) h).
      { repeat split; eauto.
        { apply h7. left. auto. }
        { apply h6; left; auto. }
        { inversion h5; auto. }
        { inversion h5; auto. }
        { intros. eapply h6. right; auto. }
        { intros; apply h7; right; auto. }
        { intros. apply H0. 1: left; auto.
          1: right; auto.
          inversion h5; subst.
          intros contra; subst. auto. }
        { intros. apply H0. 1: right; auto.
          1: right; auto.
          auto. } }
      constructor; auto.
      ** apply IHs_st; auto.
         constructor; auto.
      ** intros contra. apply h4. right; auto.
      ** apply disj_sym. eapply h8.
         1: left; auto.
      ** intros.
         apply h8. right; auto.
  - intros.
    induction st.
    1: constructor.
    destruct a as [[[vm m_id] s_id] s_st].
    eapply invert_valid_stack in H as [H [H1]].
    constructor.
    + apply IHst. easy.
    + intros.
      unfold stf_disjoint.
      intros.
      eapply H1.
      easy.
      + assumption.
Qed.

Ltac invert_stack st hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2 :=
  apply invert_valid_stack in st as [hst [hdisj [hevm [hpre [hvalid [hnin [hnodup [hvalid1 [hpre1 [hdisj1 hdisj2]]]]]]]]]].

Lemma valid_stack_pop stf st :
  ∀ h, valid_stack (stf :: st) h ->
       valid_stack st h.
Proof.
  intros h H.
  destruct stf as [[[? ?] ?] ?].
  eapply valid_stack_valid_stack; eassumption.
Qed.

Lemma valid_stack_push_sub vm m_id s_id s_st st :
  ∀ h, valid_stack ((vm, m_id, s_id, s_st) :: st) h ->
       valid_stack ((vm, m_id, s_id~1, s_id~0 :: s_st) :: st) h.
Proof.
  intros h vst.
  invert_stack vst hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
  constructor; eauto with prefix.
  - eapply valid_stack_cons; unfold valid_stack_frame; split_and; eauto with prefix.
    + intros contra.
      eapply disj_antirefl.
      eapply disj_prec_l.
      1: eapply fresh1.
      eapply hdisj1.
      assumption.
    + intros s_id' s_in'.
      eapply disj_prec_l.
      1: eapply fresh1.
      apply hdisj1.
      assumption.
  - intros contra.
      eapply disj_antirefl.
      eapply disj_prec_l.
      1: eapply fresh2.
      eapply hdisj1.
      assumption.
  - apply fresh_disj.
  - intros s_id' s_in'.
      eapply disj_prec_l.
      1: eapply fresh2.
      apply hdisj1.
      assumption.
Qed.

Lemma valid_stack_pop_sub vm m_id s_id s_id' s_st st :
  ∀ h, valid_stack ((vm, m_id, s_id', s_id :: s_st) :: st) h ->
       valid_stack ((vm, m_id, s_id, s_st) :: st) h.
Proof.
  intros h vst.
  inversion vst.
  assumption.
Qed.

Lemma valid_stack_push vm m_id s_id s_st st :
  ∀ h, valid_stack ((vm, m_id, s_id, s_st) :: st) h ->
       valid_stack ((vmap0, s_id~1, s_id~1, [::]) :: ((vm, m_id, s_id~0, s_st) :: st)) h.
Proof.
  intros h vst.
  assert (vst2:=vst).
  invert_stack vst2 hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
  eapply valid_stack_push_sub in vst.
  eapply valid_stack_pop_sub in vst.
  constructor; eauto with prefix.
  - eapply empty_stack_spec.
    eapply hvalid.
    apply fresh2.
  - intros stf [|stf_in]; subst; split.
    + apply disj_sym. apply fresh_disj.
    + intros s_id' s_in'.
      eapply disj_prec_l.
        1: apply fresh2.
        eapply hdisj1.
        assumption.
    + eapply disj_prec_l.
      1: etransitivity.
      1: eapply hpre.
      1: eapply fresh2.
      eapply (proj1 (hdisj stf stf_in)).
    + intros s_id' s_in'.
      eapply disj_prec_l.
      1: etransitivity.
      1: eapply hpre.
      1: eapply fresh2.
      eapply hdisj; eauto.
Qed.

Lemma valid_stack_set_glob ptr sz (w : word sz) st m :
  valid_stack st m ->
  valid_stack st (set_heap m mem_loc (write_mem (get_heap m mem_loc) ptr w)).
Proof.
  intros val.
  induction val; auto.
  - constructor; auto.
  - constructor; auto.
    + intros v hv ev.
      rewrite get_set_heap_neq.
      2:{ rewrite eq_sym. apply mem_loc_translate_var_neq. }
      apply H. assumption.
    + intros i' hpre v.
      rewrite get_set_heap_neq.
      2:{ rewrite eq_sym. apply mem_loc_translate_var_neq. }
      apply H1.
      assumption.
  - constructor; auto.
     intros i' hpre v.
      rewrite get_set_heap_neq.
      2:{ rewrite eq_sym. apply mem_loc_translate_var_neq. }
      apply H0.
      assumption.
Qed.

Lemma valid_stack_set_heap i v vm m_id s_id s_st st m :
  valid_stack ((vm, m_id, s_id, s_st) :: st) m ->
  valid_stack st (set_heap m (translate_var m_id i) v).
Proof.
  intros vs.
  invert_stack vs hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
  induction hst as [
    |st vm' m_id' s_id' h hst IH hevm' hpre' hvalid' hdisj'
    |st vm' m_id' s_id' s_id'' s_st' h hst IH hpre' hvalid' hnin' hdisj1' hdisj2'].
  - constructor.
  - constructor; auto.
    + eapply IH; auto; simpl.
      intros stf stf_in.
      apply hdisj.
      right; auto.
    + apply rel_vmap_set_heap_neq; auto.
      intros contra; subst.
      eapply disj_antirefl.
      eapply disj_prec_r.
      1: eapply hpre'.
      apply disj_sym.
      specialize (hdisj (vm', m_id, s_id', [::]) ltac:(left;auto)).
      easy.
    + apply valid_set_heap_disj; auto.
      apply disj_sym.
      specialize (hdisj (vm', m_id', s_id', [::]) ltac:(left;auto)).
      easy.
  - constructor; auto.
    + eapply IH; auto.
      intros stf [|stf_in]; subst; split.
      * eapply hdisj.
        1: left; auto.
        left; auto.
      * intros s_id''' s_in'''.
       eapply hdisj.
        1: left; auto.
        right; auto.
      * specialize (hdisj stf ltac:(right;auto)).
        easy.
      * intros s_id''' s_in'''.
        eapply hdisj.
        1: right; eauto.
        assumption.
    + eapply valid_set_heap_disj; auto.
      eapply disj_sym .
      specialize (hdisj (vm', m_id', s_id'', s_id' :: s_st') ltac:(left;auto)).
      easy.
Qed.

Definition rel_estate (s : estate) (m_id : p_id) (s_id : p_id) (s_st : list p_id) (st : stack) (h : heap) :=
  rel_mem s.(emem) h /\ valid_stack ((s.(evm), m_id, s_id, s_st) :: st) h.


Lemma translate_read_estate :
  ∀ s ptr sz w m_id s_id s_st c_stack m,
    rel_estate s m_id s_id s_st c_stack m →
    read (emem s) ptr sz = ok w →
    read_mem (get_heap m mem_loc) ptr sz = w.
Proof.
  intros s ptr sz w m m_id s_id s_st c_stack rel h.
  eapply translate_read. 2: eassumption.
  apply rel.
Qed.

Lemma translate_write_estate :
  ∀ sz s cm ptr w m_id s_id s_st st m,
    write s.(emem) ptr (sz := sz) w = ok cm →
    rel_estate s m_id s_id s_st st m →
    rel_estate {| escs := s.(escs) ; emem := cm ; evm := s.(evm) |} m_id s_id s_st st (set_heap m mem_loc (write_mem (get_heap m mem_loc) ptr w)).
Proof.
  intros sz s cm ptr w m_id s_id s_st st m hw [hmem hstack].
  split.
  - simpl. eapply translate_write_mem_correct. all: eassumption.
  - simpl.
    apply valid_stack_set_glob.
    assumption.
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

Lemma get_var_get_heap :
  ∀ x s v m_id m,
    get_var (evm s) x = ok v →
    rel_vmap (evm s) m_id m →
    get_heap m (translate_var m_id x) =
    coerce_to_choice_type _ (translate_value v).
Proof.
  intros x s v m c_stack ev hevm.
  unfold get_var in ev.
  eapply on_vuP. 3: exact ev. 2: discriminate.
  intros sx esx esv.
  eapply hevm in esx. subst.
  rewrite coerce_to_choice_type_translate_value_to_val.
  rewrite esx. rewrite coerce_to_choice_type_K. reflexivity.
Qed.

Lemma translate_get_var_correct :
  ∀ x s v m_id s_id s_st st (cond : heap → Prop),
    get_var (evm s) x = ok v →
    (∀ m, cond m → rel_estate s m_id s_id s_st st m) →
    ⊢ ⦃ cond ⦄
      translate_get_var m_id x ⇓ coerce_to_choice_type _ (translate_value v)
    ⦃ cond ⦄.
Proof.
  intros x s v m_id s_id s_st st cond ev hcond.
  unfold translate_get_var.
  eapply u_get_remember. intros vx.
  eapply u_ret. intros m [hm hx].
  split. 1: assumption.
  unfold u_get in hx. subst.
  eapply get_var_get_heap.
  - eassumption.
  - apply hcond in hm as [_ hst].
    invert_stack hst hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
Qed.

Lemma translate_gvar_correct (x : gvar) (v : value) s (cond : heap → Prop) m_id s_id s_st st :
  get_gvar gd (evm s) x = ok v →
  (∀ m, cond m → rel_estate s m_id s_id s_st st m) →
  ⊢ ⦃ cond ⦄
    translate_gvar m_id x ⇓ coerce_to_choice_type _ (translate_value v)
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

Lemma translate_to_arr :
  ∀ len v a,
    to_arr len v = ok a →
    coerce_to_choice_type 'array (translate_value v) = translate_value (Varr a).
Proof.
  intros len v a e.
  destruct v as [| | len' t' | |]. all: try discriminate.
  simpl in e. unfold WArray.cast in e.
  destruct (_ : bool) eqn:eb. 2: discriminate.
  noconf e. simpl.
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

Lemma translate_pexpr_type p s₁ e v :
  sem_pexpr gd s₁ e = ok v →
  (translate_pexpr p e).π1 = choice_type_of_val v.
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
  WArray.get_sub aa sz len a i = ok t →
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

Lemma chArray_set_sub_correct :
  ∀ ws (lena len : BinNums.positive) a aa b p t,
  @WArray.set_sub lena aa ws len a p b = ok t →
  chArray_set_sub ws len aa (translate_value (Varr a)) p (translate_value (Varr b))
  = translate_value (Varr t).
Proof.
  intros ws lena len a aa b p t e.
  unfold WArray.set_sub in e.
  destruct (_ : bool) eqn:eb. 2: discriminate.
  noconf e.
  unfold chArray_set_sub. unfold WArray.set_sub_data.
  move: eb => /andP [e1 e2].
  rewrite <- !foldl_rev.
  apply ziota_ind.
  - reflexivity.
  - intros i l hi ih.
    rewrite rev_cons.
    rewrite !foldl_rcons.
    rewrite ih.
    rewrite fold_get.
    destruct Mz.get eqn:e.
    + rewrite fold_set.
      reflexivity.
    + rewrite fold_rem.
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

Lemma translate_pexprs_types p s1 es vs :
  mapM (sem_pexpr gd s1) es = ok vs →
  [seq (translate_pexpr p e).π1 | e <- es] = [seq choice_type_of_val v | v <- vs].
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

Lemma app_sopn_nil_ok_size {T} {of_T : forall t, T -> exec (sem_t t)} :
  ∀ A ts (f : sem_prod ts (exec A)) vs v,
    app_sopn of_T f vs = ok v →
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

#[export] Instance WArray_ext_eq_equiv {len} : Equivalence (@WArray_ext_eq len).
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

Lemma unembed_embed_sarr {len} (a : sem_t (sarr len)) :
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

Lemma unembed_embed t a :
  match t as t0 return sem_t t0 -> Prop with
  | sbool => λ a, unembed (embed a) = a
  | sint => λ a, unembed (embed a) = a
  | sarr p => λ a, unembed (embed a) =ₑ a
  | sword s => λ a, unembed (embed a) = a
  end a.
Proof.
  destruct t.
  - reflexivity.
  - reflexivity.
  - apply unembed_embed_sarr.
  - reflexivity.
Qed.

#[export] Instance unembed_embed_Proper {len} : Proper ((=ₑ) ==> (=ₑ)) (λ (a : sem_t (sarr len)), unembed (embed a)).
Proof.
  intros x y H.
  rewrite !(unembed_embed (sarr len)).
  assumption.
Qed.

#[export] Instance WArray_get8_Proper {len} : Proper ((=ₑ) ==> eq ==> eq) (@WArray.get8 len).
  intros a b H ? ? Hi.
  unfold WArray.get8, WArray.in_bound, WArray.is_init.
  rewrite H Hi.
  reflexivity.
Qed.

#[export] Instance WArray_get_Proper {len ws} : Proper ((=ₑ) ==> eq ==> eq) (@WArray.get len AAscale ws).
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

#[export] Instance WArray_copy_Proper {ws p} : Proper ((=ₑ) ==> eq) (@WArray.copy ws p).
Proof.
  intros a b H.
  unfold WArray.copy, WArray.fcopy.
  apply eq_foldM.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma list_tuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p : sem_tuple (t1 :: t2 :: ts)) :
  list_ltuple p = (oto_val p.1) :: (list_ltuple (p.2 : sem_tuple (t2 :: ts))).
Proof. reflexivity. Qed.

Lemma embed_tuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p : sem_tuple (t1 :: t2 :: ts)) :
  embed_tuple p = (embed_ot p.1, embed_tuple (p.2 : sem_tuple (t2 :: ts))).
Proof. reflexivity. Qed.

Lemma list_lchtuple_cons_cons {t1 t2 : stype}  {ts : seq stype} (p1 : encode t1) (p2 : lchtuple [seq encode t | t <- (t2 :: ts)]) :
  list_lchtuple ((p1, p2) : lchtuple [seq encode t | t <- (t1 :: t2 :: ts)]) = (totce p1) :: (list_lchtuple p2).
Proof. reflexivity. Qed.

Lemma app_sopn_cons {rT} t ts v vs sem :
  @app_sopn _ of_val rT (t :: ts) sem (v :: vs) =
  Let v' := of_val t v in @app_sopn _ of_val rT ts (sem v') vs.
Proof. reflexivity. Qed.

Lemma sem_prod_cons t ts S :
  sem_prod (t :: ts) S = (sem_t t → sem_prod ts S).
Proof. reflexivity. Qed.

Inductive sem_correct {R} : ∀ (ts : seq stype), (sem_prod ts (exec R)) → Prop :=
| sem_nil s : sem_correct [::] s
| sem_cons t ts s : (∀ v, (s (unembed (embed v)) = s v)) → (∀ v, sem_correct ts (s v)) → sem_correct (t :: ts) s.

Lemma tr_app_sopn_correct {R S} (can : S) emb ts vs vs' (s : sem_prod ts (exec R)) :
  sem_correct ts s →
  app_sopn of_val s vs = ok vs' →
  tr_app_sopn can emb ts s [seq to_typed_chElement (translate_value v) | v <- vs]
  = emb vs'.
Proof.
  intros hs H.
  induction hs as [s | t ts s es hs ih] in vs, vs', H |- *.
  - destruct vs. 2: discriminate.
    simpl in *. subst.
    reflexivity.
  - simpl in *.
    destruct vs as [| v₀ vs]. 1: discriminate.
    jbind H v' hv'.
    eapply ih in H.
    simpl.
    erewrite translate_of_val. 2: eassumption.
    rewrite coerce_to_choice_type_translate_value_to_val.
    rewrite es.
    assumption.
Qed.

Context `{asm_correct : ∀ o, sem_correct (tin (get_instr_desc (Oasm o))) (sopn_sem (Oasm o))}.

Lemma app_sopn_list_tuple_correct o vs vs' :
  app_sopn of_val (sopn_sem o) vs = ok vs' →
  tr_app_sopn_tuple _ (sopn_sem o) [seq to_typed_chElement (translate_value v) | v <- vs]
  =
  embed_tuple vs'.
Proof using asm_correct.
  intros.
  unfold tr_app_sopn_tuple.
  erewrite tr_app_sopn_correct.
  - reflexivity.
  - destruct o.
    + repeat constructor.
      cbn -[wsize_size WArray.copy unembed embed truncate_el] in *; intros.
      rewrite (unembed_embed (sarr _)).
      reflexivity.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
    + apply asm_correct.
  - assumption.
Qed.

Lemma translate_exec_sopn_correct (o : sopn) (ins outs : values) :
  exec_sopn o ins = ok outs →
  translate_exec_sopn o [seq totce (translate_value v) | v <- ins] =
  [seq totce (translate_value v) | v <- outs].
Proof using asm_correct.
  intros H.
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
      destruct vs as [e es]. simpl.
      destruct a. 2-4: reflexivity.
      destruct e. all: reflexivity.
Qed.

Lemma tr_app_sopn_single_correct (op : opN) (v : sem_t (type_of_opN op).2) (vs : values) :
  app_sopn of_val (sem_opN_typed op) vs = ok v →
  tr_app_sopn_single
    (type_of_opN op).1
    (sem_opN_typed op)
    [seq to_typed_chElement (translate_value v) | v <- vs]
  =
  embed v.
Proof.
  intro H.
  unfold tr_app_sopn_single.
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
  - erewrite tr_app_sopn_correct.
    + reflexivity.
    + repeat constructor.
    + assumption.
Qed.

Lemma translate_pexpr_correct :
  ∀ (e : pexpr) s₁ v (cond : heap → Prop) m_id s_id s_st st,
    sem_pexpr gd s₁ e = ok v →
    (∀ m, cond m → rel_estate s₁ m_id s_id s_st st m) →
    ⊢ ⦃ cond ⦄
      (translate_pexpr m_id e).π2 ⇓
      coerce_to_choice_type _ (translate_value v)
    ⦃ cond ⦄.
Proof.
  intros e s1 v cond m_id s_id s_st st h1 hcond.
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
      apply hcond in hm.
      destruct hm as [hm hst].
      invert_stack hst hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
      apply hevm in e1. rewrite e1.
      simpl. rewrite coerce_to_choice_type_K.
      rewrite coerce_to_choice_type_translate_value_to_val.
      reflexivity.
    + simpl.
      rewrite h1.
      apply u_ret. auto.
  - simpl in *.
    jbind h1 nt ent. destruct nt. all: try discriminate.
    jbind h1 j ej. jbind ej j' ej'.
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
    jbind h1 j hj. jbind hj j' hj'. jbind h1 t ht. noconf h1.
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
    assert (hm2:=hm).
    destruct hm2 as [hm2 hst].
    invert_stack hst hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
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
      apply translate_pexpr_type with (p:=m_id) in h2.
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
    apply translate_pexpr_type with (p:=m_id) in h2.
    apply translate_pexpr_type with (p:=m_id) in h3.
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
      * {
        clear -h2 H hcond.
        revert v' h2 H.
        induction es; intros.
        - inversion h2.
          constructor.
        - inversion h2.
          jbind H1 x Hx.
          jbind H1 y Hy.
          noconf H1.
          constructor.
          + eapply H.
            1: now constructor.
            1: eassumption.
            assumption.
          + eapply IHes.
            1: assumption.
            intros.
            eapply H.
            { apply List.in_cons. assumption. }
            1: eassumption.
            assumption.
      }
    + apply u_ret.
      intros; split; auto.
      rewrite coerce_to_choice_type_translate_value_to_val.
      apply tr_app_sopn_single_correct.
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

Lemma translate_pexprs_correct s m_id s_id s_st st vs es :
  sem_pexprs gd s es = ok vs →
  List.Forall2 (λ c v,
    ⊢ ⦃ rel_estate s m_id s_id s_st st ⦄
      c.π2
      ⇓ coerce_to_choice_type _ (translate_value v)
    ⦃ rel_estate s m_id s_id s_st st ⦄
  ) [seq translate_pexpr m_id e | e <- es] vs.
Proof.
  intro hvs.
  induction es in vs, hvs |- *.
  - destruct vs.
    + constructor.
    + inversion hvs.
  - destruct vs.
    + simpl in hvs.
      jbind hvs vs' hvs'.
      jbind hvs vs'' hvs''.
      noconf hvs.
    + simpl in hvs.
      jbind hvs vs' hvs'.
      jbind hvs vs'' hvs''.
      noconf hvs.
      rewrite map_cons.
      constructor.
      * eapply translate_pexpr_correct. 1: eassumption.
        eauto.
      * eapply IHes.
        assumption.
Qed.

Corollary bind_list_pexpr_correct
  (cond : heap → Prop) (es : pexprs) (vs : list value)
  (s1 : estate) m_id s_id s_st st
  (hc : ∀ m : heap, cond m → rel_estate s1 m_id s_id s_st st m)
  (h : sem_pexprs gd s1 es = ok vs) :
  ⊢ ⦃ cond ⦄
    bind_list [seq translate_pexpr m_id e | e <- es] ⇓
    [seq totce (translate_value v) | v <- vs]
    ⦃ cond ⦄.
Proof.
  eapply bind_list_correct with (vs := vs).
  - rewrite <- map_comp.
    unfold comp.
    eapply translate_pexprs_types.
    exact h.
  - revert vs h.
    induction es; intros.
    + inversion h.
      constructor.
    + inversion h as [H1].
      jbind H1 x Hx.
      jbind H1 y Hy.
      noconf H1.
      constructor.
      * eapply translate_pexpr_correct.
        all: eassumption.
      * simpl. eapply IHes.
        assumption.
Qed.

Corollary translate_pexpr_correct_cast :
  ∀ (e : pexpr) s₁ v m_id s_id s_st st (cond : heap → Prop),
    sem_pexpr gd s₁ e = ok v →
    (∀ m, cond m → rel_estate s₁ m_id s_id s_st st m) →
    ⊢ ⦃ cond ⦄
      coerce_typed_code _ (translate_pexpr m_id e) ⇓
      translate_value v
    ⦃ cond ⦄.
Proof.
  intros e s v m_id s_id s_st st cond he hcond.
  eapply translate_pexpr_correct in he as h. 2: exact hcond.
  eapply translate_pexpr_type with (p := m_id) in he.
  unfold choice_type_of_val in he.
  destruct (translate_pexpr) as [? exp] eqn:?. simpl in *. subst.
  rewrite coerce_to_choice_type_K in h.
  rewrite coerce_typed_code_K. assumption.
Qed.


Lemma translate_write_correct :
  ∀ sz s ptr (w : word sz) cm m_id s_id s_st st (cond : heap → Prop),
    (∀ m, cond m → write s.(emem) ptr w = ok cm ∧ rel_estate s m_id s_id s_st st m) →
    ⊢ ⦃ cond ⦄ translate_write ptr w ⇓ tt ⦃ rel_estate {| escs := s.(escs) ; emem := cm ; evm := s.(evm) |} m_id s_id s_st st ⦄.
Proof.
  intros sz s ptr w cm m_id s_id s_st st cond h.
  unfold translate_write.
  eapply u_get_remember. intros m.
  eapply u_put.
  eapply u_ret_eq.
  intros ? [m' [[h1 h2] ?]]. subst.
  unfold u_get in h2. subst.
  eapply h in h1. destruct h1.
  eapply translate_write_estate. all: assumption.
Qed.

Lemma valid_stack_set_var i v vm s m_id s_id s_st st m :
  valid_stack ((s.(evm), m_id, s_id, s_st) :: st) m ->
  set_var (evm s) i v = ok vm ->
  valid_stack ((vm, m_id, s_id, s_st) :: st) (set_heap m (translate_var m_id i) (truncate_el (vtype i) (translate_value v))).
Proof.
  intros vs hsv.
  assert (vs':=vs).
  invert_stack vs hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2; auto.
  eapply set_varP. 3: exact hsv.
  - intros v1 hv1 eyl; subst.
    eapply valid_stack_cons; unfold valid_stack_frame; split_and; eauto.
    + eapply valid_stack_set_heap.
      eassumption.
    + intros vi vt ev.
     destruct (vi == i) eqn:evar.
      all: move: evar => /eqP evar.
      * subst. rewrite Fv.setP_eq in ev. noconf ev.
        rewrite get_set_heap_eq. rewrite coerce_to_choice_type_K.
        eapply translate_of_val in hv1 as e.
        rewrite e. apply coerce_to_choice_type_translate_value_to_val.
      * rewrite Fv.setP_neq in ev.
        2:{ apply /eqP. eauto. }
        rewrite get_set_heap_neq.
        2:{
          apply /eqP. intro ee.
          apply injective_translate_var in ee.
          contradiction.
        }
        eapply hevm in ev. assumption.
    + eapply valid_set_heap_prec; auto.
    + intros s_id' s_in'.
      eapply valid_set_heap_prec.
      1: apply hvalid1; auto.
      apply hpre1. assumption.
  - intros hbo hyl hset; subst.
    eapply valid_stack_cons; unfold valid_stack_frame; split_and; auto.
    + eapply valid_stack_set_heap.
      eassumption.
    + intros vi vt ev.
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
      eapply hevm in ev. assumption.
    + eapply valid_set_heap_prec; auto.
    + intros s_id' s_in'.
      eapply valid_set_heap_prec.
      1: apply hvalid1; auto.
      apply hpre1. assumption.
Qed.

Lemma translate_write_var_estate :
  ∀ i v s1 s2 m_id s_id s_st st m,
    write_var i v s1 = ok s2 →
    rel_estate s1 m_id s_id s_st st m →
    rel_estate s2 m_id s_id s_st st (set_heap m (translate_var m_id i) (truncate_el i.(vtype) (translate_value v))).
Proof using asm_correct gd.
  intros i v s1 s2 m_id s_id s_st st m hw [hmem hst].
  unfold write_var in hw. jbind hw vm hvm. noconf hw.
  all: simpl.
  split.
  - intros ptr v' er.
    eapply hmem in er.
    rewrite get_set_heap_neq. 2: apply mem_loc_translate_var_neq.
    assumption.
  - eapply valid_stack_set_var; eauto.
Qed.

Lemma translate_write_var_correct :
  ∀ es₁ es₂ m_id s_id s_st st y v,
    write_var y v es₁ = ok es₂ →
    ⊢ ⦃ rel_estate es₁ m_id s_id s_st st ⦄
      translate_write_var m_id y (totce (translate_value v))
      ⇓ tt
    ⦃ rel_estate es₂ m_id s_id s_st st ⦄.
Proof using asm_correct gd.
  intros es₁ es₂ m_id s_id s_st st y v hw.
  simpl. unfold translate_write_var. simpl in hw.
  simpl.
  eapply u_put.
  apply u_ret_eq.
  intros m' [m [hm e]]. subst.
  eapply translate_write_var_estate. all: eassumption.
Qed.

Lemma translate_write_lval_correct :
  ∀ es₁ es₂ m_id s_id s_st st y v,
    write_lval gd y v es₁ = ok es₂ →
    ⊢ ⦃ rel_estate es₁ m_id s_id s_st st ⦄
      translate_write_lval m_id y (totce (translate_value v))
      ⇓ tt
    ⦃ rel_estate es₂ m_id s_id s_st st ⦄.
Proof using asm_correct.
  intros es₁ es₂ m_id s_id s_st st y v hw.
  destruct y as [ | yl | | aa ws x ei | ] eqn:case_lval.
  - simpl. apply u_ret_eq.
    intros hp hr.
    simpl in hw. unfold write_none in hw.
    destruct is_sbool eqn:eb.
    + unfold on_vu in hw. destruct of_val as [| []].
      all: noconf hw. all: assumption.
    + unfold on_vu in hw. destruct of_val as [| []].
      all: noconf hw. assumption.
  - now eapply translate_write_var_correct.
  - simpl. simpl in hw.
    jbind hw vx hvx. jbind hvx vx' hvx'. jbind hw ve hve.
    jbind hve ve' hve'. jbind hw w hw'. jbind hw m hm.
    noconf hw.
    eapply u_get_remember. intros tv.
    eapply u_bind.
    1:{
      eapply translate_pexpr_correct.
      - eassumption.
      - intros ? []. eassumption.
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
    erewrite get_var_get_heap.
    3: eapply invert_valid_stack; apply hm'.
    2: eassumption.
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
      - intros ? []. eassumption.
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
    erewrite get_var_get_heap.
    3: eapply invert_valid_stack; apply hs.
    2: eassumption.
    Opaque translate_value. simpl. Transparent translate_value.
    eapply type_of_get_var in hnt as ety. simpl in ety.
    apply (f_equal encode) in ety. simpl in ety.
    rewrite -ety. rewrite !coerce_to_choice_type_K.
    erewrite chArray_set_correct. 2: eassumption.
    eapply translate_write_var_estate in hs.
    2: eassumption.
    assumption.
  - simpl. simpl in hw.
    jbind hw nt hnt. destruct nt. all: try discriminate.
    jbind hw i hi. jbind hi i' hi'.
    jbind hw t' ht'. jbind hw t ht.
    eapply u_get_remember. simpl. intros vx.
    rewrite !bind_assoc. simpl.
    eapply u_bind.
    1:{
      eapply translate_pexpr_correct.
      - eassumption.
      - intros ? []. eassumption.
    }
    unfold translate_write_var. simpl.
    eapply u_put.
    eapply u_ret_eq.
    intros ? [m [[hs hm] ?]]. subst.
    unfold u_get in hm. subst.
    erewrite translate_pexpr_type. 2: eassumption.
    rewrite !coerce_to_choice_type_K.
    erewrite translate_to_int. 2: eassumption.
    erewrite translate_to_arr. 2: eassumption.
    erewrite get_var_get_heap.
    3: eapply invert_valid_stack; apply hs.
    2: eassumption.
    Opaque translate_value. simpl. Transparent translate_value.
    eapply type_of_get_var in hnt as ety. simpl in ety.
    apply (f_equal encode) in ety. simpl in ety.
    rewrite -ety. rewrite !coerce_to_choice_type_K.
    erewrite chArray_set_sub_correct. 2: eassumption.
    eapply translate_write_var_estate in hs.
    2: eassumption.
    assumption.
Qed.

Lemma translate_write_lvals_cons p l ls v vs :
  translate_write_lvals p (l :: ls) (v :: vs) = (translate_write_lval p l v ;; translate_write_lvals p ls vs).
Proof. reflexivity. Qed.

Lemma translate_write_lvals_correct m_id s_id s_st st s1 ls vs s2 :
  write_lvals gd s1 ls vs = ok s2 →
  ⊢ ⦃ rel_estate s1 m_id s_id s_st st ⦄
    translate_write_lvals m_id ls [seq totce (translate_value v) | v <- vs]
    ⇓ tt
  ⦃ rel_estate s2 m_id s_id s_st st ⦄.
Proof using asm_correct.
  intros h.
  induction ls as [| l ls] in s1, vs, h |- *.
  - destruct vs. 2: discriminate.
    noconf h.
    apply u_ret_eq. auto.
  - destruct vs. 1: noconf h.
    simpl in h.
    jbind h s3 Hs3.
    rewrite map_cons.
    rewrite translate_write_lvals_cons.
    eapply u_bind.
    + eapply translate_write_lval_correct.
      all: eassumption.
    + apply IHls.
      assumption.
Qed.

Lemma translate_write_vars_cons p l ls v vs :
  translate_write_vars p (l :: ls) (v :: vs) =
    (translate_write_var p l v ;; translate_write_vars p ls vs).
Proof.
  reflexivity.
Qed.

Lemma translate_write_vars_correct m_id s_id s_st st s1 ls vs s2 :
  write_vars ls vs s1 = ok s2 →
  ⊢ ⦃ rel_estate s1 m_id s_id s_st st ⦄
    translate_write_vars m_id ls [seq totce (translate_value v) | v <- vs]
    ⇓ tt
  ⦃ rel_estate s2 m_id s_id s_st st ⦄.
Proof using asm_correct gd.
  intros h.
  induction ls as [| l ls] in s1, vs, h |- *.
  - destruct vs. 2: discriminate.
    noconf h.
    apply u_ret_eq. auto.
  - destruct vs. 1: noconf h.
    simpl in h.
    jbind h s3 Hs3.
    rewrite map_cons.
    rewrite translate_write_vars_cons.
    eapply u_bind.
    + simpl.
      eapply translate_write_var_correct.
      all: eassumption.
    + apply IHls.
      assumption.
Qed.

End Translation.

Section Translation.

Context `{asmop : asmOp}.

Context {pd : PointerData}.
Context {fcp : FlagCombinationParams}.

Context (P : uprog).

Definition instr_d (i : instr) : instr_r :=
  match i with MkI _ i => i end.

Definition trunc_list :=
  (λ tys (vs : seq typed_chElement),
    [seq let '(ty, v) := ty_v in totce (truncate_el ty v.π2) | ty_v <- zip tys vs]).

(* The type of translated function *bodies* *)
Definition fdefs :=
  (* ∀ p fdef, get_fundef (p_funcs P) p = Some fdef → raw_code 'unit. *)
  list (funname * (p_id -> raw_code 'unit)).

Definition tchlist := [choiceType of seq typed_chElement].

(* The type of translated function "calls" *)
Definition trfun :=
  p_id -> tchlist → raw_code tchlist.

Definition translate_call_body
  (fn : funname) (tr_f_body : p_id -> raw_code 'unit) : trfun.
Proof using P asm_op asmop pd.
  (* sem_call *)
  refine (λ sid vargs',
           match (get_fundef (p_funcs P) fn) with
           | Some f => _
           | None => ret [::] end).
  pose (trunc_list (f_tyin f) vargs') as vargs.
  apply (bind (translate_write_vars sid (f_params f) vargs)) => _.
  (* Perform the function body. *)
  apply (bind (tr_f_body sid)) => _.
  eapply bind.
  - (* Look up the results in their locations... *)
    exact (bind_list [seq totc _ (translate_get_var sid (v_var x))
                     | x <- f_res f]).
  - intros vres.
    (* ...and coerce them to the codomain of f. *)
    pose (trunc_list (f_tyout f) vres) as vres'.
    exact (ret vres').
Defined.

Definition translate_call (fn : funname) (tr_f_body : fdefs) : trfun.
Proof using P asm_op asmop pd.
  refine (λ sid vargs, match assoc tr_f_body fn with
          | Some tr_f => _ | None => ret [::] end).
  exact (translate_call_body fn tr_f sid vargs).
Defined.

Fixpoint translate_instr_r
  (tr_f_body : fdefs)
  (i : instr_r) (m_id : p_id) (s_id : p_id) {struct i}
  : p_id * raw_code 'unit

with translate_instr (tr_f_body : fdefs)
       (i : instr) (m_id : p_id) (s_id : p_id) {struct i} : p_id * raw_code 'unit :=
  translate_instr_r tr_f_body (instr_d i) m_id s_id.
Proof using P asm_op asmop pd fcp.
  pose proof (translate_cmd :=
    (fix translate_cmd (tr_f_body : fdefs) (c : cmd) (m_id : p_id) (s_id : p_id) : p_id * raw_code 'unit :=
      match c with
      | [::] => (s_id, ret tt)
      | i :: c =>
          let (s_id', i') := translate_instr tr_f_body i m_id s_id in
          let (s_id'', c') := translate_cmd tr_f_body c m_id s_id' in
          (s_id'', i' ;; c')
      end
    )
             ).
  refine
    match i with
    | Cassgn l _ s e =>
        let tr_p := translate_pexpr (p_globs P) m_id e in
        (s_id,
          v ← tr_p.π2 ;;
          (translate_write_lval (p_globs P) m_id l (totce (truncate_el s v)))
        )
    | Copn ls _ o es =>
        let cs := [seq (translate_pexpr (p_globs P) m_id e) | e <- es] in
        let vs := bind_list cs in

        (s_id,
          bvs ← vs ;;
          translate_write_lvals (p_globs P) m_id ls (translate_exec_sopn o bvs)
        )
    | Cif e c1 c2 =>
        let (s_id', c1') := translate_cmd tr_f_body c1 m_id s_id in
        let (s_id'', c2') := translate_cmd tr_f_body c2 m_id s_id' in
        let e' := translate_pexpr (p_globs P) m_id e in
        let rb := coerce_typed_code 'bool e' in
        (s_id'',
          b ← rb ;; if b then c1' else c2'
        )
    | Cfor i r c =>
        let '(d, lo, hi) := r in
        let (s_id', fresh) := fresh_id s_id in
        let loᵗ := coerce_typed_code 'int (translate_pexpr (p_globs P) m_id lo) in
        let hiᵗ := coerce_typed_code 'int (translate_pexpr (p_globs P) m_id hi) in
        let cᵗ := translate_cmd tr_f_body c m_id in
        (s_id',
          vlo ← loᵗ ;;
          vhi ← hiᵗ ;;
          translate_for i (wrange d vlo vhi) m_id cᵗ fresh)
    | Ccall ii xs f args =>
        let (s_id', fresh) := fresh_id s_id in
        let cs := [seq (translate_pexpr (p_globs P) m_id e) | e <- args] in
        (s_id',
          vargs ← bind_list cs ;;
          vres ← translate_call f tr_f_body fresh vargs ;;
          translate_write_lvals (p_globs P) m_id xs vres
        )
    | _ => (s_id, unsupported.π2)
    end.
Defined.

(* translate_instr is blocked because it is a fixpoint *)
Lemma translate_instr_unfold :
  ∀ ep i st,
    translate_instr ep i st = translate_instr_r ep (instr_d i) st.
Proof.
  intros ep i st.
  destruct i. reflexivity.
Qed.

(* Trick to have it expand to the same as the translate_cmd above *)
Section TranslateCMD.

Fixpoint translate_cmd (tr_f_body : fdefs) (c : cmd) (id : p_id) (sid : p_id) : p_id * raw_code 'unit :=
  match c with
  | [::] => (sid, ret tt)
  | i :: c =>
      let (sid', i') := translate_instr tr_f_body i id sid in
      let (sid'', c') := translate_cmd tr_f_body c id sid' in
      (sid'', i' ;; c')
  end.

End TranslateCMD.

Record fdef := {
  ffun : typed_raw_function ;
  locs : {fset Location} ;
  imp : Interface ;
}.
#[local] Definition ty_in fd := (ffun fd).π1.
#[local] Definition ty_out fd := ((ffun fd).π2).π1.
Definition translate_fundef
           (tr_f_body : fdefs)
           (p : p_id)
           (fd : _ufun_decl (* extra_fun_t *)) : funname * fdef.
Proof using P asm_op asmop pd fcp.
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
    pose (map (λ '(x, (ty; v)), translate_write_var p x (totce v))
              (zip f_params vargs'))
      as cargs.
    apply (foldl (λ c k, c ;; k) (ret tt)) in cargs.
    apply (bind cargs) => _.

    (* Perform the function body. *)
    apply (bind (translate_cmd tr_f_body f_body p p).2) => _.

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

End Translation.

Section Translation.

Context `{asmop : asmOp}.

Context {pd : PointerData}.
Context {fcp : FlagCombinationParams}.

Definition ssprove_prog := seq (funname * trfun).

Definition translate_prog (prog : uprog) : fdefs.
Proof using asm_op asmop pd fcp.
  destruct prog.
  induction p_funcs.
  - exact [::].
  - unfold fdefs. unfold ssprove_prog.
    apply cons. 2: exact IHp_funcs.
    pose a.1 as fn.
    split. 1: exact fn.
    destruct a. destruct _f.
    intros s_id.
    exact (translate_cmd (Build__prog p_funcs p_globs p_extra) IHp_funcs f_body s_id s_id).2.
Defined.

Definition tr_p (prog : uprog) : ssprove_prog.
Proof using asm_op asmop pd fcp.
  pose (fs := translate_prog prog).
  induction fs as [|f fs ?].
  - constructor 1.
  - constructor 2.
    2: assumption.
    exact (f.1, translate_call prog f.1 (f::fs)).
Defined.

Definition translate_funs (P : uprog) : seq _ufun_decl → fdefs * ssprove_prog :=
  let fix translate_funs (fs : seq _ufun_decl) : fdefs * ssprove_prog :=
    match fs with
    | [::] => ([::], [::])
    | f :: fs' =>
        let '(fn, f_extra) := f in
        let tr_body := fun sid => (translate_cmd P (translate_funs fs').1 (f_body f_extra) sid sid).2 in
        let tr_fs := (fn, tr_body) :: (translate_funs fs').1 in
        let tr_p := (fn, translate_call_body P fn tr_body) :: (translate_funs fs').2 in
        (tr_fs, tr_p)
    end
  in translate_funs.

Definition translate_prog' P :=
  translate_funs P (p_funcs P).

Fixpoint translate_funs_static (P : uprog) (fs : seq _ufun_decl) (st_funcs : fdefs) : fdefs * ssprove_prog :=
    match fs with
    | [::] => ([::], [::])
    | f :: fs' =>
        let '(tr_fs', tr_p') := translate_funs_static P fs' st_funcs in
        let '(fn, f_extra) := f in
        let tr_body := fun sid => (translate_cmd P st_funcs (f_body f_extra) sid sid).2 in
        let tr_fs := (fn, tr_body) :: tr_fs' in
        let tr_p := (fn, translate_call_body P fn tr_body) :: tr_p' in
        (tr_fs, tr_p)
    end.

Definition translate_prog_static P st_funcs :=
  translate_funs_static P (p_funcs P) st_funcs.

Definition get_translated_static_fun P fn st_func :=
  match assoc (translate_prog_static P st_func).2 fn with
  | Some f => f
  | None => fun _ _ => ret [::]
  end.

Lemma tr_prog_inv {P fn f} :
  get_fundef (p_funcs P) fn = Some f →
  ∑ fs' l,
    p_funcs P = l ++ (fn, f) :: fs' ∧
      assoc (translate_prog' P).1 fn = Some (fun sid => (translate_cmd P (translate_funs P fs').1 (f_body f) sid sid).2) /\
      assoc (translate_prog' P).2 fn = Some (translate_call P fn (translate_funs P ((fn, f) :: fs')).1).
Proof.
  unfold translate_prog'.
  induction (p_funcs P) as [|[gn g] fs' ih_fs'].
  - move => //.
  - (* simpl in *. *)
    move => h //.
    simpl in h.
    destruct (fn == gn) eqn:e.
    + move /eqP in e.
      subst.
      noconf h.
      exists fs'.
      exists [::].
      simpl.
      destruct (translate_funs P fs') as [f_body f_prog] eqn:E2.
      simpl.
      unfold translate_call. simpl.
      assert (E : gn == gn) by now apply /eqP.
      rewrite E. easy.
    + specialize (ih_fs' h).
      simpl.
      destruct (translate_funs P fs') as [fdefs ctrrogs] eqn:E2.
      destruct ih_fs' as [fs'0 [l0 [ihl [iha ihb]]]]. simpl.
      rewrite e.
      rewrite ihl.
      exists fs'0. exists ((gn, g) :: l0).
      subst. split; [|split]; try easy.
Qed.

(** Handled programs

  This predicate eliminates programs that are currently not supported by the
  translation. This is mainly used to disallow while loops.
  It also checks programs for acyclicity and correct ordering.
*)

Fixpoint instr_r_fs
  (i : instr_r) (fs : seq _ufun_decl) {struct i}
  : bool
with instr_fs  (i : instr) (fs : seq _ufun_decl) {struct i}
  : bool  :=
  instr_r_fs (instr_d i) fs.
Proof.
  pose proof (cmd_fs :=
    (fix cmd_fs (c : cmd) (fs : seq _ufun_decl) : bool :=
      match c with
      | [::] => true
      | i :: c =>
          cmd_fs c fs && instr_fs i fs
      end
    )).
  refine
    match i with
    | Cassgn l _ s e =>
        true
    | Copn ls _ o es =>
        true
    | Csyscall ls sc es =>
        true
    | Cif e c1 c2 =>
        cmd_fs c1 fs && cmd_fs c2 fs
    | Cfor i r c =>
        cmd_fs c fs
    | Cwhile _ c1 _ c2 => cmd_fs c1 fs && cmd_fs c2 fs
    | Ccall ii xs f args =>
        f \in [seq p.1 | p <- fs]
    end.
Defined.

Section CmdFS.

Fixpoint cmd_fs (c : cmd) (fs : seq _ufun_decl) : bool :=
      match c with
      | [::] => true
      | i :: c =>
          cmd_fs c fs && instr_fs i fs
      end.

End CmdFS.

Fixpoint handled_instr (i : instr) :=
  match i with
  | MkI ii i => handled_instr_r i
  end

with handled_instr_r (i : instr_r) :=
  match i with
  | Cassgn l tag sty e => true
  | Copn l tag o es => true
  | Csyscall _ _ _ => false
  | Cif e c₁ c₂ => List.forallb handled_instr c₁ && List.forallb handled_instr c₂
  | Cfor i r c => List.forallb handled_instr c
  | Cwhile al cb e c => false
  | Ccall ii l fn es => true
  end.

Definition handled_cmd (c : cmd) :=
  List.forallb handled_instr c.

Definition handled_fundecl (f : _ufun_decl) :=
  handled_cmd f.2.(f_body).

Lemma lemma3 suf pre :
  (foldr (fun f '(b, l) => if b then (cmd_fs f.2.(f_body) l, f :: l) else (false, f :: l)) (true, [::]) (suf ++ pre)).1  ->
  (foldr (fun f '(b, l) => if b then (cmd_fs f.2.(f_body) l, f :: l) else (false, f :: l)) (true, [::]) pre).1.
Proof.
  intros H.
  induction suf.
  - easy.
  - simpl in *.
    apply IHsuf.
    destruct foldr.
    destruct b.
    + easy.
    + easy.
Qed.

Lemma lemma4 pre :
  (foldr (fun f '(b, l) => if b then (cmd_fs f.2.(f_body) l, f :: l) else (false, f :: l)) (true, [::]) pre).2 = pre.
Proof.
  induction pre.
  - reflexivity.
  - simpl.
    destruct foldr.
    destruct b; simpl in *; congruence.
Qed.

Lemma lemma2 g gn (pre suf : list _ufun_decl) :
  (foldr (fun f '(b, l) => if b then (cmd_fs f.2.(f_body) l, f :: l) else (false, f :: l)) (true, [::]) (suf ++ (gn,g) :: pre)).1  ->
  cmd_fs g.(f_body) pre.
Proof.
  intros.
  eapply lemma3 in H.
  simpl in H.
  pose proof lemma4 pre.
  destruct foldr.
  destruct b; simpl in *; congruence.
Qed.

Definition handled_program (P : uprog) :=
  List.forallb handled_fundecl P.(p_funcs) &&
    (foldr (fun f '(b, l) => if b then (cmd_fs f.2.(f_body) l, f :: l) else (false, f :: l)) (true, [::]) P.(p_funcs)).1 &&
    uniq [seq p.1 | p <- P.(p_funcs)].
Context `{sc_sem : syscall_sem }.

Fact sem_call_get_some {P m1 scs1 gn vargs m2 scs2 vres} :
  (sem_call P scs1 m1 gn vargs scs2 m2 vres →
   ∃ f, get_fundef (p_funcs P) gn = Some f ).
Proof. intros H. inversion H. exists f. easy.
Qed.

Definition get_translated_fun P fn : trfun :=
  match assoc (translate_prog' P).2 fn with
  | Some f => f
  | None => λ _ _, ret [::]
  end.

Lemma translate_call_head {P gn fs' f} :
  assoc (translate_prog' P).1 gn =
    Some (fun sid => (translate_cmd P (translate_funs P fs').1 (f_body f) sid sid).2)
  →
    translate_call P gn (translate_funs P (p_funcs P)).1
    = translate_call P gn (translate_funs P ((gn,f) :: fs')).1.
Proof.
  intros ef.
  unfold translate_call at 1.
  rewrite ef.
  simpl.
  destruct (translate_funs P fs'). simpl.
  unfold translate_call, assoc at 1.
  assert (E : gn == gn) by now apply /eqP.
  now rewrite E.
Qed.

Context `{asm_correct : ∀ o, sem_correct (tin (get_instr_desc (Oasm o))) (sopn_sem (Oasm o))}.
Context (gd : glob_decls).

Lemma translate_instr_r_if P SP e c1 c2 id sid :
  translate_instr_r P SP (Cif e c1 c2) id sid =
    let (sid', c1') := translate_cmd P SP c1 id sid in
    let (sid'', c2') := translate_cmd P SP c2 id sid' in
    let e' := translate_pexpr (p_globs P) id e in
    let rb := coe_tyc 'bool e' in (sid'', b ← rb ;;
                                         if b
                                         then c1'
                                         else c2').
Proof. reflexivity. Qed.

Lemma translate_instr_r_for P SP i r c id sid :
  translate_instr_r P SP (Cfor i r c) id sid =
    let '(d, lo, hi) := r in
    let (sid', fresh) := fresh_id sid in
    let loᵗ := coe_tyc 'int (translate_pexpr (p_globs P) id lo) in
    let hiᵗ := coe_tyc 'int (translate_pexpr (p_globs P) id hi) in
    let cᵗ := translate_cmd P SP c id in (sid', vlo ← loᵗ ;;
                                                   vhi ← hiᵗ ;;
                                                   translate_for i (wrange d vlo vhi) id cᵗ fresh).
Proof. reflexivity. Qed.


Ltac invert_stack st hst hdisj hevm hpre hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2 :=
  apply invert_valid_stack in st as [hst [hdisj [hevm [hpre [hvalid [hnin [hnodup [hvalid1 [hpre1 [hdisj1 hdisj2]]]]]]]]]].

Ltac split_and :=
  repeat lazymatch goal with
  | |- _ /\ _ => split
         end.

Lemma valid_stack_prec vm m_id s_id1 s_id2 s_st st h :
    s_id1 ⪯ s_id2 ->
    valid_stack ((vm, m_id, s_id1, s_st) :: st) h ->
    valid_stack ((vm, m_id, s_id2, s_st) :: st) h.
Proof.
  intros hpre12 vst.
  invert_stack vst hst hevm hpre hdisj hvalid hnin hnodup hvalid1 hpre1 hdisj1 hdisj2.
  eapply valid_stack_cons; unfold valid_stack_frame; split_and; eauto with prefix.
  - eapply valid_prec; eauto.
  - intros contra.
    eapply disj_antirefl.
    eapply disj_prec_r.
    1: eapply hpre12.
    apply disj_sym.
    apply hdisj1.
    assumption.
  - intros s_id' s_in'.
    eapply disj_prec_l.
    1: eapply hpre12.
    apply hdisj1.
    assumption.
Qed.

Lemma rel_estate_prec : forall h s m_id s_id1 s_id2 s_st st,
    s_id1 ⪯ s_id2 ->
    rel_estate s m_id s_id1 s_st st h ->
    rel_estate s m_id s_id2 s_st st h.
Proof.
  intros h s m_id s_id1 s_id2 s_st st hpre12 [hmem hstack]; split; auto.
  eapply valid_stack_prec; eauto.
Qed.

Lemma rel_estate_pop_sub s m_id s_id s_id' s_st st :
  ∀ h, rel_estate s m_id s_id (s_id' :: s_st) st h → rel_estate s m_id s_id' s_st st h.
Proof.
  intros h [hmem hstack].
  split.
  - assumption.
  - eapply valid_stack_pop_sub; eassumption.
Qed.

Lemma rel_estate_pop scs m vm vm' m_id m_id' s_id s_id' s_st s_st' st :
  ∀ h, rel_estate {| escs := scs ; emem := m ; evm := vm |} m_id s_id s_st ((vm',m_id',s_id',s_st') :: st) h →
       rel_estate {| escs := scs ; emem := m ; evm := vm' |} m_id' s_id' s_st' st h.
Proof.
  intros h [hmem hstack].
  split.
  - assumption.
  - eapply valid_stack_pop; eassumption.
Qed.

Lemma rel_estate_push_sub s m_id s_id s_st st :
  ∀ h : heap, rel_estate s m_id s_id s_st st h →
              rel_estate s m_id s_id~1 (s_id~0 :: s_st) st h.
Proof.
  intros h [hmem hstack]; split.
  - assumption.
  - eapply valid_stack_push_sub; eassumption.
Qed.

Lemma rel_estate_push m vm scs m_id s_id s_st st :
  ∀ h : heap, rel_estate {| escs := scs ; emem := m ; evm := vm |} m_id s_id s_st st h →
              rel_estate {| escs := scs ; emem := m ; evm := vmap0 |} s_id~1 s_id~1 [::] ((vm, m_id, s_id~0, s_st) :: st) h.
Proof.
  intros h [hmem hstack]; split.
  - assumption.
  - eapply valid_stack_push; eassumption.
Qed.

Lemma translate_cmd_preceq P SP c m_id s_id :
  let (s_id', _) := translate_cmd P SP c m_id s_id in s_id ⪯ s_id'.
Proof.
  revert s_id.
  set (Pr := fun (i : instr_r) =>
               forall s_id, let (s_id', _) := translate_instr_r P SP i m_id s_id in
                 s_id ⪯ s_id').
  set (Pi := fun (i : instr) =>
               Pr (instr_d i)).
  set (Pc := fun (c : cmd) =>
               forall s_id,
                 let (s_id', _) := translate_cmd P SP c m_id s_id in
                 s_id ⪯ s_id').
  eapply cmd_rect with
    (Pr := Pr)
    (Pi := Pi)
    (Pc := Pc);
    try easy
  .
  - intros s_id.
    simpl; reflexivity.
  - intros i c0 ihi ihc s_id.
    simpl.
    rewrite translate_instr_unfold.
    specialize (ihi s_id).
    destruct translate_instr_r as [s_id' ?].
    specialize (ihc s_id').
    destruct translate_cmd.
    etransitivity; eauto.
  - intros x tg ty e i; simpl; reflexivity.
  - intros xs t o es i; simpl; reflexivity.
  - intros xs o es i; simpl; reflexivity.
  - intros e c1 c2 ihc1 ihc2 s_id.
    rewrite translate_instr_r_if.
    specialize (ihc1 s_id).
    destruct translate_cmd as [s_id' ?].
    specialize (ihc2 s_id').
    destruct translate_cmd as [s_id'' ?].
    simpl.
    etransitivity; eauto.
  - intros v dir lo hi c' ihc s_id.
    rewrite translate_instr_r_for.
    simpl.
    apply fresh1.
  - intros a c1 e c2 ihc1 ihc2 s_id.
    simpl; reflexivity.
  - intros i xs f es st'.
    simpl.
    apply fresh1.
Qed.

Lemma translate_instr_r_preceq P SP i id s_id :
  let (s_id', _) := translate_instr_r P SP i id s_id in s_id ⪯ s_id'.
Proof.
  revert s_id.
  set (Pr := fun (i : instr_r) =>
               forall s_id, let (s_id', _) := translate_instr_r P SP i id s_id in
                 s_id ⪯ s_id').
  set (Pi := fun (i : instr) =>
               Pr (instr_d i)).
  set (Pc := fun (c : cmd) =>
               forall s_id,
                 let (s_id', _) := translate_cmd P SP c id s_id in
                 s_id ⪯ s_id').
  eapply instr_r_Rect with
    (Pr := Pr)
    (Pi := Pi)
    (Pc := Pc);
    try easy
  .
  - intros s_id.
    simpl; reflexivity.
  - intros i' c0 ihi ihc s_id.
    simpl.
    rewrite translate_instr_unfold.
    specialize (ihi s_id).
    destruct translate_instr_r as [s_id' ?].
    specialize (ihc s_id').
    destruct translate_cmd.
    etransitivity; eauto.
  - intros x tg ty e i'; simpl; reflexivity.
  - intros xs t o es i'; simpl; reflexivity.
  - intros xs o es i'; simpl; reflexivity.
  - intros e c1 c2 ihc1 ihc2 s_id.
    rewrite translate_instr_r_if.
    specialize (ihc1 s_id).
    destruct translate_cmd as [s_id' ?].
    specialize (ihc2 s_id').
    destruct translate_cmd as [s_id'' ?].
    simpl.
    etransitivity; eauto.
  - intros v dir lo hi c' ihc s_id.
    rewrite translate_instr_r_for.
    simpl.
    apply fresh1.
  - intros a c1 e c2 ihc1 ihc2 s_id.
    simpl; reflexivity.
  - intros i' xs f es st'.
    simpl.
    apply fresh1.
Qed.

Lemma translate_instr_r_pres P SP c s m_id s_id s_st st h :
  let (s_id', _) := translate_instr_r P SP c m_id s_id in
  rel_estate s m_id s_id s_st st h -> rel_estate s m_id s_id' s_st st h.
Proof.
  pose proof translate_instr_r_preceq P SP c m_id s_id.
  destruct translate_instr_r as [s_id' ?].
  apply rel_estate_prec; assumption.
Qed.

Lemma translate_cmd_pres P SP c s m_id s_id s_st st h :
  let (s_id', _) := translate_cmd P SP c m_id s_id in
  rel_estate s m_id s_id s_st st h -> rel_estate s m_id s_id' s_st st h.
Proof.
  pose proof translate_cmd_preceq P SP c m_id s_id.
  destruct translate_cmd as [s_id' ?].
  apply rel_estate_prec; assumption.
Qed.

Definition Pfun (P : uprog) (fn : funname) scs m va scs' m' vr vm m_id s_id s_st st :=
  ⊢ ⦃ rel_estate {| escs := scs ; emem := m; evm := vm |} m_id s_id s_st st ⦄
      get_translated_fun P fn s_id~1 [seq totce (translate_value v) | v <- va]
      ⇓ [seq totce (translate_value v) | v <- vr]
      ⦃ rel_estate {| escs := scs' ; emem := m' ; evm := vm |} m_id s_id~0 s_st st ⦄.

Lemma hget_lemma (l : seq var_i) vm vres :
  mapM (λ x : var_i, get_var vm x) l = ok vres ->
  [seq encode (vtype (v_var x)) | x <- l] = [seq choice_type_of_val v | v <- vres].
Proof.
  revert vres vm.
  induction l; intros.
  - inversion H; reflexivity.
  - inversion H.
    jbind H1 v Hv.
    jbind H1 v' Hv'.
    noconf H1.
    simpl.
    unfold choice_type_of_val.
    erewrite type_of_get_var by eassumption.
    erewrite IHl by eassumption.
    reflexivity.
Qed.

Lemma hget_lemma2 l scs m vm vres m_id s_id s_st st :
  mapM (λ x : var_i, get_var vm x) l = ok vres ->
  List.Forall2
    (λ (c : ∑ a : choice_type, raw_code a) (v : value),
      ⊢ ⦃ rel_estate {| escs := scs ; emem := m; evm := vm |} m_id s_id s_st st ⦄
          c.π2 ⇓ coe_cht c.π1 (translate_value v)
          ⦃ rel_estate {| escs := scs ; emem := m; evm := vm |} m_id s_id s_st st ⦄)
    [seq totc (encode (vtype (v_var x))) (translate_get_var m_id x) | x <- l] vres.
Proof.
  revert m vm vres m_id s_id s_st st.
  induction l; intros.
  - inversion H. constructor.
  - inversion H.
    jbind H1 v Hv.
    jbind H1 v' Hv'.
    noconf H1.
    constructor.
    + simpl.
      eapply translate_get_var_correct; eauto.
      simpl. assumption.
    + eapply IHl. assumption.
Qed.

Lemma htrunc_lemma1 l vargs vargs':
  mapM2 ErrType truncate_val l vargs' = ok vargs
  -> (trunc_list l [seq totce (translate_value v) | v <- vargs']) = [seq totce (translate_value v) | v <- vargs].
Proof.
  revert vargs vargs'.
  induction l; intros.
  - destruct vargs'.
    + inversion H; reflexivity.
    + inversion H.
  - destruct vargs'.
    + inversion H.
    + inversion H.
      jbind H1 v' Hv'.
      jbind H1 v'' Hv''.
      noconf H1.
      simpl.
      unfold trunc_list.
      simpl.
      erewrite totce_truncate_translate by eassumption.
      f_equal.
      apply IHl.
      assumption.
Qed.

Lemma translate_for_ext v l m_id s_id c c' :
  (forall s_id, c s_id = c' s_id) ->
  translate_for v l m_id c s_id = translate_for v l m_id c' s_id.
Proof.
  revert s_id.
  induction l; intros s_id hext.
  - reflexivity.
  - simpl.
    rewrite hext.
    destruct c'.
    rewrite IHl; auto.
Qed.

Lemma lemma1 P pre c suf m_id :
  uniq [seq p.1 | p <- suf ++ pre] ->
  forall s_id,
  cmd_fs c pre ->
  translate_cmd P (translate_funs P (suf ++ pre)).1 c m_id s_id
  = translate_cmd P (translate_funs P pre).1 c m_id s_id.
Proof.
  intros huniq.
  set (Pr := fun (i : instr_r) =>
               forall s_id,
                 instr_r_fs i pre ->
               translate_instr_r P (translate_funs P (suf ++ pre)).1 i m_id s_id
               = translate_instr_r P (translate_funs P pre).1 i m_id s_id).
  set (Pi := fun (i : instr) =>
               Pr (instr_d i)).
  set (Pc := fun (c : cmd) =>
               forall s_id,
                 cmd_fs c pre ->
               translate_cmd P (translate_funs P (suf ++ pre)).1 c m_id s_id
               = translate_cmd P (translate_funs P pre).1 c m_id s_id).
  eapply cmd_rect with
    (Pr := Pr)
    (Pi := Pi)
    (Pc := Pc);
    try easy
  .
  - intros i c' ihi ihc s_id' hpre.
    unfold Pc.
    simpl.
    unfold Pi in ihi.
    red in ihi.
    rewrite !translate_instr_unfold.
    simpl in hpre.
    move: hpre => /andP [hi hc].
    rewrite ihi.
    2: destruct i; auto.
    destruct translate_instr_r as [s_id'' i'].
    rewrite ihc; auto.
  - intros e c1 c2 ihc1 ihc2 s_id' hpre.
    rewrite !translate_instr_r_if.
    simpl in hpre.
    fold cmd_fs in hpre.
    move: hpre => /andP [hc1 hc2].
    rewrite ihc1; auto.
    destruct translate_cmd as [s_id'' c'].
    rewrite ihc2; auto.
  - intros v d lo hi c' ihc s_id hpre.
    simpl in hpre.
    fold cmd_fs in hpre.
    rewrite !translate_instr_r_for.
    red in ihc.
    simpl.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros lb.
    f_equal.
    apply functional_extensionality.
    intros ub.
    erewrite translate_for_ext; eauto.
  - intros i lvals f es s_id hpre.
    simpl in hpre.
    unfold translate_instr_r.
    simpl.
    f_equal.
    unfold translate_call.
    symmetry; destruct assoc eqn:E.
    +  assert (H2 : exists r', assoc pre f = Some r').
      * clear -E.
        induction pre. 1: discriminate.
        destruct a.
        simpl in *.
        destruct (f == s).
        ** eexists. reflexivity.
        ** apply IHpre; auto.
      * destruct H2 as [r'].
        assert (assoc (translate_funs P (suf ++ pre)).1 f = Some r).
        ** eapply mem_uniq_assoc.
           *** clear -E.
               induction suf.
               **** induction pre.
                    ***** discriminate.
                    *****
                    destruct a.
                    simpl in *.
                    destruct (f==s) eqn:E2.
                    ******
                      move: E2 => /eqP ->. left. noconf E.
                    reflexivity.
                    ****** right.
                    apply IHpre. assumption.
               **** destruct a.
                    simpl.
                    right.
                    assumption.
           *** clear -huniq.
               induction suf.
               **** induction pre.
                    ***** easy.
                    ***** destruct a.
                    simpl in *.
                    move: huniq => /andP [huniq1 huniq2].
                    apply /andP; split.
                    ****** clear -huniq1. induction pre.
                    ******* easy.
                    ******* destruct a.
                    Check [eqType of BinNums.positive].
                    simpl in huniq1.
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- pre] s.
                    rewrite H in huniq1.
                    move: huniq1 => /andP [huniq11 huniq12].
                    simpl.
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- (translate_funs P pre).1] s.
                    rewrite H0.
                    apply /andP.
                    split; auto.
                    ****** apply IHpre. assumption.
               **** destruct a.
                    simpl in *.
                    move: huniq => /andP [huniq1 huniq2].
                    apply /andP.
                    split.
                    ****** clear -huniq1. induction suf.
                    ******* induction pre.
                    ******** easy.
                    ******** destruct a.
                    simpl in *.
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- pre] s.
                    rewrite H in huniq1.
                    move: huniq1 => /andP [huniq11 huniq12].
                    simpl.
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- (translate_funs P pre).1] s.
                    rewrite H0.
                    apply /andP.
                    split; auto.
                    *******
                      destruct a.
                    simpl in *.
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- suf ++ pre] s.
                    rewrite H in huniq1.
                    move: huniq1 => /andP [huniq11 huniq12].
                    pose proof notin_cons [eqType of BinNums.positive] p [seq p.1 | p <- (translate_funs P (suf ++ pre)).1] s.
                    rewrite H0.
                    apply /andP.
                    split; auto.
                    ****** apply IHsuf; auto.
        ** rewrite H0. reflexivity.
    + exfalso.
      assert (H2 : assoc pre f = None).
      * clear -E.
        induction pre.
        **  reflexivity.
        **  simpl in *.
            destruct a.
            simpl in *.
            destruct (f == p).
            *** discriminate.
            *** apply IHpre; auto.
      * clear -H2 hpre.
        induction pre.
        ** easy.
        ** destruct a.
           simpl in *.
           rewrite in_cons in hpre.
           destruct (f == s).
           *** simpl in *.
               discriminate.
           *** simpl in *.
               apply IHpre; auto.
Qed.

Theorem translate_prog_correct P scs m vargs scs' m' vres :
  ∀ fn,
    sem.sem_call (P : @uprog asm_op asmop) scs m fn vargs scs' m' vres →
    handled_program P ->
    ∀ vm m_id s_id s_st st,
    Pfun P fn scs m vargs scs' m' vres vm m_id s_id s_st st.
Proof using gd asm_correct.
  intros fn H hP.
  set (Pfun := λ (scs : syscall_state_t) (m : mem) (fn : funname) (va : seq value) (scs' : syscall_state_t) (m' : mem) (vr : seq value),
         handled_program P -> forall vm m_id s_id s_st st, Pfun P fn scs m va scs' m' vr vm m_id s_id s_st st
      ).
  set (SP := (translate_prog' P).1).
  set (Pi_r :=
         λ (s1 : estate) (i : instr_r) (s2 : estate),
         ∀ m_id s_id s_st st,
           handled_instr_r i →
           let (s_id', i') := translate_instr_r P SP i m_id s_id in
           ⊢ ⦃ rel_estate s1 m_id s_id s_st st ⦄
               i' ⇓ tt
               ⦃ rel_estate s2 m_id s_id' s_st st ⦄).
  set (Pi := λ s1 i s2, Pi_r s1 (instr_d i) s2).
  set (Pc :=
         λ (s1 : estate) (c : cmd) (s2 : estate),
         ∀ m_id s_id s_st st,
           handled_cmd c →
           let (s_id', c') := translate_cmd P SP c m_id s_id in
           ⊢ ⦃ rel_estate s1 m_id s_id s_st st ⦄
                 c' ⇓ tt
               ⦃ rel_estate s2 m_id s_id' s_st st ⦄).
  set (Pfor :=
    λ (v : var_i) (ws : seq Z) (s1 : estate) (c : cmd) (s2 : estate),
         ∀ m_id s_id s_id' s_st st,
           handled_cmd c →
           s_id~1 ⪯ s_id' ->
           exists s_id'',
      ⊢ ⦃ rel_estate s1 m_id s_id' (s_id~0 :: s_st) st ⦄
        translate_for v ws m_id (translate_cmd P SP c m_id) s_id' ⇓ tt
      ⦃ rel_estate s2 m_id s_id'' (s_id~0 :: s_st) st ⦄
  ).
  unshelve eapply (@sem_call_Ind asm_op syscall_state mk_spp _ Pc Pi_r Pi Pfor Pfun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  - (* nil *)
    intros s m_id s_id s_st st _. simpl.
    eapply u_ret_eq.
    intros h preh. auto.
  - (* cons *)
    red.
    intros s1 s2 s3 i c hi ihi hc ihc m_id s_id s_st st hp. (* sp fp ctr h fp_prec. *)
    inversion hp.
    move: H1 => /andP [hdi hdc].
    unfold Pi in ihi. unfold Pi_r in ihi.
    simpl.
    rewrite translate_instr_unfold.
    pose proof translate_instr_r_preceq P SP (instr_d i) m_id s_id.
    specialize (ihi m_id s_id).
    pose proof (translate_instr_r_pres P SP (instr_d i) s1 m_id s_id).
    destruct translate_instr_r as [s_id' i'] eqn:E.
    unfold Pc in ihc.
    specialize (ihc m_id s_id').
    pose proof (translate_cmd_preceq P SP c m_id s_id').
    pose proof (translate_cmd_pres P SP c s1 m_id s_id').
    destruct translate_cmd as [s_id'' c'] eqn:Ec.
    split.
    + eapply u_bind.
      * eapply ihi.
        1: destruct i; apply hdi.
      * eapply ihc.
        1: assumption.
  - (* mkI *)
    red. intros ii i s1 s2 hi ihi.
    apply ihi.
  - (* assgn *)
    red. intros s₁ s₂ x tag ty e v v' he hv hw m_id s_id s_st st hp.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct. all: eauto. }
    erewrite translate_pexpr_type by eassumption.
    rewrite coerce_to_choice_type_K.
    erewrite totce_truncate_translate by eassumption.
    eapply u_post_weaken_rule.
    1: eapply u_pre_weaken_rule.
    1: eapply translate_write_lval_correct. all: eauto.
  - (* opn *)
    red.
    (* easy. *)
    intros s1 s2 tag o xs es ho m_id s_id s_st st hp.
    jbind ho vs hv.
    jbind hv vs' hv'.
    eapply u_bind.
    + eapply bind_list_pexpr_correct. 2: eassumption.
      eauto.
    + unshelve erewrite translate_exec_sopn_correct by eassumption.
      1: assumption.
      eapply u_post_weaken_rule.
      1: apply translate_write_lvals_correct.
      all: eauto.
  - (* sys_call *)
    easy.
  - (* if_true *)
    intros s1 s2 e c1 c2 he hc1 ihc1 m_id s_id s_st st hp.
    inversion hp.
    move: H1 => /andP [hdc1 hdc2].
    rewrite translate_instr_r_if.
    simpl.
    unfold Pc in ihc1.
    specialize (ihc1 m_id s_id s_st st).
    pose proof translate_cmd_pres P SP c1 s1 m_id s_id s_st st.
    destruct (translate_cmd P SP c1 m_id s_id) as [s_id'' c1'] eqn:E1.
    pose proof translate_cmd_pres P SP c2 s2 m_id s_id'' s_st st.
    destruct (translate_cmd P SP c2 m_id s_id'') as [s_id''' c2'] eqn:E2.
    split.
    + eapply u_bind.
      1:{ eapply translate_pexpr_correct_cast in he. all: eauto. }
    eapply u_post_weaken_rule.
    1: eapply ihc1.
    1: eapply hdc1.
    1: assumption.
  - (* if_false *)
    intros s1 s2 e c1 c2 he hc2 ihc2 m_id s_id s_st st hp.
    inversion hp.
    move: H1 => /andP [hdc1 hdc2].
    rewrite translate_instr_r_if.
    simpl.
    unfold Pc in ihc2.
    pose proof translate_cmd_pres P SP c1 s1 m_id s_id s_st st.
    destruct (translate_cmd P SP c1 m_id s_id) as [s_id'' c1'] eqn:E1.
    specialize (ihc2 m_id s_id'' s_st st).
    destruct (translate_cmd P SP c2 m_id s_id'') as [s_id''' c2'] eqn:E2.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in he. all: eauto. }
    eapply u_pre_weaken_rule.
    1: eapply u_post_weaken_rule.
    1: eapply ihc2.
    1: assumption.
    1: { intros h rel. eapply rel_estate_prec. 1:reflexivity. 1: eassumption. }
    assumption.
  - (* while_true *)
    easy.
  - (* while_false *)
    easy.
  - (* for *)
    intros s s2 i d lo hi c vlo vhi hlo hhi hfor ihfor m_id s_id s_st st hp.
    rewrite translate_instr_r_for.
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in hlo. all: eauto. }
    eapply u_bind.
    1:{ eapply translate_pexpr_correct_cast in hhi. all: eauto. }
    unfold Pfor in ihfor.
    simpl in ihfor.
    specialize (ihfor m_id s_id s_id~1 s_st st ltac:(apply hp) ltac:(reflexivity)).
    destruct ihfor as [s_id''].
    eapply u_pre_weaken_rule.
    1: eapply u_post_weaken_rule.
    1: exact H0.
    1: apply rel_estate_pop_sub.
    apply rel_estate_push_sub.
  - (* for_nil *)
    intros s i c m_id s_id s_id' s_st st hdc hpre.
    simpl.
    exists s_id'.
    apply u_ret_eq.
    easy.
  - (* for_cons *)
    intros s1 s1' s2 s3 i w ws c hw hc ihc hfor ihfor m_id s_id s_id' s_st st hdc hpre.
    simpl.
    specialize (ihc m_id s_id' (s_id~0 :: s_st) st hdc).
    pose proof translate_cmd_preceq P SP c m_id s_id'.
    destruct translate_cmd as [s_id'' c'] eqn:E.
    specialize (ihfor m_id s_id s_id'' s_st st hdc ltac:(etransitivity;eauto)) as [s_id''' ihfor].
    exists s_id'''.
    eapply u_put.
    eapply u_pre_weaken_rule.
    2: {
      intros ? [me [hme ?]]. subst.
      eapply translate_write_var_estate. all: try eassumption.
    }
    eapply u_bind.
    1: eapply ihc.
    eapply ihfor.
  - (* call *)
    intros s1 scs1 m2 s2 ii xs gn args vargs' vres' hargs hgn ihgn hwr_vres m_id s_id s_st st hdi.
    unfold Pfun, Translation.Pfun, get_translated_fun in ihgn.
    simpl.
    eapply u_bind.
    1: eapply bind_list_pexpr_correct with (s_id:=s_id) (s_st:=s_st) (st:=st); try eassumption; easy.
    eapply u_bind with (v₁ := [seq totce (translate_value v) | v <- vres']).
    1: specialize (ihgn hP (evm s1) m_id s_id s_st st).
    1: eapply u_pre_weaken_rule.
    * destruct (sem_call_get_some hgn) as [f hf].
      destruct (tr_prog_inv hf) as [fs' [l [hl [ef ep]]]].
      simpl in ep.
      rewrite ep in ihgn.
      pose (translate_call_head ef) as hc.
      rewrite hc.
      eapply ihgn.
    * easy.
    * eapply translate_write_lvals_correct.
      1:assumption.
      exact hwr_vres.
  - (* proc *)
    intros scs1 m1 scs2 m2 gn g vargs' vargs'' s1 vm2 vres' vres''.
    intros hg hvars hwr hbody ihbody hget htrunc.
    intros hp vm m_id s_id s_st st.
    unfold Translation.Pfun.
    unfold get_translated_fun.
    destruct (tr_prog_inv hg) as [fs' [l [hl ]]].
    unfold Pc, SP, translate_prog' in ihbody.
    unfold translate_prog' in *.
    rewrite hl in ihbody.
    rewrite hl.
    destruct H0 as [ef ep].
    rewrite hl in ef.
    rewrite hl in ep.
    subst SP.
    rewrite ep.
    unfold translate_call.
    simpl.
    destruct (translate_funs P fs') as [tr_fs' tsp'] eqn:Efuns.
    simpl.
    assert (E : gn == gn) by now apply /eqP.
    rewrite E; clear E.
    unfold translate_call_body.
    rewrite hg.
    eapply u_bind.
    1: {
      erewrite htrunc_lemma1 by eassumption.
      eapply u_pre_weaken_rule.
      1: eapply translate_write_vars_correct; eassumption.
      eapply rel_estate_push.
    }
    assert (handled_cmd (f_body g)) as hpbody.
    {
      clear -hg hp.
      pose (gd := (gn, g)).
      unfold handled_program in *.
      move: hp => /andP [] /andP [] hp1 hp2 hp3.
      pose (hh := (List.forallb_forall handled_fundecl (p_funcs P)).1 hp1 gd).
      destruct g.
      apply hh. simpl.
      now apply (assoc_mem' hg).
    }
    specialize (ihbody s_id~1 s_id~1 [::] ((vm, m_id, s_id~0, s_st) :: st) hpbody). clear hpbody.
    assert ((l ++ (gn,g) :: fs') = ((l ++ [:: (gn,g)]) ++ fs')) by (rewrite <- List.app_assoc; reflexivity).
    assert (htr : translate_cmd P (translate_funs P (l ++ ((gn,g) :: fs'))).1 (f_body g) s_id~1 s_id~1
                  = translate_cmd P (translate_funs P fs').1 (f_body g) s_id~1 s_id~1).
    { rewrite H0.
      eapply lemma1.
      { clear -hp hl H0.
        unfold handled_program in *.
        move: hp => /andP [] /andP [_ _].
        now rewrite hl H0.
      }
      clear -hp hl.
      move: hp => /andP [] /andP [_ hp2 _].
      rewrite hl in hp2.
      eapply lemma2.
      eassumption.
    }
    rewrite htr in ihbody.
    rewrite Efuns in ihbody.
    destruct (translate_cmd P tr_fs' (f_body g) s_id~1 s_id~1) as [s_id' c'] eqn:E.
    rewrite E in ihbody.
    rewrite E.
    simpl.

    eapply u_bind with (v₁ := tt).
    + eapply ihbody.
    + eapply u_bind.
      * eapply bind_list_correct.
        ** rewrite <- map_comp.
           unfold comp.
           simpl.
           eapply hget_lemma; eassumption.
        ** eapply hget_lemma2.
           assumption.
      * clear -htrunc.
        eapply u_ret.
        split.
        1: eapply rel_estate_pop.
        1: eassumption.
        eapply htrunc_lemma1.
        eassumption.
  - assumption.
Qed.

Lemma deterministic_seq {A} (c1 : raw_code A) {B} (c2 : raw_code B) :
  deterministic c1 ->
  deterministic c2 ->
  deterministic (c1 ;; c2).
Proof.
  intros.
  revert X0. revert c2. (* generalize (B c1). *)
  induction c1; eauto; intros.
  - inversion X.
  - simpl. constructor. inversion X.
    noconf H1; subst; simpl in *. intros. eapply X0; eauto.
  - simpl. constructor. inversion X.
    noconf H1; subst; simpl in *. intros. eapply IHc1; eauto.
  - inversion X.
Qed.

Lemma deterministic_bind {A} (c1 : raw_code A) {B} (c2 : A -> raw_code B) :
  deterministic c1 ->
  (forall x, deterministic (c2 x)) ->
  deterministic (x ← c1 ;; c2 x).
Proof.
  intros.
  revert X0. revert c2. (* generalize (B c1). *)
  induction c1; eauto; intros.
  - simpl. inversion X.
  - simpl. constructor. inversion X.
    noconf H1; subst; simpl in *. intros. eapply X0; eauto.
  - simpl. constructor. inversion X.
    noconf H1; subst; simpl in *. intros. eapply IHc1; eauto.
  - inversion X.
Qed.

Lemma translate_write_vars_deterministic i vs ts :
  deterministic (translate_write_vars i vs ts).
Proof.
  revert vs ts.
  induction vs, ts.
  1,2,3: unfold translate_write_vars; simpl; econstructor.
  unfold translate_write_vars in *.  eapply deterministic_seq.
  - unfold translate_write_var. constructor. constructor.
  - eapply IHvs.
Qed.

Lemma translate_gvar_deterministic g i v :
  deterministic (translate_gvar g i v).
Proof.
  unfold translate_gvar. destruct is_lvar.
  * unfold translate_get_var. constructor. intros; constructor.
  * destruct get_global; constructor.
Qed.

Lemma translate_pexpr_deterministic g i e :
  deterministic (translate_pexpr g i e).π2.
Proof.
  revert i g.
  refine (
      (fix aux (e1 : pexpr) :=
    match e1 with
    | _ => _ end) e
   ).
  destruct e1; intros; simpl; try constructor.
  - apply translate_gvar_deterministic.
  - simpl.
    eapply deterministic_bind.
    + eapply translate_gvar_deterministic.
    + intros. simpl.
      rewrite bind_assoc.
      eapply deterministic_bind.
      * eapply aux.
      * intros. constructor.
  - eapply deterministic_bind.
    + eapply translate_gvar_deterministic.
    + intros. simpl.
      rewrite bind_assoc.
      eapply deterministic_bind.
      * eapply aux.
      * intros. constructor.
  - intros.
    rewrite bind_assoc.
    eapply deterministic_bind; try constructor.
    + eapply aux.
    + intros. constructor.
  - rewrite bind_assoc.
    eapply deterministic_bind; try constructor.
    eapply aux.
  - rewrite !bind_assoc.
    eapply deterministic_bind; try constructor.
    + eapply aux.
    + intros.
      eapply deterministic_bind; try constructor.
      intros.
      eapply deterministic_bind; try constructor; auto.
      eapply deterministic_bind; try constructor; auto.
  - epose proof deterministic_bind (bind_list [seq translate_pexpr g i e0 | e0 <- l]) (fun vs => ret (tr_app_sopn_single (type_of_opN o).1 (sem_opN_typed o) vs)).
    eapply X.
    + clear -aux. induction l.
      * constructor.
      * simpl. eapply deterministic_bind.
        ** eapply aux.
        ** intros.
           epose proof deterministic_bind (bind_list [seq translate_pexpr g i e0 | e0 <- l]).
           eapply X.
           *** assumption.
           *** constructor.
    + constructor.
  - rewrite bind_assoc.
    eapply deterministic_bind; try constructor.
    + apply aux.
    + intros.
      eapply deterministic_bind; try constructor.
      intros.
      destruct x0.
      * eapply deterministic_bind; try constructor; auto.
      * eapply deterministic_bind; try constructor; auto.
Qed.

Lemma translate_write_var_deterministic i H v :
  deterministic (translate_write_var i H v).
Proof.
  repeat constructor.
Qed.

Lemma translate_write_lval_deterministic g i l v :
  deterministic (translate_write_lval g i l v).
Proof.
  destruct l; intros; simpl.
  - constructor.
  - eapply translate_write_var_deterministic.
  - constructor; intros.
    eapply deterministic_bind; try constructor; auto.
    1: eapply translate_pexpr_deterministic. intros.
    repeat constructor.
  - constructor; intros.
    eapply deterministic_bind; try constructor; auto.
    + eapply deterministic_bind; try constructor.
      eapply translate_pexpr_deterministic.
    + constructor.
  - constructor; intros.
    eapply deterministic_bind; try constructor; auto.
    + eapply deterministic_bind; try constructor.
      eapply translate_pexpr_deterministic.
    + constructor.
Qed.

Lemma translate_write_lvals_deterministic g i l vs :
  deterministic (translate_write_lvals g i l vs).
Proof.
  revert l vs.
  induction l, vs.
  1,2,3: constructor.
  unfold translate_write_lvals.
  simpl.
  eapply deterministic_seq.
  1: eapply translate_write_lval_deterministic.
  eapply IHl.
Qed.

Lemma translate_call_body_deterministic P f fd i vs :
  deterministic (fd i) ->
  deterministic (translate_call_body P f fd i vs).
Proof.
  intros.
  unfold translate_call_body.
  induction p_funcs.
  - constructor.
  - simpl. destruct a. destruct (f == f0) eqn:E.
    + eapply deterministic_seq.
      1: eapply translate_write_vars_deterministic.
      eapply deterministic_seq.
      1: eapply X.
      eapply deterministic_bind with (c2:= (fun vres => ret (trunc_list (f_tyout _f) vres))).
      * clear -_f. induction f_res.
       ** constructor.
       ** simpl. constructor.
         intros. eapply deterministic_bind with (c2 := (fun vs => ret (totce x :: vs))).
            1: eapply IHl.
            constructor.
      * constructor.
    + eapply IHl.
Qed.

Lemma translate_call_deterministic P f (fd : fdefs) i vs :
  deterministic (match assoc fd f with Some f => f i | _ => ret tt end) ->
  deterministic (translate_call P f fd i vs).
Proof.
  intros.
  unfold translate_call.
  destruct assoc.
  2: constructor.
  eapply translate_call_body_deterministic.
  assumption.
Qed.

Lemma coe_tyc_deterministic t c :
  deterministic c.π2 -> deterministic (coe_tyc t c).
Proof.
  destruct c.
  intros.
  destruct (x == t) eqn:E.
  + move: E => /eqP. intros; subst.
    rewrite coerce_typed_code_K; try constructor.
    assumption.
  + rewrite coerce_typed_code_neq; try constructor.
    move: E => /eqP //.
Qed.

Lemma translate_for_deterministic v l i0 f i1 :
  (forall i, deterministic (f i).2) ->
 deterministic (translate_for v l i0 f i1).
Proof.
  intros.
  revert i1.
  induction l; intros.
  - constructor.
  - simpl.
    specialize (X i1).
    destruct (f i1).
    simpl in *.
    constructor.
    eapply deterministic_seq.
    1: assumption.
    eapply IHl.
Qed.

Fixpoint translate_instr_deterministic p (fd : fdefs) i i1 i2 {struct i} :
  (forall f i, deterministic (match assoc fd f with Some f => f i | _ => ret tt end)) ->
  deterministic (translate_instr p fd i i1 i2).2.
Proof.
  revert i1 i2.
  intros.
  epose proof (translate_cmd_deterministic :=
            (fix translate_cmd (c : cmd) (s_id : p_id) : deterministic (translate_cmd p fd c i1 s_id).2 :=
          match c with
          | [::] => _
          | i :: c => _
          end
            )
    ).
  destruct i; destruct i0; simpl in *; intros.
  - simpl. eapply deterministic_bind.
    + eapply translate_pexpr_deterministic.
    + intros.
      eapply translate_write_lval_deterministic.
  - eapply deterministic_bind with (c1 := bind_list _).
    + clear -i1.
      induction l0.
      * constructor.
      * simpl.
        eapply deterministic_bind.
        1: eapply translate_pexpr_deterministic.
        intros.
        eapply deterministic_bind with (c1 := bind_list _).
        1: eapply IHl0.
        constructor.
    + intros.
      eapply translate_write_lvals_deterministic.
  - constructor.
  - rewrite translate_instr_unfold. simpl.
    rewrite translate_instr_r_if.
    pose proof (translate_cmd_deterministic l i2).
    destruct translate_cmd. simpl.
    pose proof (translate_cmd_deterministic l0 p1).
    destruct translate_cmd. simpl.
    eapply deterministic_bind.
    + eapply coe_tyc_deterministic with (t := 'bool).
      eapply translate_pexpr_deterministic.
    + destruct x; assumption.
  - rewrite translate_instr_unfold.
    rewrite translate_instr_r_for.
    destruct r as [[d lo] hi].
    simpl.
    eapply deterministic_bind.
    1: eapply coe_tyc_deterministic with (t:= 'int); eapply translate_pexpr_deterministic.
    intros; eapply deterministic_bind.
    1: eapply coe_tyc_deterministic with (t:= 'int); eapply translate_pexpr_deterministic.
    intros.
    eapply translate_for_deterministic.
    intros.
    eapply translate_cmd_deterministic.
  - constructor.
  - eapply deterministic_bind with (c1 := bind_list _).
    + clear -i1.
      induction l0.
      * constructor.
      * simpl.
        eapply deterministic_bind.
        1: eapply translate_pexpr_deterministic.
        intros.
        eapply deterministic_bind with (c1 := bind_list _).
        1: eapply IHl0.
        constructor.
      + intros; simpl.
        eapply deterministic_bind with (c1 := translate_call _ _ _ _ _).
        1: eapply translate_call_deterministic.
        1: eapply X.
        eapply translate_write_lvals_deterministic.
        Unshelve.
        1: constructor.
        simpl.
        specialize (translate_instr_deterministic p fd i i1 s_id).
        destruct translate_instr.
        specialize (translate_cmd c p0).
        destruct jasmin_translate.translate_cmd.
        eapply deterministic_seq.
        1: eapply translate_instr_deterministic.
        all: try assumption.
Qed.

Lemma translate_cmd_deterministic p fd c i1 i2 :
  (forall f i, deterministic (match assoc fd f with Some f => f i | _ => ret tt end)) ->
  deterministic (translate_cmd p fd c i1 i2).2.
Proof.
  revert i1 i2.
  induction c; intros.
  - constructor.
  - simpl.
    pose proof translate_instr_deterministic p fd a i1 i2 X.
    destruct translate_instr.
    specialize (IHc i1 p0 X).
    destruct translate_cmd.
    simpl in *.
    eapply deterministic_seq; auto.
Qed.

Lemma translate_funs_deterministic P fn :
  forall f i, deterministic (match assoc (translate_funs P fn).1 f with Some f => f i | _ => ret tt end).
Proof.
  induction fn; intros.
  - constructor.
  - simpl. destruct a. simpl.
    destruct (f == f0).
    + eapply translate_cmd_deterministic.
      assumption.
    + eapply IHfn.
Qed.

Lemma get_translated_fun_deterministic P fn i vs :
  deterministic (get_translated_fun P fn i vs).
Proof.
  (* destruct P. *)
  unfold get_translated_fun.
  unfold translate_prog'. simpl.
  induction p_funcs.
  - simpl. constructor.
  - simpl. destruct a. simpl.
    destruct (fn == f).
    + eapply translate_call_body_deterministic.
      eapply translate_cmd_deterministic.
      eapply translate_funs_deterministic.
    + assumption.
Qed.

End Translation.
