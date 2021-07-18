(** Invariants on state

  These can be very useful when proving program equivalences.
*)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph chUniverse pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_lookup pkg_advantage.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, who knows why. *)
From Crypt Require Import FreeProbProg.

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

Definition precond := heap * heap → Prop.
Definition postcond A B := (A * heap) → (B * heap) → Prop.

Definition INV (L : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, l \in L → get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, l \in L → I (set_heap s1 l v, set_heap s2 l v)).

Definition INV' (L1 L2 : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, l \notin L1 → l \notin L2 →
      get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, l \notin L1 → l \notin L2 →
      I (set_heap s1 l v, set_heap s2 l v)).

Lemma INV'_to_INV (L L1 L2 : {fset Location})
  (I : heap_choiceType * heap_choiceType → Prop)
  (HINV' : INV' L1 L2 I)
  (Hdisjoint1 : fdisjoint L L1) (Hdisjoint2 : fdisjoint L L2) :
  INV L I.
Proof.
  unfold INV.
  intros s1 s2. split.
  - intros hi l hin.
    apply HINV'.
    + assumption.
    + move: Hdisjoint1. move /fdisjointP => Hdisjoint1.
      apply Hdisjoint1. assumption.
    + move: Hdisjoint2. move /fdisjointP => Hdisjoint2.
      apply Hdisjoint2. assumption.
  - intros hi l v hin.
    apply HINV'.
    + assumption.
    + move: Hdisjoint1. move /fdisjointP => Hdisjoint1.
      apply Hdisjoint1. assumption.
    + move: Hdisjoint2. move /fdisjointP => Hdisjoint2.
      apply Hdisjoint2. assumption.
Qed.

Class Invariant L₀ L₁ inv := {
  inv_INV' : INV' L₀ L₁ inv ;
  inv_empty : inv (empty_heap, empty_heap)
}.

Create HintDb ssprove_invariant.

#[export] Hint Extern 100 =>
  shelve
  : ssprove_invariant.

Ltac ssprove_invariant :=
  (unshelve typeclasses eauto with ssprove_invariant) ; shelve_unifiable.

Lemma Invariant_eq :
  ∀ L₀ L₁,
    Invariant L₀ L₁ (λ '(s₀, s₁), s₀ = s₁).
Proof.
  split.
  - intros s₀ s₁. split.
    + intro e. rewrite e. auto.
    + intro e. rewrite e. auto.
  - reflexivity.
Qed.

#[export] Hint Extern 10 (Invariant _ _ (λ '(s₀, s₁), s₀ = s₁)) =>
  eapply Invariant_eq
  : typeclass_instances ssprove_invariant.

Definition heap_ignore (L : {fset Location}) : precond :=
  λ '(h₀, h₁),
    ∀ (ℓ : Location), ℓ \notin L → get_heap h₀ ℓ = get_heap h₁ ℓ.

Arguments heap_ignore : simpl never.

Lemma heap_ignore_empty :
  ∀ L,
    heap_ignore L (empty_heap, empty_heap).
Proof.
  intros L ℓ hℓ. reflexivity.
Qed.

Lemma INV'_heap_ignore :
  ∀ L L₀ L₁,
    fsubset L (L₀ :|: L₁) →
    INV' L₀ L₁ (heap_ignore L).
Proof.
  intros L L₀ L₁ hs h₀ h₁. split.
  - intros hh ℓ n₀ n₁.
    eapply hh.
    apply /negP. intro h.
    eapply injectSubset in h. 2: eauto.
    rewrite in_fsetU in h. move: h => /orP [h | h].
    + rewrite h in n₀. discriminate.
    + rewrite h in n₁. discriminate.
  - intros h ℓ v n₀ n₁ ℓ' n.
    destruct (ℓ' != ℓ) eqn:e.
    + rewrite get_set_heap_neq. 2: auto.
      rewrite get_set_heap_neq. 2: auto.
      apply h. auto.
    + move: e => /eqP e. subst.
      rewrite !get_set_heap_eq. reflexivity.
Qed.

Lemma Invariant_heap_ignore :
  ∀ L L₀ L₁,
    fsubset L (L₀ :|: L₁) →
    Invariant L₀ L₁ (heap_ignore L).
Proof.
  intros L L₀ L₁ h. split.
  - apply INV'_heap_ignore. auto.
  - apply heap_ignore_empty.
Qed.

#[export] Hint Extern 10 (Invariant _ _ (heap_ignore _)) =>
  eapply Invariant_heap_ignore
  : (* typeclass_instances *) ssprove_invariant.

(* Not-really-symmetric (in use) conjunction of invariants *)
Definition inv_conj (inv inv' : precond) :=
  λ s, inv s ∧ inv' s.

Notation "I ⋊ J" :=
  (inv_conj I J) (at level 19, left associativity) : package_scope.

Arguments inv_conj : simpl never.

Class SemiInvariant (L₀ L₁ : {fset Location}) (sinv : precond) := {
  sinv_set :
    ∀ s₀ s₁ ℓ v,
      ℓ \notin L₀ →
      ℓ \notin L₁ →
      sinv (s₀, s₁) →
      sinv (set_heap s₀ ℓ v, set_heap s₁ ℓ v) ;
  sinv_empty : sinv (empty_heap, empty_heap)
}.

Lemma Invariant_inv_conj :
  ∀ L₀ L₁ inv sinv,
    Invariant L₀ L₁ inv →
    SemiInvariant L₀ L₁ sinv →
    Invariant L₀ L₁ (inv ⋊ sinv).
Proof.
  intros L₀ L₁ inv sinv [his hie] [hss hse]. split.
  - intros s₀ s₁. specialize (his s₀ s₁). destruct his. split.
    + intros []. eauto.
    + intros [] ℓ v h₀ h₁. split. all: eauto.
  - split. all: eauto.
Qed.

#[export] Hint Extern 10 (Invariant _ _ (_ ⋊ _)) =>
  eapply Invariant_inv_conj
  : typeclass_instances ssprove_invariant.

Definition couple_lhs ℓ ℓ' (R : _ → _ → Prop) : precond :=
  λ '(s₀, s₁), R (get_heap s₀ ℓ) (get_heap s₀ ℓ').

Lemma SemiInvariant_couple_lhs :
  ∀ L₀ L₁ ℓ ℓ' (R : _ → _ → Prop),
    ℓ \in L₀ :|: L₁ →
    ℓ' \in L₀ :|: L₁ →
    R (get_heap empty_heap ℓ) (get_heap empty_heap ℓ') →
    SemiInvariant L₀ L₁ (couple_lhs ℓ ℓ' R).
Proof.
  intros L₀ L₁ ℓ ℓ' h hℓ hℓ' he. split.
  - intros s₀ s₁ l v hl₀ hl₁ ?.
    assert (hl : l \notin L₀ :|: L₁).
    { rewrite in_fsetU. rewrite (negbTE hl₀) (negbTE hl₁). reflexivity. }
    unfold couple_lhs.
    rewrite !get_set_heap_neq.
    + auto.
    + apply /negP => /eqP e. subst. rewrite hℓ' in hl. discriminate.
    + apply /negP => /eqP e. subst. rewrite hℓ in hl. discriminate.
  - simpl. auto.
Qed.

Arguments couple_lhs : simpl never.

#[export] Hint Extern 10 (SemiInvariant _ _ (couple_lhs _ _ _)) =>
  eapply SemiInvariant_couple_lhs
  : (* typeclass_instances *) ssprove_invariant.

Definition couple_rhs ℓ ℓ' (R : _ → _ → Prop) : precond :=
  λ '(s₀, s₁), R (get_heap s₁ ℓ) (get_heap s₁ ℓ').

Lemma SemiInvariant_couple_rhs :
  ∀ L₀ L₁ ℓ ℓ' (R : _ → _ → Prop),
    ℓ \in L₀ :|: L₁ →
    ℓ' \in L₀ :|: L₁ →
    R (get_heap empty_heap ℓ) (get_heap empty_heap ℓ') →
    SemiInvariant L₀ L₁ (couple_rhs ℓ ℓ' R).
Proof.
  intros L₀ L₁ ℓ ℓ' h hℓ hℓ' he. split.
  - intros s₀ s₁ l v hl₀ hl₁ ?.
    assert (hl : l \notin L₀ :|: L₁).
    { rewrite in_fsetU. rewrite (negbTE hl₀) (negbTE hl₁). reflexivity. }
    unfold couple_rhs.
    rewrite !get_set_heap_neq.
    + auto.
    + apply /negP => /eqP e. subst. rewrite hℓ' in hl. discriminate.
    + apply /negP => /eqP e. subst. rewrite hℓ in hl. discriminate.
  - simpl. auto.
Qed.

Arguments couple_rhs : simpl never.

#[export] Hint Extern 10 (SemiInvariant _ _ (couple_rhs _ _ _)) =>
  eapply SemiInvariant_couple_rhs
  : (* typeclass_instances *) ssprove_invariant.

(* TODO triple_lhs, or even better, something more generic *)
Definition triple_rhs ℓ₁ ℓ₂ ℓ₃ (R : _ → _ → _ → Prop) : precond :=
  λ '(s₀, s₁), R (get_heap s₁ ℓ₁) (get_heap s₁ ℓ₂) (get_heap s₁ ℓ₃).

Lemma SemiInvariant_triple_rhs :
  ∀ L₀ L₁ ℓ₁ ℓ₂ ℓ₃ (R : _ → _ → _ → Prop),
    ℓ₁ \in L₀ :|: L₁ →
    ℓ₂ \in L₀ :|: L₁ →
    ℓ₃ \in L₀ :|: L₁ →
    R (get_heap empty_heap ℓ₁) (get_heap empty_heap ℓ₂) (get_heap empty_heap ℓ₃) →
    SemiInvariant L₀ L₁ (triple_rhs ℓ₁ ℓ₂ ℓ₃ R).
Proof.
  intros L₀ L₁ ℓ₁ ℓ₂ ℓ₃ R h₁ h₂ h₃ he. split.
  - intros s₀ s₁ ℓ v hℓ₀ hℓ₁ ?.
    assert (hℓ : ℓ \notin L₀ :|: L₁).
    { rewrite in_fsetU. rewrite (negbTE hℓ₀) (negbTE hℓ₁). reflexivity. }
    unfold triple_rhs.
    rewrite !get_set_heap_neq.
    + auto.
    + apply /negP => /eqP e. subst. rewrite h₃ in hℓ. discriminate.
    + apply /negP => /eqP e. subst. rewrite h₂ in hℓ. discriminate.
    + apply /negP => /eqP e. subst. rewrite h₁ in hℓ. discriminate.
  - simpl. auto.
Qed.

Arguments triple_rhs : simpl never.

#[export] Hint Extern 10 (SemiInvariant _ _ (triple_rhs _ _ _ _)) =>
  eapply SemiInvariant_triple_rhs
  : (* typeclass_instances *) ssprove_invariant.

Inductive side := lhs | rhs.

Definition choose_heap s₀ s₁ (s : side) : heap :=
  match s with
  | lhs => s₀
  | rhs => s₁
  end.

Lemma choose_heap_same :
  ∀ s si,
    choose_heap s s si = s.
Proof.
  intros s si.
  destruct si.
  all: reflexivity.
Qed.

Fixpoint locRel (l : list (Location * side)) :=
  match l with
  | (ℓ, _) :: l => ℓ → locRel l
  | [::] => Prop
  end.

Fixpoint heapLocRel (s₀ s₁ : heap) l (R : locRel l) : Prop :=
  match l return locRel l → Prop with
  | (ℓ, s) :: l =>
    λ R, heapLocRel s₀ s₁ l (R (get_heap (choose_heap s₀ s₁ s) ℓ))
  | [::] => λ R, R
  end R.

Definition loc_rel (l : list (Location * side)) (R : locRel l) : precond :=
  λ '(s₀, s₁), heapLocRel s₀ s₁ l R.

Lemma SemiInvariant_loc_rel :
  ∀ L₀ L₁ l (R : locRel l),
    List.forallb (λ '(ℓ,_), ℓ \in L₀ :|: L₁) l →
    heapLocRel empty_heap empty_heap l R →
    SemiInvariant L₀ L₁ (loc_rel l R).
Proof.
  intros L₀ L₁ l R h he. split.
  - intros s₀ s₁ ℓ v hℓ₀ hℓ₁ hh.
    assert (hℓ : ℓ \notin L₀ :|: L₁).
    { rewrite in_fsetU. rewrite (negbTE hℓ₀) (negbTE hℓ₁). reflexivity. }
    unfold loc_rel.
    induction l as [| [ℓ' si] l ih] in s₀, s₁, R, hh, h(* , he *) |- *.
    + assumption.
    + simpl. apply ih.
      * simpl in h. move: h => /andP [_ h]. assumption.
      * simpl in h. move: h => /andP [h _].
        destruct si. all: simpl.
        all: rewrite !get_set_heap_neq.
        1,3: assumption.
        -- apply /negP => /eqP e. subst. rewrite h in hℓ. discriminate.
        -- apply /negP => /eqP e. subst. rewrite h in hℓ. discriminate.
  - simpl. assumption.
Qed.

Arguments loc_rel : simpl never.

#[export] Hint Extern 10 (SemiInvariant _ _ (loc_rel _ _)) =>
  eapply SemiInvariant_loc_rel
  : (* typeclass_instances *) ssprove_invariant.

Definition get_pre_cond ℓ (pre : precond) :=
  ∀ s₀ s₁, pre (s₀, s₁) → get_heap s₀ ℓ = get_heap s₁ ℓ.

Lemma get_pre_cond_heap_ignore :
  ∀ (ℓ : Location) (L : {fset Location}),
    ℓ \notin L →
    get_pre_cond ℓ (heap_ignore L).
Proof.
  intros ℓ L hℓ s₀ s₁ h. apply h. auto.
Qed.

#[export] Hint Extern 10 (get_pre_cond _ (heap_ignore _)) =>
  apply get_pre_cond_heap_ignore
  : ssprove_invariant.

Lemma get_pre_cond_conj :
  ∀ ℓ (pre spre : precond),
    get_pre_cond ℓ pre →
    get_pre_cond ℓ (pre ⋊ spre).
Proof.
  intros ℓ pre spre h s₀ s₁ []. apply h. auto.
Qed.

#[export] Hint Extern 10 (get_pre_cond _ (_ ⋊ _)) =>
  apply get_pre_cond_conj
  : ssprove_invariant.

Definition put_pre_cond ℓ v (pre : precond) :=
  ∀ s₀ s₁, pre (s₀, s₁) → pre (set_heap s₀ ℓ v, set_heap s₁ ℓ v).

Lemma put_pre_cond_heap_ignore :
  ∀ ℓ v L,
    put_pre_cond ℓ v (heap_ignore L).
Proof.
  intros ℓ v L s₀ s₁ h ℓ' hn.
  destruct (ℓ' != ℓ) eqn:e.
  - rewrite get_set_heap_neq. 2: auto.
    rewrite get_set_heap_neq. 2: auto.
    apply h. auto.
  - move: e => /eqP e. subst.
    rewrite !get_set_heap_eq. reflexivity.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (heap_ignore _)) =>
  apply put_pre_cond_heap_ignore
  : ssprove_invariant.

Lemma put_pre_cond_conj :
  ∀ ℓ v pre spre,
    put_pre_cond ℓ v pre →
    put_pre_cond ℓ v spre →
    put_pre_cond ℓ v (pre ⋊ spre).
Proof.
  intros ℓ v pre spre h hs.
  intros s₀ s₁ []. split. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (_ ⋊ _)) =>
  apply put_pre_cond_conj
  : ssprove_invariant.

Lemma put_pre_cond_couple_lhs :
  ∀ ℓ v ℓ₀ ℓ₁ h,
    ℓ₀ != ℓ →
    ℓ₁ != ℓ →
    put_pre_cond ℓ v (couple_lhs ℓ₀ ℓ₁ h).
Proof.
  intros ℓ v ℓ₀ ℓ₁ h n₀ n₁ s₀ s₁ hc.
  unfold couple_lhs in *.
  rewrite !get_set_heap_neq. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (couple_lhs _ _ _)) =>
  apply put_pre_cond_couple_lhs
  : ssprove_invariant.

Lemma put_pre_cond_couple_rhs :
  ∀ ℓ v ℓ₀ ℓ₁ h,
    ℓ₀ != ℓ →
    ℓ₁ != ℓ →
    put_pre_cond ℓ v (couple_rhs ℓ₀ ℓ₁ h).
Proof.
  intros ℓ v ℓ₀ ℓ₁ h n₀ n₁ s₀ s₁ hc.
  unfold couple_rhs in *.
  rewrite !get_set_heap_neq. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (couple_rhs _ _ _)) =>
  apply put_pre_cond_couple_rhs
  : ssprove_invariant.

Lemma put_pre_cond_triple_rhs :
  ∀ ℓ v ℓ₁ ℓ₂ ℓ₃ h,
    ℓ₁ != ℓ →
    ℓ₂ != ℓ →
    ℓ₃ != ℓ →
    put_pre_cond ℓ v (triple_rhs ℓ₁ ℓ₂ ℓ₃ h).
Proof.
  intros ℓ v ℓ₁ ℓ₂ ℓ₃ h n₁ n₂ n₃ s₀ s₁ hc.
  unfold triple_rhs in *.
  rewrite !get_set_heap_neq. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (triple_rhs _ _ _ _)) =>
  apply put_pre_cond_triple_rhs
  : ssprove_invariant.

(** Predicates on invariants

  The idea is to use them as side-conditions for rules.
*)

Class Syncs ℓ pre :=
  is_tracking : ∀ s₀ s₁, pre (s₀, s₁) → get_heap s₀ ℓ = get_heap s₁ ℓ.

Class Couples_lhs ℓ ℓ' R pre :=
  is_coupling_lhs : ∀ s, pre s → couple_lhs ℓ ℓ' R s.

Class Couples_rhs ℓ ℓ' R pre :=
  is_coupling_rhs : ∀ s, pre s → couple_rhs ℓ ℓ' R s.

Class Triple_rhs ℓ₁ ℓ₂ ℓ₃ R pre :=
  is_triple_rhs : ∀ s, pre s → triple_rhs ℓ₁ ℓ₂ ℓ₃ R s.

Lemma Syncs_eq :
  ∀ ℓ, Syncs ℓ (λ '(s₀, s₁), s₀ = s₁).
Proof.
  intros ℓ s₀ s₁ e. subst. reflexivity.
Qed.

#[export] Hint Extern 10 (Syncs _ (λ '(s₀, s₁), s₀ = s₁)) =>
  apply Syncs_eq
  : typeclass_instances ssprove_invariant.

Lemma Syncs_heap_ignore :
  ∀ ℓ L,
    ℓ \notin L →
    Syncs ℓ (heap_ignore L).
Proof.
  intros ℓ L hn s₀ s₁ h.
  apply h. auto.
Qed.

#[export] Hint Extern 10 (Syncs _ (heap_ignore _)) =>
  apply Syncs_heap_ignore
  : typeclass_instances ssprove_invariant.

Lemma Syncs_conj :
  ∀ ℓ (pre spre : precond),
    Syncs ℓ pre →
    Syncs ℓ (pre ⋊ spre).
Proof.
  intros ℓ pre spre hpre s₀ s₁ [].
  apply hpre. auto.
Qed.

#[export] Hint Extern 10 (Syncs _ (_ ⋊ _)) =>
  apply Syncs_conj
  : typeclass_instances ssprove_invariant.

Lemma Couples_couple_lhs :
  ∀ ℓ ℓ' R,
    Couples_lhs ℓ ℓ' R (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R s h. auto.
Qed.

#[export] Hint Extern 10 (Couples_lhs _ _ _ (couple_lhs _ _ _)) =>
  eapply Couples_couple_lhs
  : typeclass_instances ssprove_invariant.

Lemma Couples_couple_rhs :
  ∀ ℓ ℓ' R,
    Couples_rhs ℓ ℓ' R (couple_rhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R s h. auto.
Qed.

#[export] Hint Extern 10 (Couples_rhs _ _ _ (couple_rhs _ _ _)) =>
  eapply Couples_couple_rhs
  : typeclass_instances ssprove_invariant.

Lemma Triple_triple_rhs :
  ∀ ℓ₁ ℓ₂ ℓ₃ R,
    Triple_rhs ℓ₁ ℓ₂ ℓ₃ R (triple_rhs ℓ₁ ℓ₂ ℓ₃ R).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R s h. auto.
Qed.

#[export] Hint Extern 10 (Triple_rhs _ _ _ _ (triple_rhs _ _ _ _)) =>
  eapply Triple_triple_rhs
  : typeclass_instances ssprove_invariant.

Lemma Couples_lhs_conj_right :
  ∀ ℓ ℓ' R (pre spre : precond),
    Couples_lhs ℓ ℓ' R spre →
    Couples_lhs ℓ ℓ' R (pre ⋊ spre).
Proof.
  intros ℓ ℓ' R pre spre h s [].
  apply h. auto.
Qed.

Lemma Couples_lhs_conj_left :
  ∀ ℓ ℓ' R (pre spre : precond),
    Couples_lhs ℓ ℓ' R pre →
    Couples_lhs ℓ ℓ' R (pre ⋊ spre).
Proof.
  intros ℓ ℓ' R pre spre h s [].
  apply h. auto.
Qed.

#[export] Hint Extern 9 (Couples_lhs _ _ _ (_ ⋊ _)) =>
  eapply Couples_lhs_conj_right
  : typeclass_instances ssprove_invariant.

#[export] Hint Extern 11 (Couples_lhs _ _ _ (_ ⋊ _)) =>
  eapply Couples_lhs_conj_left
  : typeclass_instances ssprove_invariant.

Lemma Couples_rhs_conj_right :
  ∀ ℓ ℓ' R (pre spre : precond),
    Couples_rhs ℓ ℓ' R spre →
    Couples_rhs ℓ ℓ' R (pre ⋊ spre).
Proof.
  intros ℓ ℓ' R pre spre h s [].
  apply h. auto.
Qed.

Lemma Couples_rhs_conj_left :
  ∀ ℓ ℓ' R (pre spre : precond),
    Couples_rhs ℓ ℓ' R pre →
    Couples_rhs ℓ ℓ' R (pre ⋊ spre).
Proof.
  intros ℓ ℓ' R pre spre h s [].
  apply h. auto.
Qed.

#[export] Hint Extern 9 (Couples_rhs _ _ _ (_ ⋊ _)) =>
  eapply Couples_rhs_conj_right
  : typeclass_instances ssprove_invariant.

#[export] Hint Extern 11 (Couples_rhs _ _ _ (_ ⋊ _)) =>
  eapply Couples_rhs_conj_left
  : typeclass_instances ssprove_invariant.

Lemma Triple_rhs_conj_right :
  ∀ ℓ₁ ℓ₂ ℓ₃ R (pre spre : precond),
    Triple_rhs ℓ₁ ℓ₂ ℓ₃ R spre →
    Triple_rhs ℓ₁ ℓ₂ ℓ₃ R (pre ⋊ spre).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R pre spre h s [].
  apply h. auto.
Qed.

Lemma Triple_rhs_conj_left :
  ∀ ℓ₁ ℓ₂ ℓ₃ R (pre spre : precond),
    Triple_rhs ℓ₁ ℓ₂ ℓ₃ R pre →
    Triple_rhs ℓ₁ ℓ₂ ℓ₃ R (pre ⋊ spre).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R pre spre h s [].
  apply h. auto.
Qed.

#[export] Hint Extern 9 (Triple_rhs _ _ _ _ (_ ⋊ _)) =>
  eapply Triple_rhs_conj_right
  : typeclass_instances ssprove_invariant.

#[export] Hint Extern 11 (Triple_rhs _ _ _ _ (_ ⋊ _)) =>
  eapply Triple_rhs_conj_left
  : typeclass_instances ssprove_invariant.

Definition rem_lhs ℓ v : precond :=
  λ '(s₀, s₁), get_heap s₀ ℓ = v.

Definition rem_rhs ℓ v : precond :=
  λ '(s₀, s₁), get_heap s₁ ℓ = v.

Class Remembers_lhs ℓ v pre :=
  is_remembering_lhs : ∀ s₀ s₁, pre (s₀, s₁) → rem_lhs ℓ v (s₀, s₁).

Class Remembers_rhs ℓ v pre :=
  is_remembering_rhs : ∀ s₀ s₁, pre (s₀, s₁) → rem_rhs ℓ v (s₀, s₁).

Lemma Remembers_lhs_rem_lhs :
  ∀ ℓ v,
    Remembers_lhs ℓ v (rem_lhs ℓ v).
Proof.
  intros ℓ v. intros s₀ s₁ h. auto.
Qed.

#[export] Hint Extern 10 (Remembers_lhs _ _ (rem_lhs _ _)) =>
  eapply Remembers_lhs_rem_lhs
  : typeclass_instances ssprove_invariant.

Lemma Remembers_rhs_rem_rhs :
  ∀ ℓ v,
    Remembers_rhs ℓ v (rem_rhs ℓ v).
Proof.
  intros ℓ v. intros s₀ s₁ h. auto.
Qed.

#[export] Hint Extern 10 (Remembers_rhs _ _ (rem_rhs _ _)) =>
  eapply Remembers_rhs_rem_rhs
  : typeclass_instances ssprove_invariant.

Lemma Remembers_lhs_conj_right :
  ∀ ℓ v (pre spre : precond),
    Remembers_lhs ℓ v spre →
    Remembers_lhs ℓ v (pre ⋊ spre).
Proof.
  intros ℓ v pre spre h.
  intros s₀ s₁ []. apply h. auto.
Qed.

Lemma Remembers_lhs_conj_left :
  ∀ ℓ v (pre spre : precond),
    Remembers_lhs ℓ v pre →
    Remembers_lhs ℓ v (pre ⋊ spre).
Proof.
  intros ℓ v pre spre h.
  intros s₀ s₁ []. apply h. auto.
Qed.

#[export] Hint Extern 9 (Remembers_lhs _ _ (_ ⋊ _)) =>
  eapply Remembers_lhs_conj_right
  : typeclass_instances ssprove_invariant.

#[export] Hint Extern 11 (Remembers_lhs _ _ (_ ⋊ _)) =>
  eapply Remembers_lhs_conj_left
  : typeclass_instances ssprove_invariant.

Lemma Remembers_rhs_conj_right :
  ∀ ℓ v (pre spre : precond),
    Remembers_rhs ℓ v spre →
    Remembers_rhs ℓ v (pre ⋊ spre).
Proof.
  intros ℓ v pre spre h.
  intros s₀ s₁ []. apply h. auto.
Qed.

Lemma Remembers_rhs_conj_left :
  ∀ ℓ v (pre spre : precond),
    Remembers_rhs ℓ v pre →
    Remembers_rhs ℓ v (pre ⋊ spre).
Proof.
  intros ℓ v pre spre h.
  intros s₀ s₁ []. apply h. auto.
Qed.

#[export] Hint Extern 9 (Remembers_rhs _ _ (_ ⋊ _)) =>
  eapply Remembers_rhs_conj_right
  : typeclass_instances ssprove_invariant.

#[export] Hint Extern 11 (Remembers_rhs _ _ (_ ⋊ _)) =>
  eapply Remembers_rhs_conj_left
  : typeclass_instances ssprove_invariant.

Lemma Remembers_lhs_from_tracked_rhs :
  ∀ ℓ v pre,
    Remembers_rhs ℓ v pre →
    Syncs ℓ pre →
    Remembers_lhs ℓ v pre.
Proof.
  intros ℓ v pre hr ht.
  intros s₀ s₁ hpre. simpl.
  specialize (hr _ _ hpre). specialize (ht _ _ hpre).
  rewrite ht. apply hr.
Qed.

Lemma Remembers_rhs_from_tracked_lhs :
  ∀ ℓ v pre,
    Remembers_lhs ℓ v pre →
    Syncs ℓ pre →
    Remembers_rhs ℓ v pre.
Proof.
  intros ℓ v pre hr ht.
  intros s₀ s₁ hpre. simpl.
  specialize (hr _ _ hpre). specialize (ht _ _ hpre).
  rewrite -ht. apply hr.
Qed.

Lemma put_pre_cond_rem_lhs :
  ∀ ℓ v ℓ' v',
    ℓ' != ℓ →
    put_pre_cond ℓ v (rem_lhs ℓ' v').
Proof.
  intros ℓ v ℓ' v' hn s₀ s₁ hc.
  unfold rem_lhs in *.
  rewrite get_set_heap_neq. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (rem_lhs _ _)) =>
  apply put_pre_cond_rem_lhs
  : ssprove_invariant.

Lemma put_pre_cond_rem_rhs :
  ∀ ℓ v ℓ' v',
    ℓ' != ℓ →
    put_pre_cond ℓ v (rem_rhs ℓ' v').
Proof.
  intros ℓ v ℓ' v' hn s₀ s₁ hc.
  unfold rem_rhs in *.
  rewrite get_set_heap_neq. all: auto.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (rem_rhs _ _)) =>
  apply put_pre_cond_rem_rhs
  : ssprove_invariant.

(** Dually to rem_lhs/rem_rhs we create "invariants" to represent a deviation
    of invariant, or a deficit which will need to be paid later to restore
    the proper invariant.
*)

Definition set_lhs ℓ v (pre : precond) : precond :=
  λ '(s₀, s₁),
    ∃ s₀', pre (s₀', s₁) ∧ s₀ = set_heap s₀' ℓ v.

Arguments set_lhs : simpl never.

Definition set_rhs ℓ v (pre : precond) : precond :=
  λ '(s₀, s₁),
    ∃ s₁', pre (s₀, s₁') ∧ s₁ = set_heap s₁' ℓ v.

Arguments set_rhs : simpl never.

Lemma restore_set_lhs :
  ∀ ℓ v pre s₀ s₁,
    set_lhs ℓ v pre (s₀, s₁) →
    (∀ s₀', pre (s₀', s₁) → pre (set_heap s₀' ℓ v, s₁)) →
    pre (s₀, s₁).
Proof.
  intros ℓ v pre s₀ s₁ h hpre.
  destruct h as [? [? ?]]. subst.
  eapply hpre. auto.
Qed.

Lemma restore_set_rhs :
  ∀ ℓ v pre s₀ s₁,
    set_rhs ℓ v pre (s₀, s₁) →
    (∀ s₁', pre (s₀, s₁') → pre (s₀, set_heap s₁' ℓ v)) →
    pre (s₀, s₁).
Proof.
  intros ℓ v pre s₀ s₁ h hpre.
  destruct h as [? [? ?]]. subst.
  eapply hpre. auto.
Qed.

(** Representation of affectations in a heap

  They can be interpreted as updates or as read data depending on the context.
*)

Inductive heap_val :=
| hpv_l (ℓ : Location) (v : ℓ)
| hpv_r (ℓ : Location) (v : ℓ).

Definition loc_val_pair (ℓ : Location) (v : ℓ) : ∑ ℓ : Location, ℓ :=
  (ℓ ; v).

Definition heap_val_eq : rel heap_val :=
  λ u v,
    match u, v with
    | hpv_l ℓ v, hpv_l ℓ' v' => loc_val_pair ℓ v == (ℓ' ; v')
    | hpv_r ℓ v, hpv_r ℓ' v' => loc_val_pair ℓ v == (ℓ' ; v')
    | _, _ => false
    end.

Lemma heap_val_eqP : Equality.axiom heap_val_eq.
Proof.
  intros u v.
  destruct u, v. all: simpl. 2,3: constructor. 2,3: discriminate.
  all: unfold loc_val_pair.
  all: destruct eq_op eqn:e.
  all: move: e => /eqP e. all: noconf e.
  all: constructor.
  all: try reflexivity.
  all: intro h. all: inversion h. all: contradiction.
Qed.

Canonical heap_val_eqMixin := EqMixin heap_val_eqP.
Canonical heap_val_eqType :=
  Eval hnf in EqType heap_val heap_val_eqMixin.

Derive NoConfusion for heap_val.

Fixpoint update_pre (l : list heap_val) (pre : precond) :=
  match l with
  | hpv_l ℓ v :: l => set_lhs ℓ v (update_pre l pre)
  | hpv_r ℓ v :: l => set_rhs ℓ v (update_pre l pre)
  | [::] => pre
  end.

Fixpoint update_heaps (l : list heap_val) s₀ s₁ :=
  match l with
  | hpv_l ℓ v :: l =>
    let '(s₀, s₁) := update_heaps l s₀ s₁ in
    (set_heap s₀ ℓ v, s₁)
  | hpv_r ℓ v :: l =>
    let '(s₀, s₁) := update_heaps l s₀ s₁ in
    (s₀, set_heap s₁ ℓ v)
  | [::] => (s₀, s₁)
  end.

Lemma update_pre_spec :
  ∀ l pre s₀ s₁,
    update_pre l pre (s₀, s₁) →
    ∃ s₀' s₁', pre (s₀', s₁') ∧ (s₀, s₁) = update_heaps l s₀' s₁'.
Proof.
  intros l pre s₀ s₁ h.
  induction l as [| [] l ih] in pre, s₀, s₁, h |- *.
  - simpl in h. simpl.
    eexists _, _. intuition eauto.
  - simpl in h. simpl.
    destruct h as [s [h ?]]. subst.
    eapply ih in h. destruct h as [? [? [? e]]].
    eexists _, _. split. 1: eauto.
    rewrite -e. reflexivity.
  - simpl in h. simpl.
    destruct h as [s [h ?]]. subst.
    eapply ih in h. destruct h as [? [? [? e]]].
    eexists _, _. split. 1: eauto.
    rewrite -e. reflexivity.
Qed.

Definition is_hpv_l u :=
  match u with
  | hpv_l _ _ => true
  | _ => false
  end.

Definition is_hpv_r u :=
  match u with
  | hpv_r _ _ => true
  | _ => false
  end.

Lemma update_heaps_filter_l :
  ∀ l s₀ s₁,
    (update_heaps (filter is_hpv_l l) s₀ s₁).1 =
    (update_heaps l s₀ s₁).1.
Proof.
  intros l s₀ s₁.
  induction l as [| [] l ih] in s₀, s₁ |- *.
  - reflexivity.
  - simpl. destruct update_heaps eqn:e1.
    destruct (update_heaps l s₀ s₁) eqn:e2.
    simpl. specialize (ih s₀ s₁).
    rewrite e2 e1 in ih. simpl in ih. subst. reflexivity.
  - simpl. destruct update_heaps eqn:e1.
    destruct (update_heaps l s₀ s₁) eqn:e2.
    simpl. specialize (ih s₀ s₁).
    rewrite e2 e1 in ih. simpl in ih. auto.
Qed.

Lemma update_heaps_filter_r :
  ∀ l s₀ s₁,
    (update_heaps (filter is_hpv_r l) s₀ s₁).2 =
    (update_heaps l s₀ s₁).2.
Proof.
  intros l s₀ s₁.
  induction l as [| [] l ih] in s₀, s₁ |- *.
  - reflexivity.
  - simpl. destruct update_heaps eqn:e1.
    destruct (update_heaps l s₀ s₁) eqn:e2.
    simpl. specialize (ih s₀ s₁).
    rewrite e2 e1 in ih. simpl in ih. auto.
  - simpl. destruct update_heaps eqn:e1.
    destruct (update_heaps l s₀ s₁) eqn:e2.
    simpl. specialize (ih s₀ s₁).
    rewrite e2 e1 in ih. simpl in ih. subst. reflexivity.
Qed.

Fixpoint remember_pre (l : list heap_val) (pre : precond) :=
  match l with
  | hpv_l ℓ v :: l => remember_pre l pre ⋊ rem_lhs ℓ v
  | hpv_r ℓ v :: l => remember_pre l pre ⋊ rem_rhs ℓ v
  | [::] => pre
  end.

Lemma remember_pre_pre :
  ∀ m pre s₀ s₁,
    remember_pre m pre (s₀, s₁) →
    pre (s₀, s₁).
Proof.
  intros m pre s₀ s₁ h.
  induction m as [| [] m ih] in pre, s₀, s₁, h |- *.
  - auto.
  - simpl in h. destruct h as [h _].
    eapply ih. auto.
  - simpl in h. destruct h as [h _].
    eapply ih. auto.
Qed.

Lemma remember_pre_conj :
  ∀ m pre spre s₀ s₁,
    remember_pre m (pre ⋊ spre) (s₀, s₁) →
    remember_pre m pre (s₀, s₁) ∧
    remember_pre m spre (s₀, s₁).
Proof.
  intros m pre spre s₀ s₁ h.
  induction m as [| [] m ih] in pre, spre, s₀, s₁, h |- *.
  - simpl. auto.
  - simpl in h. simpl. destruct h as [h hm].
    eapply ih in h. destruct h.
    split. all: split. all: auto.
  - simpl in h. simpl. destruct h as [h hm].
    eapply ih in h. destruct h.
    split. all: split. all: auto.
Qed.

Definition cast_loc_val {ℓ ℓ' : Location} (e : ℓ = ℓ') (v : ℓ) : ℓ'.
Proof.
  subst. auto.
Defined.

Lemma cast_loc_val_K :
  ∀ ℓ e v,
    @cast_loc_val ℓ ℓ e v = v.
Proof.
  intros ℓ e v.
  assert (e = erefl).
  { apply eq_irrelevance. }
  subst. reflexivity.
Qed.

Equations? lookup_hpv_l (ℓ : Location) (l : seq heap_val) : option ℓ :=
  lookup_hpv_l ℓ (hpv_l ℓ' v' :: l) with inspect (ℓ == ℓ') := {
  | @exist true e := Some (cast_loc_val _ v') ;
  | @exist false e := lookup_hpv_l ℓ l
  } ;
  lookup_hpv_l ℓ (hpv_r _ _ :: l) := lookup_hpv_l ℓ l ;
  lookup_hpv_l ℓ [::] := None.
Proof.
  symmetry in e.
  move: e => /eqP e. subst. reflexivity.
Qed.

Equations? lookup_hpv_r (ℓ : Location) (l : seq heap_val) : option ℓ :=
  lookup_hpv_r ℓ (hpv_r ℓ' v' :: l) with inspect (ℓ == ℓ') := {
  | @exist true e := Some (cast_loc_val _ v') ;
  | @exist false e := lookup_hpv_r ℓ l
  } ;
  lookup_hpv_r ℓ (hpv_l _ _ :: l) := lookup_hpv_r ℓ l ;
  lookup_hpv_r ℓ [::] := None.
Proof.
  symmetry in e.
  move: e => /eqP e. subst. reflexivity.
Qed.

Lemma lookup_hpv_l_eq :
  ∀ ℓ v l,
    lookup_hpv_l ℓ (hpv_l ℓ v :: l) = Some v.
Proof.
  intros ℓ v l.
  funelim (lookup_hpv_l ℓ (hpv_l ℓ v :: l)).
  - rewrite -Heqcall. rewrite cast_loc_val_K. reflexivity.
  - exfalso. pose proof e as e'. symmetry in e'. move: e' => /eqP e'.
    contradiction.
Qed.

Lemma lookup_hpv_l_neq :
  ∀ ℓ ℓ' v l,
    ℓ' != ℓ →
    lookup_hpv_l ℓ' (hpv_l ℓ v :: l) = lookup_hpv_l ℓ' l.
Proof.
  intros ℓ ℓ' v l hn.
  funelim (lookup_hpv_l ℓ' (hpv_l ℓ v :: l)).
  - exfalso. rewrite -e in hn. discriminate.
  - rewrite -Heqcall. reflexivity.
Qed.

Lemma lookup_hpv_r_eq :
  ∀ ℓ v l,
    lookup_hpv_r ℓ (hpv_r ℓ v :: l) = Some v.
Proof.
  intros ℓ v l.
  funelim (lookup_hpv_r ℓ (hpv_r ℓ v :: l)).
  - rewrite -Heqcall. rewrite cast_loc_val_K. reflexivity.
  - exfalso. pose proof e as e'. symmetry in e'. move: e' => /eqP e'.
    contradiction.
Qed.

Lemma lookup_hpv_r_neq :
  ∀ ℓ ℓ' v l,
    ℓ' != ℓ →
    lookup_hpv_r ℓ' (hpv_r ℓ v :: l) = lookup_hpv_r ℓ' l.
Proof.
  intros ℓ ℓ' v l hn.
  funelim (lookup_hpv_r ℓ' (hpv_r ℓ v :: l)).
  - exfalso. rewrite -e in hn. discriminate.
  - rewrite -Heqcall. reflexivity.
Qed.

Lemma lookup_hpv_l_spec :
  ∀ ℓ v l s₀ s₁ h₀ h₁,
    lookup_hpv_l ℓ l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₀ ℓ = v.
Proof.
  intros ℓ v l s₀ s₁ h₀ h₁ hl e.
  funelim (lookup_hpv_l ℓ l).
  - discriminate.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eauto.
  - rewrite -Heqcall in hl. noconf hl.
    simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    pose proof e as e'.
    symmetry in e'. move: e' => /eqP ?. subst.
    rewrite cast_loc_val_K.
    apply get_set_heap_eq.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    rewrite -Heqcall in hl. eauto.
Qed.

Lemma lookup_hpv_r_spec :
  ∀ ℓ v l s₀ s₁ h₀ h₁,
    lookup_hpv_r ℓ l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₁ ℓ = v.
Proof.
  intros ℓ v l s₀ s₁ h₀ h₁ hl e.
  funelim (lookup_hpv_r ℓ l).
  - discriminate.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eauto.
  - rewrite -Heqcall in hl. noconf hl.
    simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    pose proof e as e'.
    symmetry in e'. move: e' => /eqP ?. subst.
    rewrite cast_loc_val_K.
    apply get_set_heap_eq.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    rewrite -Heqcall in hl. eauto.
Qed.

Lemma lookup_hpv_l_None_spec :
  ∀ ℓ l s₀ s₁ h₀ h₁,
    lookup_hpv_l ℓ l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₀ ℓ = get_heap s₀ ℓ.
Proof.
  intros ℓ l s₀ s₁ h₀ h₁ hl e.
  funelim (lookup_hpv_l ℓ l).
  - simpl in e. noconf e. reflexivity.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eauto.
  - rewrite -Heqcall in hl. noconf hl.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    rewrite -Heqcall in hl. eauto.
Qed.

Lemma lookup_hpv_r_None_spec :
  ∀ ℓ l s₀ s₁ h₀ h₁,
    lookup_hpv_r ℓ l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₁ ℓ = get_heap s₁ ℓ.
Proof.
  intros ℓ l s₀ s₁ h₀ h₁ hl e.
  funelim (lookup_hpv_r ℓ l).
  - simpl in e. noconf e. reflexivity.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eauto.
  - rewrite -Heqcall in hl. noconf hl.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    rewrite -Heqcall in hl. eauto.
Qed.

(** Predicate of preservation of precond after updates, retaining memory *)

Definition preserve_update_mem l m (pre : precond) :=
  ∀ s₀ s₁, (remember_pre m pre) (s₀, s₁) → pre (update_heaps l s₀ s₁).

Notation preserve_update_pre l pre :=
  (preserve_update_mem l [::] pre).

Lemma preserve_update_pre_mem :
  ∀ l m pre,
    preserve_update_pre l pre →
    preserve_update_mem l m pre.
Proof.
  intros l m pre h.
  intros s₀ s₁ hi.
  eapply remember_pre_pre in hi. apply h. auto.
Qed.

Lemma restore_update_mem :
  ∀ l m pre s₀ s₁,
    update_pre l (remember_pre m pre) (s₀, s₁) →
    preserve_update_mem l m pre →
    pre (s₀, s₁).
Proof.
  intros l m pre s₀ s₁ hu hp.
  eapply update_pre_spec in hu. destruct hu as [s₀' [s₁' [hpre e]]].
  rewrite e. eapply hp. auto.
Qed.

Lemma restore_update_pre :
  ∀ l pre s₀ s₁,
    update_pre l pre (s₀, s₁) →
    preserve_update_pre l pre →
    pre (s₀, s₁).
Proof.
  intros l pre s₀ s₁ hu hp.
  eapply restore_update_mem. 2: exact hp.
  auto.
Qed.

Lemma preserve_update_mem_nil :
  ∀ m pre,
    preserve_update_mem [::] m pre.
Proof.
  intros m pre.
  intros s₀ s₁ h.
  apply remember_pre_pre in h. auto.
Qed.

#[export] Hint Extern 9 (preserve_update_mem [::] _ _) =>
  eapply preserve_update_mem_nil
  : ssprove_invariant.

Lemma preserve_update_mem_conj :
  ∀ (pre spre : precond) l m,
    preserve_update_mem l m pre →
    preserve_update_mem l m spre →
    preserve_update_mem l m (pre ⋊ spre).
Proof.
  intros pre spre l m h hs.
  intros s₀ s₁ hh. eapply remember_pre_conj in hh.
  split. all: intuition auto.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (_ ⋊ _)) =>
  eapply preserve_update_mem_conj
  : ssprove_invariant.

Lemma preserve_update_cons_sym_eq :
  ∀ ℓ v l m,
    preserve_update_mem l m (λ '(h₀, h₁), h₀ = h₁) →
    preserve_update_mem (hpv_r ℓ v :: hpv_l ℓ v :: l) m (λ '(h₀, h₁), h₀ = h₁).
Proof.
  intros ℓ v l m h.
  intros s₀ s₁ e.
  simpl. destruct update_heaps eqn:e'.
  eapply h in e as h'.
  rewrite e' in h'.
  subst. reflexivity.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (λ '(h₀, h₁), h₀ = h₁)) =>
  eapply preserve_update_cons_sym_eq
  : ssprove_invariant.

Lemma preserve_update_cons_sym_heap_ignore :
  ∀ L ℓ v l m,
    preserve_update_mem l m (heap_ignore L) →
    preserve_update_mem (hpv_r ℓ v :: hpv_l ℓ v :: l) m (heap_ignore L).
Proof.
  intros L ℓ v l m h.
  intros s₀ s₁ hh.
  simpl. destruct update_heaps eqn:e.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀ != ℓ) eqn:e1.
  - rewrite !get_set_heap_neq. 2,3: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP e1. subst.
    rewrite !get_set_heap_eq. reflexivity.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_cons_sym_heap_ignore
  : ssprove_invariant.

Lemma preserve_update_l_ignored_heap_ignore :
  ∀ L ℓ v l m,
    ℓ \in L →
    preserve_update_mem l m (heap_ignore L) →
    preserve_update_mem (hpv_l ℓ v :: l) m (heap_ignore L).
Proof.
  intros L ℓ v l m hin h.
  intros s₀ s₁ hh.
  simpl. destruct update_heaps eqn:e.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀ != ℓ) eqn:e1.
  - rewrite get_set_heap_neq. 2: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP e1. subst.
    rewrite hin in hℓ₀. discriminate.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_l_ignored_heap_ignore ; [
    solve [ auto_in_fset ]
  | idtac
  ]
  : ssprove_invariant.

Lemma preserve_update_r_ignored_heap_ignore :
  ∀ L ℓ v l m,
    ℓ \in L →
    preserve_update_mem l m (heap_ignore L) →
    preserve_update_mem (hpv_r ℓ v :: l) m (heap_ignore L).
Proof.
  intros L ℓ v l m hin h.
  intros s₀ s₁ hh.
  simpl. destruct update_heaps eqn:e.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀ != ℓ) eqn:e1.
  - rewrite get_set_heap_neq. 2: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP e1. subst.
    rewrite hin in hℓ₀. discriminate.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_r_ignored_heap_ignore ; [
    solve [ auto_in_fset ]
  | idtac
  ]
  : ssprove_invariant.

Lemma preserve_update_filter_couple_lhs :
  ∀ ℓ ℓ' R l m,
    preserve_update_mem (filter is_hpv_l l) m (couple_lhs ℓ ℓ' R) →
    preserve_update_mem l m (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R l m h.
  intros s₀ s₁ hh.
  eapply h in hh.
  destruct update_heaps eqn:e1.
  destruct (update_heaps l s₀ s₁) eqn:e2.
  apply (f_equal (λ x, x.1)) in e1.
  rewrite update_heaps_filter_l in e1. rewrite e2 in e1.
  simpl in e1. subst. auto.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (couple_lhs _ _ _)) =>
  progress (eapply preserve_update_filter_couple_lhs ; simpl)
: ssprove_invariant.

Lemma preserve_update_filter_couple_rhs :
  ∀ ℓ ℓ' R l m,
    preserve_update_mem (filter is_hpv_r l) m (couple_rhs ℓ ℓ' R) →
    preserve_update_mem l m (couple_rhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R l m h.
  intros s₀ s₁ hh.
  eapply h in hh.
  destruct update_heaps eqn:e1.
  destruct (update_heaps l s₀ s₁) eqn:e2.
  apply (f_equal (λ x, x.2)) in e1.
  rewrite update_heaps_filter_r in e1. rewrite e2 in e1.
  simpl in e1. subst. auto.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (couple_rhs _ _ _)) =>
  progress (eapply preserve_update_filter_couple_rhs ; simpl)
: ssprove_invariant.

Lemma preserve_update_filter_triple_rhs :
  ∀ ℓ₁ ℓ₂ ℓ₃ R l m,
    preserve_update_mem (filter is_hpv_r l) m (triple_rhs ℓ₁ ℓ₂ ℓ₃ R) →
    preserve_update_mem l m (triple_rhs ℓ₁ ℓ₂ ℓ₃ R).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R l m h.
  intros s₀ s₁ hh.
  eapply h in hh.
  destruct update_heaps eqn:e1.
  destruct (update_heaps l s₀ s₁) eqn:e2.
  apply (f_equal (λ x, x.2)) in e1.
  rewrite update_heaps_filter_r in e1. rewrite e2 in e1.
  simpl in e1. subst. auto.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (triple_rhs _ _ _ _)) =>
  progress (eapply preserve_update_filter_triple_rhs ; simpl)
: ssprove_invariant.

Lemma preserve_update_couple_lhs_lookup :
  ∀ ℓ ℓ' (R : _ → _ → Prop) v v' (l : seq heap_val) m,
    lookup_hpv_l ℓ l = Some v →
    lookup_hpv_l ℓ' l = Some v' →
    R v v' →
    preserve_update_mem l m (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R v v' l m hl hr h.
  intros s₀ s₁ hh. unfold couple_lhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_l_spec. 2,3: eauto.
  erewrite lookup_hpv_l_spec. 2,3: eauto.
  auto.
Qed.

Lemma preserve_update_couple_rhs_lookup :
  ∀ ℓ ℓ' (R : _ → _ → Prop) v v' (l : seq heap_val) m,
    lookup_hpv_r ℓ l = Some v →
    lookup_hpv_r ℓ' l = Some v' →
    R v v' →
    preserve_update_mem l m (couple_rhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R v v' l m hl hr h.
  intros s₀ s₁ hh. unfold couple_rhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  auto.
Qed.

Lemma preserve_update_triple_rhs_lookup :
  ∀ ℓ₁ ℓ₂ ℓ₃ (R : _ → _ → _ → Prop) v₁ v₂ v₃ (l : seq heap_val) m,
    lookup_hpv_r ℓ₁ l = Some v₁ →
    lookup_hpv_r ℓ₂ l = Some v₂ →
    lookup_hpv_r ℓ₃ l = Some v₃ →
    R v₁ v₂ v₃ →
    preserve_update_mem l m (triple_rhs ℓ₁ ℓ₂ ℓ₃ R).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R v₁ v₂ v₃ l m h₁ h₂ h₃ h.
  intros s₀ s₁ hh. unfold triple_rhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  auto.
Qed.

Lemma preserve_update_couple_lhs_lookup_None :
  ∀ ℓ ℓ' (R : _ → _ → Prop) (l : seq heap_val) m,
    lookup_hpv_l ℓ l = None →
    lookup_hpv_l ℓ' l = None →
    preserve_update_mem l m (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R l m h h'.
  intros s₀ s₁ hh. unfold couple_lhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_l_None_spec. 2,3: eauto.
  erewrite lookup_hpv_l_None_spec with (ℓ := ℓ'). 2,3: eauto.
  eapply remember_pre_pre in hh.
  auto.
Qed.

Lemma preserve_update_couple_rhs_lookup_None :
  ∀ ℓ ℓ' (R : _ → _ → Prop) (l : seq heap_val) m,
    lookup_hpv_r ℓ l = None →
    lookup_hpv_r ℓ' l = None →
    preserve_update_mem l m (couple_rhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R l m h h'.
  intros s₀ s₁ hh. unfold couple_rhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_None_spec. 2,3: eauto.
  erewrite lookup_hpv_r_None_spec with (ℓ := ℓ'). 2,3: eauto.
  eapply remember_pre_pre in hh.
  auto.
Qed.

Lemma preserve_update_triple_rhs_lookup_None :
  ∀ ℓ₁ ℓ₂ ℓ₃ (R : _ → _ → _ → Prop) (l : seq heap_val) m,
    lookup_hpv_r ℓ₁ l = None →
    lookup_hpv_r ℓ₂ l = None →
    lookup_hpv_r ℓ₃ l = None →
    preserve_update_mem l m (triple_rhs ℓ₁ ℓ₂ ℓ₃ R).
Proof.
  intros ℓ₁ ℓ₂ ℓ₃ R l m h₁ h₂ h₃.
  intros s₀ s₁ hh. unfold triple_rhs in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_None_spec. 2,3: eauto.
  erewrite lookup_hpv_r_None_spec with (ℓ := ℓ₂). 2,3: eauto.
  erewrite lookup_hpv_r_None_spec with (ℓ := ℓ₃). 2,3: eauto.
  eapply remember_pre_pre in hh.
  auto.
Qed.