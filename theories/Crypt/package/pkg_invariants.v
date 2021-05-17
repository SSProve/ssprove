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

Definition heap_ignore (L : {fset Location}) (hh : heap * heap) : Prop :=
  let '(h₀, h₁) := hh in
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

Definition couple_lhs ℓ ℓ' (h : _ → _ → Prop) (s : heap * heap) :=
  let '(s₀, s₁) := s in
  h (get_heap s₀ ℓ) (get_heap s₀ ℓ').

Lemma SemiInvariant_couple_lhs :
  ∀ L₀ L₁ ℓ ℓ' (h : _ → _ → Prop),
    ℓ \in L₀ :|: L₁ →
    ℓ' \in L₀ :|: L₁ →
    h (get_heap empty_heap ℓ) (get_heap empty_heap ℓ') →
    SemiInvariant L₀ L₁ (couple_lhs ℓ ℓ' h).
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

Definition couple_rhs ℓ ℓ' (h : _ → _ → Prop) (s : heap * heap) :=
  let '(s₀, s₁) := s in
  h (get_heap s₁ ℓ) (get_heap s₁ ℓ').

Lemma SemiInvariant_couple_rhs :
  ∀ L₀ L₁ ℓ ℓ' (h : _ → _ → Prop),
    ℓ \in L₀ :|: L₁ →
    ℓ' \in L₀ :|: L₁ →
    h (get_heap empty_heap ℓ) (get_heap empty_heap ℓ') →
    SemiInvariant L₀ L₁ (couple_rhs ℓ ℓ' h).
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

(** Predicates on invariants

  The idea is to use them as side-conditions for rules.
*)

Class Tracks ℓ pre :=
  is_tracking : ∀ s₀ s₁, pre (s₀, s₁) → get_heap s₀ ℓ = get_heap s₁ ℓ.

Class Couples_lhs ℓ ℓ' R pre :=
  is_coupling_lhs : ∀ s, pre s → couple_lhs ℓ ℓ' R s.

Class Couples_rhs ℓ ℓ' R pre :=
  is_coupling_rhs : ∀ s, pre s → couple_rhs ℓ ℓ' R s.

Lemma Tracks_eq :
  ∀ ℓ, Tracks ℓ (λ '(s₀, s₁), s₀ = s₁).
Proof.
  intros ℓ s₀ s₁ e. subst. reflexivity.
Qed.

#[export] Hint Extern 10 (Tracks _ (λ '(s₀, s₁), s₀ = s₁)) =>
  apply Tracks_eq
  : typeclass_instances ssprove_invariant.

Lemma Tracks_heap_ignore :
  ∀ ℓ L,
    ℓ \notin L →
    Tracks ℓ (heap_ignore L).
Proof.
  intros ℓ L hn s₀ s₁ h.
  apply h. auto.
Qed.

#[export] Hint Extern 10 (Tracks _ (heap_ignore _)) =>
  apply Tracks_heap_ignore
  : typeclass_instances ssprove_invariant.

Lemma Tracks_conj :
  ∀ ℓ (pre spre : precond),
    Tracks ℓ pre →
    Tracks ℓ (pre ⋊ spre).
Proof.
  intros ℓ pre spre hpre s₀ s₁ [].
  apply hpre. auto.
Qed.

#[export] Hint Extern 10 (Tracks _ (_ ⋊ _)) =>
  apply Tracks_conj
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
    Tracks ℓ pre →
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
    Tracks ℓ pre →
    Remembers_rhs ℓ v pre.
Proof.
  intros ℓ v pre hr ht.
  intros s₀ s₁ hpre. simpl.
  specialize (hr _ _ hpre). specialize (ht _ _ hpre).
  rewrite -ht. apply hr.
Qed.

(* Weaker than Invariant *)
Definition preserve_set_set ℓ v ℓ' v' pre :=
  ∀ s₀ s₁,
    pre (s₀, s₁) →
    pre (set_heap (set_heap s₀ ℓ v) ℓ' v', set_heap (set_heap s₁ ℓ v) ℓ' v').

Lemma preserve_set_set_eq :
  ∀ ℓ v ℓ' v',
    preserve_set_set ℓ v ℓ' v' (λ '(s₀, s₁), s₀ = s₁).
Proof.
  intros ℓ v ℓ' v' s₀ s₁ e. subst. reflexivity.
Qed.

#[export] Hint Extern 10 (preserve_set_set _ _ _ _ (λ '(s₀, s₁), s₀ = s₁)) =>
  eapply preserve_set_set_eq
  : ssprove_invariant.

Lemma preserve_set_set_heap_ignore :
  ∀ ℓ v ℓ' v' L,
    preserve_set_set ℓ v ℓ' v' (heap_ignore L).
Proof.
  intros ℓ v ℓ' v' L.
  intros s₀ s₁ h.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀ != ℓ') eqn:e1.
  - rewrite get_set_heap_neq. 2: auto.
    rewrite [RHS]get_set_heap_neq. 2: auto.
    destruct (ℓ₀ != ℓ) eqn:e2.
    + rewrite !get_set_heap_neq. 2,3: auto.
      apply h. auto.
    + move: e2 => /eqP e2. subst.
      rewrite !get_set_heap_eq. reflexivity.
  - move: e1 => /eqP e1. subst.
    rewrite !get_set_heap_eq. reflexivity.
Qed.

#[export] Hint Extern 10 (preserve_set_set _ _ _ _ (heap_ignore _)) =>
  eapply preserve_set_set_heap_ignore
  : ssprove_invariant.

Lemma preserve_set_set_conj :
  ∀ (pre spre : precond) ℓ ℓ' v v',
    preserve_set_set ℓ v ℓ' v' pre →
    preserve_set_set ℓ v ℓ' v' spre →
    preserve_set_set ℓ v ℓ' v' (pre ⋊ spre).
Proof.
  intros pre spre ℓ ℓ' v v' h hs.
  intros s₀ s₁ []. split.
  all: auto.
Qed.

#[export] Hint Extern 10 (preserve_set_set _ _ _ _ (_ ⋊ _)) =>
  eapply preserve_set_set_conj
  : ssprove_invariant.

Lemma preserve_set_set_couple_lhs_eq :
  ∀ ℓ ℓ' v v' (R : _ → _ → Prop),
    ℓ != ℓ' →
    R v v' →
    preserve_set_set ℓ v ℓ' v' (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' v v' R hn hR.
  intros s₀ s₁ h.
  unfold couple_lhs in *.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_eq.
  auto.
Qed.

Lemma preserve_set_set_couple_rhs_neq :
  ∀ ℓ ℓ' v v' ℓ₀ ℓ₁ (R : _ → _ → Prop),
    ℓ₀ != ℓ →
    ℓ₀ != ℓ' →
    ℓ₁ != ℓ →
    ℓ₁ != ℓ' →
    preserve_set_set ℓ v ℓ' v' (couple_rhs ℓ₀ ℓ₁ R).
Proof.
  intros ℓ ℓ' v v' ℓ₀ ℓ₁ R ? ? ? ?.
  intros s₀ s₁ h.
  unfold couple_rhs in *.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_neq. 2: auto.
  auto.
Qed.

Definition preserve_set_setR ℓ v ℓ' v' pre :=
  ∀ s₀ s₁,
    pre (s₀, s₁) →
    pre (set_heap s₀ ℓ v, set_heap (set_heap s₁ ℓ v) ℓ' v').

Lemma preserve_set_setR_heap_ignore :
  ∀ ℓ v ℓ' v' L,
    ℓ' \in L →
    preserve_set_setR ℓ v ℓ' v' (heap_ignore L).
Proof.
  intros ℓ v ℓ' v' L hℓ'.
  intros s₀ s₁ h.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀ != ℓ') eqn:e1.
  - rewrite [RHS]get_set_heap_neq. 2: auto.
    destruct (ℓ₀ != ℓ) eqn:e2.
    + rewrite !get_set_heap_neq. 2,3: auto.
      apply h. auto.
    + move: e2 => /eqP e2. subst.
      rewrite !get_set_heap_eq. reflexivity.
  - move: e1 => /eqP e1. subst.
    rewrite hℓ' in hℓ₀. discriminate.
Qed.

#[export] Hint Extern 10 (preserve_set_setR _ _ _ _ (heap_ignore _)) =>
  eapply preserve_set_setR_heap_ignore
  : ssprove_invariant.

Lemma preserve_set_setR_conj :
  ∀ (pre spre : precond) ℓ ℓ' v v',
    preserve_set_setR ℓ v ℓ' v' pre →
    preserve_set_setR ℓ v ℓ' v' spre →
    preserve_set_setR ℓ v ℓ' v' (pre ⋊ spre).
Proof.
  intros pre spre ℓ ℓ' v v' h hs.
  intros s₀ s₁ []. split.
  all: auto.
Qed.

#[export] Hint Extern 10 (preserve_set_setR _ _ _ _ (_ ⋊ _)) =>
  eapply preserve_set_setR_conj
  : ssprove_invariant.

Lemma preserve_set_setR_couple_rhs_eq :
  ∀ ℓ ℓ' v v' (R : _ → _ → Prop),
    ℓ != ℓ' →
    R v v' →
    preserve_set_setR ℓ v ℓ' v' (couple_rhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' v v' R hn hR.
  intros s₀ s₁ h.
  unfold couple_rhs in *.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_eq.
  rewrite get_set_heap_eq.
  auto.
Qed.

Lemma preserve_set_setR_couple_lhs_neq :
  ∀ ℓ ℓ' v v' ℓ₀ ℓ₁ (R : _ → _ → Prop),
    ℓ₀ != ℓ →
    ℓ₁ != ℓ →
    preserve_set_setR ℓ v ℓ' v' (couple_lhs ℓ₀ ℓ₁ R).
Proof.
  intros ℓ ℓ' v v' ℓ₀ ℓ₁ R ? ?.
  intros s₀ s₁ h.
  unfold couple_lhs in *.
  rewrite get_set_heap_neq. 2: auto.
  rewrite get_set_heap_neq. 2: auto.
  auto.
Qed.

(** Dually to rem_lhs/rem_rhs we create "invariants" to represent a deviation
    of invariant, or a deficit which will need to be paid later to restore
    the proper invariant.

    TODO: Kill the above
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