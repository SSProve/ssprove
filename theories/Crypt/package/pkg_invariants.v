(** Invariants on state

  These can be very useful when proving program equivalences.
*)


From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From HB Require Import structures.

From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Prelude Axioms fmap_extra
  choice_type pkg_core_definition pkg_heap.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

Definition precond := heap * heap → Prop.
Definition postcond A B := (A * heap) → (B * heap) → Prop.

Definition INV (L : Locations)
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, fhas L l → get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, fhas L l → I (set_heap s1 l v, set_heap s2 l v)).

Definition INV' (L1 L2 : Locations)
  (I : heap_choiceType * heap_choiceType → Prop) :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, l.1 \notin domm L1 → l.1 \notin domm L2 →
      get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, l.1 \notin domm L1 → l.1 \notin domm L2 →
      I (set_heap s1 l v, set_heap s2 l v)).

Definition pINV' (P1 P2 : Location -> Prop)
  (I : heap_choiceType * heap_choiceType → Prop)
   :=
  ∀ s1 s2,
    (I (s1, s2) → ∀ l, ~ P1 l → ~ P2 l →
      get_heap s1 l = get_heap s2 l) ∧
    (I (s1, s2) → ∀ l v, ~ P1 l -> ~ P2 l →
      I (set_heap s1 l v, set_heap s2 l v)).

(* TODO: move? *)
Definition pdisjoint (L : Locations) (P : Location -> Prop) := forall l, ~ (fhas L l /\ P l).

Lemma pINV'_to_INV (L : Locations) P1 P2
  (I : heap_choiceType * heap_choiceType → Prop)
  (HpINV' : pINV' P1 P2 I)
  (Hdisjoint1 : pdisjoint L P1)
  (Hdisjoint2 : pdisjoint L P2) :
  INV L I.
Proof.
  unfold INV.
  intros s1 s2. split.
  - intros hi l hin.
    apply HpINV'.
    + assumption.
    + intros contra.
      eapply Hdisjoint1. eauto.
    + intros contra.
      eapply Hdisjoint2. eauto.
  - intros hi l v hin.
    apply HpINV'.
    + assumption.
    + intros contra.
      eapply Hdisjoint1. eauto.
    + intros contra.
      eapply Hdisjoint2. eauto.
Qed.

Lemma INV'_to_INV (L L1 L2 : Locations)
  (I : heap_choiceType * heap_choiceType → Prop)
  (HINV' : INV' L1 L2 I)
  (Hdisjoint1 : fseparate L L1) (Hdisjoint2 : fseparate L L2) :
  INV L I.
Proof.
  unfold INV.
  intros s1 s2. split.
  - intros hi l hin.
    apply HINV'; fmap_solve.
  - intros hi l v hin.
    apply HINV'; fmap_solve.
Qed.

(* TODO: add automation? *)
Class pInvariant P₀ P₁ pinv := {
  pinv_pINV' : pINV' P₀ P₁ pinv ;
  pinv_empty : pinv (empty_heap, empty_heap)
}.

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

Definition heap_ignore (L : Locations) : precond :=
  λ '(h₀, h₁),
    ∀ (ℓ : Location), ℓ.1 \notin domm L → get_heap h₀ ℓ = get_heap h₁ ℓ.

Definition heap_ignore_pred (P : Location -> Prop) : precond :=
  λ '(h₀, h₁),
    forall (ℓ : Location), ~ P ℓ -> get_heap h₀ ℓ = get_heap h₁ ℓ.

Arguments heap_ignore : simpl never.
Arguments heap_ignore_pred : simpl never.

Lemma heap_ignore_empty :
  ∀ L,
    heap_ignore L (empty_heap, empty_heap).
Proof.
  intros L ℓ hℓ. reflexivity.
Qed.

Lemma heap_ignore_pred_empty :
  ∀ P,
    heap_ignore_pred P (empty_heap, empty_heap).
Proof.
  intros P ℓ hℓ. reflexivity.
Qed.

Lemma INV'_heap_ignore_pred (P : Location -> Prop) :
  ∀ L0 L1 : Locations,
    (forall ℓ : Location, P ℓ -> fhas (unionm L0 L1) ℓ) ->
    INV' L0 L1 (heap_ignore_pred P).
Proof.
  intros L0 L1 hP h0 h1. split.
  - intros hh l nin0 nin1.
    eapply hh.
    intros contra.
    apply hP in contra as h.
    apply fhas_in in h.
    rewrite domm_union in_fsetU in h. move: h => /orP [h | h].
    + rewrite h in nin0. discriminate.
    + rewrite h in nin1. discriminate.
  - intros h ℓ v n₀ n₁ ℓ' n.
    destruct (ℓ'.1 != ℓ.1) eqn:e.
    + rewrite get_set_heap_neq. 2: auto.
      rewrite get_set_heap_neq. 2: auto.
      apply h. auto.
    + move: e => /eqP e.
      rewrite /get_heap e 2!setmE eq_refl //=.
Qed.

Lemma INV'_heap_ignore :
  ∀ L L₀ L₁,
    fsubmap L (unionm L₀ L₁) →
    INV' L₀ L₁ (heap_ignore L).
Proof.
  intros L L₀ L₁ hs h₀ h₁. split.
  - intros hh ℓ n₀ n₁.
    apply hh.
    apply /dommPn.
    move: n₀ => /dommPn.
    move: n₁ => /dommPn.
    intros H H'.
    assert (H'' : unionm L₀ L₁ ℓ.1 = None).
    { rewrite unionmE H H' //. }
    rewrite -hs in H''.
    rewrite unionmE in H''.
    destruct (L ℓ.1) eqn:E => //.
  - intros h ℓ v n₀ n₁ ℓ' n.
    destruct (ℓ'.1 != ℓ.1) eqn:e.
    + rewrite get_set_heap_neq. 2: auto.
      rewrite get_set_heap_neq. 2: auto.
      apply h. auto.
    + move: e => /eqP e. subst.
      rewrite /get_heap e 2!setmE eq_refl //=.
Qed.

Lemma Invariant_heap_ignore_pred :
  ∀ L0 L1 (P : Location -> Prop),
    (forall ℓ : Location, P ℓ -> fhas (unionm L0 L1) ℓ) ->
    Invariant L0 L1 (heap_ignore_pred P).
Proof.
  intros L P h. split.
  - apply INV'_heap_ignore_pred. auto.
  - apply heap_ignore_pred_empty.
Qed.

Lemma Invariant_heap_ignore :
  ∀ L L₀ L₁,
    fsubmap L (unionm L₀ L₁) →
    Invariant L₀ L₁ (heap_ignore L).
Proof.
  intros L L₀ L₁ h. split.
  - apply INV'_heap_ignore; auto.
  - apply heap_ignore_empty.
Qed.

#[export] Hint Extern 10 (Invariant _ _ (heap_ignore _)) =>
  eapply Invariant_heap_ignore
  : (* typeclass_instances *) ssprove_invariant.

(* TODO: naming? This doesn't seem to correspond to heap_ignore, due to the missing negation, but I use it that way *)
Definition pheap_ignore (P : Location -> Prop) : precond :=
  λ '(h₀, h₁),
    forall (ℓ : Location), P ℓ -> get_heap h₀ ℓ = get_heap h₁ ℓ.

Lemma pheap_ignore_empty :
  ∀ P,
    pheap_ignore P (empty_heap, empty_heap).
Proof. intros P ℓ hℓ. reflexivity. Qed.

Lemma pINV'_pheap_ignore (P : Location -> Prop) :
  ∀ P0 P1 : Location -> Prop,
    (forall ℓ : Location, ~ P0 ℓ /\ ~ P1 ℓ -> P ℓ) ->
    pINV' P0 P1 (pheap_ignore P).
Proof.
  intros P0 P1 hP h0 h1. split.
  - intros hh l nin1 nin2.
    eapply hh.
    apply hP.
    eauto.
  - intros h ℓ v nin0 nin1 ℓ' n.
    destruct (ℓ'.1 != ℓ.1) eqn:e.
    + rewrite get_set_heap_neq. 2: auto.
      rewrite get_set_heap_neq. 2: auto.
      apply h. auto.
    + move: e => /eqP e. subst.
      rewrite /get_heap e 2!setmE eq_refl //=.
Qed.

Lemma pInvariant_pheap_ignore :
  ∀ P0 P1 (P : Location -> Prop),
    (forall ℓ : Location, ~ P0 ℓ /\ ~ P1 ℓ -> P ℓ) ->
    pInvariant P0 P1 (pheap_ignore P).
Proof.
  intros L P h. split.
  - apply pINV'_pheap_ignore. auto.
  - apply pheap_ignore_empty.
Qed.

(* Not-really-symmetric (in use) conjunction of invariants *)
Definition inv_conj (inv inv' : precond) :=
  λ s, inv s ∧ inv' s.

Notation "I ⋊ J" :=
  (inv_conj I J) (at level 19, left associativity) : package_scope.

Arguments inv_conj : simpl never.

Class SemiInvariant (L₀ L₁ : Locations) (sinv : precond) := {
  sinv_set :
    ∀ s₀ s₁ (ℓ : Location) v,
      ℓ.1 \notin domm L₀ →
      ℓ.1 \notin domm L₁ →
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


Inductive side := lhs | rhs.

Definition get_side : heap * heap → ∀ l : side * Location, snd l
  := λ hh s, match s with
    | (lhs, l) => get_heap hh.1 l
    | (rhs, l) => get_heap hh.2 l
    end.

Definition other s := match s with lhs => rhs | rhs => lhs end.

(* Locations Relation Invariants *)

Fixpoint rel_type (ls : list (side * Location)) :=
  match ls with
  | l :: ls => l.2 → rel_type ls
  | [::] => Prop
  end.

Fixpoint rel_app {ls} : rel_type ls → precond :=
    match ls with
    | l :: ls => λ R s, rel_app (R (get_side s l)) s
    | [::] => λ R _, R
    end.
Arguments rel_app : clear implicits.

Fixpoint rel_empty {ls} : rel_type ls → Prop :=
    match ls with
    | l :: ls => λ R, rel_empty (R (heap_init (snd l)))
    | [::] => λ R, R
    end.
Arguments rel_empty : clear implicits.

Fixpoint rel_in ls : Locations * Locations → Prop := λ L,
  match ls with
  | (lhs, l) :: ls => fhas L.1 l ∧ rel_in ls L
  | (rhs, l) :: ls => fhas L.2 l ∧ rel_in ls L
  | [::] => True
  end.

#[export] Hint Extern 10 (rel_in [::] _) => done
  : ssprove_invariant.

#[export] Hint Extern 10 (rel_in (_ :: _) _) =>
  split; [ solve [ fmap_solve ] |]
  : ssprove_invariant.

#[export] Hint Extern 10 (fsubmap _ _) =>
  solve [ fmap_solve ]
  : ssprove_invariant.

Lemma SemiInvariant_relApp :
  ∀ (L₀ L₁ : Locations) ls R,
    rel_in ls (L₀, L₁) →
    rel_empty ls R →
    SemiInvariant L₀ L₁ (rel_app ls R).
Proof.
  intros L₀ L₁ ls R Hin Hempty. split.
  2: {
    move=> {Hin}.
    induction ls.
    - apply Hempty.
    - apply IHls.
      destruct a as [[] ?]; apply Hempty.
  }
  move=> {Hempty} s0 s1 l v H0 H1 H2.
  induction ls as [|s ls IHls]=> //.
  destruct s as [[] loc].
  - simpl.
    destruct Hin as [Hin1 Hin2].
    rewrite get_set_heap_neq.
    { apply IHls => //. }
    apply /eqP => H.
    apply fhas_in in Hin1.
    move: H0 => /negP.
    rewrite -H Hin1 //.
  - simpl.
    destruct Hin as [Hin1 Hin2].
    rewrite get_set_heap_neq.
    { apply IHls => //. }
    apply /eqP => H.
    apply fhas_in in Hin1.
    move: H1 => /negP.
    rewrite -H Hin1 //.
Qed.

#[export] Hint Extern 10 (SemiInvariant _ _ (rel_app _ _)) =>
  eapply SemiInvariant_relApp
  : ssprove_invariant.

Arguments rel_app : simpl never.

Notation single_lhs ℓ R :=
  (rel_app [:: (lhs, ℓ) ] R).

Notation single_rhs ℓ R :=
  (rel_app [:: (rhs, ℓ) ] R).

Notation couple_lhs ℓ ℓ' R :=
  (rel_app [:: (lhs, ℓ); (lhs, ℓ')] R).

Notation couple_rhs ℓ ℓ' R :=
  (rel_app [:: (rhs, ℓ); (rhs, ℓ')] R).

Notation couple_cross ℓ ℓ' R :=
  (rel_app [:: (lhs, ℓ); (rhs, ℓ')] R).

Notation triple_lhs ℓ₁ ℓ₂ ℓ₃ R :=
  (rel_app [:: (lhs, ℓ₁); (lhs, ℓ₂); (lhs, ℓ₃)] R).

Notation triple_rhs ℓ₁ ℓ₂ ℓ₃ R :=
  (rel_app [:: (rhs, ℓ₁); (rhs, ℓ₂); (rhs, ℓ₃)] R).

Notation syncs l :=
  (rel_app [:: (lhs, l); (rhs, l)] eq).


Definition get_pre_cond ℓ (pre : precond) :=
  ∀ s₀ s₁, pre (s₀, s₁) → get_heap s₀ ℓ = get_heap s₁ ℓ.

Lemma get_pre_cond_heap_ignore :
  ∀ (ℓ : Location) (L : Locations),
    ℓ.1 \notin domm L →
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
  destruct (ℓ'.1 != ℓ.1) eqn:e.
  - rewrite get_set_heap_neq. 2: auto.
    rewrite get_set_heap_neq. 2: auto.
    apply h. auto.
  - move: e => /eqP e. subst.
    rewrite /get_heap e 2!setmE eq_refl //=.
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

Lemma rel_app_nil {R : rel_type [::]} {s} : rel_app [::] R s = R.
Proof. done. Qed.

Lemma rel_app_cons {l ls} {R : rel_type (l :: ls)} {s}
  : rel_app (l :: ls) R s = rel_app ls (R (get_side s l)) s.
Proof. done. Qed.

Lemma put_pre_cond_rel_app :
  ∀ ℓ v (ls : list (side * Location)) h,
    ℓ.1 \notin map (fst \o snd) ls →
    put_pre_cond ℓ v (rel_app ls h).
Proof.
  intros ℓ v ls R h s₀ s₁ hc.
  induction ls => //.
  rewrite 2!rel_app_cons in hc |- *.
  rewrite /= in_cons negb_or in h.
  move: h => /andP [h h'].
  apply IHls => //.
  destruct a as [[] ?] => /=.
  1,2: rewrite get_set_heap_neq // eq_sym //.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (rel_app _ _)) =>
  apply put_pre_cond_rel_app; [ done ]
  : ssprove_invariant.


(** Predicates on invariants

  The idea is to use them as side-conditions for rules.
*)

(* ProvenBy pre pre' indicates that the invariant pre'
    shows the fact pre *)
Class ProvenBy (pre pre' : precond) :=
  proven_by : ∀ s, pre' s → pre s.

Instance ProvenBy_refl {pre} : ProvenBy pre pre.
Proof. done. Qed.

Instance ProvenBy_conj_left {tgt pre spre : precond} :
  ProvenBy tgt pre → ProvenBy tgt (pre ⋊ spre).
Proof. intros ? ? []. auto. Qed.

Instance ProvenBy_conj_right {tgt pre spre : precond} :
  ProvenBy tgt spre → ProvenBy tgt (pre ⋊ spre).
Proof. intros ? ? []. auto. Qed.

Lemma syncs_proven_by_eq {l}
  : ProvenBy (syncs l) (λ '(s₀, s₁), s₀ = s₁).
Proof. by intros [h0 h1] ->. Qed.

#[export] Hint Extern 10 (ProvenBy (syncs _) _) =>
  apply syncs_proven_by_eq
  : typeclass_instances.

Lemma syncs_proven_by_heap_ignore {l} {L} :
    l.1 \notin domm L →
    ProvenBy (syncs l) (heap_ignore L).
Proof. intros hn [h₀ h₁] h. apply h, hn. Qed.

#[export] Hint Extern 10 (ProvenBy (syncs _) _) =>
  apply syncs_proven_by_heap_ignore
  : typeclass_instances.

Definition rem_inv s (ℓ : Location) (v : ℓ) : precond :=
  λ h, get_side h (s, ℓ) = v.

Notation rem_lhs := (rem_inv lhs).
Notation rem_rhs := (rem_inv rhs).

Inductive Remembers : ∀ ls, rel_type ls → Prop → precond → Prop :=
  | Remembers_nil : ∀ {R} pre, Remembers [::] R R pre
  | Remembers_cons : ∀ {s l ls} {R P} {v} (pre : precond),
      ProvenBy (rem_inv s l v) pre →
      Remembers ls (R v) P pre →
      Remembers ((s, l) :: ls) R P pre.

Existing Class Remembers.

Hint Resolve Remembers_nil Remembers_cons
  : typeclass_instances.

Lemma Remembers_syncs :
  ∀ s ℓ v pre,
    ProvenBy (rem_inv (other s) ℓ v) pre →
    ProvenBy (syncs ℓ) pre →
    ProvenBy (rem_inv s ℓ v) pre.
Proof.
  intros s ℓ v pre hr ht.
  intros [s₀ s₁] hpre. simpl.
  specialize (hr _ hpre). specialize (ht _ hpre).
  rewrite /(syncs _) /= in ht.
  destruct s; rewrite /rem_inv /=.
  - rewrite ht. apply hr.
  - rewrite -ht. apply hr.
Qed.

Lemma Remembers_cons_syncs {s l ls} {R P} {v} (pre : precond) :
    ProvenBy (rem_inv (other s) l v) pre →
    ProvenBy (syncs l) pre →
    Remembers ls (R v) P pre →
    Remembers ((s, l) :: ls) R P pre.
Proof.
  intros hr hs hI.
  eapply Remembers_cons.
  - apply Remembers_syncs => //.
    apply hr.
  - apply hI.
Qed.

Hint Resolve Remembers_cons_syncs : typeclass_instances.

Lemma put_pre_cond_rem :
  ∀ s ℓ v ℓ' v',
    ℓ'.1 != ℓ.1 →
    put_pre_cond ℓ v (rem_inv s ℓ' v').
Proof.
  intros s ℓ v ℓ' v' hn s₀ s₁ hc.
  destruct s; rewrite /rem_inv /= get_set_heap_neq //.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ _) =>
  apply put_pre_cond_rem
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

Definition set_inv s ℓ v (pre : precond) : precond :=
  (match s with lhs => set_lhs | rhs => set_rhs end) ℓ v pre.

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

Fixpoint lookup_hpv_l (l : Location) (lv : seq heap_val) : option l :=
  match lv with
  | [::] => None
  | (hpv_l l' v :: lv) =>
      if l.1 == l'.1 then Some (coerce v) else lookup_hpv_l l lv
  | (hpv_r _ _ :: lv) => lookup_hpv_l l lv
  end.

Fixpoint lookup_hpv_r (l : Location) (lv : seq heap_val) : option l :=
  match lv with
  | [::] => None
  | (hpv_l _ _ :: lv) => lookup_hpv_r l lv
  | (hpv_r l' v :: lv) =>
      if l.1 == l'.1 then Some (coerce v) else lookup_hpv_r l lv
  end.

Definition lookup_hpv (ℓ : Location) (s : side) (l : seq heap_val) : option ℓ :=
  match s with
  | lhs => lookup_hpv_l ℓ l
  | rhs => lookup_hpv_r ℓ l
  end.

Lemma lookup_hpv_l_eq :
  ∀ ℓ v l,
    lookup_hpv_l ℓ (hpv_l ℓ v :: l) = Some v.
Proof. intros. rewrite /= eq_refl coerceE //. Qed.

Lemma lookup_hpv_l_neq :
  ∀ ℓ ℓ' v l,
    ℓ'.1 != ℓ.1 →
    lookup_hpv_l ℓ' (hpv_l ℓ v :: l) = lookup_hpv_l ℓ' l.
Proof. intros. rewrite /= -(negbK (_ == _)) H //. Qed.

Lemma lookup_hpv_r_eq :
  ∀ ℓ v l,
    lookup_hpv_r ℓ (hpv_r ℓ v :: l) = Some v.
Proof. intros. rewrite /= eq_refl coerceE //. Qed.

Lemma lookup_hpv_r_neq :
  ∀ ℓ ℓ' v l,
    ℓ'.1 != ℓ.1 →
    lookup_hpv_r ℓ' (hpv_r ℓ v :: l) = lookup_hpv_r ℓ' l.
Proof. intros. rewrite /= -(negbK (_ == _)) H //. Qed.

Lemma lookup_hpv_l_spec :
  ∀ ℓ v l s₀ s₁ h₀ h₁,
    lookup_hpv_l ℓ l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₀ ℓ = v.
Proof.
  intros ℓ v.
  elim => // l lv ih s0 s1 h0 h1 h e.
  destruct l as [l v'|l v'].
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    destruct (_ == _) eqn:e.
    + rewrite /get_heap setmE e.
      by noconf h.
    + rewrite get_set_heap_neq ?e //.
      eapply ih => //.
      apply e1.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eapply ih => //.
    apply e1.
Qed.

Lemma lookup_hpv_r_spec :
  ∀ ℓ v l s₀ s₁ h₀ h₁,
    lookup_hpv_r ℓ l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₁ ℓ = v.
Proof.
  intros ℓ v.
  elim => // l lv ih s0 s1 h0 h1 h e.
  destruct l as [l v'|l v'].
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eapply ih => //.
    apply e1.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    destruct (_ == _) eqn:e.
    + rewrite /get_heap setmE e.
      by noconf h.
    + rewrite get_set_heap_neq ?e //.
      eapply ih => //.
      apply e1.
Qed.

Lemma lookup_hpv_spec :
  ∀ {ℓ s v l s₀ s₁ h₀ h₁},
    lookup_hpv ℓ s l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_side (h₀, h₁) (s, ℓ) = v.
Proof.
  intros ℓ s v l s₀ s₁ h₀ h₁ hl e.
  destruct s.
  - eapply lookup_hpv_l_spec. all: eauto.
  - eapply lookup_hpv_r_spec. all: eauto.
Qed.

Lemma lookup_hpv_l_None_spec :
  ∀ ℓ l s₀ s₁ h₀ h₁,
    lookup_hpv_l ℓ l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₀ ℓ = get_heap s₀ ℓ.
Proof.
  intros ℓ. elim.
  { intros ? ? ? ? ? H. by noconf H. }
  intros a l ih s0 s1 h0 h1 h e.
  destruct a; simpl in *;
    destruct update_heaps eqn:e1; noconf e.
  - destruct (_ == _) eqn:e => //.
    transitivity (get_heap h2 ℓ).
    1: rewrite /get_heap setmE e //.
    eapply ih => //.
    apply e1.
  - eapply ih => //.
    apply e1.
Qed.

Lemma lookup_hpv_r_None_spec :
  ∀ ℓ l s₀ s₁ h₀ h₁,
    lookup_hpv_r ℓ l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap h₁ ℓ = get_heap s₁ ℓ.
Proof.
  intros ℓ. elim.
  { intros ? ? ? ? ? H. by noconf H. }
  intros a l ih s0 s1 h0 h1 h e.
  destruct a; simpl in *;
    destruct update_heaps eqn:e1; noconf e.
  - eapply ih => //.
    apply e1.
  - destruct (_ == _) eqn:e => //.
    transitivity (get_heap h3 ℓ).
    1: rewrite /get_heap setmE e //.
    eapply ih => //.
    apply e1.
Qed.

Lemma lookup_hpv_None_spec :
  ∀ {ℓ s l s₀ s₁ h₀ h₁},
    lookup_hpv ℓ s l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_side (h₀, h₁) (s, ℓ) = get_side (s₀, s₁) (s, ℓ).
Proof.
  intros ℓ s l s₀ s₁ h₀ h₁ hl e.
  destruct s.
  - eapply lookup_hpv_l_None_spec. all: eauto.
  - eapply lookup_hpv_r_None_spec. all: eauto.
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
  destruct (ℓ₀.1 != ℓ.1) eqn:e1.
  - rewrite !get_set_heap_neq. 2,3: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP /eqP e1. subst.
    rewrite /get_heap 2!setmE e1 //.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_cons_sym_heap_ignore
  : ssprove_invariant.

Lemma preserve_update_l_ignored_heap_ignore :
  ∀ L ℓ v l m,
    fhas L ℓ →
    preserve_update_mem l m (heap_ignore L) →
    preserve_update_mem (hpv_l ℓ v :: l) m (heap_ignore L).
Proof.
  intros L ℓ v l m hin h.
  intros s₀ s₁ hh.
  simpl. destruct update_heaps eqn:e.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀.1 != ℓ.1) eqn:e1.
  - rewrite get_set_heap_neq. 2: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP e1. subst.
    destruct ℓ.
    move: hℓ₀ => /dommPn //= H.
    rewrite e1 //= hin // in H.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_l_ignored_heap_ignore ; [
    solve [ fmap_solve ]
  | idtac
  ]
  : ssprove_invariant.

Lemma preserve_update_r_ignored_heap_ignore :
  ∀ L ℓ v l m,
    fhas L ℓ →
    preserve_update_mem l m (heap_ignore L) →
    preserve_update_mem (hpv_r ℓ v :: l) m (heap_ignore L).
Proof.
  intros L ℓ v l m hin h.
  intros s₀ s₁ hh.
  simpl. destruct update_heaps eqn:e.
  intros ℓ₀ hℓ₀.
  destruct (ℓ₀.1 != ℓ.1) eqn:e1.
  - rewrite get_set_heap_neq. 2: auto.
    eapply h in hh. rewrite e in hh.
    apply hh. auto.
  - move: e1 => /eqP e1. subst.
    destruct ℓ.
    move: hℓ₀  => /dommPn //= H.
    rewrite e1 //= hin // in H.
Qed.

#[export] Hint Extern 10 (preserve_update_mem _ _ (heap_ignore _)) =>
  eapply preserve_update_r_ignored_heap_ignore ; [
    solve [ fmap_solve ]
  | idtac
  ]
  : ssprove_invariant.


Definition preserve_update_rel l m ls (R R' : rel_type ls) :=
  ∀ s₀ s₁, (remember_pre m (rel_app ls R)) (s₀, s₁)
    → rel_app ls R' (update_heaps l s₀ s₁).

Lemma preserve_update_rel_nil {set get P P'} :
  (P → P') →
  preserve_update_rel set get [::] P P'.
Proof.
  move=> H s0 s1 /remember_pre_pre.
  rewrite 2!rel_app_nil //.
Qed.

Lemma preserve_update_mem_rel {set get ls R} :
  preserve_update_rel set get ls R R →
  preserve_update_mem set get (rel_app ls R).
Proof. auto. Qed.

Lemma remember_pre_exchange :
  ∀ get (pre pre' : precond) s0 s1,
  (pre (s0, s1) → pre' (s0, s1)) →
  remember_pre get pre (s0, s1) →
  remember_pre get pre' (s0, s1).
Proof.
  intros get pre pre' s0 s1 h.
  induction get => //.
  destruct a => /=; move=> [h0 h1]; split; auto.
Qed.

Lemma preserve_update_rel_1 :
  ∀ s l ls R R' (set get : seq heap_val) v v',
  lookup_hpv l s set = Some v' →
  ProvenBy (rem_inv s l v) (remember_pre get (rel_app ((s, l) :: ls) R)) →
  preserve_update_rel set get ls (R v) (R' v') →
  preserve_update_rel set get ((s, l) :: ls) R R'.
Proof.
  intros s l ls R R' set get v v' hv' hv ih.
  intros s0 s1 h.
  specialize (ih s0 s1).
  destruct update_heaps eqn:e.
  rewrite rel_app_cons (lookup_hpv_spec hv' e).
  apply ih.
  eapply remember_pre_exchange; [| exact h ].
  rewrite rel_app_cons.
  apply hv in h.
  by rewrite h.
Qed.

Lemma preserve_update_rel_2 :
  ∀ s l ls R R' (set get : seq heap_val) v',
  lookup_hpv l s set = Some v' →
  (∀ v, preserve_update_rel set get ls (R v) (R' v')) →
  preserve_update_rel set get ((s, l) :: ls) R R'.
Proof.
  intros s l ls R R' set get v' hv' ih.
  intros s0 s1 h.
  specialize (ih (get_side (s0, s1) (s, l)) s0 s1).
  destruct update_heaps eqn:e.
  rewrite rel_app_cons (lookup_hpv_spec hv' e).
  apply ih.
  eapply remember_pre_exchange; [| exact h ].
  rewrite rel_app_cons //.
Qed.

Lemma preserve_update_rel_3 :
  ∀ s l ls R R' (set get : seq heap_val) v,
  lookup_hpv l s set = None →
  ProvenBy (rem_inv s l v) (remember_pre get (rel_app ((s, l) :: ls) R)) →
  preserve_update_rel set get ls (R v) (R' v) →
  preserve_update_rel set get ((s, l) :: ls) R R'.
Proof.
  intros s l ls R R' set get v hv' hv ih.
  intros s0 s1 h.
  specialize (ih s0 s1).
  destruct update_heaps eqn:e.
  rewrite rel_app_cons (lookup_hpv_None_spec hv' e).
  apply hv in h as h'.
  rewrite h'.
  apply ih.
  eapply remember_pre_exchange; [| exact h ].
  rewrite rel_app_cons h' //.
Qed.

Lemma preserve_update_rel_4 :
  ∀ s l ls R R' (set get : seq heap_val),
  lookup_hpv l s set = None →
  (∀ v, preserve_update_rel set get ls (R v) (R' v)) →
  preserve_update_rel set get ((s, l) :: ls) R R'.
Proof.
  intros s l ls R R' set get hv' ih.
  intros s0 s1 h.
  specialize (ih (get_side (s0, s1) (s, l)) s0 s1).
  destruct update_heaps eqn:e.
  rewrite rel_app_cons (lookup_hpv_None_spec hv' e).
  apply ih.
  eapply remember_pre_exchange; [| exact h ].
  by rewrite rel_app_cons.
Qed.

#[export] Hint Resolve preserve_update_mem_rel
  : ssprove_invariant.

#[export] Hint Extern 2 (preserve_update_rel _ _ [::] _ _) =>
  eapply preserve_update_rel_nil; auto : ssprove_invariant.

#[export] Hint Extern 11 (preserve_update_rel _ _ _ _ _) =>
  eapply preserve_update_rel_1 ;
    [ reflexivity
    | exact _
    | rewrite coerceE
    ] : ssprove_invariant.

#[export] Hint Extern 12 (preserve_update_rel _ _ _ _ _) =>
  eapply preserve_update_rel_2 ;
    [ reflexivity
    | rewrite coerceE; intros ?
    ] : ssprove_invariant.

#[export] Hint Extern 13 (preserve_update_rel _ _ _ _ _) =>
  eapply preserve_update_rel_3 ;
    [ reflexivity
    | exact _
    | idtac
    ] : ssprove_invariant.

#[export] Hint Extern 14 (preserve_update_rel _ _ _ _ _) =>
  eapply preserve_update_rel_4 ;
    [ reflexivity
    | intros ?
    ] : ssprove_invariant.
