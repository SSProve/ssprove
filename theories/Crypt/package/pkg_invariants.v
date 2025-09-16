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


(* Locations Relation Invariants *)

Inductive Side :=
| lhs' (l : Location)
| rhs' (l : Location).

Definition loc s :=
  match s with
  | lhs' l => l
  | rhs' l => l
  end.

Coercion loc : Side >-> Location.

Fixpoint relType (ls : list Side) :=
  match ls with
  | l :: ls => l → relType ls
  | [::] => Prop
  end.

Definition get_side : heap * heap → ∀ l : Side, l
  := λ hh s, match s with
    | lhs' l => get_heap hh.1 l
    | rhs' l => get_heap hh.2 l
    end.

Fixpoint relApp {ls} : relType ls → precond :=
    match ls with
    | l :: ls => λ R s, relApp (R (get_side s l)) s
    | [::] => λ R _, R
    end.
Arguments relApp : clear implicits.

Fixpoint relEmpty {ls} : relType ls → Prop :=
    match ls with
    | l :: ls => λ R, relEmpty (R (heap_init l))
    | [::] => λ R, R
    end.
Arguments relEmpty : clear implicits.

Fixpoint relIn ls : Locations * Locations → Prop := λ L,
  match ls with
  | lhs' l :: ls => fhas L.1 l ∧ relIn ls L
  | rhs' l :: ls => fhas L.2 l ∧ relIn ls L
  | [::] => True
  end.

#[export] Hint Extern 10 (relIn [::] _) => done
  : ssprove_invariant.

#[export] Hint Extern 10 (relIn (_ :: _) _) =>
  split; [ solve [ fmap_solve ] |]
  : ssprove_invariant.

#[export] Hint Extern 10 (fsubmap _ _) =>
  solve [ fmap_solve ]
  : ssprove_invariant.

Lemma SemiInvariant_relApp :
  ∀ (L₀ L₁ : Locations) ls R,
    relIn ls (L₀, L₁) →
    relEmpty ls R →
    SemiInvariant L₀ L₁ (relApp ls R).
Proof.
  intros L₀ L₁ ls R Hin Hempty. split.
  2: {
    move=> {Hin}.
    induction ls.
    - apply Hempty.
    - apply IHls.
      destruct a; apply Hempty.
  }
  move=> {Hempty} s0 s1 l v H0 H1 H2.
  induction ls as [|s ls IHls]=> //.
  destruct s.
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

#[export] Hint Extern 10 (SemiInvariant _ _ (relApp _ _)) =>
  eapply SemiInvariant_relApp
  : ssprove_invariant.

Arguments relApp : simpl never.

Notation couple_lhs ℓ ℓ' R :=
  (relApp [:: lhs' ℓ; lhs' ℓ'] R).

Notation couple_rhs ℓ ℓ' R :=
  (relApp [:: rhs' ℓ; rhs' ℓ'] R).

Notation triple_rhs ℓ₁ ℓ₂ ℓ₃ R :=
  (relApp [:: rhs' ℓ₁; rhs' ℓ₂; rhs' ℓ₃] R).

Notation syncs l :=
  (relApp [:: lhs' l; rhs' l] eq).

(*** OLD ***)

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

Lemma relApp_nil {R : relType [::]} {s} : relApp [::] R s = R.
Proof. done. Qed.

Lemma relApp_cons {l ls} {R : relType (l :: ls)} {s}
  : relApp (l :: ls) R s = relApp ls (R (get_side s l)) s.
Proof. done. Qed.

Lemma put_pre_cond_rel_app :
  ∀ ℓ v (ls : list Side) h,
    ℓ.1 \notin map (fst \o loc) ls →
    put_pre_cond ℓ v (relApp ls h).
Proof.
  intros ℓ v ls R h s₀ s₁ hc.
  induction ls => //.
  rewrite 2!relApp_cons in hc |- *.
  rewrite /= in_cons negb_or in h.
  move: h => /andP [h h'].
  apply IHls => //.
  destruct a => /=.
  1,2: rewrite get_set_heap_neq // eq_sym //.
Qed.

#[export] Hint Extern 10 (put_pre_cond _ _ (relApp _ _)) =>
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

Definition rem_lhs ℓ v : precond :=
  λ '(s₀, s₁), get_heap s₀ ℓ = v.

Definition rem_rhs ℓ v : precond :=
  λ '(s₀, s₁), get_heap s₁ ℓ = v.

Inductive Remembers : ∀ ls, relType ls → Prop → precond → Prop :=
  | Remembers_nil : ∀ {R} pre, Remembers [::] R R pre
  | Remembers_cons_lhs : ∀ {l ls} {R P} {v} (pre : precond),
      ProvenBy (rem_lhs l v) pre →
      Remembers ls (R v) P pre →
      Remembers (lhs' l :: ls) R P pre
  | Remembers_cons_rhs : ∀ {l ls} {R P} {v} (pre : precond),
      ProvenBy (rem_rhs l v) pre →
      Remembers ls (R v) P pre →
      Remembers (rhs' l :: ls) R P pre.

Existing Class Remembers.

Hint Resolve Remembers_nil Remembers_cons_lhs Remembers_cons_rhs
  : typeclass_instances.

Lemma Remembers_lhs_from_tracked_rhs :
  ∀ ℓ v pre,
    ProvenBy (rem_rhs ℓ v) pre →
    ProvenBy (syncs ℓ) pre →
    ProvenBy (rem_lhs ℓ v) pre.
Proof.
  intros ℓ v pre hr ht.
  intros [s₀ s₁] hpre. simpl.
  specialize (hr _ hpre). specialize (ht _ hpre).
  rewrite /(syncs _) /= in ht.
  rewrite ht. apply hr.
Qed.

Lemma Remembers_rhs_from_tracked_lhs :
  ∀ ℓ v pre,
    ProvenBy (rem_lhs ℓ v) pre →
    ProvenBy (syncs ℓ) pre →
    ProvenBy (rem_rhs ℓ v) pre.
Proof.
  intros ℓ v pre hr ht.
  intros [s₀ s₁] hpre. simpl.
  specialize (hr _ hpre). specialize (ht _ hpre).
  rewrite /(syncs _) /= in ht.
  rewrite -ht. apply hr.
Qed.

Lemma Remembers_cons_from_rhs {l ls} {R P} {v} (pre : precond) :
    ProvenBy (rem_rhs l v) pre →
    ProvenBy (syncs l) pre →
    Remembers ls (R v) P pre →
    Remembers (lhs' l :: ls) R P pre.
Proof.
  intros hr hs hI.
  eapply Remembers_cons_lhs.
  - apply Remembers_lhs_from_tracked_rhs => //.
    apply hr.
  - apply hI.
Qed.

Lemma Remembers_cons_from_lhs {l ls} {R P} {v} (pre : precond) :
    ProvenBy (rem_lhs l v) pre →
    ProvenBy (syncs l) pre →
    Remembers ls (R v) P pre →
    Remembers (rhs' l :: ls) R P pre.
Proof.
  intros hl hs hI.
  eapply Remembers_cons_rhs.
  - apply Remembers_rhs_from_tracked_lhs => //.
    apply hl.
  - apply hI.
Qed.

Hint Resolve Remembers_cons_from_rhs Remembers_cons_from_lhs
  : typeclass_instances.

Lemma put_pre_cond_rem_lhs :
  ∀ ℓ v ℓ' v',
    ℓ'.1 != ℓ.1 →
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
    ℓ'.1 != ℓ.1 →
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

(* MK: better to not use Equations here? *)
Equations lookup_hpv_l (ℓ : Location) (l : seq heap_val) : option ℓ :=
  lookup_hpv_l ℓ (hpv_l ℓ' v' :: l) with inspect (ℓ.1 == ℓ'.1) := {
  | @exist true e => Some (coerce v')
  | @exist false e => lookup_hpv_l ℓ l
  } ;
  lookup_hpv_l ℓ (hpv_r _ _ :: l) := lookup_hpv_l ℓ l ;
  lookup_hpv_l ℓ [::] := None.

Equations lookup_hpv_r (ℓ : Location) (l : seq heap_val) : option ℓ :=
  lookup_hpv_r ℓ (hpv_r ℓ' v' :: l) with inspect (ℓ.1 == ℓ'.1) := {
  | @exist true e => Some (coerce v')
  | @exist false e => lookup_hpv_r ℓ l
  } ;
  lookup_hpv_r ℓ (hpv_l _ _ :: l) := lookup_hpv_r ℓ l ;
  lookup_hpv_r ℓ [::] := None.

Definition lookup_hpv (ℓ : Location) (s : side) (l : seq heap_val) : option ℓ :=
  match s with
  | lhs => lookup_hpv_l ℓ l
  | rhs => lookup_hpv_r ℓ l
  end.

Lemma lookup_hpv_l_eq :
  ∀ ℓ v l,
    lookup_hpv_l ℓ (hpv_l ℓ v :: l) = Some v.
Proof.
  intros ℓ v l.
  funelim (lookup_hpv_l ℓ (hpv_l ℓ v :: l)).
  - try rewrite -Heqcall. rewrite coerceE. reflexivity.
  - exfalso. pose proof e as e'. symmetry in e'. move: e' => /eqP e'.
    contradiction.
Qed.

Lemma lookup_hpv_l_neq :
  ∀ ℓ ℓ' v l,
    ℓ'.1 != ℓ.1 →
    lookup_hpv_l ℓ' (hpv_l ℓ v :: l) = lookup_hpv_l ℓ' l.
Proof.
  intros ℓ ℓ' v l hn.
  funelim (lookup_hpv_l ℓ' (hpv_l ℓ v :: l)).
  - exfalso. rewrite -e in hn. discriminate.
  - try rewrite -Heqcall. reflexivity.
Qed.

Lemma lookup_hpv_r_eq :
  ∀ ℓ v l,
    lookup_hpv_r ℓ (hpv_r ℓ v :: l) = Some v.
Proof.
  intros ℓ v l.
  funelim (lookup_hpv_r ℓ (hpv_r ℓ v :: l)).
  - try rewrite -Heqcall. rewrite coerceE. reflexivity.
  - exfalso. pose proof e as e'. symmetry in e'. move: e' => /eqP e'.
    contradiction.
Qed.

Lemma lookup_hpv_r_neq :
  ∀ ℓ ℓ' v l,
    ℓ'.1 != ℓ.1 →
    lookup_hpv_r ℓ' (hpv_r ℓ v :: l) = lookup_hpv_r ℓ' l.
Proof.
  intros ℓ ℓ' v l hn.
  funelim (lookup_hpv_r ℓ' (hpv_r ℓ v :: l)).
  - exfalso. rewrite -e in hn. discriminate.
  - try rewrite -Heqcall. reflexivity.
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
  - try rewrite -Heqcall in hl. noconf hl.
    simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    pose proof e as e'.
    symmetry in e'. move: e' => /eqP ?. subst.
    rewrite /get_heap setmE -e //=.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    try rewrite -Heqcall in hl. eauto.
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
  - try rewrite -Heqcall in hl. noconf hl.
    simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    pose proof e as e'.
    symmetry in e'. move: e' => /eqP ?. subst.
    rewrite /get_heap setmE -e //=.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    try rewrite -Heqcall in hl. eauto.
Qed.

Lemma lookup_hpv_spec :
  ∀ ℓ s v l s₀ s₁ h₀ h₁,
    lookup_hpv ℓ s l = Some v →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap (choose_heap h₀ h₁ s) ℓ = v.
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
  intros ℓ l s₀ s₁ h₀ h₁ hl e.
  funelim (lookup_hpv_l ℓ l).
  - simpl in e. noconf e. reflexivity.
  - simpl in *.
    destruct update_heaps eqn:e1. noconf e.
    eauto.
  - try rewrite -Heqcall in hl. noconf hl.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    try rewrite -Heqcall in hl. eauto.
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
  - try rewrite -Heqcall in hl. noconf hl.
  - simpl in e0.
    destruct update_heaps eqn:e1. noconf e0.
    rewrite get_set_heap_neq. 2:{ rewrite -e. auto. }
    try rewrite -Heqcall in hl. eauto.
Qed.

Lemma lookup_hpv_None_spec :
  ∀ ℓ s l s₀ s₁ h₀ h₁,
    lookup_hpv ℓ s l = None →
    update_heaps l s₀ s₁ = (h₀, h₁) →
    get_heap (choose_heap h₀ h₁ s) ℓ = get_heap (choose_heap s₀ s₁ s) ℓ.
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
  intros s₀ s₁ hh. unfold couple_lhs, get_side in *.
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
  intros s₀ s₁ hh. unfold couple_rhs, get_side in *.
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
  intros s₀ s₁ hh. unfold triple_rhs, get_side in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  erewrite lookup_hpv_r_spec. 2,3: eauto.
  auto.
Qed.

(* TODO MOVE? *)
(*
Fixpoint hpv_locRel (l : seq heap_val) ll (R : locRel ll) :=
  match ll return locRel ll → Prop with
  | (ℓ, s) :: ll =>
    λ R,
    match lookup_hpv ℓ s l with
    | Some v => hpv_locRel l ll (R v)
    | None => False
    end
  | [::] => λ R, R
  end R.

Lemma preserve_update_loc_rel_lookup :
  ∀ ll (R : locRel ll) (l : seq heap_val) m,
    hpv_locRel l ll R →
    preserve_update_mem l m (loc_rel ll R).
Proof.
  intros ll R l m h.
  intros s₀ s₁ hh.
  unfold loc_rel in *.
  induction ll as [| [ℓ si] ll ih] in R, l, h, s₀, s₁ |- *.
  - simpl. simpl in h.
    destruct update_heaps.
    assumption.
  - simpl in *.
    destruct lookup_hpv eqn:e1. 2: contradiction.
    destruct update_heaps eqn:e.
    erewrite lookup_hpv_spec. 2,3: eauto.
    specialize ih with (1 := h).
    specialize (ih s₀ s₁).
    rewrite e in ih. apply ih.
Qed.
 *)

Lemma preserve_update_couple_lhs_lookup_None :
  ∀ ℓ ℓ' (R : _ → _ → Prop) (l : seq heap_val) m,
    lookup_hpv_l ℓ l = None →
    lookup_hpv_l ℓ' l = None →
    preserve_update_mem l m (couple_lhs ℓ ℓ' R).
Proof.
  intros ℓ ℓ' R l m h h'.
  intros s₀ s₁ hh. unfold couple_lhs, get_side in *.
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
  intros s₀ s₁ hh. unfold couple_rhs, get_side in *.
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
  intros s₀ s₁ hh. unfold triple_rhs, get_side in *.
  destruct update_heaps eqn:e.
  erewrite lookup_hpv_r_None_spec. 2,3: eauto.
  erewrite lookup_hpv_r_None_spec with (ℓ := ℓ₂). 2,3: eauto.
  erewrite lookup_hpv_r_None_spec with (ℓ := ℓ₃). 2,3: eauto.
  eapply remember_pre_pre in hh.
  auto.
Qed.

(*
Lemma preserve_update_loc_rel_lookup_None :
  ∀ ll (R : locRel ll) (l : seq heap_val) m,
    List.forallb (λ '(ℓ, s), ~~ isSome (lookup_hpv ℓ s l)) ll →
    preserve_update_mem l m (loc_rel ll R).
Proof.
  intros ll R l m h.
  intros s₀ s₁ hh.
  unfold loc_rel in *.
  eapply remember_pre_pre in hh.
  induction ll as [| [ℓ si] ll ih] in R, l, h, s₀, s₁, hh |- *.
  - simpl. simpl in hh.
    destruct update_heaps.
    assumption.
  - simpl in *.
    move: h => /andP [hl h].
    destruct lookup_hpv eqn:e1. 1: discriminate.
    destruct update_heaps eqn:e.
    erewrite lookup_hpv_None_spec. 2,3: eauto.
    specialize ih with (1 := h).
    specialize ih with (1 := hh).
    rewrite e in ih. apply ih.
Qed.
 *)
