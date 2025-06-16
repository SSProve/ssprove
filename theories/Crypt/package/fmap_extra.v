From Coq Require Import Utf8.

From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

From extructures Require Import ord fset fmap.

#[local] Open Scope fset.

(******************************************************************************)
(* Extra definitions and lemmas about fmap from extructures.                  *)
(* This file also provides fmap_solve, which automates proofs of the defs.    *)
(* below using auto based on the hint database fmap_solve_db. fmap_solve has  *)
(* some support for symbolic terms, but generally does not deconstruct        *)
(* assumptions in the context. More hints may be added to extend the solver.  *)
(* Definitions:                                                               *)
(*             fhas m kv == the key-value pair kv is present in m             *)
(*          fsubmap m m' == m is a submap of m' i.e. when m has value v at    *)
(*                          key k, then m' has value v at key k.              *)
(*          fcompat m m' == if both maps define a key it has the same value   *)
(*        fseparate m m' == maps m and m' define a disjoint set of keys.      *)
(*                          Separation of maps implies compatability.         *)
(******************************************************************************)

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(* Note that fsubmap is defined into Prop unlike other extructures operators.
   A bool definition would require S to be an eqType, which would make it
   hard to have maps into e.g. Type or choiceType. *)
Definition fsubmap {T : ordType} {S} (m m' : {fmap T → S}) : Prop
  := unionm m m' = m'.

Definition fhas {T : ordType} {S} (m : {fmap T → S}) kv
  := let '(k, v) := kv in (m k = Some v).

Lemma fhas_fsubmap {T : ordType} {S} (m m' : {fmap T → S})
  : (∀ kv, fhas m kv → fhas m' kv) ↔ fsubmap m m'.
Proof.
  split.
  - intros H.
    apply eq_fmap => t.
    rewrite unionmE.
    destruct (m t) eqn:E => //.
    specialize (H (t, s) E).
    rewrite H //.
  - intros H [t s] H'.
    rewrite -H //=.
    rewrite unionmE H' //=.
Qed.

Lemma fsubmap_fhas {T : ordType} {S} (m m' : {fmap T → S}) kv
  : fsubmap m m' → fhas m kv → fhas m' kv.
Proof. rewrite -fhas_fsubmap. auto. Qed.


Definition fcompat {T : ordType} {S} (m m' : {fmap T → S}) :=
  unionm m m' = unionm m' m.

Lemma fsubmapUl {T : ordType} {S} (m m' : {fmap T → S}) :
  fsubmap m (unionm m m').
Proof.
  apply eq_fmap => t.
  rewrite 2!unionmE.
  destruct (m t), (m' t) => //.
Qed.

Lemma fsubmapUr {T : ordType} {S} (m m' : {fmap T → S}) :
  fcompat m m' → fsubmap m' (unionm m m').
Proof.
  move=> ->.
  apply eq_fmap => t.
  rewrite 2!unionmE.
  destruct (m t), (m' t) => //.
Qed.

Lemma fsubmap_trans {T : ordType} {S} (m m' m'' : {fmap T → S}) :
  fsubmap m m' → fsubmap m' m'' → fsubmap m m''.
Proof.
  intros H H'.
  apply eq_fmap => t.
  rewrite -{2}H' -H -unionmA H' //.
Qed.

Lemma fsubmapUl_trans {T : ordType} {S} (m m' m'' : {fmap T → S}) :
  fsubmap m m' → fsubmap m (unionm m' m'').
Proof.
  intros H. eapply fsubmap_trans;
  [ apply H | apply fsubmapUl ].
Qed.

Lemma fsubmapUr_trans {T : ordType} {S} (m m' m'' : {fmap T → S}) :
  fcompat m' m'' → fsubmap m m'' → fsubmap m (unionm m' m'').
Proof.
  intros H H'. eapply fsubmap_trans;
  [ apply H' | apply fsubmapUr, H ].
Qed.

Lemma fsubUmap {T : ordType} {S} (m m' m'' : {fmap T → S}) :
  fsubmap m m'' → fsubmap m' m'' → fsubmap (unionm m m') m''.
Proof.
  intros H H'.
  rewrite /fsubmap -unionmA H' H //.
Qed.

Lemma fsub0map {T : ordType} {S} (m : {fmap T → S}) : fsubmap emptym m.
Proof. rewrite /fsubmap union0m //. Qed.

Lemma fsubmap_fcompat {T : ordType} {S} (m m' m'' : {fmap T → S}) :
  fsubmap m' m → fsubmap m'' m → fcompat m' m''.
Proof.
  intros H H'.
  apply eq_fmap in H, H'.
  apply eq_fmap => t.
  specialize (H t).
  rewrite unionmE in H.
  specialize (H' t).
  rewrite unionmE in H'.
  rewrite 2!unionmE.
  destruct (m' t), (m'' t) => //.
  rewrite H H' //.
Qed.

Lemma fhas_in {T : ordType} {S} (m : {fmap T → S}) ts
  : fhas m ts → ts.1 \in domm m.
Proof.
  move: ts => [t s] H.
  apply /dommP.
  by exists s.
Qed.

Lemma fhas_empty {T : ordType} {S} k : ¬ fhas (@emptym T S) k.
Proof. by destruct k. Qed.

Lemma fhas_set {T : ordType} {S} k v (m : {fmap T → S}) :
  fhas (setm m k v) (k, v).
Proof. rewrite //= setmE eq_refl //. Qed.

Lemma fhas_set_next {T : ordType} {S} (m : {fmap T → S}) k k' v v' :
  k ≠ k' → fhas m (k, v) → fhas (setm m k' v') (k, v).
Proof.
  move=> /eqP H H'.
  rewrite //= setmE.
  destruct (k == k') => //.
Qed.

Lemma fsubmapxx {T : ordType} {S} (m : {fmap T → S}) : fsubmap m m.
Proof. rewrite /fsubmap unionmI //. Qed.

Lemma fsubmap_implies_fcompat :
  forall {T : ordType} {S} {E E' : _},
    fsubmap E' E →
    fcompat (T := T) (S := S) E' E.
Proof.
  intros.
  eapply fsubmap_fcompat.
  1: apply H.
  apply fsubmapxx.
Qed.

Lemma fsubmap_eq {T : ordType} {S} (m m' : {fmap T → S}) :
  fsubmap m m' → fsubmap m' m → m = m'.
Proof.
  unfold fsubmap.
  intros H H'.
  rewrite -H -{1}H'.
  eapply fsubmap_fcompat.
  1: apply H'.
  apply fsubmapxx.
Qed.

Lemma fhas_set_case {T : ordType} {S} x y (m : {fmap T → S}) :
  fhas (setm m x.1 x.2) y → (x = y) ∨ fhas m y.
Proof.
  move: x y => [k v] [k' v'] H.
  rewrite /fhas //= setmE in H.
  destruct (k' == k) eqn:E.
  - left.
    move: E => /eqP -> {k'}.
    by noconf H.
  - by right.
Qed.

Lemma fhas_union {S : ordType} {T} m m' (k : S) (v : T)
  : fhas (unionm m m') (k, v) → fhas m (k, v) ∨ fhas m' (k, v).
Proof.
  rewrite /fhas unionmE.
  destruct (m k) => //=; auto.
Qed.

Lemma fhas_union_l {S : ordType} {T} m m' (k : S) (v : T)
  : fhas m (k, v) → fhas (unionm m m') (k, v).
Proof.
  rewrite /fhas unionmE.
  destruct (m k) => //=; auto.
Qed.


(* Tactics *)

Ltac fmap_invert H :=
  (by apply fhas_empty in H) ||
  ( let x := fresh "x" in
    apply fhas_set_case in H ;
    destruct H as [x|H]; [ noconf x | fmap_invert H ]
  ).

Create HintDb fmap_solve_db.

#[export] Hint Extern 2 (fhas ?m ?k) =>
  apply fhas_set
  : fmap_solve_db.

#[export] Hint Extern 3 (fhas ?m ?k) =>
  apply fhas_set_next; [ done |]
  : fmap_solve_db.

#[export] Hint Resolve fsubmapUl_trans fsubmapUr_trans
  : fmap_solve_db.

#[export] Hint Extern 1 (fcompat ?m ?m') =>
  reflexivity
  : fmap_solve_db.

Hint Extern 1 (fsubmap ?m ?m') =>
  apply fsubmapxx
  : fmap_solve_db.


Ltac fmap_solve :=
  typeclasses eauto with fmap_solve_db.


Definition fcompat11 {T : ordType} {S} (x x' : T * S)
  := x.1 ≠ x'.1 ∨ x.2 = x'.2.

Lemma fcompat0m {T : ordType} {S} (m : {fmap T → S})
  : fcompat emptym m.
Proof. rewrite /fcompat unionm0 //. Qed.

Lemma fcompatm0 {T : ordType} {S} (m : {fmap T → S})
  : fcompat m emptym.
Proof. rewrite /fcompat unionm0 //. Qed.

Lemma fcompat11_swap {T : ordType} {S} (x y : T * S) m
  : fcompat11 x y
  → setm (setm m y.1 y.2) x.1 x.2 = setm (setm m x.1 x.2) y.1 y.2.
Proof.
  intros [H|H].
  - rewrite setmC //.
    rewrite eq_sym; by apply /eqP.
  - destruct (y.1 == x.1) eqn:E.
    + move: E H => /eqP.
      destruct x, y => //= H H'.
      subst. rewrite setmI // setmE eq_refl //.
    + rewrite setmC // E //.
Qed.

Lemma fcompat_cons1 {T : ordType} {S} (x : T * S) y ys
  : fcompat11 x y
  → fcompat [fmap x] (mkfmap ys)
  → fcompat [fmap x] (mkfmap (y :: ys)).
Proof.
  intros H H'.
  rewrite /fcompat //= -setm_union union0m.
  rewrite -setm_union -H'.
  rewrite (fcompat11_swap _ _ _ H) //.
Qed.

Lemma fcompat_cons {T : ordType} {S} (x x' : T * S) xs ys
  : fcompat [fmap x] (mkfmap ys)
  → fcompat (mkfmap (x' :: xs)) (mkfmap ys)
  → fcompat (mkfmap (x :: x' :: xs)) (mkfmap ys).
Proof.
  intros H H'.
  rewrite /fcompat //= -setm_union H'.
  rewrite /fcompat -setm_union union0m in H.
  rewrite setm_union H -unionmA //.
Qed.

Hint Extern 1 (fcompat11 ?m ?m') =>
  (by left) || (by right)
  : fmap_solve_db.

Hint Resolve fcompat_cons1 fcompat_cons fcompatm0 fcompat0m : fmap_solve_db.

Lemma union_fcompat {T : ordType} {S} (m m' m'' : {fmap T →  S})
  : fcompat m m''
  → fcompat m' m''
  → fcompat (unionm m m') m''.
Proof.
  intros H H'.
  rewrite /fcompat unionmA -H -unionmA H' unionmA //.
Qed.

Lemma fcompat_union {T : ordType} {S} (m m' m'' : {fmap T →  S})
  : fcompat m m'
  → fcompat m m''
  → fcompat m (unionm m' m'').
Proof.
  intros H H'.
  rewrite /fcompat unionmA H -unionmA H' unionmA //.
Qed.

Hint Resolve union_fcompat fcompat_union : fmap_solve_db.


Lemma fsubmap_set {T : ordType} {S} (k : T) (v : S) m m'
  : fhas m' (k, v)
  → fsubmap m m'
  → fsubmap (setm m k v) m'.
Proof.
  intros H H'.
  rewrite /fsubmap -setm_union H' setmI //.
Qed.

Hint Resolve fsub0map fsubUmap fsubmap_set : fmap_solve_db.



Inductive fseparate {T : ordType} {S S' : Type}
  (m : {fmap T → S}) (m' : {fmap T → S'}) :=
  | fsep : domm m :#: domm m' → fseparate m m'.

Lemma fseparateUl {T : ordType} {S S' : Type}
  (m m' : {fmap T → S}) (m'' : {fmap T → S'})
  : fseparate m m'' → fseparate m' m'' → fseparate (unionm m m') m''.
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite domm_union fdisjointUl H H' //.
Qed.

Lemma fseparateUr {T : ordType} {S S'}
  (m : {fmap T → S}) (m' m'' : {fmap T → S'})
  : fseparate m m' → fseparate m m'' → fseparate m (unionm m' m'').
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite domm_union fdisjointUr H H' //.
Qed.

Lemma fseparate_set {T : ordType} {S S'} (k k' : T) (v v' : S)
  (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate (setm emptym k v) m'
  → fseparate (setm m k' v') m'
  → fseparate (setm (setm m k' v') k v) m'.
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite domm_set domm0 fsetU0 in H.
  rewrite domm_set fdisjointUl H' H //.
Qed.

Lemma fseparate_set1 {T : ordType} {S S'} (k k' : T)
  (v : S) (v' : S') (m' : {fmap T → S'})
  : k ≠ k'
  → fseparate (setm emptym k v) m'
  → fseparate (setm emptym k v) (setm m' k' v').
Proof.
  intros H [H'].
  apply fsep.
  rewrite domm_set domm0 fsetU0 in H'.
  rewrite 2!domm_set domm0 fsetU0 fdisjointUr H'.
  apply /andP; split => //.
  apply /fdisjointP => x /fset1P -> {x}.
  apply /negP => /fset1P //.
Qed.

Lemma fseparate0m {T : ordType} {S S'} (m : {fmap T → S'})
  : fseparate (@emptym T S) m.
Proof. apply fsep. rewrite domm0 fdisjoint0s //. Qed.

Lemma fseparatem0 {T : ordType} {S S'} (m : {fmap T → S})
  : fseparate m (@emptym T S').
Proof. apply fsep. rewrite domm0 fdisjoints0 //. Qed.

Lemma fseparateE {T : ordType} {S S'} (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → domm m :#: domm m'.
Proof. by intros [?]. Qed.

Lemma fseparateMl {T : ordType} {S S' S'' : Type}
  (f : S → S') (m : {fmap T → S}) (m' : {fmap T → S''})
  : fseparate m m' → fseparate (mapm f m) m'.
Proof. intros [H]. apply fsep. rewrite domm_map //. Qed.

Lemma fseparateMil {T : ordType} {S S' S'' : Type}
  (f : T → S → S') (m : {fmap T → S}) (m' : {fmap T → S''})
  : fseparate m m' → fseparate (mapim f m) m'.
Proof. intros [H]. apply fsep. rewrite domm_mapi //. Qed.

Lemma fseparateMr {T : ordType} {S S' S'' : Type}
  (f : S' → S'') (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → fseparate m (mapm f m').
Proof. intros [H]. apply fsep. rewrite domm_map //. Qed.

Lemma fseparateMir {T : ordType} {S S' S'' : Type}
  (f : T → S' → S'') (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → fseparate m (mapim f m').
Proof. intros [H]. apply fsep. rewrite domm_mapi //. Qed.

Lemma notin_fseparate {T : ordType} {S S'} (x : T * S) (m : {fmap T → S'})
  : fseparate [fmap x] m → x.1 \notin domm m.
Proof.
  move=> [] /fdisjointP H.
  apply H.
  rewrite domm_set in_fsetU1 eq_refl //.
Qed.


Hint Extern 2 (?x ≠ ?y) =>
  done : fmap_solve_db.

Hint Resolve fseparateE fseparate0m fseparatem0 : fmap_solve_db.
Hint Resolve fseparateUl fseparateUr : fmap_solve_db.
Hint Resolve fseparateMl fseparateMr : fmap_solve_db.
Hint Resolve fseparateMil fseparateMir : fmap_solve_db.
Hint Resolve notin_fseparate fseparate_set fseparate_set1 : fmap_solve_db.


(* case over booleans *)

Lemma fsubmap_case_l {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fsubmap m m'' → fsubmap m' m'' → fsubmap (if b then m else m') m''.
Proof. by move: b => []. Qed.

Lemma fsubmap_case_r {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fsubmap m m' → fsubmap m m'' → fsubmap m (if b then m' else m'').
Proof. by move: b => []. Qed.

Hint Resolve fsubmap_case_l fsubmap_case_r : fmap_solve_db.

Lemma fcompat_case_l {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fcompat m m'' → fcompat m' m'' → fcompat (if b then m else m') m''.
Proof. by move: b => []. Qed.

Lemma fcompat_case_r {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fcompat m m' → fcompat m m'' → fcompat m (if b then m' else m'').
Proof. by move: b => []. Qed.

Hint Resolve fcompat_case_l fcompat_case_r : fmap_solve_db.

Lemma fseparate_case_l {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fseparate m m'' → fseparate m' m'' → fseparate (if b then m else m') m''.
Proof. by move: b => []. Qed.

Lemma fseparate_case_r {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fseparate m m' → fseparate m m'' → fseparate m (if b then m' else m'').
Proof. by move: b => []. Qed.

Hint Resolve fseparate_case_l fseparate_case_r : fmap_solve_db.


Lemma fseparate_compat {T : ordType} {S : Type} (m m' : {fmap T → S})
  : fseparate m m' → fcompat m m'.
Proof. intros [H]. rewrite /fcompat unionmC //. Qed.
(* danger of two solution paths? (more expensive search) *)
Hint Resolve fseparate_compat : fmap_solve_db.

Lemma fcompatC {T : ordType} {S : Type} (m m' : {fmap T → S})
  : fcompat m m' → fcompat m' m.
Proof. done. Qed.

Lemma fseparateC {T : ordType} {S S' : Type}
  (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → fseparate m' m.
Proof. intros [H]. apply fsep. rewrite fdisjointC //. Qed.

Lemma fseparate_trans_l {T : ordType} {S S' : Type}
  (m m'' : {fmap T → S}) (m' : {fmap T → S'})
  : fsubmap m m'' → fseparate m'' m' → fseparate m m'.
Proof.
  unfold fsubmap.
  intros H [H'].
  apply fsep.
  eapply (fdisjoint_trans _ H').
  Unshelve.
  rewrite -H domm_union fsubsetUl //.
Qed.

Lemma fseparate_trans_r {T : ordType} {S S' : Type}
  (m : {fmap T → S}) (m' m'' : {fmap T → S'})
  : fsubmap m' m'' → fseparate m m'' → fseparate m m'.
Proof.
  unfold fsubmap.
  intros H [H'].
  apply fsep.
  rewrite fdisjointC in H'.
  rewrite fdisjointC.
  eapply (fdisjoint_trans _ H').
  Unshelve.
  rewrite -H domm_union fsubsetUl //.
Qed.

Hint Extern 4 (fcompat _ _) =>
  apply fcompatC; done : fmap_solve_db.

Hint Extern 4 (fseparate _ _) =>
  apply fseparateC; done : fmap_solve_db.

Lemma notin_has_separate {T : ordType} {S : Type} (m m' : {fmap T → S}) (l : T * S)
  : fhas m l → fseparate m m' → l.1 \notin domm m'.
Proof.
  move=> H [H'].
  apply fhas_in in H.
  apply /fdisjointP; eassumption.
Qed.

Hint Extern 4 (is_true (_ \notin _)) =>
  eapply notin_has_separate; [ eassumption | ] : fmap_solve_db.

Lemma fmap_as_list :
  forall {T : ordType} {S} (p2 : {fmap T -> S}),
  exists l, mkfmap l = p2.
Proof.
  destruct p2.
  exists fmval.
  - apply eq_fmap.
    apply mkfmapE.
Qed.

Lemma fmapK_list :
  forall {T : ordType} {S} (p2 : {fmap T -> S}),
  mkfmap (FMap.fmval p2) = p2.
Proof.
  destruct p2.
  apply eq_fmap.
  apply mkfmapE.
Qed.

Lemma in_cat :
  forall (X : eqType) l1 l2, forall (x : X), (x \in (l1 ++ l2)) = ((x \in l1) || (x \in l2)).
Proof.
  intros.
  generalize dependent l1.
  induction l2 ; intros.
  + setoid_rewrite List.app_nil_r.
    now rewrite Bool.orb_false_r.
  + replace (l1 ++ _) with ((l1 ++ [:: a]) ++ l2).
    2:{
      rewrite <- List.app_assoc.
      reflexivity.
    }
    rewrite IHl2.
    rewrite in_cons.
    induction l1.
    * simpl.
      rewrite in_cons.
      rewrite in_nil.
      now rewrite Bool.orb_false_r.
    * simpl.
      rewrite !in_cons.
      rewrite <- !orbA.
      now rewrite IHl1.
Qed.

Lemma fdisjoint_weak : (forall {T : ordType}, forall (A B C : {fset T}), A :#: B -> A :#: (B :\: C)).
Proof.
  intros.
  apply /fsetDidPl.
  rewrite fsetDDr.
  move /fsetDidPl: H ->.
  apply eq_fset.
  intros i.
  rewrite in_fset.
  simpl.
  rewrite in_cat.
  rewrite in_fsetI.
  destruct (i \in A) eqn:i_in ; now rewrite i_in.
Qed.

Lemma fsubmap_split :
  forall {T : ordType} {S}, forall (A B : {fmap T -> S}), fsubmap A B -> exists C, unionm A C = B /\ fseparate A C.
Proof.
  clear ; intros.
  exists (filterm (fun x y => x \notin domm A) B).

  assert (unionm A (filterm (λ (x : T) (_ : S), x \notin domm A) B) = B).
  {
    apply eq_fmap.
    intros ?.
    rewrite unionmE.
    destruct (A x) eqn:Ahas.
    + simpl.
      symmetry.
      apply (fsubmap_fhas _ _ (x, s) H Ahas).
    + simpl.
      rewrite filtermE.
      unfold obind, oapp.
      move /dommPn: Ahas ->.
      now destruct (B x).
  }
  split.
  - apply H0.
  - simpl.
    rewrite <- (fmapK_list B) in H, H0 |- *.
    destruct B ; simpl in *.
    simpl.
    constructor.
    clear i H H0.
    induction fmval.
    + rewrite filterm0.
      rewrite domm0.
      apply fdisjoints0.
    + simpl.
      rewrite filterm_set.

      destruct (a.1 \notin domm A) eqn:a_not_in_A.
      2: rewrite domm_rem ; apply fdisjoint_weak.
      1: rewrite domm_set ; rewrite fdisjointUr ; rewrite fdisjoints1 ; rewrite a_not_in_A ; simpl.
      1,2: apply IHfmval.
Qed.
