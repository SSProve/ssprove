From Coq Require Import Utf8.

From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

From extructures Require Import ord fset fmap.

#[local] Open Scope fset.

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

Lemma fhas_cons {T : ordType} {S} x' x (xs : seq (T * S)) :
  fhas (mkfmap (x :: xs)) x' → x = x' ∨ fhas (mkfmap xs) x'.
Proof.
  move: x x' => [t s] [t' s'] H.
  rewrite /fhas //= setmE in H.
  destruct (t' == t) eqn:E.
  - left.
    move: E => /eqP -> {t'}.
    by noconf H.
  - by right.
Qed.

(* Tactics *)

Ltac fmap_invert H :=
  (by apply fhas_empty in H) ||
  ( let x := fresh "x" in
    apply fhas_cons in H ;
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

(*
Goal ((3, 5).1 \notin domm [fmap (5,6); (6,8)]).
Proof.
  fmap_solve.
Qed.
 *)

  (*

  Lemma fcompat_11 {T : ordType} {S} (x : T * S) y
    : fcompat11 x y → fcompat [fmap x] [fmap y].
  Proof.
  Hint Resolve fcompat_11 : fmap_solve_db.
   *)
