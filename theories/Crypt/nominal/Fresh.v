Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap ffun fperm.

From HB Require Import structures.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Import Nominal.

(******************************************************************************)
(* This file provides the definition for working with fresh atoms.            *)
(* `neu` chooses a fresh atom in the context of a set of atoms.               *)
(* Using `neu` we show fset itself to be a nominal set.                       *)
(* `fresh` given arguments x and y produces a permutation such that when it   *)
(* is applied to y, its support is disjoint from x.                           *)
(* `split_pi` combines two permutations and preserves the behaviour on both   *)
(* when they are sufficiently separated.                                      *)
(******************************************************************************)


(* offset *)

Definition offset : {fset atom} → nat
  := λ A, \max_(a <- A) succn (natize a).

Lemma offset_fset0 : offset fset0 = 0%N.
Proof. rewrite /offset finmap.big_seq_fset0 //. Qed.

Lemma offset_fsetU1 {a} {A}
  : offset (a |: A)%fset = maxn (natize a).+1 (offset A).
Proof.
  rewrite /offset big_idem_fsetU1 //=.
  apply maxnn.
Qed.

Lemma offset_fsetU {A B}
  : offset (A :|: B)%fset = maxn (offset A) (offset B).
Proof.
  rewrite /offset big_idem_fsetU //=.
  apply maxnn.
Qed.

Lemma ltn_offset : ∀ {A : {fset atom}} {a}, a \in A → (natize a < offset A)%N.
Proof.
  refine (fset_ind _ _); simpl.
  { intros a H. rewrite in_fset0 in H. discriminate. }
  move => a A H IH a'.
  rewrite in_fsetU in_fset1 offset_fsetU1.
  move => /orP [H'|H'].
  + move: H' => /eqP H'.
    subst.
    apply leq_maxl.
  + eapply leq_trans.
    - by apply IH.
    -  apply leq_maxr.
Qed.


(* fresh *)

Definition fresh {X Y : nomType} (x : X) (y : Y) : {fperm atom} :=
  fperm (λ a, atomize (offset (supp x) + natize a)) (supp y).

Lemma fresh_disjoint {X Y : nomType} {x : X} {y : Y}
  : disj x (fresh x y ∙ y).
Proof.
  rewrite /disj -supp_equi.
  rewrite adjoin_disc_r; [| apply: fdisjoint_equi ].
  apply /fdisjointP => a H.
  rewrite -(adjoin_disc_l in_mem_equi) in H.
  apply ltn_offset in H.
  apply /negP => H'.
  rewrite /rename //= in H.
  rewrite fpermE //= in H.
  + rewrite -{2}(addn0 (offset (supp x))) in H.
    rewrite ltn_add2l in H.
    rewrite ltn0 // in H.
  + apply in2W.
    eapply can_inj.
    eapply (can_comp atomizeK).
    eapply (can_comp (addKn _)).
    eapply natizeK.
Qed.

Lemma supp_fsubset {X Y : nomType} : ∀{f : X → Y}, equivariant f → ∀ x, fsubset (supp (f x)) (supp x).
Proof.
  intros f Ef x.
  apply support_sub.
  apply equi_support_set; [ done |].
  apply is_support.
Qed.

Lemma disjC {X Y : nomType} : ∀ (x : X) (y : Y), disj x y = disj y x.
Proof.
  move => x y.
  rewrite /disj fdisjointC //.
Qed.

Lemma equi_disj {X Y Z: nomType} (f : X → Z) {E : equivariant f}
  : ∀ (x : X) (y : Y), disj x y → disj (f x) y.
Proof.
  move => x y.
  unfold disj.
  intros H.
  eapply fdisjointSl.
  + by apply supp_fsubset.
  + apply H.
Qed.


Program Definition atom_IsNominal
  : IsNominal atom
  := IsNominal.Build _ (λ a, fset1 a) _ _.
Obligation 1.
  intros π H.
  apply H.
  rewrite in_fset1 //.
Qed.
Obligation 2.
  rewrite fsub1set.
  unfold support_set in H.
  apply /negP => H'.
  pose (a' := atomize (offset (x |: F)%fset)).
  specialize (H (fperm2 x a')).
  setoid_rewrite fperm2L in H.
  assert (H'' :  ∀ a, a \in F → fperm2 x a' a = a).
  { intros y H''.
    rewrite fperm2D //.
    + apply /negP => /eqP E.
      subst.
      apply H', H''.
    + apply /negP => /eqP E.
      subst.
      apply ltn_offset in H''.
      rewrite /a' atomizeK offset_fsetU1 in H''.
      rewrite gtn_max ltnn Bool.andb_false_r // in H''.
  }
  specialize (H H'').
  assert (natize x < natize a').
  { rewrite atomizeK.
    apply ltn_offset.
    rewrite in_fsetU1 eq_refl //.
  }
  rewrite H ltnn // in H0.
Qed.

HB.instance Definition _ : IsNominal atom
  := atom_IsNominal.

Lemma support_set_imp {X : nomType} {x : X} {F} {a} {a'}
  : support_set x F → a \notin F → a' \notin F → fperm2 a a' ∙ x = x.
Proof.
  intros SS Ha Ha'.
  apply SS.
  intros a'' H.
  rewrite fperm2D //.
  1,2: apply /negP => /eqP E.
  1,2: subst.
  1: move: Ha => /negP Ha; apply Ha.
  2: move: Ha' => /negP Ha'; apply Ha'.
  1,2: apply H.
Qed.

Definition neu F := atomize (offset F).

Lemma support_set_neu {X : nomType} {x : X} {F} {a}
  : support_set x F → a \notin F → fperm2 a (neu F) ∙ x = x.
Proof.
  intros H H'.
  apply (support_set_imp (F:=F)); try done.
  apply /negP => H''.
  apply ltn_offset in H''.
  rewrite /neu atomizeK ltnn // in H''.
Qed.


Lemma neuE {A B} : (B :<=: A)%fset → neu A \notin B.
Proof.
  move => /fsubsetP H.
  apply /negP => H'.
  specialize (H _ H').
  apply ltn_offset in H.
  rewrite atomizeK ltnn // in H.
Qed.

(* nomType for {fset X} *)

Definition fsetSupp {X : nomOrdType} (xs : {fset X}) := (\bigcup_(x <- xs) (supp x))%fset.

Lemma fsetSuppU {X : nomOrdType} (x y : {fset X})
  : (fsetSupp (x :|: y) = fsetSupp x :|: fsetSupp y)%fset.
Proof. apply bigcup_fsetU. Qed.

Lemma fsetSupp0 {X : nomOrdType} : fsetSupp (@fset0 X) = fset0.
Proof.
  unfold fsetSupp.
  apply eq_fset => a.
  apply /bigcupP.
  move => [].
  discriminate.
Qed.

Lemma fsetSupp1 {X : nomOrdType} (x : X) : fsetSupp (fset1 x) = supp x.
Proof.
  unfold fsetSupp.
  rewrite -(fsetU0 (fset1 x)).
  rewrite bigcup_fsetU1.
  rewrite -{2}(fsetU0 (supp x)).
  f_equal.
  apply fsetSupp0.
Qed.

Lemma fsetSuppE {X : nomOrdType} : equivariant (@fsetSupp X).
Proof.
  intros π.
  refine (fset_ind _ _).
  { rewrite /rename //= fsetSupp0 2!imfset0 fsetSupp0 //. }
  intros x xs _ IH.
  rewrite (equi2_use _ fsetU_equi) fset1_equi.
  rewrite 2!fsetSuppU 2!fsetSupp1.
  rewrite (equi2_use _ fsetU_equi) supp_equi IH //.
Qed.

Lemma offset_mono {A B : {fset atom}}
  : (A :<=: B)%fset → offset A <= offset B.
Proof.
  move: A.
  refine (fset_ind _ _); simpl.
  { intros H. rewrite offset_fset0 leq0n //. }
  intros a A _ IH H.
  rewrite offset_fsetU1.
  rewrite geq_max.
  rewrite fsubU1set in H.
  move: H => /andP [H1 H2].
  rewrite IH //.
  rewrite ltn_offset //.
Qed.

Lemma fsubset_equi {X : actionType} {x : X} {F} {f : X → {fset atom}}
  : equivariant f → support_set x F → (f x :<=: F)%fset.
Proof.
  intros H H'.
  apply /fsubsetP => a.
  apply boolp.contraPP => /negP H''.
  apply (equi_support_set H) in H'.
  specialize (H' (fperm2 a (neu (a |: F :|: f x)%fset))).
  rewrite -H'.
  2: {
    intros a' H'''.
    rewrite fperm2D //.
    + apply /negP => /eqP E.
      subst.
      move: H'' => /negP H''.
      contradiction.
    + apply /negP => /eqP E.
      subst.
      apply ltn_offset in H'''.
      rewrite atomizeK in H'''.
      eapply leq_ltn_trans in H'''.
      2: eapply offset_mono.
      2: eapply fsubset_trans.
      3: eapply fsubsetUl.
      2: eapply fsubsetUr.
      rewrite ltnn // in H'''.
  }
  rewrite (adjoin_disc_r in_mem_equi).
  rewrite fperm2V /rename //= fperm2L.
  apply /negP.
  apply neuE.
  apply fsubsetU.
  rewrite fsubsetxx.
  apply /orP; by right.
Qed.

Lemma suppP {π : {fperm atom}} {F} : reflect (∀ a, a \in F → π a = a) (F :#: ffun.supp π)%fset.
Proof.
  apply (iffP fdisjointP) => H a H'; apply /suppPn; by apply H.
Qed.


Program Definition fset_IsNominal {X : nomOrdType}
  : IsNominal {fset X}
  := IsNominal.Build _ (λ x : {fset X}, fsetSupp x) _ _.
Obligation 1.
  move: x.
  refine (fset_ind _ _).
  { intros π. rewrite /rename //= imfset0 //. }
  move => x xs _ IH π /suppP H.
  rewrite (equi2_use _ fsetU_equi) fset1_equi.
  rewrite fsetSuppU fsetSupp1 fdisjointUl in H.
  move: H => /andP [H1 H2].
  move: H1 => /suppP H1.
  move: H2 => /suppP H2.
  rewrite is_support //.
  rewrite IH //.
Qed.
Obligation 2.
  apply fsubset_equi.
  + apply fsetSuppE.
  + apply H.
Qed.

HB.instance Definition _ {X : nomOrdType} : IsNominal {fset X}
  := fset_IsNominal.

Open Scope fset.

Definition split_fun (f g : {fperm atom}) (F : {fset atom})
  := λ x, if x \in F then f x else g x.

Definition split_pi (f g : {fperm atom}) (F G : {fset atom}) :=
  fperm (split_fun f g F) (F :|: G).

Lemma split_fun_inj {f g : {fperm atom}} {F G} :
  fdisjoint (f @: F) (g @: G) →
  {in F &, injective f} →
  {in G &, injective g} →
  {in (F :|: G) &, injective (split_fun f g F)}.
Proof.
  unfold split_fun.
  (* rewrite fdisjointC. *)
  move => /fdisjointP D Hf Hg x y xFG yFG inj.
  (* apply (mem_imfset f) in xFG. *)
  destruct (x \in F) eqn:Ex, (y \in F) eqn:Ey.
  + by apply Hf.
  + apply (mem_imfset f) in Ex.
    specialize (D _ Ex).
    rewrite inj in D.
    move: yFG => /fsetUP [H|H].
    * rewrite H // in Ey.
    * apply (mem_imfset g) in H. rewrite H // in D.
  + apply (mem_imfset f) in Ey.
    specialize (D _ Ey).
    rewrite -inj in D.
    move: xFG => /fsetUP [H|H].
    * rewrite H // in Ex.
    * apply (mem_imfset g) in H. rewrite H // in D.
  + apply Hg; [ | | assumption ].
    * move: xFG => /fsetUP [H|H].
      - rewrite H // in Ex.
      - done.
    * move: yFG => /fsetUP [H|H].
      - rewrite H // in Ey.
      - done.
Qed.

Lemma split_pi_left {X : nomType} {π τ : {fperm atom}} {F G : {fset atom}} {x : X} :
  @support_set X x F →
  fdisjoint (@rename _ π F) (@rename _ τ G) →
  split_pi π τ F G ∙ x = @rename X π x.
Proof.
  intros s D.
  unfold split_pi.
  eapply eq_in_F. { apply s. }
  intros x' xmemF.
  rewrite fpermE.
  + rewrite /split_fun xmemF //.
  + apply split_fun_inj.
    - apply D.
    - intros y y' _ _. apply fperm_inj.
    - intros y y' _ _. apply fperm_inj.
  + apply /fsetUP; by left.
Qed.

Lemma split_supp_left {X Y Z : nomType} :
  ∀ {x : X} {y : Y} {π τ} {f : X → Z},
  equivariant f →
  disj (π ∙ x) (τ ∙ y) →
  split_pi π τ (supp x) (supp y) ∙ f x = f (π ∙ x).
Proof.
  intros x y π τ f E D.
  rewrite split_pi_left.
  + apply E.
  + apply equi_support_set; [ done | apply is_support ].
  + rewrite 2!supp_equi //.
Qed.

Lemma split_pi_right {X : nomType} {f g : {fperm atom}} {F G} {O : X} :
  @support_set X O G →
  fdisjoint F G →
  fdisjoint (@rename _ f F) (@rename _ g G) →
  split_pi f g F G ∙ O = g ∙ O.
Proof.
  intros s D1 D2.
  unfold split_pi.
  eapply eq_in_F. { apply s. }
  intros x xmemF.
  rewrite fpermE.
  + rewrite fdisjointC in D1.
    move: D1 => /fdisjointP D1.
    specialize (D1 _ xmemF).
    move: D1 => /negPf D1.
    rewrite /split_fun D1 //.
  + apply split_fun_inj.
    - apply D2.
    - intros y y' _ _. apply fperm_inj.
    - intros y y' _ _. apply fperm_inj.
  + apply /fsetUP; by right.
Qed.

Lemma fresh_equi {X Y Z : nomType} {f : Y → Z} {x : X} {y : Y}
  : equivariant f → fresh x (f y) ∙ (f y) = fresh x y ∙ (f y).
Proof.
  intros E.
  apply eq_in_supp => a H.
  unfold fresh.
  rewrite /fresh fpermE ?fpermE //.
  + intros [n] [m] _ _.
    rewrite 2!atomizeK.
    intros Eq.
    inversion Eq.
    eapply (can_inj (addKn _)) in H1.
    by subst.
  + eapply (supp_fsubset) in E.
    move: E => /fsubsetP E.
    apply E, H.
  + intros [n] [m] _ _.
    rewrite 2!atomizeK.
    intros Eq.
    inversion Eq.
    eapply (can_inj (addKn _)) in H1.
    by subst.
Qed.


Definition move {X Y : nomType} (x : X) (y : Y) : Y := fresh x y ∙ y.
Arguments move : simpl never.

Lemma move_equi {X Y Z : nomType} {f : Y → Z} {x : X} {y : Y}
  : equivariant f → move x (f y) = f (move x y).
Proof.
  intros E.
  rewrite /move fresh_equi //.
Qed.

Lemma move_supp {X Y Z : nomType} {x : X} {z : Z} {y : Y}
  : supp x = supp z → move x y = move z y.
Proof.
  intros E.
  rewrite /move /fresh E //.
Qed.

Lemma move_inj {X Y} : ∀ x, injective (@move X Y x).
Proof.
  move => x y y' H.
  change y with (y, y').1 in H.
  change y' with (y, y').2 in H.
  rewrite move_equi in H.
  2: by intros ? [? ?].
  symmetry in H.
  rewrite move_equi //= in H.
  2: by intros ? [? ?].
  rewrite adjoin_disc_r in H; try apply eq_equi.
  by rewrite renameK in H.
Qed.

Lemma move_disj {X Y : nomType} (x : X) (y : Y) : disj x (move x y).
Proof. apply fresh_disjoint. Qed.

Lemma move_pair {X Y Z : nomType} {x : X} {y : Y} {z : Z}
  : move x (y, z) = (move x y, move x z).
Proof.
  rewrite {1}/move /rename //=.
  change y with (y, z).1.
  rewrite -fresh_equi //=.
  2: move => π [? ?] //=.
  f_equal.
  change z with (y, z).2.
  rewrite -(fresh_equi (f:=snd)) //=.
  move => π [? ?] //=.
Qed.

Lemma move_equi2 {X Y Z W : nomType} {f : Y → Z → W} {x : X} {y z} :
  equivariant f → move x (f y z) = f (move x y) (move x z).
Proof.
  move => H.
  change (f y z) with (uncurry f (y, z)).
  rewrite move_equi.
  2: intros π [y' z']; rewrite //= equi2_use //=.
  rewrite move_pair //.
Qed.

Definition dpair {X Y : nomType} (x : X) (y : Y) := pair x (move x y).

Lemma move_dpair {X Y Z : nomType} {x : X} {y : Y} {z : Z} : move (x, move x y) z  = move (dpair x y) z.
Proof. done. Qed.

Lemma move_dpairU {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f : X → Y → W}
  : supp (f x y) = supp x :|: supp y → move (f x y) z  = move (x, y) z.
Proof.
  intros H.
  apply move_supp.
  rewrite H //.
Qed.

Lemma freshE {X Y : nomType} {x : X} {y : Y} {a}
  : a \in supp y → fresh x y a = atomize (offset (supp x) + natize a).
Proof.
  rewrite /fresh => H.
  rewrite fpermE //.
  intros a' a'' H' H'' E.
  apply (can_inj natizeK).
  eapply (can_inj (addKn _)).
  apply (can_inj atomizeK).
  apply E.
Qed.

Lemma move0 {X Y : nomType} (x : X) (y : Y) : supp x = fset0 → move x y = y.
Proof.
  intros H.
  rewrite /move -{3}(rename_id y).
  apply eq_in_supp => a H'.
  rewrite freshE // H.
  rewrite offset_fset0 add0n natizeK //.
Qed.

Lemma supp_atom {F : {fset atom}} : supp F = F.
Proof.
  move: F.
  refine (fset_ind _ _).
  { rewrite /supp //= fsetSupp0 //. }
  move => x F H H'.
  rewrite /supp //= fsetSuppU fsetSupp1.
  f_equal.
  apply H'.
Qed.

Lemma supp_supp {X : nomType} {x : X} : supp (supp x) = supp x.
Proof.
  rewrite supp_atom //.
Qed.

Lemma fresh_supp_l {X Y : nomType} {x : X} {y : Y} :
  fresh (supp x) y = fresh x y.
Proof. rewrite /fresh supp_supp //. Qed.

Lemma fresh_supp_r {X Y : nomType} {x : X} {y : Y} :
  fresh x (supp y) = fresh x y.
Proof. rewrite /fresh supp_supp //. Qed.

Lemma offset_move {X Y : nomType} {x : X} {y : Y}
  : maxn (offset (supp x)) (offset (supp (move x y))) = offset (supp x) + offset (supp y).
Proof.
  rewrite -(move_equi supp_equi).
  move: (supp y).
  refine (fset_ind _ _). {
    rewrite offset_fset0 addn0.
    rewrite -{2}(maxn0 (offset (supp x))).
    f_equal.
    rewrite /move /rename //= imfset0 offset_fset0 //.
  }
  intros a F H H'.
  rewrite offset_fsetU1.
  rewrite addn_maxr.
  rewrite -H'.
  rewrite maxnA -(maxnC (offset (supp x))) -maxnA.
  f_equal.
  rewrite (move_equi2 fsetU_equi) (move_equi fset1_equi).
  rewrite offset_fsetU1.
  f_equal.
  rewrite /move /rename //= freshE.
  2: { rewrite /supp in_fset1 //. }
  rewrite atomizeK addnS //.
Qed.

Notation "A #: B" := (move A B) (at level 150, right associativity).

Lemma dpair_move {X Y Z : nomType} {x : X} {y : Y} {z : Z} :
  move (dpair x y) z = move x (move y z).
Proof.
  unfold dpair, move.
  rewrite -rename_comp.
  apply eq_in_supp => a H.
  rewrite freshE //= fpermM //=.
  rewrite freshE //=.
  2: {
    rewrite -supp_equi (adjoin_disc_r in_mem_equi).
    rewrite renameK //.
  }
  f_equal.
  rewrite freshE // atomizeK.
  change (supp (x, fresh x y ∙ y)) with (supp x :|: supp (fresh x y ∙ y)).
  rewrite offset_fsetU.
  rewrite addnA.
  f_equal.
  fold (move x y).
  rewrite offset_move //.
Qed.
