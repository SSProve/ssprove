Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  reals distr realsum fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap ffun fperm.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal Fresh Pr Share Sep.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(******************************************************************************)
(* This file introduces advantage `Adv` based on `sep_link`. It is shown that *)
(* Adv is alpha-congruent in all arguments, and that perfectly                *)
(* indistinguishable (`perfect`) packages may replace either argument freely. *)
(* Various reduction lemmas are also proven about `Adv`.                      *)
(******************************************************************************)

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.


Definition Pr' : nom_package → distr R bool := Pr.

Definition Adv (G G' A : nom_package) : R
  := `| Pr' (A ∘ G) true - Pr' (A ∘ G') true |.

Add Parametric Morphism : val with
  signature alpha ==> alpha as val_mor.
Proof.
  intros x y [π E].
  rewrite -E.
  exists π.
  reflexivity.
Qed.

Add Parametric Morphism : Pr' with
  signature alpha ==> eq as Pr'_mor.
Proof.
  intros x y [π' H0].
  unfold Pr'.
  rewrite -H0.
  apply distr_ext => z.
  apply Pr_rename.
Qed.

Add Parametric Morphism : Adv with
  signature alpha ==> alpha ==> alpha ==> eq as Adv_mor.
Proof.
  intros.
  unfold Adv.
  rewrite H H0 H1 //.
Qed.

Lemma Adv_triangle {G1 G2 G3 : nom_package} A
  : Adv G1 G3 A <= Adv G1 G2 A + Adv G2 G3 A.
Proof. unfold Adv, Pr'. apply Advantage_triangle. Qed.

Lemma Adv_same (G A : nom_package) : Adv G G A = 0.
Proof. rewrite /Adv addrN. rewrite normr0 //. Qed.

Lemma Adv_sym (G G' A : nom_package) : Adv G G' A = Adv G' G A.
Proof. apply: distrC. Qed.

Lemma Adv_alpha (G G' A : nom_package)
  : G ≡ G' → Adv G G' A = 0.
Proof.
  intros Eq.
  rewrite Eq.
  apply Adv_same.
Qed.

Lemma Adv_reduction (G G' D A : nom_package) :
  Adv (D ∘ G) (D ∘ G') A = Adv G G' (A ∘ D).
Proof.
  unfold Adv.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  done.
Qed.

Lemma Adv_AdvantageE (G G' A : nom_package) :
  disj A G ->
  disj A G' ->
  Adv G G' A = AdvantageE G G' A.
Proof.
  intros D1 D2.
  unfold Adv, AdvantageE.
  rewrite link_sep_link ?link_sep_link //.
Qed.

Lemma supp_prod {X Y : nomType} (x : X) (y : Y)
  : supp (x, y) = supp x :|: supp y.
Proof. done. Qed.

#[export] Hint Resolve supp_prod subs_refl : nominal_db.

Lemma Adv_adv_equiv {L L' E} {G G' : nom_package} {ε : raw_package → R}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  equivariant ε →
  G ≈[ ε ] G' →
  ∀ {LA} (A : nom_package), ValidPackage LA E A_export A → Adv G G' A = ε A.
Proof.
  intros equieps adv LA A VA.
  pose (π := fresh ((L, G), (L', G')) (LA, A)).
  setoid_rewrite <- (@rename_alpha _ A π).
  rewrite Adv_AdvantageE.
  1: rewrite -(absorb π (ε A)).
  1: rewrite equieps.
  1: rewrite adv //.

  1,2: rewrite fseparate_disj.
  1-4: eauto with nominal_db nocore.
Qed.

Lemma Adv_perf {L L' E} {G G' : nom_package}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  G ≈₀ G' →
  ∀ {LA} (A : nom_package), ValidPackage LA E A_export A → Adv G G' A = 0.
Proof.
  intros adv LA A VA.
  eapply (Adv_adv_equiv (ε := λ _, 0)).
  1: done.
  1: apply adv.
  apply VA.
Qed.

Lemma Adv_perf_l {P P' Q A : nom_package} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → Adv P Q A = Adv P' Q A.
Proof.
  intros Indish.
  apply le_anti.
  apply /andP; split.
  - eapply le_trans; [ eapply Adv_triangle |].
    erewrite (Adv_perf Indish).
    + rewrite GRing.add0r //.
    + eassumption.
  - eapply le_trans; [ eapply Adv_triangle |].
    erewrite (Adv_perf (adv_equiv_sym _ _ _ _ _ _ _ _ Indish)).
    + rewrite GRing.add0r //.
    + eassumption.
Qed.

Lemma Adv_perf_r {P P' Q A : nom_package} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → Adv Q P A = Adv Q P' A.
Proof.
  intros Indish.
  rewrite Adv_sym.
  erewrite Adv_perf_l; [| done].
  rewrite Adv_sym //.
Qed.

Definition perfect I G G' :=
  ∀ LA (A : nom_package)
    (VA : ValidPackage LA I A_export A), Adv G G' A = 0.

Lemma perfect_refl {I G} : perfect I G G.
Proof. intros LA A VA. rewrite Adv_same //. Qed.

Lemma perfect_sym {I G G'} : perfect I G' G → perfect I G G'.
Proof. intros H LA A VA. rewrite Adv_sym H //. Qed.

Add Parametric Morphism : perfect with
  signature eq ==> alpha ==> alpha ==> iff as perfect_mor.
Proof.
  intros I G0 G0' H0 G1 G1' H1.
  split.
  - intros H LA A VA.
    rewrite -H0 -H1 H //.
  - intros H LA A VA.
    rewrite H0 H1 H //.
Qed.

Lemma Adv_perfect_l {L E} {P P' Q A : nom_package}
  {V : ValidPackage L E A_export A} :
  perfect E P P' → Adv P Q A = Adv P' Q A.
Proof.
  intros H.
  apply le_anti.
  apply /andP; split.
  - eapply le_trans; [ eapply (@Adv_triangle _ P') |].
    rewrite H GRing.add0r //.
  - eapply le_trans; [ eapply (@Adv_triangle _ P) |].
    rewrite Adv_sym H GRing.add0r //.
Qed.

Lemma Adv_perfect_r {L E} {P P' Q A : nom_package}
  {V : ValidPackage L E A_export A} :
  perfect E P P' → Adv Q P A = Adv Q P' A.
Proof. intros H. rewrite Adv_sym (Adv_perfect_l H) Adv_sym //. Qed.

Lemma perfect_trans {I G G' G''}
  : perfect I G G' → perfect I G' G'' → perfect I G G''.
Proof. intros H1 H2 LA A VA. rewrite (Adv_perfect_l H1) H2 //. Qed.

Lemma prove_perfect {L L'} {E} {G G' : nom_package} :
  ∀ (V  : ValidPackage L  Game_import E G )
    (V' : ValidPackage L' Game_import E G'),
    G ≈₀ G' → perfect E G G'.
Proof. intros V V' H LA A VA. apply (Adv_perf H _ VA). Qed.

Lemma Adv_par_link_r (P₀ P₁ P₁' G G' A : nom_package)
  {LP₀ LP₁ LP₁'} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₁ I₁ E₁ P₁}
  {V3 : ValidPackage LP₁' I₁ E₁ P₁'} :
  fseparate I₀ (val P₁) →
  fseparate I₀ (val P₁') →
  Adv ((P₀ || P₁) ∘ G) ((P₀ || P₁') ∘ G') A
    = Adv ((ID I₀ || P₁) ∘ G) ((ID I₀ || P₁') ∘ G') (A ∘ (P₀ || (ID E₁))).
Proof.
  intros H H'.
  rewrite <- Adv_reduction.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  erewrite <- sep_par_factor_l, <- sep_par_factor_l.
  all: ssprove_valid.
  1: reflexivity.
Qed.

Lemma Adv_par_r (G₀ G₁ G₁' A : nom_package)
  {L₀ L₁ L₁'} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₁ Game_import E₁ G₁}
  {V3 : ValidPackage L₁' Game_import E₁ G₁'} :
  Adv (G₀ || G₁) (G₀ || G₁') A = Adv G₁ G₁' (A ∘ (G₀ || ID E₁)).
Proof.
  rewrite -Adv_reduction.
  rewrite sep_par_factor_l.
  2: fmap_solve.
  rewrite sep_par_empty_l.
  rewrite (@sep_par_factor_l _ _ _ _ _ _ _ G₁').
  2: fmap_solve.
  rewrite sep_par_empty_l.
  reflexivity.
Qed.

Lemma Adv_par_link_l (P₀ P₀' P₁ G G' A : nom_package)
  {LP₀ LP₀' LP₁} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₀' I₀ E₀ P₀'}
  {V3 : ValidPackage LP₁ I₁ E₁ P₁} :
  fseparate (val P₀) I₁ →
  fseparate (val P₀') I₁ →
  Adv ((P₀ || P₁) ∘ G) ((P₀' || P₁) ∘ G') A
    = Adv ((P₀ || ID I₁) ∘ G) ((P₀' || ID I₁) ∘ G') (A ∘ (ID E₀ || P₁)).
Proof.
  intros H H'.
  erewrite <- Adv_reduction.
  erewrite sep_link_assoc, sep_link_assoc.
  erewrite <- @sep_par_factor_r, <- @sep_par_factor_r.
  all: ssprove_valid.
  reflexivity.
Qed.

Lemma Adv_par_l (G₀ G₀' G₁ A : nom_package) {L₀ L₀'  L₁} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₀' Game_import E₀ G₀'}
  {V3 : ValidPackage L₁ Game_import E₁ G₁} :
  Adv (G₀ || G₁) (G₀' || G₁) A = Adv G₀ G₀' (A ∘ (ID E₀ || G₁)).
Proof.
  rewrite -Adv_reduction.
  rewrite sep_par_factor_r.
  2: fmap_solve.
  rewrite sep_par_empty_r.
  rewrite (@sep_par_factor_r _ _ _ _ _ _ G₀').
  2: fmap_solve.
  rewrite sep_par_empty_r.
  reflexivity.
Qed.


Notation AdvOf GG A := (Adv (GG true) (GG false) A).

Lemma AdvOf_perfect {L E} {G G'} {A : nom_package}
  {V : ValidPackage L E A_export A} :
  (∀ b : bool, perfect E (G b) (G' b)) →
  AdvOf G A = AdvOf G' A.
Proof.
  intros H.
  rewrite (Adv_perfect_r (H false)).
  rewrite (Adv_perfect_l (H true)) //.
Qed.
