Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.



Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.

From extructures Require Import ffun fperm.

From SSProve.Crypt Require Import
  Nominal Fresh Pr Share.

(* sep_scope Section *)

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Bind Scope sep_scope with nom_package.
Bind Scope sep_scope with package.
Open Scope sep.


(* nom_db *)

Create HintDb nominal_db.

#[export] Hint Extern 10 (alpha _ _) =>
  reflexivity : nominal_db.
  
Lemma rename_alpha {X : actionType} (O : X) π : π ∙ O ≡ O.
Proof.
  exists (π^-1)%fperm.
  rewrite renameK //.
Qed.

#[export] Hint Extern 1 (alpha (rename _ _) _) =>
  rewrite rename_alpha : nominal_db.

#[export] Hint Extern 1 (alpha _ (rename _ _)) =>
  rewrite rename_alpha : nominal_db.

Lemma move_alpha {X Y : nomType} (x : X) (y : Y) : (x #: y) ≡ y.
Proof. rewrite /move rename_alpha. reflexivity. Qed.

#[export] Hint Extern 1 (alpha (move _ _) _) =>
  rewrite move_alpha : nominal_db.

#[export] Hint Extern 1 (alpha _ (move _ _)) =>
  rewrite move_alpha : nominal_db.

#[export] Hint Resolve share_link_congr share_par_congr : nominal_db.

Lemma disj_rename {X Y : nomType} {x : X} {y : Y} {π} :
  disj x y → disj (π ∙ x) (π ∙ y).
Proof.
  intros H.
  rewrite -(equi2_use _ disj_equi) H //.
Qed.

#[export] Hint Resolve disj_rename : nominal_db.

(*
Lemma fresh_disjoint'
  : ∀ {X Y : nomType} {x : X} {y : Y}, disj (fresh x y ∙ y) x.
Proof. intros. rewrite disjC fresh_disjoint //. Qed.

#[export] Hint Resolve fresh_disjoint fresh_disjoint' : nominal_db.
 *)

Lemma supp_empty_Location : supp (emptym : Locations) = fset0.
Proof. rewrite //= /supp //= domm0 imfset0 //. Qed.

Lemma disj_ID_l {X : nomType} {x : X} {I} : disj (ID I : nom_package) x.
Proof.
  rewrite /disj /supp //=.
  rewrite supp_empty_Location.
  apply fdisjoint0s.
Qed.

Lemma disj_ID_r {X : nomType} {x : X} {I} : disj x (ID I : nom_package).
Proof. rewrite disjC. apply disj_ID_l. Qed.

#[export] Hint Resolve disj_ID_l disj_ID_r : nominal_db.


Lemma subs_refl {X : nomType} {x : X} : subs x x.
Proof.
  apply fsubsetxx.
Qed.

Lemma subs_fresh_disj {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj (fresh y x ∙ x') y'.
Proof.
  intros subsx subsy.
  erewrite <- absorb in subsx.
  rewrite -> equi2_use in subsx.
  2: apply subsE.
  eapply fdisjoint_trans.
  1: apply subsx.
  rewrite fdisjointC.
  eapply fdisjoint_trans.
  1: apply subsy.
  apply fresh_disjoint.
Qed.

Lemma subs_fresh_disj' {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x → subs y' y → disj y' (fresh y x ∙ x').
Proof. rewrite disjC. apply subs_fresh_disj. Qed.

#[export] Hint Resolve subs_refl subs_fresh_disj' subs_fresh_disj : nominal_db.

Lemma disj_equi2 {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj x (f y z).
Proof.
  intros E D1 D2.
  rewrite disjC.
  change (f y z) with (uncurry f (y, z)).
  eapply fdisjoint_trans.
  + eapply supp_fsubset.
    intros π [x' y'].
    rewrite //= (equi2_use _ E) //.
  + rewrite fdisjointUl.
    apply /andP.
    split; rewrite fdisjointC //.
Qed.

Lemma disj_equi2' {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj (f y z) x.
Proof.
  intros E D1 D2.
  rewrite disjC.
  by apply disj_equi2.
Qed.

#[export] Hint Resolve disj_equi2 disj_equi2' : nominal_db.

Lemma equi_share_link : equivariant share_link.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_link.
Qed.

Lemma equi_share_par : equivariant share_par.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_par.
Qed.

#[export] Hint Resolve equi_share_link equi_share_par : nominal_db.

Lemma subs_supp_fsetUl {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x y → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUl.
Qed.

Lemma subs_supp_fsetUr {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x z → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUr.
Qed.

#[export] Hint Resolve subs_supp_fsetUl subs_supp_fsetUr : nominal_db.

#[export] Hint Resolve s_share_link s_share_par : nominal_db.


(* sep_link *)

Definition sep_link (P P' : nom_package)
  := share_link P (move P P').

Notation "p1 ∘ p2" :=
  (sep_link p1 p2) (right associativity, at level 20) : sep_scope.

Add Parametric Morphism : sep_link with
  signature alpha ==> alpha ==> alpha as sep_link_mor.
Proof. eauto 6 with nominal_db. Qed.

Lemma sep_link_id {L I E} (P : nom_package) :
  ValidPackage L I E P → P ∘ (ID I) ≡ P.
Proof.
  intros V.
  rewrite /sep_link /move -{3}(@share_link_id _ _ _ _ V).
  eauto with nominal_db nocore.
Qed.

Lemma id_sep_link {L I E} (P : nom_package) (V : ValidPackage L I E P)
  : ID E ∘ P ≡ P.
Proof.
  rewrite /sep_link /move id_share_link.
  eauto with nominal_db nocore.
Qed.

Lemma sep_link_assoc (p1 p2 p3 : nom_package)
  : p1 ∘ p2 ∘ p3 ≡ (p1 ∘ p2) ∘ p3.
Proof.
  rewrite /sep_link /move rename_share_link share_link_assoc.
  eauto 20 with nominal_db nocore.
Qed.


(* sep_par *)

Definition sep_par (P P' : nom_package)
  := share_par P (move P P').

Notation "p1 || p2" :=
  (sep_par p1 p2) : sep_scope.

Add Parametric Morphism : sep_par with
  signature alpha ==> alpha ==> alpha as sep_par_mor.
Proof.
  intros P P' EP Q Q' EQ.
  unfold sep_par, move.
  auto with nominal_db nocore.
Qed.

Lemma fseparate_disj {L1 L2 : Locations}
  : fseparate L1 L2 <-> disj L1 L2.
Proof.
  split.
  - move=> [] /eqP H.
    apply /eqP.
    rewrite -imfsetI ?H ?imfset0 //.
    intros ? ? ? ?; eapply can_inj, atomizeK.
  - move=> /eqP H.
    apply fsep.
    apply /eqP.
    apply (imfset_inj (can_inj atomizeK)).
    rewrite imfsetI ?H ?imfset0 //.
    intros ? ? ? ?; eapply can_inj, atomizeK.
Qed.

Lemma disj_loc_fcompat {p1 p2} :
  disj p1 p2 → fcompat (loc p1) (loc p2).
Proof.
  rewrite -fseparate_disj.
  apply fseparate_compat.
Qed.

#[export] Hint Resolve disj_loc_fcompat : nominal_db.

Lemma rename_val_fseparate {p1 p2 : nom_package} {π} :
  fseparate (val p1) (val p2) → fseparate (val p1) (val (π ∙ p2)).
Proof.
  intros H.
  apply fsep.
  rewrite domm_map.
  apply H.
Qed.

Lemma rename_val_fseparate' {p1 p2 : nom_package} {π} :
  fseparate (val p1) (val p2) → fseparate (val (π ∙ p1)) (val p2).
Proof.
  intros H.
  apply fseparateC.
  apply rename_val_fseparate.
  by apply fseparateC.
Qed.

#[export] Hint Resolve rename_val_fseparate rename_val_fseparate' : nominal_db.

#[export] Hint Resolve fseparate_compat : nominal_db.

Lemma sep_par_commut (p1 p2 : nom_package)
  : fseparate (val p1) (val p2) → (p1 || p2) ≡ (p2 || p1).
Proof.
  intros H. unfold sep_par, move.
  rewrite share_par_commut.
  all: auto with nominal_db nocore.
Qed.

Lemma sep_par_assoc {P1 P2 P3 : nom_package}
  : (P1 || (P2 || P3)) ≡ ((P1 || P2) || P3).
Proof.
  rewrite /sep_par /move rename_share_par share_par_assoc.
  auto with nominal_db nocore.
Qed.

Lemma sep_interchange {A B C D E F} {L1 L2 L3 L4} (p1 p2 p3 p4 : nom_package) :
  ValidPackage L1 B A p1 → ValidPackage L2 E D p2 →
  ValidPackage L3 C B p3 → ValidPackage L4 F E p4 →
  fseparate (val p3) (val p4) →
  (p1 ∘ p3) || (p2 ∘ p4) ≡ (p1 || p2) ∘  (p3 || p4).
Proof.
  intros V1 V2 V3 V4 P34.
  rewrite /sep_par /sep_link /move
    rename_share_par rename_share_link share_interchange.
  all: auto 10 with nominal_db nocore.
Qed.




(*
Lemma disj_rename {X Y : nomType} {x : X} {y : Y} {π} :
  disj x y → disj (π ∙ x) (π ∙ y).
Proof.
  intros H.
  rewrite -(equi2_use _ disj_equi) H //.
Qed.

Lemma fsetUl : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s2 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUl.
  + by apply fsetSU.
Qed.

Lemma fsetUr : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s3 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUr.
  + by apply fsetUS.
Qed.


Lemma subs_equi {X Y : nomType} {x : X} {f : X → Y} :
  equivariant f → subs (f x) x.
Proof.
  intros E.
  by apply supp_fsubset.
Qed.

Lemma subs_equi_eq {X Y : nomType} {x : X} {y : Y} {f : X → Y} :
  equivariant f → y = f x → subs y x.
Proof.
  intros Ef eq.
  rewrite eq.
  by apply subs_equi.
Qed.

Lemma subs_fresh_disj {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj (fresh y x ∙ x') y'.
Proof.
  intros subsx subsy.
  erewrite <- absorb in subsx.
  rewrite -> equi2_use in subsx.
  2: apply subsE.
  eapply fdisjoint_trans.
  1: apply subsx.
  rewrite fdisjointC.
  eapply fdisjoint_trans.
  1: apply subsy.
  apply fresh_disjoint.
Qed.

Lemma subs_fresh_disj_2 {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x → subs y' y → disj y' (fresh y x ∙ x').
Proof. rewrite disjC. apply subs_fresh_disj. Qed.

Create HintDb alpha_db.
#[export] Hint Resolve subs_fresh_disj subs_fresh_disj_2 : alpha_db.
#[export] Hint Resolve disj_rename : alpha_db.

Lemma subs_supp_fsetUl {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x y → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUl.
Qed.

Lemma subs_supp_fsetUr {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x z → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUr.
Qed.

#[export] Hint Resolve subs_supp_fsetUl subs_supp_fsetUr : alpha_db.

Lemma supp_pair {X Y : nomType} {x : X} {y : Y}
  : supp (pair x y) = supp x :|: supp y.
Proof. done. Qed.

#[export] Hint Resolve s_share_link s_share_par supp_pair : alpha_db.


Lemma subs_refl {X : nomType} {x : X} : subs x x.
Proof.
  apply fsubsetxx.
Qed.

#[export] Hint Resolve subs_refl : alpha_db.

Lemma disj_share_link {X : nomType} {x : X} {P Q}
  : disj x P → disj x Q → disj x (P ∘ Q)%share.
Proof.
  intros dP dQ.
  unfold disj.
  rewrite s_share_link.
  rewrite fdisjointUr.
  apply /andP.
  by split.
Qed.

Lemma disj_share_link2 {X : nomType} {x : X} {P Q}
  : disj P x → disj Q x → disj (P ∘ Q)%share x.
Proof.
  intros dP dQ.
  rewrite disjC.
  rewrite disj_share_link //; rewrite disjC //.
Qed.

Lemma disj_equi2 {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj x (f y z).
Proof.
  intros E D1 D2.
  rewrite disjC.
  change (f y z) with (uncurry f (y, z)).
  eapply fdisjoint_trans.
  + eapply supp_fsubset.
    intros π [x' y'].
    rewrite //= (equi2_use _ E) //.
  + rewrite fdisjointUl.
    apply /andP.
    split; rewrite fdisjointC //.
Qed.

Lemma disj_equi2' {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj (f y z) x.
Proof.
  intros E D1 D2.
  rewrite disjC.
  by apply disj_equi2.
Qed.

Lemma equi_share_link : equivariant share_link.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_link.
Qed.

Lemma equi_share_par : equivariant share_par.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_par.
Qed.

 *)
(*
Lemma supp0 {X : nomOrdType} : supp (@fset0 X) = fset0.
Proof.
  rewrite /supp //= fsetSupp0 //.
Qed.

(* #[export] Hint Resolve disj_link disj_link2 : alpha_db. *)
#[export] Hint Resolve disj_equi2 disj_equi2' : alpha_db.
#[export] Hint Resolve equi_share_link equi_share_par : alpha_db.

#[export] Hint Resolve share_link_congr share_par_congr : alpha_db.

Lemma sep_link_assoc (p1 p2 p3 : nom_package)
  : p1 ∘ p2 ∘ p3 ≡ (p1 ∘ p2) ∘ p3.
Proof.
  rewrite /sep_link /move rename_share_link share_link_assoc.
  auto with alpha_db nocore.
Qed.


(* ID *)

Lemma share_link_adj {P P'} {π}
  : (P ∘ (π ∙ P'))%share ≡ ((π^-1 ∙ P)%fperm ∘ P')%share.
Proof.
  exists (π^-1)%fperm.
  rewrite rename_share_link.
  rewrite renameK //.
Qed.

 *)

(* Adv *)

Definition Pr' : nom_package → R := λ P, Pr P true.

Definition Adv (G G' A : nom_package) : R
  := `| Pr' (A ∘ G) - Pr' (A ∘ G') |.

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
  apply Pr_rename.
Qed.

Lemma Pr'_def {P} : Pr' P = Pr (val P) true.
Proof. done. Qed.

Add Parametric Morphism : Adv with
  signature alpha ==> alpha ==> alpha ==> eq as Adv_mor.
Proof.
  intros.
  unfold Adv.
  rewrite H H0 H1 //.
Qed.

(*
Add Parametric Morphism : (@GRing.add R) with
  signature ler ++> ler ++> ler as add_mor.
Proof.
  intros.
  by apply lerD.
Qed.
 *)

Lemma alpha_eq {X : actionType} {P P' : X} : P = P' → P ≡ P'.
Proof. move=> ->. eexists. by erewrite rename_id. Qed.

Lemma alpha_equi {X Y : actionType} {P P'} {f : X → Y}
: equivariant f → P ≡ P' → f P ≡ f P'.
Proof.
  intros equif [π eq].
  exists π.
  rewrite equif.
  f_equal.
  apply eq.
Qed.

Lemma Adv_triangle {G1 G2 G3 : nom_package} A
  : Adv G1 G3 A <= Adv G1 G2 A + Adv G2 G3 A.
Proof. unfold Adv, Pr'. apply Advantage_triangle. Qed.

Ltac ssprove_ehop :=
  eapply le_trans;
    [ eapply Adv_triangle |].

Ltac ssprove_hop M :=
  eapply le_trans;
    [ eapply (@Adv_triangle _ M%sep) |].

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

Lemma Adv_sep_link (G G' D A : nom_package) :
  Adv (D ∘ G) (D ∘ G') A = Adv G G' (A ∘ D).
Proof.
  unfold Adv.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  done.
Qed.

Lemma share_link_sep_link {P P' : nom_package} :
  disj P P' →
  (P ∘ P')%share ≡ (P ∘ P').
Proof.
  intros D.
  unfold sep_link, move.
  auto with nominal_db nocore.
Qed.

Lemma link_sep_link {P P' : nom_package} :
  disj P P' →
  (P ∘ P')%pack ≡ val (P ∘ P').
Proof.
  intros D.
  change (link P P') with (val (share_link P P')).
  apply alpha_equi; [ done |].
  apply share_link_sep_link, D.
Qed.

Lemma share_par_sep_par {P P' : nom_package} :
  disj P P' →
  (P || P')%share ≡ (P || P').
Proof.
  intros D.
  unfold sep_par, move.
  auto with nominal_db nocore.
Qed.

Lemma par_sep_par {P P' : nom_package} :
  disj P P' →
  (par P P' : raw_package) ≡ val (P || P').
Proof.
  intros D.
  change (par P P') with (val (share_par P P')).
  apply alpha_equi; [ done |].
  apply share_par_sep_par, D.
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
  - ssprove_ehop.
    erewrite (Adv_perf Indish).
    + rewrite GRing.add0r //.
    + eassumption.
  - ssprove_ehop.
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
  - ssprove_hop P'.
    rewrite H GRing.add0r //.
  - ssprove_hop P.
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

Lemma id_sep_par {I I' : Interface}
  : ID I || ID I' ≡ ID (unionm I I').
Proof.
  rewrite <- share_par_sep_par by auto with nominal_db.
  apply alpha_eq.
  apply eq_raw_module; [ done |].
  simpl. unfold par.
  apply eq_fmap => n.
  rewrite /ID_raw unionmE 3!mapimE unionmE.
  destruct (I n); destruct (I' n) => //=.
Qed.

Lemma swish
  {L L' : Locations} {I I' E E' : Interface} {P P' : nom_package} :
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  fseparate (val (ID I)) (val P') →
  (P || P') ≡ (P || ID E') ∘ (ID I || P').
Proof.
  intros V1 V2 H.
  erewrite <- sep_interchange.
  all: try ssprove_valid.
  rewrite id_sep_link //.
  rewrite sep_link_id //.
  setoid_reflexivity.
Qed.

Lemma swash {L L' I I' E E'} {P P' : nom_package} :
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  fseparate (val P) (val (ID I')) →
  (P || P') ≡ (ID E || P') ∘ (P || ID I').
Proof.
  intros V1 V2 H.
  erewrite <- sep_interchange.
  all: try ssprove_valid.
  rewrite id_sep_link //.
  rewrite sep_link_id //.
  reflexivity.
Qed.

Lemma sep_par_empty_l {P} : (ID (Game_import) || P) ≡ P.
Proof.
  rewrite <- share_par_sep_par.
  2: auto with nominal_db.
  apply alpha_eq.
  by apply eq_raw_module.
Qed.

Lemma sep_par_empty_r {P} : (P || ID (Game_import)) ≡ P.
Proof.
  rewrite -> sep_par_commut.
  - apply sep_par_empty_l.
  - fmap_solve.
Qed.

Lemma sep_par_game_l {LP LQ LR EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R} :
  ((P ∘ Q) || R) ≡ (P || R) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_r Q).
  erewrite <- sep_interchange.
  2-6: ssprove_valid.
  rewrite sep_link_id.
  reflexivity.
Qed.

Lemma sep_par_game_r {LP LQ LR EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R} :
  (R || (P ∘ Q)) ≡ (R || P) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_l Q).
  erewrite <- sep_interchange.
  2-6: ssprove_valid.
  rewrite sep_link_id.
  reflexivity.
Qed.

Lemma Adv_par_link_r (P₀ P₁ P₁' G G' A : nom_package)
  {LP₀ LP₁ LP₁'} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₁ I₁ E₁ P₁}
  {V3 : ValidPackage LP₁' I₁ E₁ P₁'} :
  fseparate (val (ID I₀)) (val P₁) →
  fseparate (val (ID I₀)) (val P₁') →
  Adv ((P₀ || P₁) ∘ G) ((P₀ || P₁') ∘ G') A
    = Adv ((ID I₀ || P₁) ∘ G) ((ID I₀ || P₁') ∘ G') (A ∘ (P₀ || (ID E₁))).
Proof.
  intros H H'.
  rewrite <- Adv_sep_link.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  erewrite <- @swish, <- @swish.
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
  rewrite -Adv_sep_link.
  rewrite swish.
  2: fmap_solve.
  rewrite sep_par_empty_l.
  rewrite (@swish _ _ _ _ _ _ _ G₁').
  2: fmap_solve.
  rewrite sep_par_empty_l.
  reflexivity.
Qed.

Lemma Adv_par_link_l (P₀ P₀' P₁ G G' A : nom_package)
  {LP₀ LP₀' LP₁} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₀' I₀ E₀ P₀'}
  {V3 : ValidPackage LP₁ I₁ E₁ P₁} :
  fseparate (val P₀) (val (ID I₁)) →
  fseparate (val P₀') (val (ID I₁)) →
  Adv ((P₀ || P₁) ∘ G) ((P₀' || P₁) ∘ G') A
    = Adv ((P₀ || ID I₁) ∘ G) ((P₀' || ID I₁) ∘ G') (A ∘ (ID E₀ || P₁)).
Proof.
  intros H H'.
  erewrite <- Adv_sep_link.
  erewrite sep_link_assoc, sep_link_assoc.
  erewrite <- @swash, <- @swash.
  all: ssprove_valid.
  reflexivity.
Qed.

Lemma Adv_par_l (G₀ G₀' G₁ A : nom_package) {L₀ L₀'  L₁} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₀' Game_import E₀ G₀'}
  {V3 : ValidPackage L₁ Game_import E₁ G₁} :
  fseparate (val (ID E₀)) (val G₁) →
  Adv (G₀ || G₁) (G₀' || G₁) A = Adv G₀ G₀' (A ∘ (ID E₀ || G₁)).
Proof.
  intros H.
  rewrite -Adv_sep_link.
  rewrite swash.
  2: fmap_solve.
  rewrite sep_par_empty_r.
  rewrite (@swash _ _ _ _ _ _ G₀').
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
