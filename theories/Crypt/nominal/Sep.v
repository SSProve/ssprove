Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  reals distr realsum fingroup.fingroup solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap ffun fperm.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal Fresh Pr Share.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(******************************************************************************)
(* This file defines `sep_link` and `sep_par` using fresh.                    *)
(* Algebraic equations are re-established and they are shown to be alpha-     *)
(* congruent. The operators are given ∘ and || notation in %sep scope.        *)
(******************************************************************************)

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.


(* sep_scope Section *)

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Bind Scope sep_scope with nom_package.
Bind Scope sep_scope with package.
Open Scope sep.


(* nominal_db *)

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


(* sep_link *)

Definition sep_link (P P' : nom_package)
  := share_link P (move P P').

Notation "p1 ∘ p2" :=
  (sep_link p1 p2) (right associativity, at level 20) : sep_scope.

Add Parametric Morphism : sep_link with
  signature alpha ==> alpha ==> alpha as sep_link_mor.
Proof. eauto 6 with nominal_db. Qed.

Lemma valid_sep_link_weak :
  ∀ I M1 M2 E P1 P2,
    ValidPackage (loc P1) M1 E P1 →
    ValidPackage (loc P2) I M2 P2 →
    fsubmap M1 M2 →
    ValidPackage (loc (P1 ∘ P2)%sep) I E (P1 ∘ P2)%sep.
Proof. intros.
  eapply valid_link_weak.
  1,4: eassumption.
  1: unfold move; by apply rename_valid.
  apply fseparate_compat.
  rewrite fseparate_disj //=.
  rewrite -fresh_supp_l -fresh_supp_r /supp.
  rewrite //= fresh_supp_l fresh_supp_r.
  auto with nominal_db.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (sep_link ?p1 ?p2))) =>
  package_evar ; [ eapply valid_sep_link_weak | .. ]
  : typeclass_instances ssprove_valid_db.

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

Lemma sep_link_id {I E} (P : nom_package) :
  ValidPackage (loc P) I E P → P ∘ ID I ≡ P.
Proof.
  intros V.
  rewrite /sep_link /move -{3}(@share_link_id _ _ _ V).
  eauto with nominal_db nocore.
Qed.

Lemma id_sep_link {I E} (P : nom_package) (V : ValidPackage (loc P) I E P)
  : ID E ∘ P ≡ P.
Proof.
  rewrite /sep_link /move id_share_link.
  eauto with nominal_db nocore.
Qed.

Lemma sep_link_assoc (p1 p2 p3 : nom_package)
  : p1 ∘ p2 ∘ p3 ≡ (p1 ∘ p2) ∘ p3.
Proof.
  rewrite /sep_link /move (equi2_use _ equi_share_link) share_link_assoc.
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

Lemma valid_sep_par {I1 I2 E1 E2} {p1 p2 : nom_package} :
  ValidPackage (loc p1) I1 E1 p1 →
  ValidPackage (loc p2) I2 E2 p2 →
  fcompat I1 I2 →
  ValidPackage (loc (p1 || p2)%sep)
    (unionm I1 I2) (unionm E1 E2) (p1 || p2)%sep.
Proof.
  intros. unfold sep_par. apply valid_par; try done.
  1: unfold move; by apply rename_valid.
  apply fseparate_compat.
  rewrite fseparate_disj //=.
  rewrite -fresh_supp_l -fresh_supp_r /supp.
  rewrite //= fresh_supp_l fresh_supp_r.
  auto with nominal_db.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (val (sep_par ?p1 ?p2))) =>
  package_evar ; [ eapply valid_sep_par | .. ]
  : typeclass_instances ssprove_valid_db.

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
  rewrite /sep_par /move (equi2_use _ equi_share_par) share_par_assoc.
  auto with nominal_db nocore.
Qed.

Lemma sep_interchange {A B C D E F} (p1 p2 p3 p4 : nom_package) :
  ValidPackage (loc p1) B A p1 → ValidPackage (loc p2) E D p2 →
  ValidPackage (loc p3) C B p3 → ValidPackage (loc p4) F E p4 →
  fseparate (val p3) (val p4) →
  (p1 ∘ p3) || (p2 ∘ p4) ≡ (p1 || p2) ∘ (p3 || p4).
Proof.
  intros V1 V2 V3 V4 P34.
  rewrite /sep_par /sep_link /move
    (equi2_use _ equi_share_par) (equi2_use _ equi_share_link) share_interchange.
  all: auto 10 with nominal_db nocore.
Qed.


(* Extra theorems about sep_link and sep_par *)

Lemma id_sep_par {I I' : Interface}
  : ID I || ID I' ≡ ID (unionm I I').
Proof.
  rewrite <- share_par_sep_par by auto with nominal_db.
  apply alpha_eq.
  apply eq_nom_package; [ done |].
  simpl. unfold par.
  apply eq_fmap => n.
  rewrite /ID_raw unionmE 3!mapimE unionmE.
  destruct (I n); destruct (I' n) => //=.
Qed.

Lemma sep_par_factor_l
  {I I' E E' : Interface} {P P' : nom_package} :
  ValidPackage (loc P) I E P → ValidPackage (loc P') I' E' P' →
  fseparate I (val P') →
  (P || P') ≡ (P || ID E') ∘ (ID I || P').
Proof.
  intros V1 V2 H.
  erewrite <- sep_interchange.
  all: try ssprove_valid.
  rewrite id_sep_link //.
  rewrite sep_link_id //.
  setoid_reflexivity.
Qed.

Lemma sep_par_factor_r {I I' E E'} {P P' : nom_package} :
  ValidPackage (loc P) I E P → ValidPackage (loc P') I' E' P' →
  fseparate (val P) I' →
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
  by apply eq_nom_package.
Qed.

Lemma sep_par_empty_r {P} : (P || ID (Game_import)) ≡ P.
Proof.
  rewrite -> sep_par_commut.
  - apply sep_par_empty_l.
  - fmap_solve.
Qed.

Lemma sep_par_factor_game_l {I' E E' : Interface} {P P' : nom_package}
  : ValidPackage (loc P) Game_import E P → ValidPackage (loc P') I' E' P'
  → (P || P') ≡ ((P || ID E') ∘ P')%sep.
Proof.
  intros VP VP'.
  rewrite sep_par_factor_l; [| fmap_solve ].
  rewrite sep_par_empty_l.
  reflexivity.
Qed.

Lemma sep_par_factor_game_r {I E E' : Interface} {P P' : nom_package}
  : ValidPackage (loc P) I E P → ValidPackage (loc P') Game_import E' P'
  → (P || P') ≡ ((ID E || P') ∘ P)%sep.
Proof.
  intros VP VP'.
  rewrite sep_par_factor_r; [| fmap_solve ].
  rewrite sep_par_empty_r.
  reflexivity.
Qed.

Lemma sep_par_game_l {EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage (loc P) EQ EP P}
  {VQ : ValidPackage (loc Q) IQ EQ Q}
  {VR : ValidPackage (loc R) Game_import ER R} :
  ((P ∘ Q) || R) ≡ (P || R) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_r Q).
  erewrite <- sep_interchange.
  2-6: ssprove_valid.
  rewrite sep_link_id.
  reflexivity.
Qed.

Lemma sep_par_game_r {EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage (loc P) EQ EP P}
  {VQ : ValidPackage (loc Q) IQ EQ Q}
  {VR : ValidPackage (loc R) Game_import ER R} :
  (R || (P ∘ Q)) ≡ (R || P) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_l Q).
  erewrite <- sep_interchange.
  2-6: ssprove_valid.
  rewrite sep_link_id.
  reflexivity.
Qed.
