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

From HB Require Import structures.

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

From SSProve.Crypt Require Import Nominal Fresh Pr.

(* Support lemmas *)

Program Definition Location_IsNominal
  : IsNominal Location
  := IsNominal.Build _ (λ (l : Location), fset1 (atomize l.1)) _ _.
Obligation 1.
  intros π H.
  unfold rename; simpl.
  rewrite H ?atomizeK; [ by destruct x |].
  rewrite in_fset1 //.
Qed.
Obligation 2.
  eapply fsubset_trans.
  2: eapply (support_sub (atomize x.1)).
  1: apply fsubsetxx.
  Unshelve.
  intros π H'.
  specialize (H π H').
  rewrite /rename //= in H |- *.
  destruct x => //=.
  noconf H.
  rewrite -(natizeK (π _)) H //.
Qed.

HB.instance Definition _ : IsNominal Location 
  := Location_IsNominal.

Lemma mapm2E_cancel
  [T T' : ordType] [S S' : Type] [f : T → T'] [f' : T' → T] (g : S → S') 
    (m : {fmap T → S}) (x : T') :
    injective f → cancel f' f →
    mapm2 (T:=T) (T':=T') f g m x = omap g (m (f' x)).
Proof.
  intros H H'.
  rewrite -{1}(H' x).
  rewrite mapm2E //.
Qed.

Lemma rename_emptym_Locations π :
  π ∙ (emptym : Locations) = emptym.
Proof. done. Qed.

Lemma rename_setm_Locations π (m : Locations) n A :
  π ∙ (setm m n A : Locations)
    = setm (π ∙ m : Locations) (natize (π (atomize n))) A.
Proof.
  apply eq_fmap => n'.
  unfold rename. simpl.
  erewrite mapm2E_cancel.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply (can_comp (can_comp natizeK (fpermKV _)) atomizeK).
  rewrite omap_id 2!setmE //=.
  erewrite mapm2E_cancel.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply (can_comp (can_comp natizeK (fpermKV _)) atomizeK).
  rewrite omap_id.
  destruct (n' == natize (π (atomize n)))%B eqn:E.
  - rewrite E.
    move: E => /eqP E; subst.
    rewrite natizeK fpermK atomizeK eq_refl //.
  - rewrite E.
    move: E => /eqP E.
    assert ((natize ((π^-1)%fperm (atomize n')) == n)%B = false).
    2: rewrite H //=.
    apply /eqP => H.
    subst.
    rewrite natizeK fpermKV atomizeK // in E.
Qed.

Program Definition Locations_IsNominal
  : IsNominal Locations
  := IsNominal.Build _ (λ L : Locations, atomize @: domm L) _ _.
Obligation 1.
  move: x.
  refine (fmap_ind _ _); [ done |].
  move=> m H n A /dommPn H'.
  rewrite domm_set imfsetU1.
  intros π H''.
  rewrite rename_setm_Locations.
  apply eq_fmap => n'.
  rewrite 2!setmE.
  rewrite (H'' (atomize n)) ?atomizeK.
  2: apply /fsetU1P; by left.
  rewrite H //.
  intros a H'''.
  apply H''.
  apply /fsetU1P; by right.
Qed.
Obligation 2.
  apply (@fsubset_equi Locations x F (λ x, atomize @: domm x)).
  2: done. move=> {H} {x} {F}.
  intros π.
  refine (fmap_ind _ _).
  1: rewrite rename_emptym_Locations domm0 imfset0 /rename //= imfset0 //.
  intros m H n A H'.
  rewrite rename_setm_Locations.
  rewrite 2!domm_set 2!imfsetU 2!imfset1 natizeK -H.
  rewrite /rename //= imfsetU imfset1 //.
Qed.

HB.instance Definition _ : IsNominal Locations
  := Locations_IsNominal.

Lemma supp_Locations {l : Location} {L : Locations}
  : fhas L l → (supp l :<=: supp L)%fset.
Proof.
  intros H.
  destruct l.
  unfold supp; simpl.
  rewrite fsub1set.
  apply mem_imfset.
  apply /dommP.
  exists c.
  apply H.
Qed.

Lemma valid_support_code {T S : choice_type} {L I} (c : T → raw_code S) {x : T}
  : ValidCode L I (c x) → support_set (c x) (supp L).
Proof.
  intros V.
  induction V => π H'.
  + done.
  + unfold rename; simpl.
    f_equal.
    apply functional_extensionality.
    intros t.
    apply H1, H'.
  + unfold rename; simpl.
    destruct l.
    unfold rename; simpl.
    f_equal.
    * intros _ eq eq'.
      noconf eq.
      rewrite H2 eq'.
      f_equal.
    * rewrite H' //.
      apply supp_Locations in H.
      rewrite fsub1set in H.
      apply H.
    * apply functional_extensionality => t.
      apply H1, H'.
  + unfold rename; simpl.
    destruct l.
    unfold rename; simpl.
    f_equal.
    * intros _ eq _ eq'.
      noconf eq.
      rewrite H0 eq'.
      f_equal.
    * rewrite H' //.
      apply supp_Locations in H.
      rewrite fsub1set in H.
      apply H.
    * apply IHV, H'.
  + unfold rename; simpl.
    f_equal.
    apply functional_extensionality => t.
    apply H0, H'.
Qed.

Lemma valid_support_package {L I E p} `{ValidPackage L I E p}
  : support_set p (supp L).
Proof.
  move: H => V.
  intros π H.
  unfold rename; simpl.
  apply eq_fmap => k.

  rewrite mapmE.
  destruct (p k) as [[T [S c]]|] eqn:eq; [| done ].
  simpl; f_equal.
  unfold rename; simpl.
  simpl; do 2 f_equal.
  apply functional_extensionality.
  destruct V as [Ve Vi].
  specialize (Ve (k, (T, S))).
  intros x.
  specialize (Vi k (T; _) x eq).
  simpl in Vi.
  eapply valid_support_code.
  { apply Vi. }
  apply H.
Qed.


(* Modules *)

Record nom_package := mkNom
  { loc : Locations
  ; val :> raw_package
  ; has_support : support_set val (supp loc)
  }.

Definition nom_package_from_valid {L I E} p
  `{H : ValidPackage L I E p} : nom_package :=
  {| loc := L
  ;  val := p
  ;  has_support := @valid_support_package _ _ _ _ H
  |}.

Definition as_nom {I E} : package I E → nom_package
  := λ t, nom_package_from_valid (pack t).

Coercion as_nom : package >-> nom_package.


Lemma eq_raw_module {P P' : nom_package}
  : loc P = loc P'
  → val P = val P'
  → P = P'.
Proof.
  intros H1 H2.
  destruct P, P'.
  simpl in *.
  subst.
  rewrite (proof_irrelevance _ has_support0 has_support1) //.
Qed.


(* Linking lemmas *)

Lemma rename_resolve f p o x : f ∙ (resolve p o x) = resolve (f ∙ p) o x.
Proof.
  unfold resolve.
  rewrite mapmE //=.
  destruct (p o.1) => //=.
  destruct t as [S [T g]].
  rewrite coerce_kleisli_rename //.
Qed.

Lemma rename_link : ∀ f p q, rename f (p ∘ q) = rename f p ∘ rename f q.
Proof.
  intros f p q.
  rewrite /link /rename //=.
  rewrite -mapm_comp -mapm_comp.
  apply eq_mapm => t.
  destruct t as [T [P k]].
  unfold rename; simpl.
  do 2 f_equal.
  apply functional_extensionality => t.
  generalize (k t); elim.
  + done.
  + intros.
    rewrite {2}/rename //=.
    rewrite mcode_bind.
    rewrite rename_resolve.
    by setoid_rewrite <- H.
  + intros.
    destruct l.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
  + intros.
    destruct l.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
  + intros.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
Qed.

Lemma supp_fsetU {X : nomOrdType} {A B : {fset X}} : supp (A :|: B) = supp A :|: supp B.
Proof. apply fsetSuppU. Qed.

Lemma supp_Locations_unionm {A B : Locations} : supp (unionm A B : Locations) = supp A :|: supp B.
Proof. rewrite /supp //= domm_union imfsetU //. Qed.

(* holds for any equivariant binary function? *)
Lemma support_link {P P'} {S S' : Locations}
  : support_set P (supp S) → support_set P' (supp S')
  → support_set (P ∘ P') (supp (unionm S S' : Locations)).
Proof.
  intros s1 s2 π H.
  rewrite rename_link.
  f_equal.
  - apply s1.
    intros a M.
    apply H.
    rewrite supp_Locations_unionm.
    apply /fsetUP; by left.
  - apply s2.
    intros a M.
    apply H.
    rewrite supp_Locations_unionm.
    apply /fsetUP; by right.
Qed.

Definition share_link (P P' : nom_package)
  := {| loc := unionm (loc P) (loc P')
      ; val := link (val P) (val P')
      ; has_support := support_link (has_support P) (has_support P')
      |}.

Declare Scope share_scope.
Delimit Scope share_scope with share.
(* Bind Scope share_scope with raw_module. *)
Open Scope share.


Notation "p1 ∘ p2" :=
  (share_link p1 p2) (right associativity, at level 20) : share_scope.


Lemma share_link_assoc p1 p2 p3
  : p1 ∘ p2 ∘ p3 = (p1 ∘ p2) ∘ p3.
Proof.
  apply eq_raw_module; rewrite //=.
  - rewrite unionmA //.
  - rewrite link_assoc //.
Qed.


(* ID lemmas *)

Lemma share_link_id {L I E} {p : nom_package} `{ValidPackage L I E p}
  : p ∘ ID I = p.
Proof.
  apply eq_raw_module; rewrite //=.
  - rewrite unionm0 //.
  - rewrite link_id //.
Qed.

Lemma id_share_link {L I E} {p : nom_package} `{ValidPackage L I E p}
  : ID E ∘ p = p.
Proof.
  apply eq_raw_module; rewrite //= id_link //.
Qed.


(* Par theorems *)

Lemma rename_par : ∀ f p q, rename f (par p q : raw_package) = par (rename f p) (rename f q).
Proof.
  intros f p q.
  rewrite /par /rename //=.
  apply eq_fmap => n.
  rewrite unionmE 3!mapmE unionmE.
  destruct (p n), (q n); done.
Qed.

Lemma support_par {P P'} {S S' : Locations}
  : support_set P (supp S) → support_set P' (supp S') → support_set (par P P' : raw_package) (supp (unionm S S' : Locations)).
Proof.
  intros s1 s2 π H.
  rewrite rename_par.
  f_equal.
  - apply s1.
    intros a M.
    apply H.
    rewrite supp_Locations_unionm.
    apply /fsetUP; by left.
  - apply s2.
    intros a M.
    apply H.
    rewrite supp_Locations_unionm.
    apply /fsetUP; by right.
Qed.

Definition share_par (P P' : nom_package)
  := {| loc := unionm (loc P) (loc P')
      ; val := par (val P) (val P')
      ; has_support := support_par (has_support P) (has_support P')
      |}.

Notation "p1 || p2" :=
  (share_par p1 p2) : share_scope.

Lemma share_par_commut (p1 p2 : nom_package) :
  fcompat (loc p1) (loc p2) →
  fcompat (val p1) (val p2) →
  p1 || p2 = p2 || p1.
Proof.
  intros H1 H2.
  by apply eq_raw_module.
Qed.

Lemma share_par_assoc {P1 P2 P3 : nom_package}
  : (P1 || (P2 || P3)) = ((P1 || P2) || P3).
Proof.
  apply eq_raw_module; rewrite //=.
  - rewrite unionmA //.
  - rewrite par_assoc //.
Qed.

Lemma share_interchange {A B C D E F} {L1 L2 L3 L4} (p1 p2 p3 p4 : nom_package)
  `{ValidPackage L1 B A p1} `{ValidPackage L2 E D p2}
  `{ValidPackage L3 C B p3} `{ValidPackage L4 F E p4} :
  fcompat (loc p2) (loc p3) →
  fseparate (val p3) (val p4) →
  (p1 ∘ p3) || (p2 ∘ p4) = (p1 || p2) ∘ (p3 || p4).
Proof.
  intros loc23 val34.
  apply eq_raw_module; rewrite //=.
  - rewrite unionmA -(unionmA (loc p1)) -loc23 2!unionmA //.
  - rewrite interchange //.
Qed.


(* Definition as Nominal *)


Lemma rename_support_set {X : actionType}
  : ∀{x : X} {loc} {π}, support_set x loc → support_set (π ∙ x) (rename π loc).
Proof.
  intros x loc π ss.
  rewrite -(equi2_use _ support_set_equi).
  rewrite absorb //.
Qed.

Program Definition raw_module_HasAction
  := HasAction.Build nom_package
    (λ π P, mkNom (π ∙ loc P) (π ∙ val P) (rename_support_set (has_support P))) _ _.
Obligation 1.
  rewrite supp_equi //.
Qed.
Obligation 2.
  apply eq_raw_module; rewrite //= rename_id //.
Qed.
Obligation 3.
  apply eq_raw_module; rewrite //= rename_comp //.
Qed.

HB.instance Definition _ : HasAction nom_package
  := raw_module_HasAction.

Lemma supp_atoms (A : {fset atom}) : supp A = A.
Proof.
  unfold supp; simpl.
  rewrite -(fsvalK A).
  elim: (\val A).
  { rewrite -fset0E fsetSupp0 //. }
  intros a L H.
  rewrite fset_cons fsetSuppU fsetSupp1 H //.
Qed.

Program Definition raw_module_IsNominal
  : IsNominal nom_package
  := IsNominal.Build _ (λ p, supp (loc p)) _ _.
Obligation 1.
  intros π H.
  apply eq_raw_module; rewrite /rename //=.
  + rewrite is_support //= supp_atoms //.
  + apply has_support, H.
Qed.
Obligation 2.
  destruct x as [L p H'] => //=.
  eapply support_sub.
  intros π H''.
  specialize (H π H'') => {H''}.
  rewrite /rename //= in H.
  inversion H.
  rewrite 2!H1 //.
Qed.

HB.instance Definition _ : IsNominal nom_package
  := raw_module_IsNominal.

Lemma loc_share_link {P P' : nom_package} {π}
  : loc (π ∙ P ∘ P') = unionm (loc (π ∙ P)) (loc (π ∙ P')).
Proof.
  apply eq_fmap => n.
  simpl. unfold rename. simpl.
  erewrite mapm2E_cancel.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply (can_comp (can_comp natizeK (fpermKV _)) atomizeK).
  rewrite 2!unionmE.
  erewrite mapm2E_cancel.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply (can_comp (can_comp natizeK (fpermKV _)) atomizeK).
  erewrite mapm2E_cancel.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply (can_comp (can_comp natizeK (fpermKV _)) atomizeK).
  rewrite 3!omap_id.
  reflexivity.
Qed.

Lemma s_share_link {P P' : nom_package}
  : supp (P ∘ P') = supp P :|: supp P'.
Proof.
  rewrite -supp_Locations_unionm //.
Qed.

Lemma val_share_link {P P' : nom_package} {π}
  : val (π ∙ P ∘ P') = (π ∙ P) ∘ (π ∙ P').
Proof.  
  unfold rename; simpl.
  rewrite rename_link //.
Qed.

Lemma rename_share_link {P P' : nom_package} {π} :
  π ∙ P ∘ P' = (π ∙ P) ∘ (π ∙ P').
Proof.
  apply eq_raw_module.
  + rewrite loc_share_link //.
  + rewrite val_share_link //=.
Qed.

Lemma val_share_par {P P' : nom_package} {π}
  : val (π ∙ (P || P')) = (π ∙ P) || (π ∙ P').
Proof.
  unfold rename; simpl.
  rewrite rename_par.
  f_equal.
Qed.

Lemma s_share_par {P P' : nom_package}
  : supp (P || P') = supp P :|: supp P'.
Proof.
  rewrite -supp_Locations_unionm //.
Qed.

Lemma rename_share_par {P P' : nom_package} {π} :
  π ∙ (P || P') = (π ∙ P) || (π ∙ P').
Proof.
  apply eq_raw_module.
  + rewrite loc_share_link //.
  + rewrite val_share_par //=.
Qed.

Open Scope nominal_scope.

Lemma share_link_congr {P P' Q Q' : nom_package} :
  disj P Q → 
  disj P' Q' → 
  P ≡ P' →
  Q ≡ Q' →
  P ∘ Q ≡ P' ∘ Q'.
Proof.
  intros D1 D2 [π E1] [π' E2].
  subst.
  exists (split_pi π π' (supp P) (supp Q)).
  rewrite rename_share_link.
  rewrite split_pi_left.
  1: rewrite split_pi_right; [ done | | done |].
  1: apply (is_support Q).
  2: apply (is_support P).
  1,2: rewrite 2!supp_equi.
  1,2: apply D2.
Qed.

Lemma share_par_congr {P P' Q Q' : nom_package} :
  disj P Q →
  disj P' Q' →
  P ≡ P' →
  Q ≡ Q' →
  (P || Q) ≡ (P' || Q').
Proof.
  intros D1 D2 [π E1] [π' E2].
  subst.
  exists (split_pi π π' (supp P) (supp Q)).
  rewrite rename_share_par.
  rewrite split_pi_left.
  1: rewrite split_pi_right; [ done | | done |].
  1: apply (is_support Q).
  2: apply (is_support P).
  1,2: rewrite 2!supp_equi.
  1,2: apply D2.
Qed.
