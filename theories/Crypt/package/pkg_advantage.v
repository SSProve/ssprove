(** Notion of adversary and advantage *)


From Coq Require Import Utf8.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr
  StateTransfThetaDens choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics fmap_extra.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import PackageNotation.

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

Definition Game_import : Interface := [interface].

Notation game E := (package Game_import E).

Definition RUN := (0%N, ('unit, 'bool)).

Definition A_export : Interface := mkfmap [:: RUN ].

Notation adversary I := (package I A_export).

Lemma RUN_in_A_export : A_export RUN.1 = Some RUN.2.
Proof.
  rewrite setmE //.
Qed.


Definition Game_op_import_S : Type := {_ : ident & void}.

Definition Game_import_P : Game_op_import_S → choiceType :=
  λ v, let 'existT a b := v in match b with end.

Definition Pr_code {A} (p : raw_code A) :
  heap_choiceType → SDistr (F_choice_prod_obj ⟨ A , heap_choiceType ⟩) :=
  λ s, thetaFstd A (repr p) s.

(* TODO REMOVE? *)
Definition Pr_raw_func_code {A B} (p : A → raw_code B) :
  A → heap_choiceType → SDistr (F_choice_prod_obj ⟨ B , heap_choiceType ⟩) :=
  λ a s, Pr_code (p a) s.

Definition Pr_op (p : raw_package) (o : opsig) (x : src o) :
  heap_choiceType → SDistr (F_choice_prod_obj ⟨ tgt o , heap_choiceType ⟩) :=
  Pr_code (resolve p o x).

Arguments SDistr_bind {_ _}.

Definition Pr (p : raw_package) :
  SDistr (bool:choiceType) :=
  SDistr_bind
    (λ '(b, _), SDistr_unit _ b)
    (Pr_op p RUN tt empty_heap).

Definition Advantage (G : bool → raw_package) (A : raw_package) : R :=
  `| Pr (A ∘ (G false)) true - Pr (A ∘ (G true)) true |.

Definition AdvantageE (G₀ G₁ : raw_package) (A : raw_package) : R :=
  `| Pr (A ∘ G₀) true - Pr (A ∘ G₁) true |.

(* TODO We could have the following
  Not clear it would be an improvement. It would be shorter but maybe not
  as easy to work with.
*)

(* Record AdversaryFor {I} (G : loc_GamePair I) := mkAdversary {
  adv_pack : loc_package I A_export ;
  adv_disj_false : fdisjoint adv_pack.(locs) (G false).(locs) ;
  adv_disj_true : fdisjoint adv_pack.(locs) (G true).(locs)
}.

Coercion adv_pack : AdversaryFor >-> loc_package. *)

(* TODO Update to the new setting *)
(* Lemma pr_weak {Game_export : Interface}
  (A : Adversary4Game Game_export) (G : loc_package _ _) :
  Pr {locpackage link (turn_adversary_weak A) G } true =
  Pr {locpackage link A G } true.
Proof.
Admitted. *)

(* TODO UPDATE, first figure out what its role is *)
(* Definition perf_ind {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
  ∀ A,
    fdisjoint A.(locs) G0.(locs) →
    fdisjoint A.(locs) G1.(locs) →
    AdvantageE G0 G1 A = 0. *)

(* TODO UPDATE *)
(* Definition perf_ind_weak {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export) :=
  ∀ A, AdvantageE_weak G0 G1 A = 0. *)

(* Definition perf_ind_weak_implies_perf_ind {Game_export : Interface}
  (G0 : Game_Type Game_export) (G1 : Game_Type Game_export)
  (h : perf_ind_weak G0 G1) : perf_ind G0 G1.
Proof.
  unfold perf_ind, perf_ind_weak, AdvantageE, AdvantageE_weak in *.
  intros A H1 H2.
  rewrite -(pr_weak A G0).
  rewrite -(pr_weak A G1).
  apply h.
Qed. *)

(* Notation "ε( GP )" :=
  (AdvantageE (GP false) (GP true))
  (at level 90)
  : package_scope. *)

Definition state_pass_ {A} (p : raw_code A) :
  heap_choiceType → raw_code (prod A heap_choiceType).
Proof.
  induction p; intros h.
  - constructor.
    exact (x, h).
  - apply (opr o).
    + exact x.
    + intros v. exact (X v h).
  - apply X.
    + exact (get_heap h l).
    + exact h.
  - apply IHp.
    apply (set_heap h l v).
  - apply (sampler op).
    intros v. exact (X v h).
Defined.

Definition state_pass__valid {A} {L} {I} (p : raw_code A)
  (h : ValidCode L I p) :
  ∀ hp, ValidCode emptym I (state_pass_ p hp).
Proof.
  intro hp.
  unfold ValidCode in *.
  induction h in hp |- *.
  - cbn. constructor.
  - simpl. constructor.
    + assumption.
    + intros t. eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. constructor.
    intros v. eauto.
Qed.

Definition state_pass {A} (p : raw_code A) : raw_code A :=
  bind (state_pass_ p empty_heap) (λ '(r, _), ret r).

Definition state_pass_valid {A} {L} {I} (p : raw_code A)
  (h : ValidCode L I p) :
  ValidCode emptym I (state_pass p).
Proof.
  apply valid_bind.
  - apply (state_pass__valid p h empty_heap).
  - intros x. destruct x. constructor.
Qed.

(* MK: To be solved by nominals.
(* TODO Will have to be updated *)
(* Probably by having first an operation on raw_packages
  and then a validity proof.
*)
Definition turn_adversary_weak  {Game_export : Interface}
  (A : Adversary4Game Game_export) : Adversary4Game_weak Game_export.
Proof.
  unfold Adversary4Game_weak.
  pose (get_op A RUN RUN_in_A_export tt) as run.
  destruct run as [run valid_run].
  cbn in *.
  pose (state_pass run) as raw_run_st.
  pose (state_pass_valid run valid_run) as raw_run_st_valid.
  apply funmkpack.
  - unfold flat, A_export.
    intros n u1 u2.
    move /fset1P => h1.
    move /fset1P => h2.
    inversion h1. inversion h2.
    reflexivity.
  - intros o.
    move /fset1P => hin.
    subst. intros _.
    exists raw_run_st.
    assumption.
Defined.
*)

Definition adv_equiv {L₀ L₁ E} (G₀ G₁ : raw_package)
  `{ValidPackage L₀ Game_import E G₀} `{ValidPackage L₁ Game_import E G₁} ε :=
  ∀ LA A,
    ValidPackage LA E A_export A →
    fseparate LA L₀ →
    fseparate LA L₁ →
    AdvantageE G₀ G₁ A = ε A.

Notation " G0 ≈[ R ] G1 " :=
  (adv_equiv G0 G1 R)
  (at level 50, format " G0  ≈[  R  ]  G1")
  : package_scope.

Notation " G0 ≈₀ G1 " :=
  (G0 ≈[ λ (_ : raw_package), 0 ] G1)
  (at level 50, format " G0  ≈₀  G1")
  : package_scope.

Lemma Advantage_equiv :
  ∀ I (G : bool → game I),
    (G false) ≈[ Advantage G ] (G true).
Proof.
  intros I G. intros LA A vA hd₀ hd₁. reflexivity.
Qed.

Lemma AdvantageE_equiv :
  ∀ I (G₀ G₁ : game I),
    G₀ ≈[ AdvantageE G₀ G₁ ] G₁.
Proof.
  intros I G₀ G₁. intros LA A vA hd₀ hd₁. reflexivity.
Qed.

Lemma Advantage_E :
  ∀ (G : bool → raw_package) A,
    Advantage G A = AdvantageE (G false) (G true) A.
Proof.
  intros G A.
  reflexivity.
Qed.

Lemma Advantage_link :
  ∀ G₀ G₁ A P,
    AdvantageE G₀ G₁ (A ∘ P) =
    AdvantageE (P ∘ G₀) (P ∘ G₁) A.
Proof.
  intros G₀ G₁ A P.
  unfold AdvantageE. rewrite !link_assoc. reflexivity.
Qed.

Lemma par_empty : forall G, par emptym G = G.
Proof. now setoid_rewrite union0m. Qed.

Lemma Advantage_par_empty :
  ∀ G₀ G₁ A,
  AdvantageE (par emptym G₀) (par emptym G₁) A = AdvantageE G₀ G₁ A.
Proof.
  intros G₀ G₁ A. now rewrite !par_empty.
Qed.

Lemma Advantage_par :
  ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁,
    ValidPackage L₀ Game_import E₀ G₀ →
    ValidPackage L₁ Game_import E₁ G₁ →
    ValidPackage L₁' Game_import E₁ G₁' →
    AdvantageE (par G₀ G₁) (par G₀ G₁') A =
    AdvantageE G₁ G₁' (A ∘ par G₀ (ID E₁)).
Proof.
  intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁ Va0 Va1 Va1'.
  replace (par G₀ G₁) with ((par G₀ (ID E₁)) ∘ (par (ID Game_import) G₁)).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    2: fmap_solve.
    rewrite link_id // id_link //.
  }
  replace (par G₀ G₁') with ((par G₀ (ID E₁)) ∘ (par (ID Game_import) G₁')).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    2: fmap_solve.
    rewrite link_id // id_link //.
  }
  rewrite -Advantage_link Advantage_par_empty //.
Qed.

Lemma par_emptyR : forall G, par G emptym = G.
Proof. now setoid_rewrite unionm0. Qed.

Lemma Advantage_par_emptyR :
  ∀ G₀ G₁ A,
  AdvantageE (par G₀ emptym) (par G₁ emptym) A = AdvantageE G₀ G₁ A.
Proof.
  intros G₀ G₁ A. now rewrite !par_emptyR.
Qed.

Lemma Advantage_parR :
  ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁,
    ValidPackage L₀ Game_import E₀ G₀ →
    ValidPackage L₁ Game_import E₁ G₁ →
    ValidPackage L₁' Game_import E₁ G₁' →
    AdvantageE (par G₁ G₀) (par G₁' G₀) A =
    AdvantageE G₁ G₁' (A ∘ par (ID E₁) G₀).
Proof.
  intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁ Va0 Va1 Va1'.
  replace (par G₁ G₀) with ((par (ID E₁) G₀) ∘ (par G₁ (ID Game_import))).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    2: fmap_solve.
    rewrite link_id // id_link //.
  }
  replace (par G₁' G₀) with ((par (ID E₁) G₀) ∘ (par G₁' (ID Game_import))).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    2: fmap_solve.
    rewrite link_id // id_link //.
  }
  replace (ID Game_import) with (emptym : raw_package) by now apply eq_fmap.
  rewrite -Advantage_link !Advantage_par_emptyR //.
Qed.

Lemma Advantage_sym :
  ∀ P Q A,
    AdvantageE P Q A = AdvantageE Q P A.
Proof.
  intros P Q A.
  unfold AdvantageE.
  rewrite distrC. reflexivity.
Qed.

Lemma adv_equiv_sym :
  ∀ L₀ L₁ E G₀ G₁ h₀ h₁ ε,
    @adv_equiv L₀ L₁ E G₀ G₁ h₀ h₁ ε →
    adv_equiv G₁ G₀ ε.
Proof.
  intros L₀ L₁ E G₀ G₁ h₀ h₁ ε h.
  intros LA A hA hd₁ hd₀.
  rewrite Advantage_sym.
  eapply h. all: eauto.
Qed.

Lemma Advantage_triangle :
  ∀ P Q R A,
    AdvantageE P Q A <= AdvantageE P R A + AdvantageE R Q A.
Proof.
  intros P Q R A.
  unfold AdvantageE.
  apply ler_distD.
Qed.

Fixpoint advantage_sum P l Q A :=
  match l with
  | [::] => AdvantageE P Q A
  | R :: l => AdvantageE P R A + advantage_sum R l Q A
  end.

Lemma Advantage_triangle_chain :
  ∀ P (l : seq raw_package) Q A,
    AdvantageE P Q A <= advantage_sum P l Q A.
Proof.
  intros P l Q A.
  induction l as [| R l ih] in P, Q |- *.
  - simpl. auto.
  - simpl. eapply order.Order.POrderTheory.le_trans.
    + eapply Advantage_triangle.
    + eapply lerD.
      * auto.
      * eapply ih.
Qed.

Lemma AdvantageE_le_0 :
  ∀ G₀ G₁ A,
    AdvantageE G₀ G₁ A <= 0 →
    AdvantageE G₀ G₁ A = 0.
Proof.
  intros G₀ G₁ A h.
  unfold AdvantageE in *.
  rewrite normr_le0 in h.
  apply/normr0P. auto.
Qed.

Lemma Advantage_le_0 :
  ∀ G A,
    Advantage G A <= 0 →
    Advantage G A = 0.
Proof.
  intros G A h.
  rewrite -> Advantage_E in *. apply AdvantageE_le_0. auto.
Qed.

Lemma TriangleInequality :
  ∀ {Game_export : Interface}
    {F G H : game Game_export}
    {ϵ1 ϵ2 ϵ3},
    F ≈[ ϵ1 ] G →
    G ≈[ ϵ2 ] H →
    F ≈[ ϵ3 ] H →
    ∀ LA A,
      ValidPackage LA Game_export A_export A →
      fseparate LA F.(locs) →
      fseparate LA G.(locs) →
      fseparate LA H.(locs) →
      ϵ3 A <= ϵ1 A + ϵ2 A.
Proof.
  intros Game_export F G H ε₁ ε₂ ε₃ h1 h2 h3 LA A vA hF hG hH.
  unfold adv_equiv in *.
  erewrite <- h1, <- h2, <- h3 by eassumption.
  apply ler_distD.
Qed.

Lemma Reduction :
  ∀ (M : raw_package) (G : bool → raw_package) A b,
    `| Pr (A ∘ (M ∘ (G b))) true | =
    `| Pr ((A ∘ M) ∘ (G b)) true |.
Proof.
  intros M G A b.
  rewrite link_assoc. reflexivity.
Qed.

Lemma ReductionLem :
  ∀ L₀ L₁ E M (G : bool → raw_package)
    `{ValidPackage L₀ Game_import E (M ∘ G false)}
    `{ValidPackage L₁ Game_import E (M ∘ G true)},
    (M ∘ (G false)) ≈[ λ A, Advantage G (A ∘ M) ] (M ∘ (G true)).
Proof.
  intros L₀ L₁ E M G v₀ v₁.
  unfold adv_equiv. intros LA A vA hd₀ hd₁. rewrite Advantage_E.
  unfold AdvantageE. rewrite !link_assoc. reflexivity.
Qed.

Ltac advantage_sum_simpl_in h :=
  repeat
    change (advantage_sum ?P (?R :: ?l) ?Q ?A)
    with (AdvantageE P R A + advantage_sum R l Q A) in h ;
  change (advantage_sum ?P [::] ?Q ?A) with (AdvantageE P Q A) in h.

Ltac ssprove_triangle_as p₀ l p₁ A ineq :=
  pose proof (Advantage_triangle_chain p₀ l p₁ A) as ineq ;
  advantage_sum_simpl_in ineq ;
  rewrite ?ssralg.GRing.addrA in ineq.

Tactic Notation
  "ssprove" "triangle" constr(p₀) constr(l) constr(p₁) constr(A)
  "as" ident(ineq) :=
  ssprove_triangle_as p₀ l p₁ A ineq.

Lemma unionm_isSome :
  forall {T : ordType} {S} (m m' : {fmap T -> S}) o,
    isSome (unionm m m' o) <-> isSome (m o) ∨ isSome (m' o).
Proof.
  intros ? ? ? ? ?.
  rewrite unionmE.
  destruct (m o) ; split ; [  left |  |  right | intros [] ] ; easy.
Qed.

Lemma fhas_unionm_iff : forall {T : ordType} {S} (m m' : {fmap T -> S}) o,
    fhas (unionm m m') o <-> (fhas m o ∨ (m o.1 = None /\ fhas m' o)).
Proof.
  intros ? ? ? ? [k v].
  unfold fhas.
  simpl.
  rewrite unionmE.
  destruct (m k) ; split ; [ left | intros [ | [] ] | right | intros [] ] ; easy.
Qed.

Lemma simple_neg :
  forall (E1 : Interface) (p1 : raw_package),
  ∀ o,
    (forall (s t : choice_type), fhas E1 (o, (s, t)) ↔ (∃ f, fhas p1 (o, (s; t; f)))) ->
    (E1 o = None ↔ p1 o = None).
Proof.
  intros E1 p1 o.
  intros.
  split ; [
      destruct (p1 o) as [ [s [t f]] | ] eqn:p1o ; [ intros ; exfalso | reflexivity ]
    | destruct (E1 o) as [ [ s t ] | ] eqn:E1o ; [ intros ; exfalso | reflexivity ] ] ; specialize (H s t).
  all: rewrite <- (boolp.iff_not2) in H ; rewrite <- boolp.forallNP in H ;  simpl in H.
  - assert (E1 o <> Some (s, t)) by now rewrite H0.
    now specialize (proj1 H H1 f).
  - assert (forall x, p1 o <> Some (s; t; x)) by now intros ; rewrite H0.
    now specialize (proj2 H H1).
Qed.

Lemma simple_neg2 :
  forall (E1 : Interface) (p1 : raw_package),
  ∀ o,
    (E1 o = None ↔ p1 o = None) -> (E1 = mapm (λ '(So; To; _), (So, To)) p1) ->
    forall (s t : choice_type), fhas E1 (o, (s, t)) ↔ (∃ f, fhas p1 (o, (s; t; f))).
Proof.
  intros E1 p1 o.
  intros ?.
  intros ?.

  apply eq_fmap in H0.
  specialize (H0 o).
  rewrite mapmE in H0.
  unfold omap, obind, oapp in H0.
  simpl.
  rewrite H0 ; clear H0.

  destruct (getm p1 o) as [[s1 [t1 f1]]|] eqn:p1o_eq ; rewrite p1o_eq.
  2: now split ; [ | intros [] ].
  intros.
  split.
  - intros. inversion H0 ; subst. now exists f1.
  - now intros [] ; inversion H0 ; subst.
Qed.


Lemma ValidPackage_eq : forall L I E p, ValidPackage L I E p <-> E = mapm (λ '(So; To; _), (So, To)) p /\ ∀ (n : Datatypes_nat__canonical__Ord_Ord) (F : typed_raw_function) (x : F.π1),
    fhas p (n, F) → ValidCode L I ((F.π2).π2 x).
Proof.
  clear ; intros.
  split.
  - intros ?.
    split.
    + apply (valid_exports_eq _).
    + apply H.
  - intros [] ; subst.
    constructor.
    + intros [o [s t]].
      simpl.
      rewrite mapmE.
      unfold omap, obind, oapp.
      destruct (getm p o) as [[s1 [t1 f1]]|] eqn:p1o_eq ; rewrite p1o_eq ; [ clear p1o_eq | split ; [ | intros [] ] ; discriminate ].
      split.
      * intros. inversion H ; subst. now exists f1.
      * intros []. now inversion H ; subst.
    + apply H0.
Qed.

Lemma fcompat_fhas_case :
  forall {T : ordType} {S} {E1 E2 : {fmap T -> S}},
  fcompat E1 E2 ->
  forall o, (fhas E1 o -> (fhas E2 o \/ E2 o.1 = None)).
Proof.
  intros ? ? ? ? ? [k v] ?.
  simpl.
  epose proof (proj1 (fhas_unionm_iff E2 E1 (k, v))).
  rewrite <- H in H1.
  specialize (H1 ((fhas_union_l _ _ _ _ H0))).

  epose proof (proj1 (fhas_unionm_iff E1 E2 (k, v)) (fhas_union_l _ _ _ _ H0)).

  destruct H1 as [| []].
  + now left.
  + destruct H2 as [| [] ].
    * now right.
    * now left.
Qed.

Lemma fcompat_split_unionm :
  forall {T : ordType} {S} {E1 E2 : {fmap T -> S}},
  fcompat E1 E2 ->
  forall o,
    fhas (unionm E1 E2) o ->
    (E1 o.1 = Some o.2 <-> E2 o.1 = None)
    \/ (E1 o.1 = None <-> E2 o.1 = Some o.2)
    \/ (E1 o.1 = Some o.2 <-> E2 o.1 = Some o.2).
Proof.
  intros ? ? ? ? ? [k v] ?.

  simpl.
  epose proof (proj1 (fhas_unionm_iff E2 E1 (k, v))).
  rewrite <- H in H1.
  specialize (H1 H0).

  epose proof (proj1 (fhas_unionm_iff E1 E2 (k, v)) H0).

  destruct H1 as [| []].
  + destruct H2 as [| [] ].
    * rewrite H1 H2.
      now right ; right.
    * rewrite H1 H2.
      now right ; left.
  + rewrite H1 H3.
    now left.
Qed.

Lemma valid_package_inject_export_weak :
  ∀ L I E1 E2 p1 p2,
    fseparate E1 E2 ->
    E1 = mapm (λ '(So; To; _), (So, To)) p1 ->
    E2 = mapm (λ '(So; To; _), (So, To)) p2 ->
    ValidPackage L I E1 p1 /\ ValidPackage L I E2 p2 <->
    ValidPackage L I (unionm E1 E2) (unionm p1 p2).
Proof.
  intros ? ? ? ? ? ? ?.
  split ; [ intros [] | intros ].
  - rewrite <- (unionmI L).
    rewrite <- (unionmI I).
    now apply valid_par.
  - rewrite ValidPackage_eq in H2. destruct H2.
    rewrite !ValidPackage_eq.
    split ; split ; [ assumption | | assumption | ].
    + intros.
      eapply H3.
      apply fhas_union_l.
      apply H4.
    + intros.

      rewrite unionmC in H3.
      2:{
        destruct H as [H].
        subst.
        rewrite !domm_map in H.
        apply H.
      }
      eapply H3.
      apply fhas_union_l.
      apply H4.
Qed.

Lemma package_duplicate :
  forall p, p = par p p.
Proof.
  intros.
  unfold par.
  now rewrite unionmI.
Qed.

Lemma Advantage_split_par :
  forall {LA IA EA},
  forall {LB IB EB},
  forall {A : bool -> raw_package}
    {B : bool -> raw_package}
    {C : bool -> raw_package}
    {K : bool -> raw_package},
    fsubmap IA EB ->
    (forall b, ValidPackage LA IA EA (A b)) ->
    (forall b, ValidPackage LB IB EB (B b)) ->
    (forall b, K b = par (B b) (C b)) ->
    forall Adv,
    forall ε,
      ((AdvantageE (A false ∘ B false) (A true ∘ B true) Adv <= ε)%R) ->
      ((AdvantageE (A false ∘ K false) (A true ∘ K true) Adv <= ε)%R).
Proof.
  intros.
  subst.
  rewrite !H2.
  rewrite link_par_left ; [ | easy .. ].
  rewrite link_par_left ; [ | easy .. ].
  apply H3.
Qed.

Lemma Advantage_split_parR :
  forall {LA IA EA},
  forall {LC IC EC},
  forall {A : bool -> raw_package}
    {B : bool -> raw_package}
    {C : bool -> raw_package}
    {K : bool -> raw_package},
    fsubmap IA EC ->
    (forall b, fseparate (B b) (C b)) ->
    (forall b, ValidPackage LA IA EA (A b)) ->
    (forall b, ValidPackage LC IC EC (C b)) ->
    (forall b, K b = par (B b) (C b)) ->
    forall Adv,
    forall ε,
      ((AdvantageE (A false ∘ C false) (A true ∘ C true) Adv <= ε)%R) ->
      ((AdvantageE (A false ∘ K false) (A true ∘ K true) Adv <= ε)%R).
Proof.
  intros.
  subst.
  rewrite !H3.
  rewrite link_par_right ; [ | easy .. ].
  rewrite link_par_right ; [ | easy .. ].
  apply H4.
Qed.

Lemma Advantage_common_par :
  forall {LA IA EA},
  forall {LB IB EB},
  forall {LK IK EK},
  forall {A : bool -> raw_package}
    {B : bool -> raw_package}
    {K : bool -> raw_package},
    fsubmap IA EK ->
    fsubmap IB EK ->
    fsubmap IK [interface] ->
    (forall b, ValidPackage LA IA EA (A b)) ->
    (forall b, ValidPackage LB IB EB (B b)) ->
    (forall b, ValidPackage LK IK EK (K b)) ->
    fcompat LA LK ->
    fcompat LB LK ->
    forall Adv,
    forall ε ν,
      ((AdvantageE (A false ∘ K false) (A true ∘ K true) (Adv ∘ par (ID EA) (B true ∘ K true)) <= ε)%R) ->
      ((AdvantageE (B false ∘ K false) (B true ∘ K true) (Adv ∘ par (A false ∘ K false) (ID EB)) <= ν)%R) ->
      ((AdvantageE (par (A false) (B false) ∘ K false) (par (A true) (B true) ∘ K true) Adv <= ν + ε)%R).
Proof.
  intros.
  erewrite <- !interchange_alt.
  4,7: apply H4.
  2,4: now eapply valid_package_inject_import ; [ | eapply H2 ].
  2,3: eapply H3.
  eapply order.Order.POrderTheory.le_trans ; [ eapply Advantage_triangle with (R := par (A false ∘ K false) (B true ∘ K true)) | ].
  apply Num.Theory.lerD.
  {
    erewrite Advantage_par.
    2-4: eapply valid_link ; try eapply valid_package_inject_import ; auto ; assumption.
    apply H8.
  }
  {
    erewrite Advantage_parR.
    2-4: eapply valid_link ; try eapply valid_package_inject_import ; auto ; assumption.
    apply H7.
  }
Qed.

Corollary Advantage_common_par0 :
  forall {LA IA EA},
  forall {LB IB EB},
  forall {LK IK EK},
  forall {A : bool -> raw_package}
    {B : bool -> raw_package}
    {K : bool -> raw_package},
    fsubmap IA EK ->
    fsubmap IB EK ->
    fsubmap IK [interface] ->
    (forall b, ValidPackage LA IA EA (A b)) ->
    (forall b, ValidPackage LB IB EB (B b)) ->
    (forall b, ValidPackage LK IK EK (K b)) ->
    fcompat LA LK ->
    fcompat LB LK ->
    forall Adv,
    ((AdvantageE (A false ∘ K false) (A true ∘ K true) (Adv ∘ par (ID EA) (B true ∘ K true)) <= 0)%R) ->
    ((AdvantageE (B false ∘ K false) (B true ∘ K true) (Adv ∘ par (A false ∘ K false) (ID EB)) <= 0)%R) ->
    ((AdvantageE (par (A false) (B false) ∘ K false) (par (A true) (B true) ∘ K true) Adv <= 0)%R).
Proof. intros. rewrite <- (GRing.add0r 0%R). now rewrite Advantage_common_par. Qed.
