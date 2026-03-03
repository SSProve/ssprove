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

Import GRing.Theory Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import PackageNotation.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
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
  heap → SDistr (F_choice_prod_obj ⟨ A , heap : choiceType ⟩) :=
  λ s, thetaFstd A (repr p) s.

Definition Pr_op (p : raw_package) (o : opsig) (x : src o) :
  heap → SDistr (F_choice_prod_obj ⟨ tgt o , heap : choiceType ⟩) :=
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

Lemma Advantage_par_empty :
  ∀ G₀ G₁ A,
  AdvantageE (par emptym G₀) (par emptym G₁) A = AdvantageE G₀ G₁ A.
Proof.
  intros G₀ G₁ A.
  unfold AdvantageE.
  rewrite distrC.
  reflexivity.
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
  rewrite ?addrA in ineq.

Tactic Notation
  "ssprove" "triangle" constr(p₀) constr(l) constr(p₁) constr(A)
  "as" ident(ineq) :=
  ssprove_triangle_as p₀ l p₁ A ineq.
