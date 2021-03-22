From Coq Require Import RelationClasses Morphisms Utf8.

From Mon Require Import
     FiniteProbabilities
     SPropMonadicStructures
     SpecificationMonads
     MonadExamples
     SPropBase.

From Relational Require Import
     OrderEnrichedCategory
     OrderEnrichedRelativeMonadExamples
     Commutativity
     GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     Theta_dens
     Theta_exCP
     LaxComp
     FreeProbProg
     RelativeMonadMorph_prod.

Import SPropNotations.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.


Module DerivedRules.


Local Definition squ := commuting_unary_base_square.
Local Definition ϕ_d :=
  @RelativeMonadMorph_prod.cmtSqu _ _ _ _ _ _ squ
                                  _ _ _ _ _ _ squ.

Local Definition MFreePr := rFreePr.

Local Definition Ops := P_OP.
Local Definition Arit := P_AR.

Local Definition Call (s : Ops) : MFreePr (Arit s) :=
  ropr _ _ _ s (fun r => retrFree _ _ _ r).

Local Definition θ0 {A} (c : MFreePr A) :=
  unary_theta_dens _ c.


Lemma θ0_preserves_bind A B (c1 c2 : MFreePr A) (f1 f2 : A -> MFreePr B) (Hc : θ0 c1 = θ0 c2)
      (Hf : forall v, θ0 (f1 v) = θ0 (f2 v))
  : θ0 (bindrFree _ _ c1 f1) = θ0 (bindrFree _ _ c2 f2).
Proof.
  pose (rmm_law2 _ _ _ _ (@unary_theta_dens) _ _ f1).
  simpl in e.
  apply equal_f with (x := c1) in e.
  rewrite /θ0 /unary_theta_dens /=.
  rewrite e.
  pose (rmm_law2 _ _ _ _ (@unary_theta_dens) _ _ f2).
  simpl in e0.
  apply equal_f with (x := c2) in e0.
  rewrite /θ0 /unary_theta_dens /=.
  rewrite e0.
  rewrite /θ0 /unary_theta_dens /= in Hc.
  rewrite Hc.
  rewrite /θ0 /unary_theta_dens /= in Hf.
  f_equal.
  extensionality x.
  apply Hf.
Qed.

Notation "x <- c1 ;; c2" := (ord_relmon_bind MFreePr (fun x => c2) c1)
                             (right associativity, at level 84, c1 at next level).

Notation " x ∈ T <<- c1 ;; c2 " := (ord_relmon_bind MFreePr (fun x : T => c2) c1)
                             (right associativity, at level 90, c1 at next level).

Notation "c1 ;; c2" := (ord_relmon_bind MFreePr (fun _ => c2) c1) (at level 100, right associativity).

Definition pure {X : ord_choiceType} (x : X) := ord_relmon_unit MFreePr _ x.

Definition retF { A : choiceType } (a : A) := retrFree Ops Arit A a.

(* Notation " A <$ c " := (@sample_from probE chUniverse chElement Hch A c) (at level 100). *)


Definition M_d := (@RelativeMonadMorph_prod.Mprod _ _ _  MFreePr _ _ _ MFreePr ).

Definition ϕ_ex := ϕ.


Definition θ_dens_lax := relativeMonadMorphism_to_lax _ _ _ _ theta_dens.
Check θ_dens_lax.



Local Definition J1_d  := prod_functor choice_incl choice_incl.
Local Definition J12_d := prod_functor (ord_functor_id TypeCat) (ord_functor_id TypeCat).
Local Definition J2_d  := prod_functor choice_incl choice_incl. (* = J1_ex *)
Local Definition J12_ex := Jprod.
Local Definition J2_ex  := ord_functor_comp F_choice_prod chDiscr. (* = G *)

Definition θdex := rlmm_comp J12_d J12_ex ϕ_d ϕ M_d _ _ θ_dens_lax θ_morph.

Import OrderEnrichedRelativeMonadExamplesNotation.

Definition semantic_judgement (A1 A2 : ord_choiceType)
                              (c1 : MFreePr A1) (c2 : MFreePr A2)
                               w  : Prop :=
  (θdex ⟨A1,A2⟩) ∙1 ⟨c1,c2⟩ ≤ w.

Program Definition fromPrePost {A1 A2}
          (pre : Prop)
          (post : A1 -> A2 -> Prop)
    : WProp (A1 * A2)%type :=
    ⦑fun p =>  pre /\ forall a1 a2, post a1 a2 -> p (a1, a2)⦒.
Next Obligation.
  intros A1 A2 chA1 chA2. intros pre post.
  split; case: H0 => // HA HB.
  intros a1 a2 Hpost.
  apply H. apply HB.
  assumption.
Qed.

Declare Scope Rules_scope.
Delimit Scope Rules_scope with Rules.

Module RulesNotation.

  Notation "⊨ c1 ≈ c2 [{ w }]" :=
    (semantic_judgement _ _ c1 c2 w) : Rules_scope.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ c1 c2 (fromPrePost pre post)) : Rules_scope.

End RulesNotation.

Import RulesNotation.
Open Scope Rules_scope.

Definition flip (r : R) : SDistr (bool_choiceType).
  rewrite /SDistr_carrier.
  apply mkdistrd. intros b.
  destruct b.
  - exact r.
  - exact (1 - r).
Defined.

Definition get_d { A  : choiceType} (c : MFreePr A):=
  (Theta_dens.unary_theta_dens_obligation_1 A c).

Lemma sample_rule :
  ∀ {A1 A2} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
    (pre : Prop) (post : A1 -> A2 -> Prop)
    (c1 : MFreePr (Choice.Pack chA1))
    (c2 : MFreePr (Choice.Pack chA2))
    dc
    (Hd : coupling dc (get_d c1) (get_d c2))
    (Hpost : forall a1 a2, dc (a1, a2) > 0 -> post a1 a2),
    ⊨ ⦃ pre ⦄ c1 ≈  c2 ⦃ post ⦄.
Proof.
  move => A1 A2 chA1 chA2 pre post c1 c2 dc Hd Hpost.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  move => pi [H1 H2].
  exists dc. split.
  - apply Hd.
  - move => a1 a2 Hdp.
    apply: H2.
    by apply: Hpost.
Qed.

Lemma sample_rule_ch :
  ∀ {A1 A2 : ord_choiceType}
    (pre : Prop) (post : A1 -> A2 -> Prop)
    (c1 : MFreePr A1)
    (c2 : MFreePr A2)
    dc
    (Hd : coupling dc (get_d c1) (get_d c2))
    (Hpost : forall a1 a2, dc (a1, a2) > 0 -> post a1 a2),
    ⊨ ⦃ pre ⦄ c1 ≈  c2 ⦃ post ⦄.
Proof.
  move => [A1 chA1] [A2 chA2] pre post c1 c2 dc Hd Hpost.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  move => pi [H1 H2].
  exists dc. split.
  - apply Hd.
  - move => a1 a2 Hdp.
    apply: H2.
    by apply: Hpost.
Qed.


(* GENERIC MONADIC RULES *)

Theorem ret_ule {A1 A2 : Type}
  {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
  (a1 : A1) (a2 : A2) :
   ⊨ (ord_relmon_unit MFreePr (Choice.Pack chA1) a1) ≈
     (ord_relmon_unit MFreePr (Choice.Pack chA2) a2)
     [{ ret (a1, a2) }].
Proof.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤".  simpl.
  rewrite /MonoCont_order //=. move => π πa1a2.
  exists (SDistr_unit (F_choice_prod (npair (Choice.Pack chA1) (Choice.Pack chA2))) (a1,a2)).
  split.
  - rewrite /SubDistr.SDistr_obligation_1 /=.
      by apply: SDistr_unit_F_choice_prod_coupling.
  - move => b1 b2 Hb1b2.
    by rewrite -(distr_get _ _ Hb1b2).
Qed.

Theorem ret_rule_ch { A1 A2 : ord_choiceType } (a1 : A1) (a2 : A2) :
   ⊨ pure a1 ≈ pure a2 [{ ret (a1, a2) }].
Proof.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  by apply: ret_rule.
Qed.

Theorem weaken_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
                     {d1 : MFreePr (Choice.Pack chA1)}
                     {d2 : MFreePr (Choice.Pack chA2)} :
  forall w w', (⊨ d1 ≈ d2 [{ w }]) -> w ≤ w' -> (⊨ d1 ≈ d2 [{ w' }] ).
Proof.
  move => w w' Hjudg Hleq.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  move: (Hleq π H').
  by apply: Hjudg.
Qed.


Theorem bind_rule {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
                  {B1 B2 : Type} {chB1 : Choice.class_of B1} {chB2 : Choice.class_of B2}
                  {f1 : A1 -> MFreePr (Choice.Pack chB1)}
                  {f2 : A2 -> MFreePr (Choice.Pack chB2)}
                  (m1 : MFreePr (Choice.Pack chA1))
                  (m2 : MFreePr (Choice.Pack chA2))
                  (wm : WProp (A1 * A2)%type)
                  (judge_wm : ⊨ m1 ≈ m2 [{ wm }])
                  (wf : (A1 * A2) -> WProp (B1 * B2)%type)
                  (judge_wf : forall a1 a2, ⊨ (f1 a1) ≈ (f2 a2) [{ (wf (a1, a2)) }]) :
  ⊨ (ord_relmon_bind MFreePr
                      (fun x : (Choice.Pack chA1) => f1 x)
                        m1 ) ≈
    (ord_relmon_bind MFreePr
                     (fun x : (Choice.Pack chA2) => f2 x)
                     m2)
    [{ bind wm wf }].
Proof.
  rewrite /semantic_judgement //=.
  eapply (@transitivity _ _ _ _ _).
  apply (rlmm_law2 _ _ _ _ θdex (⟨ Choice.Pack chA1, Choice.Pack chA2 ⟩) (⟨ Choice.Pack chB1, Choice.Pack chB2 ⟩) ⟨ f1 , f2 ⟩ ⟨ m1 , m2 ⟩).
  rewrite /semantic_judgement in judge_wm, judge_wf.
  apply (@omon_bind WProp (A1 * A2) (B1 * B2) _ _ judge_wm).
  rewrite /pointwise_relation. move=> [a1 a2].
  apply (judge_wf a1 a2).
  Unshelve.
    cbv. move=> [ff1 Hff1] [ff2 Hff2] [ff3 Hff3].
    move=> H21 H32. move=> bPred.
    move=> H3.
    apply H21. apply H32. assumption.
Qed.


(* Pre-condition manipulating rules *)

Theorem pre_weaken_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
                        {d1 : MFreePr (Choice.Pack chA1)}
                        {d2 : MFreePr (Choice.Pack chA2)} :
  forall (pre pre' : Prop) post, (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄) -> (pre' -> pre) -> (⊨ ⦃ pre' ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => w w' post Hjudg Hleq.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  apply: Hjudg.
  simpl; intuition.
Qed.

Theorem pre_hypothesis_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
                        {d1 : MFreePr (Choice.Pack chA1)}
                        {d2 : MFreePr (Choice.Pack chA2)} :
  forall (pre : Prop) post, (pre -> ⊨ ⦃ True ⦄ d1 ≈ d2 ⦃ post ⦄) -> (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => pre post Hjug.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  intuition.
  (* apply Prop2SProp_truthMorphism_rightLeft in p. *)
  rename H into p. rename H1 into H. rename H0 into q.
  rewrite /semantic_judgement /θdex //= /θ0 //= in H.
  specialize (H π).
  unfold "≤" in H. simpl in H. rewrite /MonoCont_order //= in H.
  rewrite /SProp_op_order /Basics.flip in H.
  (* rewrite /SProp_op_order /s_impl /Basics.flip //= in H. *)
  intuition.
Qed.

Theorem pre_hypothesis_rule_ch  {A1 A2 : ord_choiceType}
                                {d1 : MFreePr A1}
                                {d2 : MFreePr A2} :
  forall (pre : Prop) post, (pre -> ⊨ ⦃ True ⦄ d1 ≈ d2 ⦃ post ⦄) -> (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => pre post Hjug.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  by apply: pre_hypothesis_rule.
Qed.

(* post-condition manipulating rules *)

Theorem post_weaken_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
        {d1 : MFreePr (Choice.Pack chA1)}
        {d2 : MFreePr (Choice.Pack chA2)} :
  forall (pre : Prop) (post1 post2 : A1 -> A2 -> Prop),
    (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post1 ⦄) ->
    (forall a1 a2, post1 a1 a2 -> post2 a1 a2) -> (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post2 ⦄).
Proof.
  move => pre post1 post2 Hjudg Hleq.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  apply: Hjudg.
  simpl; intuition.
Qed.

(*Rem.: same as post_weaken_rule but with ord_choice_types *)
Theorem post_weaken_rule_ch  {A1 A2 : ord_choiceType}
                             {d1 : MFreePr A1}
                             {d2 : MFreePr A2} :
  forall (pre : Prop) (post1 post2 : A1 -> A2 -> Prop),
    (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post1 ⦄) ->
    (forall a1 a2, post1 a1 a2 -> post2 a1 a2) -> (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post2 ⦄).
Proof.
  move => pre post1 post2 Hjudg Hleq.
  rewrite /semantic_judgement /θdex //= /θ0 //=.
  unfold "≤". simpl. rewrite /MonoCont_order //=.
  move => π H'.
  apply: Hjudg.
  simpl; intuition.
Qed.

(* Theorem post_trivial_rule_ch  {A1 A2 : ord_choiceType}  *)
(*                               {d1 : MFreePr A1} *)
(*                               {d2 : MFreePr A2} : *)
(*   forall (pre : Prop), (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ fun a1 a2 => True ⦄). *)
(* Proof.     *)
(* Admitted.  *)

#[local] Axiom A : ord_choiceType.
#[local] Axiom c1 c2 : MFreePr A.


Theorem seq_rule_ch  { A1 A2 : ord_choiceType }
                     { B1 B2 : ord_choiceType }
                     {f1 : A1 -> MFreePr B1}
                     {f2 : A2 -> MFreePr B2}
                     (m1 : MFreePr A1) (m2 : MFreePr A2)
                     (P : Prop) (R : A1 -> A2 -> Prop)
                     (Q : B1 -> B2 -> Prop)
                     (judge1 : ⊨ ⦃ P ⦄ m1 ≈ m2 ⦃ R ⦄ )
                     (judge2 : forall a1 a2, ⊨ ⦃ R a1 a2 ⦄ (f1 a1) ≈ (f2 a2) ⦃ Q ⦄ ) :
 ⊨ ⦃ P ⦄  x ∈ A1 <<- m1 ;; f1 x ≈  x ∈ A2 <<- m2 ;; f2 x  ⦃ Q ⦄.
Proof.
  rewrite /fromPrePost in judge1, judge2.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  destruct B1 as [B1 chB1]. destruct B2 as [B2 chB2].
  assert (forall a1 a2, ⊨ (f1 a1) ≈ (f2 a2) [{ fromPrePost (R a1 a2) Q }]) as judge2W.
  { move => a1 a2. exact (judge2 a1 a2). }
  move: (bind_rule m1 m2 (fromPrePost P R) judge1  (fun a => fromPrePost (R (fst a) (snd a)) Q) judge2W ).
  move => HH.
  rewrite /fromPrePost.
  move : HH.
  rewrite /= /MonoCont_bind /fromPrePost /=.
  rewrite /semantic_judgement.
  move => HH /=.  move => β Hβ. simpl in *.
  (* apply sand2and in Hβ. *)
  destruct Hβ as [Hbeta1 Hbeta2].
  (* rewrite PSP_retr in Hbeta1. *)
  specialize (HH β). simpl in HH.
  destruct HH.
  split.
  exact (Hbeta1).
  (* apply SProp2Prop_truthMorphism_rightLeft in Hbeta2. *)
  move => a1 a2 Ha1a2.
  split.
  assumption.
  move => b1 b2 Hb1b2.
  specialize (Hbeta2 b1 b2).
  apply: Hbeta2.
    exact Hb1b2.
  (* apply SProp2Prop_truthMorphism_rightLeft. rewrite PSP_retr. *)
    (* by apply: Prop2SProp_truthMorphism_rightLeft. *)
    destruct H as [s1 s2].
    (* apply SProp2Prop_truthMorphism_leftRight in s1. *)
    (* rewrite PSP_retr in s1. *)
    exists x. split.
      assumption.
      exact s2.
Qed.

Corollary seq_rule_ch_T  { A1 A2 : ord_choiceType } { a1 : A1 } { a2 : A2 }
                         { B1 B2 : ord_choiceType }
                         {f1 : A1 -> MFreePr B1}
                         {f2 : A2 -> MFreePr B2}
                         (m1 : MFreePr A1) (m2 : MFreePr A2)
                         (P : Prop)
                         (Q : B1 -> B2 -> Prop)
                         (judge1 : ⊨ ⦃ P ⦄ m1 ≈ m2 ⦃ fun _ _ => True ⦄ )
                         (judge2 : forall a1 a2, ⊨ ⦃ True ⦄ (f1 a1) ≈ (f2 a2) ⦃ Q ⦄ ) :
 ⊨ ⦃ P ⦄ x ∈ A1 <<- m1 ;; f1 x ≈ x ∈ A2 <<- m2 ;; f2 x ⦃ Q ⦄.
Proof. by  apply: (seq_rule_ch m1 m2 P (fun _ _ => True) Q judge1 judge2). Qed.

(* Theorem reflexivity_post_eq  { A : ord_choiceType }  *)
(*                                (m : MFreePr A)  *)
(*                                (P : Prop)  : *)
(*  ⊨ ⦃ P ⦄ m ≈ m ⦃ eq ⦄. *)
(* Proof. *)
(*   rewrite /semantic_judgement /fromPrePost /θdex /θ0. *)
(*   move => alpha [p H].  *)
(*   exists  *)



(* *)

Theorem if_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
        (c1 c2 : MFreePr (Choice.Pack chA1))
        (c1' c2' : MFreePr (Choice.Pack chA2))
        {b1 b2 : bool}
        {pre : Prop} {post : A1 -> A2 -> Prop}
        {pre_b1b2 : pre -> b1 = b2}
        { H1 : ⊨ ⦃ pre /\ b1 = true ⦄ c1 ≈ c1' ⦃ post ⦄ }
        { H2 : ⊨ ⦃ pre /\ b1 = false ⦄ c2 ≈ c2' ⦃ post ⦄ } :
    ⊨ ⦃ pre ⦄
      (if b1 then c1 else c2) ≈
      (if b2 then c1' else c2')
      ⦃ post ⦄.
Proof.
  apply pre_hypothesis_rule. move=> pre_holds.
  specialize (pre_b1b2 pre_holds).
  destruct pre_b1b2.
  destruct b1.
  apply (pre_weaken_rule (pre /\ true = true) True).
  - assumption.
  - intuition.
  apply (pre_weaken_rule (pre /\ false = false) True).
  - assumption.
  - intuition.
Qed.

Theorem if_rule_weak  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
        (c1 c2 : MFreePr (Choice.Pack chA1))
        (c1' c2' : MFreePr (Choice.Pack chA2))
        {b : bool}
        {pre : Prop} {post : A1 -> A2 -> Prop}
        { H1 : ⊨ ⦃ pre /\ b = true ⦄ c1 ≈ c1' ⦃ post ⦄ }
        { H2 : ⊨ ⦃ pre /\ b = false ⦄ c2 ≈ c2' ⦃ post ⦄ } :
    ⊨ ⦃ pre ⦄
      (if b then c1 else c2) ≈
      (if b then c1' else c2')
      ⦃ post ⦄.
Proof.
  apply if_rule; intuition.
Qed.


Axiom s_indefinite_description :
   forall (A : Type) (P : A-> Prop),
     (exists x, P x) -> { x : A | P x }.



Definition judgement_d {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2}
           {c1 : MFreePr (Choice.Pack chA1)}
           {c2 : MFreePr (Choice.Pack chA2)}
           {pre : Prop} {post : A1 -> A2 -> Prop}
           (π : A1 * A2 -> Prop)
           (Hπ : pre /\ (forall (a1 : A1) (a2 : A2), post a1 a2 -> π (a1, a2)))
           (J : ⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄) :
  { d : { distr (F_choice_prod (npair (Choice.Pack chA1) (Choice.Pack chA2))) / R } |
    coupling d
     (Theta_dens.unary_theta_dens_obligation_1 (Choice.Pack chA1) c1)
       (Theta_dens.unary_theta_dens_obligation_1 (Choice.Pack chA2) c2)
     /\ (forall (a1 : A1) (a2 : A2), 0 < d (a1, a2) -> π (a1, a2)) }.
Proof.
  move : J. rewrite /semantic_judgement //= /fromPrePost /θ0 /=.
  unfold "≤". simpl. rewrite /MonoCont_order => H.
  specialize (H π Hπ). simpl in H.
  apply s_indefinite_description in H.
  destruct H as [d H]. move: H => [H1 H2].
  (* rewrite PSP_retr in H1. *)
  now exists d.
Defined.

(* I am not sure I follow the meaning of for_loop? It executes the command only once? *)
(* Rem.: modified this to execute n-times c *)
Fixpoint for_loop {A : choiceType} (c : A -> MFreePr A) (n : nat) (a : A) :=
  match n with
  | 0  => c a
  | S m => ord_relmon_bind MFreePr (fun a' => for_loop c m a') (c a)
  end.

(* Rem.: this is a bounded version of the iteration operator found in monads with iteration *)
Fixpoint bounded_iter {A B : choiceType} (n : nat) (c : A -> MFreePr (sum_choiceType A B)) (a : A) :
  MFreePr (sum_choiceType unit_choiceType B) :=
  match n with
  | 0  => ord_relmon_unit MFreePr _ (inl Datatypes.tt)
  | S m => (ord_relmon_bind MFreePr) (fun v => match v with
                                           | inl a' => bounded_iter m c a'
                                           | inr b => ord_relmon_unit MFreePr _ (inr b)
                                           end) (c a)
  end.

Definition bounded_loop {A B : choiceType} (n : nat) (b : A -> MFreePr bool_choiceType) (c : A -> MFreePr A) (a : A) :
  MFreePr (sum_choiceType unit_choiceType A) :=
  bounded_iter n (fun a' => ord_relmon_bind MFreePr (fun b => match b with
       | true => ord_relmon_bind MFreePr (fun a2 => ord_relmon_unit MFreePr _ (inr a2)) (c a')
       | false => ord_relmon_unit MFreePr _ (inl a')
                                                        end) (b a')) a.

(* Rem.: this a variant following what's in The next 700... *)
Fixpoint bounded_do_while  (n : nat) (c : MFreePr bool_choiceType) :
  MFreePr bool_choiceType :=
  (* false means fuel emptied, true means execution finished *)
  match n with
  | 0 => ord_relmon_unit MFreePr _ false
  | S n => ord_relmon_bind MFreePr (fun b => match b with
                                         | false => ord_relmon_unit MFreePr _ true
                                         | true => bounded_do_while n c
                                         end
                                  ) c
  end.

(* Rem.: maybe something like the rule in the paper can be proven? yes...
       but I do not have intuition of how it could be used... examples needed! *)
Theorem bounded_do_while_rule  {A1 A2 : Type} {chA1 : Choice.class_of A1} {chA2 : Choice.class_of A2} {n : nat}
        (c1 c2 : MFreePr bool_choiceType)
        {inv : bool -> bool -> Prop}
        {H : ⊨ ⦃ inv true true ⦄ c1 ≈ c2 ⦃ fun b1 b2 => inv b1 b2 /\ b1 = b2 ⦄ } :
    ⊨ ⦃ inv true true ⦄ bounded_do_while n c1 ≈ bounded_do_while n c2 ⦃ fun l r => (l = false /\ r = false) \/ inv false false ⦄.
Proof.
  induction n.
  - simpl. eapply weaken_rule.
    apply ret_rule. cbv; intuition.
    (* apply Prop2SProp_truthMorphism_leftRight; eauto. *)
  - simpl. eapply weaken_rule.
    apply bind_rule. apply H.
    intros a1 a2. eapply weaken_rule. apply if_rule.
    instantiate (1 := inv a1 a2 /\ a1 = a2). intuition.
    instantiate (1 := fun l r : bool => l = false /\ r = false \/ inv false false).
    eapply weaken_rule. apply IHn. cbv; intuition.
    (* apply Prop2SProp_truthMorphism_leftRight. *)
    (* apply Prop2SProp_truthMorphism_rightLeft in p. *)
    rewrite -H3. rewrite {2}H4. assumption.
    (* intuition. destruct H1; destruct H3; assumption. *)
    eapply weaken_rule. apply ret_rule.
    cbv; intuition.
    apply H2. right. rewrite -H3. rewrite {2}H4. assumption.
(* apply q. *)
(*     apply Prop2SProp_truthMorphism_leftRight. *)
(*     right. apply Prop2SProp_truthMorphism_rightLeft in p. intuition. *)
(*     destruct H1; destruct H3; assumption. *)
    instantiate (1 := fun '(a1, a2) => fromPrePost (inv a1 a2 /\ a1 = a2) (fun l r : bool => l = false /\ r = false \/ inv false false)).
    cbv; intuition. cbv; intuition.
Qed.

Lemma Pr_eq {X Y : ord_choiceType} {A : pred X} {B : pred Y} Ψ ϕ
      (c1 : MFreePr X) (c2 : MFreePr Y)
      (H : ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄)
      (HPsi : Ψ )
      (Hpost : forall x y,  ϕ x y -> (A x) <-> (B y)) :
  \P_[ θ0 c1 ] A =
  \P_[ θ0 c2 ] B.
Proof.
  destruct X as [X chX]. destruct Y as [Y chY].
  rewrite /pr.
  rewrite /semantic_judgement /fromPrePost /OrderEnrichedRelativeMonadExamples.extract_ord /= in H.
  rewrite  /MonoCont_order in H.
  specialize (H  (fun '(a, b) => A a <-> B b)).
  rewrite /SProp_op_order /Basics.flip /= in H.
  assert (sand ( Ψ) (forall (a1 : X) (a2 : Y), ϕ a1 a2 -> A a1 <-> B a2)) as Hpre.
  { split.
    - assumption.
    - move => a1 a2 Heq.
      apply Hpost. assumption.
  }
  specialize (H Hpre). clear Hpre.
  (* apply Prop2SProp_truthMorphism_rightLeft. *)
  destruct H as [d [H1 H2]].
  (* apply Prop2SProp_truthMorphism_leftRight. *)
  (* apply Prop2SProp_truthMorphism_rightLeft in H1. *)
  rewrite /coupling in H1.
  destruct H1 as [H11 H12].
  rewrite /θ0 /unary_theta_dens /=.
  rewrite -H11 -H12.
  rewrite /lmg /rmg.
  assert ((fun x : X => (A x)%:R * dfst d x) = (fun x : X => (A x)%:R * psum (fun w => d (x, w)))) as HeqH11.
  { extensionality k. rewrite dfstE. reflexivity. }
  rewrite HeqH11.
  assert ((fun x : X => (A x)%:R * psum (fun w : Choice.Pack chY => d (x, w))) = (fun x : X => psum (fun w : Choice.Pack chY => (A x)%:R * d (x, w)))) as H4.
  { extensionality k. rewrite -psumZ. reflexivity.
    case (A k); intuition. by rewrite ler01. }
  rewrite H4.
  assert ((fun x : Y => (B x)%:R * dsnd d x) = (fun y : Y => (B y)%:R * psum (fun w => d (w, y)))) as HeqH12.
  { extensionality K. rewrite dsndE. reflexivity. }
  rewrite HeqH12.
  unfold F_choice_prod_obj in d.
  assert ((fun y : Y => (B y)%:R * psum (fun w : Choice.Pack chX => d (w, y))) = (fun y : Y => psum (fun w : Choice.Pack chX => (B y)%:R * d (w, y)))) as H5.
  { extensionality k. rewrite -psumZ. reflexivity.
    case (B k); intuition; by rewrite ler01. }
  rewrite H5.
  clear H5 H4 HeqH12 HeqH11.
  rewrite -(@psum_pair _ _ _ (fun '(x, y) => (A x)%:R * d (x, y))).
  rewrite -(@psum_pair_swap _ _ _ (fun '(x, y) => (B y)%:R * d (x, y))).
  f_equal.
  extensionality k.
  destruct k as [x y].
  case (0 < d (x, y)) eqn:Hd.
  move: Hd. move/idP => Hd.
  specialize (H2 _ _ Hd).
  (* apply Prop2SProp_truthMorphism_rightLeft in H2. *)
  case (A x) eqn:Ha.
  + case (B y) eqn: Hb.
    reflexivity.
    move: H2. intuition. rewrite H. reflexivity. auto.
    case (B y) eqn:Hb.
    intuition. rewrite H0. reflexivity. auto.
    reflexivity.
    assert (d (x, y) = 0).
    rewrite ltr_def in Hd.
    apply Bool.andb_false_iff in Hd.
    destruct Hd.
    ++ move: H. move/eqP. auto.
    ++ assert (0 <= d (x, y)) as Hn.
       { apply ge0_mu. }
       move: H. move/idP. intuition.
         by rewrite H !GRing.mulr0.
    (* summable B*)
    assert ((fun x : (prod_choiceType (Choice.Pack chX) (Choice.Pack chY)) =>
               (nat_of_bool (let '(_, y) := x in B y))%:R * d x) =
            (fun '(x, y)  => (B y)%:R * d (x, y))) as Heq1.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq1.
    pose (@summable_pr R (prod_choiceType (Choice.Pack chX) (Choice.Pack chY))
                       (fun '(x, y) => B y) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
    (* summable A *)
    assert ((fun x : (prod_choiceType (Choice.Pack chX) (Choice.Pack chY)) =>
               (nat_of_bool (let '(x, _) := x in A x))%:R * d x) =
            (fun '(x, y)  => (A x)%:R * d (x, y))) as Heq2.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq2.
    pose (@summable_pr R (prod_choiceType (Choice.Pack chX) (Choice.Pack chY))
                       (fun '(x, y) => A x) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
Qed.


Corollary coupling_eq { A : ord_choiceType }
                      (K1 K2 : MFreePr A )
                      { Ψ : Prop }
                      (H : ⊨ ⦃ Ψ ⦄ K1 ≈ K2 ⦃ eq ⦄): Ψ -> θ0 K1 = θ0 K2.
Proof.
  move => Hpsi. apply distr_ext => w.
  assert (\P_[ θ0 K1 ] (pred1 w) = \P_[ θ0 K2 ] (pred1 w)).
  { apply: (Pr_eq Ψ eq); rewrite //= => x y Heq. by subst.  }
  by repeat rewrite -pr_pred1 in H0.
Qed.

Lemma true_false_False: (true -> false) -> False.
Proof.  move => Himp. by have: false by auto. Qed.

Lemma Pr_le {X Y : ord_choiceType} {A : pred X} {B : pred Y}
      (Ψ : Prop) ϕ
      (c1 : MFreePr X) (c2 : MFreePr Y)
      (HPsi : Ψ)
      (H : ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄)
  (Hpost : forall x y, ϕ x y -> (A x) -> (B y)) :
  \P_[ θ0 c1 ] A <=
  \P_[ θ0 c2 ] B.
Proof.
  destruct X as [X chX]. destruct Y as [Y chY].
  rewrite /pr.
  rewrite /semantic_judgement /fromPrePost /OrderEnrichedRelativeMonadExamples.extract_ord /= in H.
  rewrite  /MonoCont_order in H.
  specialize (H  (fun '(a, b) => A a -> B b)).
  rewrite /SProp_op_order /Basics.flip  /= in H.
  assert (sand ( Ψ) (forall (a1 : X) (a2 : Y), ϕ a1 a2 -> A a1 -> B a2)) as Hpre.
  { split.
    - assumption.
    - move => a1 a2 Heq. apply Hpost. assumption.
  }
  specialize (H Hpre). clear Hpre.
  (* apply Prop2SProp_truthMorphism_rightLeft. *)
  destruct H as [d [H1 H2]].
  (* apply Prop2SProp_truthMorphism_leftRight. *)
  (* apply Prop2SProp_truthMorphism_rightLeft in H1. *)
  rewrite /coupling in H1.
  destruct H1 as [H11 H12].
  rewrite /θ0 /unary_theta_dens /=.
  rewrite -H11 -H12.
  rewrite /lmg /rmg.
  assert ((fun x : X => (A x)%:R * dfst d x) = (fun x : X => (A x)%:R * psum (fun w => d (x, w)))) as HeqH11.
  { extensionality k. rewrite dfstE. reflexivity. }
  rewrite HeqH11.
  assert ((fun x : X => (A x)%:R * psum (fun w : Choice.Pack chY => d (x, w))) = (fun x : X => psum (fun w : Choice.Pack chY => (A x)%:R * d (x, w)))) as H4.
  { extensionality k. rewrite -psumZ. reflexivity.
    case (A k); intuition. by rewrite ler01. }
  rewrite H4.
  assert ((fun x : Y => (B x)%:R * dsnd d x) = (fun y : Y => (B y)%:R * psum (fun w => d (w, y)))) as HeqH12.
  { extensionality K. rewrite dsndE. reflexivity. }
  rewrite HeqH12.
  unfold F_choice_prod_obj in d.
  assert ((fun y : Y => (B y)%:R * psum (fun w : Choice.Pack chX => d (w, y))) = (fun y : Y => psum (fun w : Choice.Pack chX => (B y)%:R * d (w, y)))) as H5.
  { extensionality k. rewrite -psumZ. reflexivity.
    case (B k); intuition; by rewrite ler01. }
  rewrite H5.
  clear H5 H4 HeqH12 HeqH11.
  rewrite -(@psum_pair _ _ _ (fun '(x, y) => (A x)%:R * d (x, y))).
  rewrite -(@psum_pair_swap _ _ _ (fun '(x, y) => (B y)%:R * d (x, y))).
  apply: le_psum.
  - move => [x1 x2] /=.
    apply /andP. split.
    -- apply: mulr_ge0.
       --- case: (A x1); rewrite //=. exact ler01.
       --- by inversion d.
    -- have Hd0 : 0 <= d(x1,x2) by inversion d.
       have [Hdor1 | Hdor2]: 0 == d(x1,x2) \/ 0 < d(x1,x2).
       { rewrite ler_eqVlt in Hd0.
           by move/orP: Hd0. }
       --- move/eqP : Hdor1 => Hdor1.
           by rewrite -Hdor1 !GRing.mulr0.
       --- apply: ler_pmul.
           + case: (A x1); rewrite //=. exact ler01.
           + by inversion d.
           + move:  (H2 x1 x2 Hdor2) => HAB.
             destruct (A x1) eqn: Ax1; rewrite //=;
             destruct (B x2) eqn : Bx2; rewrite //=.
             exfalso. by apply: true_false_False.
             exact ler01.
             auto.
  (* summable B *)
    assert ((fun x : (prod_choiceType (Choice.Pack chX) (Choice.Pack chY)) =>
               (nat_of_bool (let '(_, y) := x in B y))%:R * d x) =
            (fun '(x, y)  => (B y)%:R * d (x, y))) as Heq1.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq1.
    pose (@summable_pr R (prod_choiceType (Choice.Pack chX) (Choice.Pack chY))
                       (fun '(x, y) => B y) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
  (* summable B *)
    assert ((fun x : (prod_choiceType (Choice.Pack chX) (Choice.Pack chY)) =>
               (nat_of_bool (let '(_, y) := x in B y))%:R * d x) =
            (fun '(x, y)  => (B y)%:R * d (x, y))) as Heq1.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq1.
    pose (@summable_pr R (prod_choiceType (Choice.Pack chX) (Choice.Pack chY))
                       (fun '(x, y) => B y) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
    (* summable A *)
    assert ((fun x : (prod_choiceType (Choice.Pack chX) (Choice.Pack chY)) =>
               (nat_of_bool (let '(x, _) := x in A x))%:R * d x) =
            (fun '(x, y)  => (A x)%:R * d (x, y))) as Heq2.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq2.
    pose (@summable_pr R (prod_choiceType (Choice.Pack chX) (Choice.Pack chY))
                       (fun '(x, y) => A x) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
Qed.

(*Rem.: Do we have a corollary coupling_le? *)
Corollary coupling_le { A : ord_choiceType }
                      (K1 K2 : MFreePr A )
                      { Ψ : Prop }
                      (H : ⊨ ⦃ Ψ ⦄ K1 ≈ K2 ⦃ eq ⦄):
  Ψ -> (forall x, (θ0 K1) x <=  (θ0 K2) x).
Proof.
  move => Hpsi a.
  repeat rewrite pr_pred1.
  apply: (Pr_le Ψ _ ); rewrite //= => x y Heq. by subst.
Qed.


Lemma rewrite_eqDistrL { A1 A2 : ord_choiceType } { P } { Q }
      (c1 c1' : MFreePr A1) (c2 : MFreePr A2)
      (H : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
      (θeq : θ0 c1 = θ0 c1' ) :

      ⊨ ⦃ P ⦄ c1'  ≈ c2 ⦃ Q ⦄.
Proof.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  rewrite /semantic_judgement /fromPrePost /θdex /=.
  unfold "≤". rewrite /= /MonoCont_order.
  rewrite /θ0 /= in θeq.
  rewrite -θeq.
  by apply H.
Qed.

Lemma rewrite_eqDistrR { A1 A2 : ord_choiceType } { P } { Q }
      (c1 : MFreePr A1) (c2 c2' : MFreePr A2)
      (H : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
      (θeq : θ0 c2 = θ0 c2' ) :

      ⊨ ⦃ P ⦄ c1  ≈ c2' ⦃ Q ⦄.
Proof.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  rewrite /semantic_judgement /fromPrePost /θdex /=.
  unfold "≤". rewrite /= /MonoCont_order.
  rewrite /θ0 /= in θeq.
  rewrite -θeq.
  by apply H.
Qed.


(* commutativity of SDistr
 *)
Lemma SDistrC { A } (c1 c2 : SDistr A) :
  (SDistr_bind _ _  (fun _ => c2) c1) =
  (SDistr_bind _ _  (fun _ => c1) c2).
Admitted.

Lemma coupling_self { A } ( d : SDistr A) :
  { dd : SDistr _ | coupling dd d d }.
Admitted.
 (* dd: A * A    -> [0,1]
               (a1, a2)  ↦ if (a1 == a2) then (d a1)/2 else 0

               is a coupling of d with itself

  *)

Lemma reflexivity_rule { A : ord_choiceType }
                       (m : MFreePr A):
  ⊨ ⦃ True ⦄ m ≈ m ⦃ eq ⦄.
Proof.
  destruct A as [A chA].
  rewrite /semantic_judgement /fromPrePost.
  move => α [H1 H2] /=.
  destruct (coupling_self (θ0 m)) as [d Hd].
  exists d.
  split.
  (* apply: Prop2SProp_truthMorphism_leftRight. *)
  - exact Hd.
  - move => a1 a2 H. apply: H2. (* by definition of d *) admit.
Admitted.

Theorem swap_rule { A : ord_choiceType }
                  (c1 c2 : MFreePr A):
  ⊨ ⦃ True ⦄ (c1 ;; c2) ≈ (c2 ;; c1) ⦃ eq ⦄ .
Proof.
  apply: (rewrite_eqDistrL (c2;; c1) (c1;; c2) (c2 ;; c1)).
  - apply: reflexivity_rule.
  rewrite /θ0 /unary_theta_dens /=.
  pose (rmm_law2 _ _ _ _ (@unary_theta_dens) A A (fun _ => c1)).
  simpl in e.
  apply equal_f with (x := c2) in e.
  rewrite e. clear e.
  pose (rmm_law2 _ _ _ _ (@unary_theta_dens) A A (fun _ => c2)).
  simpl in e.
  apply equal_f with (x := c1) in e.
  rewrite e /=. clear e.
  by rewrite /SubDistr.SDistr_obligation_2 SDistrC.
Qed.

Corollary swap_eq { A : ord_choiceType }
          (c1 c2 : MFreePr A) :

  θ0 (c1 ;; c2) = θ0 (c2 ;; c1).
Proof.
  apply: coupling_eq.
  exact: (swap_rule c1 c2).
  auto.
Qed.


(* Lemma bind_bind_sample { A1 A2 A3: ord_choiceType } *)
(*       (c1 : MFreePr A1) *)
(*       (c2 : MFreePr A2) *)
(*       (f : A1 -> A2 -> MFreePr A3) : *)
(*   θ0 (x ∈ A1 <<- c1;; y ∈ A2 <<- c2 ;; (f x y)) = *)
(*   θ0 (f ( A1 <$ c1) ( A2 <$ c2)). *)
(* Proof. *)
(*   induction c1; induction c2. *)
(*   - by []. *)
(*   - destruct s0. simpl in r, H. *)
(*     rewrite -(H (Hch x)) //=. *)
(*     apply: f_equal. *)
(*     rewrite  /FreeProbProg.rFree_obligation_2. *)
(*     (*Rem.: the LHS is bindrFree _ _ (r ar) [eta f s] *)
(*      *) admit. *)
(*   - destruct s. simpl in r, H. *)
(*     rewrite -(H (Hch x)) //=. *)
(*     rewrite  /FreeProbProg.rFree_obligation_2. *)
(*     (*Rem.: the LHS is bindrFree _ _ (r ar) [eta f s] *)
(*       *) admit. *)
(*   - destruct s0 as [x0 p0]. simpl in H0. *)
(*     specialize (H0 (Hch x0)). *)
(*     destruct s as [x p]. simpl in H, H0. *)
(*     (* specialize (H0 H). *) *)
(* Admitted. *)


(* Theorem swap_rule_gen { A1 A2 A3: ord_choiceType } *)
(*                       (c1 : MFreePr A1) *)
(*                       (c2 : MFreePr A2) *)
(*                       (f : A1 -> A2 -> MFreePr A3): *)
(*   ⊨ ⦃ True ⦄ (x ∈ A1 <<- c1;; y ∈ A2 <<- c2 ;; (f x y)) ≈ *)
(*            (y ∈ A2 <<- c2;; x ∈ A1 <<- c1 ;; (f x y)) *)
(*     ⦃ eq ⦄ . *)
(* Proof. *)
(*   apply: rewrite_eqDistrL. *)
(*     by apply: reflexivity_rule. *)
(*   by rewrite !bind_bind_sample. *)
(* Qed. *)

Theorem async_retL { A B : ord_choiceType }
                   (m : MFreePr A) (f : A -> B )  :

        ⊨ ⦃ True ⦄ x <- m ;; retF (f x) ≈ m ⦃ fun fx x => fx = (f x) ⦄.
Proof.
  apply (rewrite_eqDistrR _ (x <- m ;; retF x)).
  apply (seq_rule_ch _ _ True eq).
  - by apply: reflexivity_rule.
  - move => a1 a2. apply: pre_hypothesis_rule_ch => Heq.
    rewrite -Heq.
    rewrite /fromPrePost.
    destruct A as [A chA]. destruct B as [B chB].
    apply (weaken_rule (ret (f a1, a1))).
    -- by apply: ret_rule.
    -- rewrite /=. move => predBA [H1 H2] /=.
       apply H2.
       reflexivity.
  - by rewrite ord_relmon_law1 /=.
Qed.

Theorem async_retR { A B : ord_choiceType }
                   (m : MFreePr A) (f : A -> B )  :

        ⊨ ⦃ True ⦄  m ≈ x <- m;; retF (f x) ⦃ fun x fx => fx = (f x) ⦄.
Proof.
  apply (rewrite_eqDistrL (x <- m ;; retF x)).
  apply (seq_rule_ch _ _ True eq).
  - by apply: reflexivity_rule.
  - move => a1 a2. apply: pre_hypothesis_rule_ch => Heq.
    rewrite -Heq.
    rewrite /fromPrePost.
    destruct A as [A chA]. destruct B as [B chB].
    apply (weaken_rule (ret (a1, f a1))).
    -- by apply: ret_rule.
    -- rewrite /=. move => predBA [H1 H2] /=.
       apply H2.
       reflexivity.
  - by rewrite ord_relmon_law1 /=.
Qed.

(* Theorem dead_code_elimL { A B } { P } { Q } *)
(*         (dead : MFreePr A) (m : MFreePr B) *)
(*         (H :  ⊨ ⦃ P ⦄ m ≈ m  ⦃ Q ⦄): *)
(*     ⊨ ⦃ P ⦄ dead ;; x ∈ _ <<- m ;; retrFree _ _ _ x ≈ m  ⦃ Q ⦄. *)
(* Proof. Admitted.  *)


(* Theorem dead_code_elimR { A B } { P } { Q } *)
(*         (dead : MFreePr A) (m : MFreePr B) *)
(*         (H :  ⊨ ⦃ P ⦄ m ≈ m  ⦃ Q ⦄): *)
(*     ⊨ ⦃ P ⦄ m ≈ dead ;; x ∈ _ <<- m ;; retrFree _ _ _ x  ⦃ Q ⦄. *)
(* Proof. Admitted.  *)


End DerivedRules.

