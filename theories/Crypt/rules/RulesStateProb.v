From Coq Require Import RelationClasses Morphisms Utf8.

From SSProve.Mon Require Import SPropMonadicStructures SpecificationMonads MonadExamples
  SPropBase FiniteProbabilities.

From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples Commutativity GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  finset finmap.finmap xfinmap .
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings Theta_dens
  Theta_exCP LaxComp FreeProbProg RelativeMonadMorph_prod
  StateTransformingLaxMorph choice_type Casts.

Import SPropNotations.
Import Num.Theory.

From HB Require Import structures.


#[local] Open Scope ring_scope.

#[local] Definition ops_StP (S : choiceType) :=
  @ops_StP S.

#[local] Definition ar_StP (S : choiceType) :=
  @ar_StP S.

(* free monad *)
Definition FrStP (S : choiceType) :=
  @FrStP S.

#[local] Definition pure {S : choiceType} {A : ord_choiceType} (a : A) :=
  ord_relmon_unit (FrStP S) A a.

#[local] Definition bindF {S : choiceType} {A B : ord_choiceType}
  (f : TypeCat ⦅ choice_incl A; FrStP S B ⦆ ) (m : FrStP S A) :=
  ord_relmon_bind (FrStP S) f m.

Definition retF {S : choiceType} {A : choiceType} (a : A) :=
  retrFree (ops_StP S) (ar_StP S) A a.


(* morphism *)
Definition θ {S1 S2 : choiceType} :=
  @thetaFstdex S1 S2.

Definition θ0 {S : choiceType} {A : ord_choiceType} (c : FrStP S A) :=
  @unaryIntState S A c.


(* spec monad *)
#[local] Definition WrelSt {S1 S2 : choiceType} :=
  rlmm_codomain (@θ S1 S2).


(* Rem.: this spec monad is a ordered relative monad, while previously we were using an ordered monad *)

Definition retW {A1 A2 : ord_choiceType} {S1 S2 : choiceType} (a : A1 * A2) :
  Base.dfst (@WrelSt S1 S2 ⟨ A1, A2 ⟩).
Proof.
  apply (ord_relmon_unit WrelSt).
  simpl.
  exact: a.
Defined.


Definition bindW {A1 A2 B1 B2 : ord_choiceType} {S1 S2 : choiceType}
  (w : Base.dfst (@WrelSt S1 S2 ⟨ A1, A2 ⟩))
  (f : A1 * A2 → Base.dfst (@WrelSt S1 S2 ⟨ B1, B2 ⟩)) :
  Base.dfst (@WrelSt S1 S2 ⟨ B1, B2 ⟩).
Proof.
  unshelve eapply (ord_relmon_bind WrelSt).
  - simpl. exact: npair A1 A2.
  - simpl.
    exists f.
    move => [a1 a2] [b1 b2] Hleq.
    inversion Hleq.
    by move => [s1 s2] π H.
  - exact: w.
Defined.

Import OrderEnrichedRelativeMonadExamplesNotation.

Definition semantic_judgement (A1 A2 : ord_choiceType) {S1 S2 : choiceType}
  (c1 : FrStP S1 A1) (c2 : FrStP S2 A2)
  (w  : Base.dfst (WrelSt ⟨ A1, A2 ⟩)) : Prop :=
   (θ ⟨A1,A2⟩)∙1 ⟨c1,c2⟩ ≤ w.

Definition fromPrePost {A1 A2 : ord_choiceType} {S1 S2: choiceType}
  (pre : (S1 * S2) → Prop)
  (post : (A1 * S1) → (A2 * S2) → Prop) :
  Base.dfst (@WrelSt S1 S2 ⟨ A1, A2 ⟩).
Proof.
  simpl.
  unshelve econstructor.
  move=> [is1 is2]. unshelve econstructor.
  move=> myPost.
  exact (
    pre (is1,is2) ∧
    ∀ as1 as2, (post as1 as2) → myPost (as1, as2)
  ).
  move => x y Hxy [H1 H2].
  split.
  - assumption.
  - move => as1 as2 post12. apply: Hxy. by apply: H2.
  move => x y Heq π.
  by rewrite Heq.
Defined.

Declare Scope rsemantic_scope.
Delimit Scope rsemantic_scope with rsem.

Module RSemanticNotation.

  Notation "⊨ c1 ≈ c2 [{ w }]" :=
    (semantic_judgement _ _ c1 c2 w) : rsemantic_scope.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ c1 c2 (fromPrePost pre post))
    : rsemantic_scope.

End RSemanticNotation.

Import RSemanticNotation.
#[local] Open Scope rsemantic_scope.

Import (* finmap.set *) finset finmap.finmap xfinmap.

Open Scope fset_scope.

Definition d_inv {A1 A2 : choiceType} (d : SDistr  (F_choice_prod ⟨ A1, A2 ⟩)) :
  SDistr  (F_choice_prod ⟨ A2, A1 ⟩) :=
  dswap d.

Lemma d_inv_coupling {A1 A2} {c1 : SDistr A1} {c2 : SDistr A2}
  (d : SDistr (F_choice_prod ⟨ A1, A2 ⟩ )) (d_coupling : coupling d c1 c2) :
  coupling (d_inv d) c2 c1.
Proof.
  unfold coupling. split.
  - unfold lmg. unfold d_inv.
    apply distr_ext. move=> x. erewrite (__deprecated__dfst_dswap d).
    destruct d_coupling as [lH rH]. rewrite -rH. unfold rmg. reflexivity.
  - unfold rmg. unfold d_inv.
    apply distr_ext. move=> x. erewrite (__deprecated__dsnd_dswap d).
    destruct d_coupling as [lH rH]. rewrite -lH. unfold lmg. reflexivity.
Qed.

Theorem inv_rule {A1 A2 : ord_choiceType} {S1 S2 : choiceType} {P Q}
  (c1 : FrStP S1 A1) (c2 : FrStP S2 A2)
  (H : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄ ) :
  ⊨ ⦃ λ '(st1,st2), P (st2, st1) ⦄ c2 ≈ c1 ⦃ λ as1 as2, Q as2 as1 ⦄.
Proof.
  move => [st1 st2] /=. move => π [H1 H2] /=.
  specialize (H (st2, st1) (fun '(as1, as2) => π (as2, as1))).
  simpl in H.
  destruct H as [d [d_coupling Hd]].
  split; auto.
  exists  (@d_inv _ _ d).
  split.
  by apply: d_inv_coupling.
  move => as2 as1 H'.
  apply: Hd.
  rewrite /d_inv /= in H'. destruct d. simpl in *.
  rewrite dswapE in H'. cbn in H'. assumption.
Qed.

(* GENERIC MONADIC RULES *)
Theorem ret_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
  (a1 : A1) (a2 : A2):
  ⊨ @pure S1 A1 a1 ≈ @pure S2 A2 a2  [{ retW (a1, a2) }].
Proof.
  rewrite /semantic_judgement /θ.
  unfold "≤". simpl.
  rewrite /MonoCont_order //=. move => [ss1 ss2] πa1a2 /=.
  exists (SDistr_unit (F_choice_prod (npair (prod_choiceType A1 S1) (prod_choiceType A2 S2)))
                 ((a1, ss1), (a2, ss2))).
  split.
  - rewrite /SubDistr.SDistr_obligation_1 /=.
    by apply SDistr_unit_F_choice_prod_coupling.
  - move => b1 b2 Hb1b2 /=.
    by rewrite -(distr_get _ _ Hb1b2).
Qed.

Theorem weaken_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
  {d1 : FrStP S1 A1}
  {d2 : FrStP S2 A2} :
  ∀ w w', (⊨ d1 ≈ d2 [{ w }]) → w ≤ w' → (⊨ d1 ≈ d2 [{ w' }] ).
Proof.
  rewrite /semantic_judgement.
  by etransitivity.
Qed.

Theorem bind_rule {A1 A2 B1 B2 : ord_choiceType} {S1 S2 : choiceType}
  {f1 : A1 → FrStP S1 B1}
  {f2 : A2 → FrStP S2 B2}
  (m1 : FrStP S1 A1)
  (m2 : FrStP S2 A2)
  (wm : Base.dfst (WrelSt ⟨ A1, A2 ⟩))
  (judge_wm : ⊨ m1 ≈ m2 [{ wm }])
  (wf : (A1 * A2) → Base.dfst (WrelSt ⟨ B1, B2 ⟩))
  (judge_wf : ∀ a1 a2, ⊨ (f1 a1) ≈ (f2 a2) [{ (wf (a1, a2)) }]) :
  ⊨ (bindF f1 m1 ) ≈ (bindF f2 m2) [{ bindW wm wf }].
Proof.
  move => [st1 st2].
  etransitivity.
  rewrite /bindF /=.
    by apply (rlmm_law2 _ _ _ _ θ ⟨ A1, A2 ⟩ ⟨ B1, B2 ⟩ ⟨ f1 , f2 ⟩ ⟨ m1 , m2 ⟩ (st1, st2)).
    rewrite /semantic_judgement in judge_wm, judge_wf.
  destruct A1 as [A1 chA1]. destruct A2 as [A2 chA2].
  destruct B1 as [B1 chB1]. destruct B2 as [B2 chB2].
  simpl in *.
  apply (@omon_bind WProp (A1 * S1 * (A2 * S2)) (B1 * S1 * (B2 * S2)) _ _ (judge_wm (st1, st2))).
  move => [[a1 st1'] [a2 st2']].
  by apply: (judge_wf a1 a2).
Qed.

Theorem bind_rule_pp {A1 A2 B1 B2 : ord_choiceType}  {S1 S2 : choiceType}
  {f1 : A1 → FrStP S1 B1}
  {f2 : A2 → FrStP S2 B2}
  (m1 : FrStP S1 A1)
  (m2 : FrStP S2 A2)
  (pre : S1 * S2 → Prop)
  (middle : (A1 * S1) → (A2 * S2) → Prop)
  (post : (B1 * S1) → (B2 * S2) → Prop)
  (judge_wm : ⊨ ⦃ pre ⦄ m1 ≈ m2 ⦃ middle ⦄)
  (judge_wf : ∀ a1 a2,
      ⊨ ⦃ λ '(s1, s2), middle (a1, s1) (a2, s2) ⦄
        f1 a1 ≈ f2 a2
        ⦃ post ⦄ ) :
  ⊨ ⦃ pre ⦄ (bindrFree _ _ m1 f1 ) ≈ (bindrFree _ _ m2 f2) ⦃ post ⦄.
Proof.
  destruct S1, S2, A1, A2, B1, B2.
  eapply weaken_rule.
  - apply bind_rule with (wf := (fun '(a1, a2) => fromPrePost (fun '(s1, s2) => middle (a1, s1) (a2, s2)) post)).
    + exact judge_wm.
    + exact judge_wf.
  - cbv.
    intuition auto with funelim.
Qed.

(* Pre-condition manipulating rules *)
Theorem pre_weaken_rule {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
  {d1 : FrStP S1 A1}
  {d2 : FrStP S2 A2} :
  ∀ (pre pre' : S1 * S2 → Prop) post,
    (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄) →
    (∀ st1 st2, pre' (st1, st2) → pre (st1, st2) ) →
    (⊨ ⦃ pre' ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => w w' post Hjudg Hleq. move => [st1 st2].
  move => π [H1 H2]. simpl in π.
  apply: Hjudg.
  rewrite /fromPrePost /=.
  split.
  - by apply: Hleq.
  - assumption.
Qed.

Theorem pre_hypothesis_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
  {d1 : FrStP S1 A1}
  {d2 : FrStP S2 A2} :
  ∀ (pre : S1 * S2 → Prop) post,
    (∀ st1 st2,
      pre (st1, st2) →
      ⊨ ⦃ (λ st, st.1 = st1 ∧ st.2 = st2 ) ⦄ d1 ≈ d2 ⦃ post ⦄
    ) →
    (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => pre post Hjudg. move => [st1 st2].
  move => π [H1 H2] /=. simpl in π.
  apply: (Hjudg st1 st2 H1 (st1, st2)).
  by rewrite /fromPrePost /=.
Qed.

Theorem pre_strong_hypothesis_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
                             {d1 : FrStP S1 A1}
                             {d2 : FrStP S2 A2} :
  forall (pre : S1 * S2 -> Prop) post, (forall st1 st2, pre (st1, st2)) -> (⊨ ⦃ (fun st => True ) ⦄ d1 ≈ d2 ⦃ post ⦄) ->
                              (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post ⦄).
Proof.
  move => pre post Hpre Hjudg.
  by apply (pre_weaken_rule (fun st => True) _).
Qed.

(* Rem.: took around 40s to Qed. *)
(* post-condition manipulating rules *)
(* Rem.: simplified the proof resorting to weaken_rule, should be quickier *)
Theorem post_weaken_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
                          {d1 : FrStP S1 A1}
                          {d2 : FrStP S2 A2} :
    forall (pre : S1 * S2 -> Prop) (post1 post2 : A1 * S1 -> A2 * S2 -> Prop),
    (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post1 ⦄) ->
    (forall as1 as2, post1 as1 as2 -> post2 as1 as2) -> (⊨ ⦃ pre ⦄ d1 ≈ d2 ⦃ post2 ⦄).
Proof.
  move => pre post1 post2 Hjudg Hleq.
  eapply weaken_rule.
  - exact Hjudg.
  - cbv. intuition.
Qed.

Declare Scope RulesStateProb_scope.
Delimit Scope RulesStateProb_scope with RSP.

Module RSPNotation.

  Notation "x <- c1 ;; c2" :=
    (bindF (fun x => c2) c1)
    (right associativity, at level 84, c1 at next level)
    : RulesStateProb_scope.

  Notation " x ∈ T <<- c1 ;; c2 " :=
    (bindF (fun x : T => c2) c1)
    (right associativity, at level 90, c1 at next level)
    : RulesStateProb_scope.

  Notation "c1 ;; c2" :=
    (bindF (fun _ => c2) c1)
    (at level 100, right associativity)
    : RulesStateProb_scope.

End RSPNotation.

Import RSPNotation.
Open Scope RulesStateProb_scope.

Theorem seq_rule  { A1 A2 : ord_choiceType }
                  { B1 B2 : ord_choiceType }
                  {S1 S2 : choiceType}
                  {f1 : A1 -> FrStP S1 B1}
                  {f2 : A2 -> FrStP S2 B2}
                  (m1 : FrStP S1 A1) (m2 : FrStP S2 A2)
                  (P : S1 * S2 -> Prop) (R : A1 * S1 -> A2 * S2 -> Prop)
                  (Q : B1 * S1 -> B2 * S2 -> Prop)
                  (judge1 : ⊨ ⦃ P ⦄ m1 ≈ m2 ⦃ R ⦄ )
                  (judge2 : forall a1 a2, ⊨ ⦃ (fun st => R (a1, st.1) (a2, st.2)) ⦄ (f1 a1) ≈ (f2 a2) ⦃ Q ⦄ ) :
 ⊨ ⦃ P ⦄  x ∈ A1 <<- m1 ;; f1 x ≈  x ∈ A2 <<- m2 ;; f2 x  ⦃ Q ⦄.
Proof.
  have H :  ⊨ x ∈ A1 <<- m1;; f1 x ≈ x ∈ A2 <<- m2;; f2 x
      [{bindW (fromPrePost P R) (fun a : A1 * A2 => fromPrePost (fun st : S1 * S2 => R (a.1, st.1) (a.2, st.2)) Q)}]
    := (bind_rule m1 m2 (fromPrePost P R) judge1
                      (fun a => fromPrePost (fun st => R (a.1, st.1) (a.2, st.2)) Q) judge2).
  rewrite /fromPrePost.
  move => [st1 st2] /=.
  move => β [Hbeta1 Hbeta2].
  specialize (H (st1, st2) β). simpl in H. destruct H as [HH1 [HH2 HH2']].
  split; auto. rewrite /fromPrePost in judge2.
  move => [a1 sst1] [a2 sst2] HR.
  specialize (judge2 a1 a2).
  split; assumption.
  exists HH1.
  split; assumption.
Qed.


(* Rem.: can we do \sum_ ( c \in C ) ... where C : choiceType? *)
Definition prod_comp { L R } { M : finType } { d1 : SDistr L } {d2 : SDistr M } { d3 : SDistr R } d12 d23
           ( H12 : coupling d12 d1 d2 ) ( H23 : coupling d23 d2 d3 ): SDistr (F_choice_prod ⟨ L,  R ⟩).
Proof.
  exists (fun '(l, r) => \sum_ ( m <- (index_enum M) | m \in (dinsupp d2) ) (d12 (l,m) * d23 (m,r)) / (d2 m)).
  - admit.
  - admit.
  - admit.
Admitted.


Definition prod_comp_coupling { L R } { M : finType} { d1 : SDistr L } {d2 : SDistr M } { d3 : SDistr R }
           { d12 d23 } (H12 : coupling d12 d1 d2) (H23 : coupling d23 d2 d3):
 coupling (@prod_comp L R M d1 d2 d3 d12 d23 H12 H23) d1 d3.
Proof. Admitted.

(* useful to introduce intermediate games [Formal Certification of Code-Based Cryptographic Proofs, page 24] *)
Theorem comp_rule { A1 A3 : ord_choiceType } { A2 S2 : finType } { S1 S3 : choiceType }
                  { P P' } { Q Q'}
                  (c1 : FrStP S1 A1) (c2 : FrStP S2 A2) (c3 : FrStP S3 A3)
                  (H12 : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
                  (H23 : ⊨ ⦃ P' ⦄ c2 ≈ c3 ⦃ Q' ⦄) :
  ⊨ ⦃ fun '(s1, s3) => exists s2, P(s1,s2) /\ P'(s2,s3) ⦄
    c1 ≈ c3
    ⦃ fun as1 as3 => exists as2, Q as1 as2 /\ Q' as2 as3⦄.
Proof.
  move => [s1 s3].
  move => π. simpl in π.
  rewrite /fromPrePost /=. move => [[s2 [HP HP']] H].
  specialize (H12 (s1, s2) (fun '(as1, as2) => forall as3, Q' as2 as3 -> π (as1, as3)) ). simpl in H12.
  destruct H12 as [d12 [coupling12 H12]].
  { split.
    assumption.
    move => as1 as2 HQ as3 HQ'.
    apply: (H as1 as3).
    exists as2. split; assumption. }
  specialize (H23 (s2, s3) (fun '(as2, as3) => forall as1, Q as1 as2 ->  π (as1, as3)) ). simpl in H23.
  destruct H23 as [d23 [coupling23 H23]].
  { split.
    assumption.
    move => as2 as3 HQ as1 HQ'.
    apply: (H as1 as3).
    exists as2. split; assumption. }
  pose d13 := prod_comp d12 d23 coupling12 coupling23.
  exists d13.
  split.
    by apply: prod_comp_coupling.
    move => as1 as3 d13_gt0.
    apply: (H as1 as3).
    (* by definition of d13*) admit.
Admitted.


(* Lemma bij_pres_summable { A B: choiceType } { d : A -> R } { f : A -> B }  {finv : B -> A } *)
(*       (kinvf  : cancel finv f) (kfinv : cancel f finv) ( H: summable (T:= A) (R:=R) d): *)
(*   summable (T:=B) (R:=R) (fun b : B => d (finv b)). *)
(* Admitted.  *)

(*CA: not used  *)
Definition d__f { A B : ord_choiceType} { d : SDistr A } { f : A -> B } : SDistr  B. Admitted.
(*CA's proof sketch
  d__f : B -> [0,1]

         b ↦ ∑_{a ∈ A: f(a) = b} d(a)  // d-measure of the pre-image of b -- in particular if b is not in image(f) then d__f(b) = 0 //


  - 0 ≤ d__f (b) because sum of non-negative quantities
  - for J ⊆ B, d__f (J) = d (f^-1 (J)) that is finite
  - ∑_{b ∈ B} d__f(b) = ∑_{a ∈ A} d(a)

 *)


(* CA: old proof for a bijective f *)
(* Proof. *)
(*   destruct d as [d Hd1 Hd2 Hd3]. *)
(*   unshelve eexists.  *)
(*   { move => b. exact: d (finv b). }  *)
(*   - move => b /=.  by apply: Hd1.  *)
(*   - by apply: bij_pres_summable.  *)
(*   - unshelve erewrite <- reindex_psum. *)
(*     { apply: predT. }  *)
(*     assumption. *)
(*       by []. *)
(*       exists f. *)
(*    -- move => x H. apply: kinvf. *)
(*    -- move => x H. apply: kfinv. *)
(* Defined.  *)

(*CA: not used *)
Theorem post_conclusion_rule {A0 A1 B : ord_choiceType} { S : choiceType } { pre : S * S -> Prop }
        {c0 : FrStP S A0 } { c1 : FrStP S A1 }
        { f0 : A0 -> B } { f1 : A1 -> B } (* (Hbij0 : bijective f0) (Hbij1 : bijective f1) *)
        (H : ⊨ ⦃ pre ⦄
               (x0 <- c0 ;; retF x0) ≈
               (x1 <- c1 ;; retF x1)
               ⦃ fun '(a0, s0) '(a1, s1) => s0 = s1 /\ f0 a0 = f1 a1 ⦄) :
  ⊨ ⦃ pre ⦄ x0 <- c0 ;; retF (f0 x0) ≈ x1 <- c1 ;; retF (f1 x1) ⦃ eq ⦄.
Proof.
  move => [s0 s1].
  specialize (H (s0, s1)).
  unfold "≤" in *. simpl. simpl in H.
  rewrite /MonoCont_order //=. rewrite /MonoCont_order //= in H.
  move => β [hs0 h].
  specialize (H (fun '(a0, s0, (a1, s1)) => (β (f0 a0 ,s0, (f1 a1, s1))))).
  destruct H as [d [H H']].
  split.
  - assumption.
  - move => [a1 st1] [a2 st2] [Heqa Heqst]. subst.
    apply: h. by rewrite Heqst.
  - unshelve eexists.
    { unshelve eapply d__f.
      exact: F_choice_prod ⟨ F_choice_prod ⟨ A0, S ⟩, F_choice_prod ⟨ A1, S ⟩ ⟩.
      exact: d.
      move => [[a0 st0] [a1 st1]]. exact: (f0 a0, st0, (f1 a1, st1)). }
    split.
    { (*CA:  let fs0 : A0 * S -> B * S = fun (a0, st) => (f a0, st)

             to prove the lmg it suffices to show that

             "θ (x <- c0 ;; ret (f0 x)) : SDistr B * S"  =

             " d__fs0 (θ (x <- c0 ;; ret x) "

             // it will map (b,s) ↦ ∑_{a0 ∈ A0: f(a0) = b} θ (x <- c0; ret x)  //

             indeed for (b1,st1),

             Σ_{(b0, st0)} d' (b0,st0) (b1,st1) =

             Σ_{(a0,st0) a1 : f0(a0) = b0 /\ f1(a1) = b1} d (a0,st0) (a1,st1) = [coupling d _ _ ]

             Σ_{a1 : f1(a1) = } θ (x <- c1 ;; ret x) (a1, st1) = θ (x <- c1 ;; ret (f1 x)

        *) admit. }
      move => [b0 st0] [b1 st1] Hgt0.
      (* by definition of d' fi^-1(bi) are both non empty
         -> exits ai s.t. fi(ai) = bi,  i = 1,2
         -> specialize H with (a0,st0) (a1,st1) and get the thesis
       *)
    admit.
Admitted.

(*CA: depends on post_conclusion_rule but is not used *)
Lemma f_preserves_eq { A B : ord_choiceType } { S : choiceType }
                     { x  y: FrStP S A }
                     (f : A -> B ) (* (Hbij : bijective f)    *)
                     ( H: ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄
                             ( X <- x ;; retF X ) ≈
                             ( Y <- y ;; retF Y)

                            ⦃ eq ⦄ ) :
    ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄
       (X <- x ;; retF (f X) ) ≈
       (Y <- y ;; retF (f Y) )

       ⦃ eq ⦄.
Proof.
  apply: post_conclusion_rule; auto.
  unshelve eapply post_weaken_rule. { exact: eq. }
  - assumption.
  - move => /= [a1 s1] [a2 s2] [H1 H2]. split; by subst.
Qed.



Theorem if_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
                 (c1 c2 : FrStP S1 A1)
                 (c1' c2' : FrStP S2 A2)
                 {b1 b2 : bool}
                 {pre : S1 * S2 -> Prop} {post : A1 * S1 -> A2 * S2 -> Prop}
                 {pre_b1b2 : forall st, pre st -> b1 = b2}
                 { H1 : ⊨ ⦃ fun st => pre st /\ b1 = true ⦄ c1 ≈ c1' ⦃ post ⦄ }
                 { H2 : ⊨ ⦃ fun st => pre st /\ b1 = false ⦄ c2 ≈ c2' ⦃ post ⦄ } :
  ⊨ ⦃ pre ⦄
      (if b1 then c1 else c2) ≈
      (if b2 then c1' else c2')
     ⦃ post ⦄.
Proof.
  apply pre_hypothesis_rule. move=> st1 st2 pre_holds.
  specialize (pre_b1b2 (st1, st2) pre_holds). subst.
  destruct b2 eqn:Hb.
  - apply (pre_weaken_rule (fun st => pre st /\ true = true)).
    assumption.
    rewrite /= => st1' st2' [Heq1 Heq2]. subst.
    split; auto.
  - apply (pre_weaken_rule (fun st => pre st /\ false = false)).
    assumption.
    rewrite /= => st1' st2' [Heq1 Heq2]. subst.
    split; auto.
Qed.

(* TODO: asymmetric variants of if_rule: if_ruleL and if_ruleR *)


Fixpoint bounded_do_while {S : choiceType}  (n : nat) (c : FrStP S bool) :
  FrStP S bool :=
  (* false means fuel emptied, true means execution finished *)
  match n with
  | 0 => retF false
  | S n => bindF (fun b => match b with
                         | false => retF true
                         | true => bounded_do_while n c
                         end
                ) c
  end.

Theorem bounded_do_while_rule  {A1 A2 : ord_choiceType} {S1 S2 : choiceType}
                               {n : nat}
                               (c1 : FrStP S1 bool)
                               (c2 : FrStP S2 bool)
                               {inv : bool -> bool -> (S1 * S2) -> Prop}
                               {H : ⊨ ⦃ inv true true ⦄ c1 ≈ c2 ⦃ fun bs1 bs2 => (inv bs1.1 bs2.1) (bs1.2,  bs2.2) /\ bs1.1 = bs2.1 ⦄ } :
  ⊨ ⦃ inv true true ⦄
    bounded_do_while n c1 ≈ bounded_do_while n c2
    ⦃ fun ls rs => (ls.1 = false /\ rs.1 = false) \/ (inv false false) (ls.2, rs.2) ⦄.
Proof.
  induction n.
  - simpl. eapply weaken_rule.
    apply ret_rule. simpl. intros [? ?] ?. simpl. cbv. intuition eauto.
  - simpl. eapply weaken_rule.
    apply bind_rule. apply H.
    move => b1 b2. eapply weaken_rule. apply if_rule.
    move => st.
    instantiate (1 := fun s => inv b1 b2 s /\ b1 = b2).
    rewrite /=. move => [hfoo heq]. assumption.
    instantiate (1 := fun ls rs => ls.1 = false /\ rs.1 = false \/ (inv false false) (ls.2, rs.2)).
    eapply weaken_rule. apply IHn. simpl. intros [? ?] ?. cbv. intuition eauto.
    rewrite -H3. rewrite {2}H4. assumption.
    eapply weaken_rule. apply ret_rule.
    simpl. intros [? ?] ?. cbv. intuition eauto.
    apply H2. right. rewrite -H3. rewrite {2}H4. assumption.
    instantiate (1 := fun '(b1, b2) => fromPrePost (fun st => (inv b1 b2 st) /\ b1 = b2)
                                                 (fun ls rs => ls.1 = false /\ rs.1 = false \/ (inv false false (ls.2, rs.2)))).
    move => [st1 st2] /=.
    cbv; intuition.
    move => [st1 st2] /=. move => β /=.
    move => [h1 h2].
    split; auto.
    move => [b1 s1] [b2 s2] /= [hh1 hh2]. subst.
    split; auto.
Qed.

(*TODO: asymmetric variants of bounded_do_while -- Rem.: low priority as not useful for our examples *)

Definition θ_dens { S : choiceType } { X : ord_choiceType } :=
  @Theta_dens.unary_theta_dens (F_choice_prod_obj ⟨ X, S ⟩).


Lemma Pr_eq {X Y : ord_choiceType} { S1 S2 : choiceType } {A : pred (X * S1)} {B : pred (Y * S2)}
            Ψ ϕ
            (c1 : FrStP S1 X) (c2 : FrStP S2 Y)
            (H : ⊨ ⦃ Ψ ⦄ c1 ≈ c2 ⦃ ϕ ⦄)
            { s1 s2 } (HPsi : Ψ (s1, s2) )
            (Hpost : forall x y,  ϕ x y -> (A x) <-> (B y)) :
  \P_[ θ_dens (θ0 c1 s1) ] A =
  \P_[ θ_dens (θ0 c2 s2) ] B.
Proof.
  rewrite /pr /=.
  specialize (H (s1,s2) (fun '(a, b) => A a <-> B b)). simpl in H.
  destruct H as [d [[H11 H12] H2]].
  split; assumption.
  rewrite /θ0 /θ_dens /unary_theta_dens /=.
  rewrite -H11 -H12.
  rewrite /lmg /rmg.
  assert ((fun x : X * S1 => (A x)%:R * dfst d x) = (fun x : X *S1 => (A x)%:R * psum (fun w => d (x, w)))) as HeqH11.
  { extensionality k. rewrite dfstE. reflexivity. }
  rewrite HeqH11. simpl in HeqH11.
  assert ((fun x : X * S1 => (A x)%:R * psum (fun w => d (x, w))) = (fun x : X * S1 => psum (fun w => (A x)%:R * d (x, w)))) as H4.
  { extensionality k. rewrite -psumZ. reflexivity.
    case (A k); intuition; by rewrite ler01. }
  rewrite H4.
  assert ((fun x : Y * S2 => (B x)%:R * dsnd d x) = (fun y : Y * S2 => (B y)%:R * psum (fun w => d (w, y)))) as HeqH12.
  { extensionality K. rewrite __deprecated__dsndE. reflexivity. }
  rewrite HeqH12.
  unfold F_choice_prod_obj in d.
  assert ((fun y : Y * S2 => (B y)%:R * psum (fun w => d (w, y))) = (fun y : Y * S2 => psum (fun w => (B y)%:R * d (w, y)))) as H5.
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
  case (A x) eqn:Ha.
  + case (B y) eqn: Hb.
    reflexivity.
    move: H2. intuition. rewrite H. reflexivity. auto.
    case (B y) eqn:Hb.
    intuition. rewrite H0. reflexivity. auto.
    reflexivity.
    assert (d (x, y) = 0).
    rewrite Order.POrderTheory.lt_def in Hd.
    apply Bool.andb_false_iff in Hd.
    destruct Hd.
    ++ move: H. move/eqP. auto.
    ++ assert (0 <= d (x, y)) as Hn.
       { apply ge0_mu. }
       move: H. move/idP. intuition.
         by rewrite H !GRing.mulr0.
    (* summable B*)
    assert ((fun x =>
               (nat_of_bool (let '(_, y) := x in B y))%:R * d x) =
            (fun '(x, y)  => (B y)%:R * d (x, y))) as Heq1.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq1.
    pose (@summable_pr R ((X * S1) * (Y * S2))%type
                                          (fun '(x, y) => B y) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
    (* summable A *)
    assert ((fun x =>
               (nat_of_bool (let '(x, _) := x in A x))%:R * d x) =
            (fun '(x, y)  => (A x)%:R * d (x, y))) as Heq2.
    { extensionality k. destruct k as [k1 k2].
      case (B k2). reflexivity. reflexivity. }
    rewrite -Heq2.
    pose (@summable_pr R ((X * S1) *(Y * S2))%type
                                          (fun '(x, y) => A x) d).
    simpl in *. unfold nat_of_bool in s. rewrite /nat_of_bool. exact s.
Qed.

Corollary coupling_eq { A : ord_choiceType } { S : choiceType }
                      (K1 K2 : FrStP S A )
                      (ψ : S * S -> Prop)
                      (H : ⊨ ⦃ ψ ⦄ K1 ≈ K2 ⦃ eq ⦄):
  forall s1 s2, ψ (s1, s2) -> θ_dens (θ0 K1 s1) = θ_dens (θ0 K2 s2).
Proof.
  move => s1 s2 psi_s1_s2.
  apply distr_ext => /= w.
  assert (\P_[ θ_dens (θ0 K1 s1) ] (pred1 w) = \P_[ θ_dens (θ0 K2 s2) ] (pred1 w)).
  { apply: (Pr_eq ψ eq); rewrite //= => x y Heq. by subst. }
  by repeat rewrite -pr_pred1 in H0.
Qed.


Lemma rewrite_eqDistrL { A1 A2 : ord_choiceType } {S1 S2 : choiceType } { P } { Q }
                       (c1 c1' : FrStP S1 A1) (c2 : FrStP S2 A2)
                       (H : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
                       (θeq : forall s : S1, θ_dens (θ0 c1 s) = θ_dens (θ0 c1' s) ) :

  ⊨ ⦃ P ⦄ c1'  ≈ c2 ⦃ Q ⦄.
Proof.
  move => [s1 s2].
  specialize (H (s1, s2)).
  specialize (θeq s1).
  rewrite /θ0 /θ_dens /= in θeq.
  rewrite /θ /= /MonoCont_order /=.
  rewrite -θeq.
  by apply H.
Qed.

Lemma rewrite_eqDistrR { A1 A2 : ord_choiceType } {S1 S2 : choiceType} { P } { Q }
                       (c1  : FrStP S1 A1) (c2 c2': FrStP S2 A2)
                       (H : ⊨ ⦃ P ⦄ c1 ≈ c2 ⦃ Q ⦄)
                       (θeq : forall s : S2, θ_dens (θ0 c2 s) = θ_dens (θ0 c2' s) ) :

  ⊨ ⦃ P ⦄ c1  ≈ c2' ⦃ Q ⦄.
Proof.
  move => [s1 s2].
  specialize (H (s1, s2)).
  specialize (θeq s2).
  rewrite /θ0 /θ_dens /= in θeq.
  rewrite /θ /= /MonoCont_order /=.
  rewrite -θeq.
  by apply H.
Qed.


Definition coupling_self_SDistr { A } ( d: SDistr A) : SDistr (F_choice_prod ⟨ A, A ⟩) :=
  dmargin (fun a => (a,a)) d.


Lemma coupling_self { A } (d : SDistr A) :
  coupling (coupling_self_SDistr d) d d.
Proof.
  unfold coupling. unfold coupling_self_SDistr. split.
  - unfold lmg. unfold dmargin.
    apply distr_ext. move=> a.
    rewrite __deprecated__dlet_dlet.
    have coucou:  d a = (\dlet_(y <- d) dunit y) a . rewrite dlet_dunit_id. reflexivity.
    rewrite coucou. f_equal. f_equal.
    apply boolp.funext. move=> y. apply distr_ext. move=> b. rewrite dlet_unit.
    reflexivity.
  - unfold rmg. unfold dmargin.
    apply distr_ext. move=> a.
    rewrite __deprecated__dlet_dlet.
    have coucou:  d a = (\dlet_(y <- d) dunit y) a . rewrite dlet_dunit_id. reflexivity.
    rewrite coucou. f_equal. f_equal.
    apply boolp.funext. move=> y. apply distr_ext. move=> b. rewrite dlet_unit.
    reflexivity.
Qed.

Lemma aux_lemma0 {A} (c : SDistr A) (a1 a2 : A) :
coupling_self_SDistr c (a1,a2) = (if a1 == a2 then c a1 else 0).
Proof.
  destruct (eqType_lem A a1 a2).
  - rewrite H. unfold coupling_self_SDistr. rewrite refl_true.
    unfold dmargin.
    have coucou : c a2 = (\dlet_(x <- c) dunit x) a2.
      symmetry. rewrite dlet_dunit_id. reflexivity.
    rewrite coucou. f_equal.
Abort.

Lemma aux_domain : forall u v : R, u * v <> 0 -> u <> 0.
Proof.
  move=> u v. apply contra_not. move=> H0. rewrite H0.
  apply GRing.Theory.mul0r.
Qed.



Lemma aux_lemma { A } {d : SDistr A} :
  forall a1 a2, 0 < (coupling_self_SDistr d) (a1,a2) -> a1 = a2.
Proof.
  move=> a1 a2. unfold coupling_self_SDistr. rewrite dmargin_psumE.
  move=> Hpsum.
  have Hpsum' : psum (fun x : A => ((x, x) == (a1, a2))%:R * d x) <> 0.
    move=> abs. rewrite -abs in Hpsum. rewrite Order.POrderTheory.ltxx in Hpsum.
    discriminate.
  clear Hpsum.
  eapply neq0_psum in Hpsum'. destruct Hpsum'.
  apply aux_domain in H.
  destruct (eqType_lem _ ((x,x) == (a1,a2)) true) as [Houi | Hnon].
  move: Houi => /eqP Houi. move: Houi => [H1 H2]. rewrite -H1 -H2. reflexivity.
  have Hnon' : (x,x) == (a1,a2) = false.
    destruct ((x,x) == (a1,a2)). contradiction. reflexivity.
  rewrite Hnon' in H. cbn in H. contradiction.
Qed.



Lemma reflexivity_rule { A : ord_choiceType } { S : choiceType }
                       (c : FrStP S A):
  ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄ c ≈ c ⦃ eq ⦄.
Proof.
  move => [st1 st] /=. move =>  α [H1 H2] /=. subst.
  exists (coupling_self_SDistr (θ_dens (θ0 c st))).
  split.
  - exact: coupling_self.
  - move => [a1 s1] [a2 s2] H.
    apply: H2. apply: aux_lemma H.
Qed.

Definition dsym { A B : ord_choiceType } { S1 S2 : choiceType } (d : SDistr_carrier
          (F_choice_prod_obj
             ⟨ ((B * S2)%type : choiceType), ((A * S1)%type : choiceType) ⟩)) :
SDistr_carrier
          (F_choice_prod_obj
             ⟨ ((A * S1)%type : choiceType), ((B * S2)%type : choiceType) ⟩) :=
dswap d.


Lemma dsym_coupling { A B : ord_choiceType } { S1 S2 : choiceType } { d : SDistr_carrier
          (F_choice_prod_obj
             ⟨ ((B * S2)%type : choiceType), ((A * S1)%type : choiceType) ⟩) }
      {d1 d2 }
      (Hcoupling : coupling d d1 d2) : coupling (dsym d) d2 d1.
Proof.
  rewrite /dsym. destruct Hcoupling as [dfst_d dsnd_d]. unfold coupling, lmg, rmg in *.
  subst. split.
  - apply: distr_ext. exact: __deprecated__dfst_dswap d.
  - apply: distr_ext. exact: __deprecated__dsnd_dswap d.
Qed.

Lemma symmetry_rule { A B : ord_choiceType } { S1 S2 : choiceType } { pre post }
      (c1  : FrStP S1 A) (c2  : FrStP S2 B)
      (H: ⊨ ⦃ fun '(s2, s1) => pre (s1, s2) ⦄ c2 ≈ c1 ⦃ fun '(b,s2) '(a,s1) => post (a,s1) (b,s2) ⦄ ):
      ⊨ ⦃ pre  ⦄ c1 ≈ c2 ⦃ post ⦄.
Proof.
  move => [s1 s2]. move => /= π.
  move => [Hpre H'].
  specialize (H (s2,s1) (fun '(a,s1,(b,s2)) => π ((b,s2,(a,s1))))).
  cbn in H.
  destruct H as [d' [H1 H2]].
  - rewrite /=. split.
    -- assumption.
    -- move => [a h1] [b h2] Hpost /=. apply: (H' (b, h2) (a, h1) Hpost).
  simpl in d', H1, H2. exists (dswap d'). split.
    - exact: dsym_coupling.
    -- move => [b h2] [a h1] Hdsym. apply: (H2 (a, h1) (b, h2)).
       apply msupp.
       have Heq: dswap (dswap d') = d'. { apply: distr_ext. exact: (dswapK d'). }
       rewrite -Heq.
       apply dinsupp_swap.
       apply /dinsuppP.
       rewrite lt0r in Hdsym.
       move /andP: Hdsym. move => [Hd1  Hd2].
       apply /eqP. assumption.
Qed.

Theorem swap_rule { A1 A2 : ord_choiceType } { S : choiceType } { I : S * S -> Prop } {post : A1 * S -> A2 * S -> Prop }
                  (c1 : FrStP S A1) (c2 : FrStP S A2)
                  (Hinv1 : ⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ post (a1,s1) (a2,s2) ⦄ )
                  (Hinv2 : ⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a2, s2) '(a1, s1) => I (s1, s2) /\ post (a1,s1) (a2,s2) ⦄ ):
  ⊨ ⦃ I ⦄ (c1 ;; c2) ≈ (c2 ;; c1) ⦃ fun '(a2, s2) '(a1, s1) => I (s1, s2) /\ post (a1,s1) (a2,s2) ⦄ .
Proof.
  apply: seq_rule.
  - exact: Hinv1.
  - move => a1 a2.
    apply: pre_weaken_rule.
    { apply: post_weaken_rule.
      exact: Hinv2.
      move => [a1' s1] [a2' s2] [HI HQ].
      split; assumption. }
    move => st1 st2 /= [HI HQ].
    assumption.
Qed.

(*Rem.: don't worry too much about indexes and order, in most cases predicates will be symmetric *)
Theorem swap_ruleL { A1 A2 B : ord_choiceType } { S : choiceType }
                   { pre I : S * S -> Prop }
                   { post :  A2 * S -> A1 * S -> Prop }
                   (l : FrStP S B) (c1 : FrStP S A1) (c2 : FrStP S A2)
                   (HL    : ⊨ ⦃ pre ⦄ l ≈ l ⦃ fun '(b1, s1) '(b2, s2) => I (s1, s2) ⦄)
                   (Hinv1 : ⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ post (a2, s2) (a1, s1)  ⦄ )
                   (Hinv2 : ⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a2, s2) '(a1, s1) => I (s1, s2) /\ post (a2, s2) (a1, s1) ⦄ ):
  ⊨ ⦃ pre ⦄ (l ;; c1 ;; c2) ≈ (l ;; c2 ;; c1) ⦃ post ⦄ .
Proof.
  apply: seq_rule.
  exact: HL.
  move => a1 a2 /=.
  unshelve apply: post_weaken_rule.
  { exact: (fun '(x2, s2) '(x1, s1) => I(s1,s2) /\ (post (x2,s2) (x1,s1))). }
  by apply: (@swap_rule A1 A2 S I (fun '(x1,h1) '(x2, h2) => post (x2,h2) (x1,h1)) c1 c2 Hinv1 Hinv2).
  move => [a1' s1] [a2' s2] [HI HHL] /=. assumption.
Qed.


Section AuxLemmasSwapRuleR.

Lemma  smMonEqu1
{A1 A2 B : ord_choiceType} {S : choiceType}
(r : A1 -> A2 -> FrStP S B) (c1 : FrStP S A1) (c2 : FrStP S A2) :
(a2 ∈ choice_incl A2 <<- c2;; a1 ∈ choice_incl A1 <<- c1;; (r a1 a2))
=
(a ∈ choice_incl (prod_choiceType A1 A2) <<-
        (a2 ∈ choice_incl A2 <<- c2;; a1 ∈ choice_incl A1 <<- c1;; retF (a1, a2));;
        r a.1 a.2).
Proof.
   symmetry.
   cbn. unfold FreeProbProg.rFree_obligation_2.
   unshelve epose (assoc := (@ord_relmon_law3 _ _ _ (FrStP S) _ _ _ _ _)).
     shelve. shelve. shelve.
     exact (fun a : A1 * A2 => r a.1 a.2).
     exact (fun a2 : A2 =>
        bindrFree (@StateTransformingLaxMorph.ops_StP S) (@StateTransformingLaxMorph.ar_StP S) c1
          (fun a1 : A1 => retF (a1, a2))).
   cbn in assoc. unfold FreeProbProg.rFree_obligation_2 in assoc.
   symmetry in assoc. unshelve eapply equal_f in assoc. exact c2. rewrite assoc.
   clear assoc.
   f_equal. apply boolp.funext. move=> a2.
   unshelve epose (assoc := (@ord_relmon_law3 _ _ _ (FrStP S) _ _ _ _ _)).
     shelve. shelve. shelve.
     exact (fun a : A1 * A2 => r a.1 a.2).
     exact (fun a1 : A1 => retF (a1, a2)).
   cbn in assoc. unfold FreeProbProg.rFree_obligation_2 in assoc.
   symmetry in assoc. unshelve eapply equal_f in assoc. exact c1. rewrite assoc.
   reflexivity.
Qed.

Lemma  smMonEqu2
{A1 A2 B : ord_choiceType} {S : choiceType}
(r : A1 -> A2 -> FrStP S B) (c1 : FrStP S A1) (c2 : FrStP S A2) :
(a1 ∈ choice_incl A1 <<- c1;; a2 ∈ choice_incl A2 <<- c2;; (r a1 a2))
=
(a ∈ choice_incl (prod_choiceType A1 A2) <<-
        (a1 ∈ choice_incl A1 <<- c1;; a2 ∈ choice_incl A2 <<- c2;; retF (a1, a2));;
        r a.1 a.2).
Proof.
   symmetry.
   cbn. unfold FreeProbProg.rFree_obligation_2.
   unshelve epose (assoc := (@ord_relmon_law3 _ _ _ (FrStP S) _ _ _ _ _)).
     shelve. shelve. shelve.
     exact (fun a : A1 * A2 => r a.1 a.2).
     exact (fun a1 : A1 =>
      bindrFree (@StateTransformingLaxMorph.ops_StP S) (@StateTransformingLaxMorph.ar_StP S) c2
        (fun a2 : A2 => retF (a1, a2))).
   cbn in assoc. unfold FreeProbProg.rFree_obligation_2 in assoc.
   symmetry in assoc. unshelve eapply equal_f in assoc. exact c1. rewrite assoc.
   clear assoc.
   f_equal. apply boolp.funext. move=> a1.
   unshelve epose (assoc := (@ord_relmon_law3 _ _ _ (FrStP S) _ _ _ _ _)).
     shelve. shelve. shelve.
     exact (fun a : A1 * A2 => r a.1 a.2).
     exact (fun a2 : A2 => retF (a1, a2)).
   cbn in assoc. unfold FreeProbProg.rFree_obligation_2 in assoc.
   symmetry in assoc. unshelve eapply equal_f in assoc. exact c2. rewrite assoc.
   reflexivity.
Qed.

Context (S : choiceType).

Let Frp_fld :=  @Frp.

Lemma theta0_vsbind {P Q : ord_choiceType} (p : FrStP S P) (q : FrStP S Q)
  (s : S) :
θ0 (x ∈ P <<- p ;; q) s
=
(ord_relmon_bind Frp_fld)
  (fun ps : P * S => let (p,s) := ps in θ0 q s)
  (θ0 p s).
Proof.
  unfold θ0.
  epose (assoc := rlmm_law2 _ _ _ _ (unaryIntState) P Q (fun _ => q) ).
  cbn in assoc. specialize (assoc p).
  cbn. unshelve eapply equal_f in assoc. exact s.
  rewrite [LHS]assoc.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  unfold FreeProbProg.rFree_obligation_2.
  reflexivity.
Qed.

Lemma some_commutativity
  {A1 A2 B : ord_choiceType}
  (post : B * S -> B * S -> Prop)
  (r : A1 -> A2 -> FrStP S B)
  (c1 : FrStP S A1)
  (c2 : FrStP S A2)
  (HR : forall (a1 : A1) (a2 : A2), ⊨ ⦃ fun '(s2, s1) => s1 = s2 ⦄ r a1 a2 ≈ r a1 a2 ⦃ post ⦄ )
  (post_eq : forall bs bs' : B * S, bs = bs' -> post bs bs')
  (Hcomm : forall s : S,
          θ_dens (θ0 (a1 ∈ choice_incl A1 <<- c1;; a2 ∈ choice_incl A2 <<- c2;; retF (a1, a2)) s) =
          θ_dens (θ0 (a2 ∈ choice_incl A2 <<- c2;; a1 ∈ choice_incl A1 <<- c1;; retF (a1, a2)) s) )
  (s : S) :
θ_dens
  (θ0
     (a ∈ choice_incl (prod_choiceType A1 A2) <<-
      (a1 ∈ choice_incl A1 <<- c1;; a2 ∈ choice_incl A2 <<- c2;; retF (a1, a2));;
      r a.1 a.2) s) =
θ_dens
  (θ0
     (a ∈ choice_incl (prod_choiceType A1 A2) <<-
      (a2 ∈ choice_incl A2 <<- c2;; a1 ∈ choice_incl A1 <<- c1;; retF (a1, a2));;
      r a.1 a.2) s).
Proof.
  (*we begin by using bind preservation of θ0 on both sides*)
  pose ( p12 :=
(a1 ∈ choice_incl A1 <<- c1;; a2 ∈ choice_incl A2 <<- c2;; retF (a1, a2)) ).
  assert (θ0_comm :
(θ0 (a ∈ choice_incl (prod_choiceType A1 A2) <<- p12 ;; r a.1 a.2) s)
=
(ord_relmon_bind Frp_fld)^~(θ0 p12 s)
  (fun xs' => let (x,s'):= xs' in θ0 (r x.1 x.2) s') ).
{
  unfold θ0.
  unshelve epose (assoc := rlmm_law2 _ _ _ _ (unaryIntState) _ _ _ ).
    shelve. shelve. shelve.
    exact (fun (a : A1 * A2) => r a.1 a.2).
  cbn in assoc. specialize (assoc p12).
  cbn. unshelve eapply equal_f in assoc. exact s.
  rewrite [LHS]assoc.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  unfold FreeProbProg.rFree_obligation_2.
  reflexivity.
}
  rewrite θ0_comm. clear θ0_comm.

  pose ( p21 :=
(a2 ∈ choice_incl A2 <<- c2;; a1 ∈ choice_incl A1 <<- c1;; retF (a1, a2)) ).
  assert (θ0_comm :
(θ0 (a ∈ choice_incl (prod_choiceType A1 A2) <<- p21 ;; r a.1 a.2) s)
=
(ord_relmon_bind Frp_fld)^~(θ0 p21 s)
  (fun xs' => let (x,s'):= xs' in θ0 (r x.1 x.2) s') ).
{
  unfold θ0.
  unshelve epose (assoc := rlmm_law2 _ _ _ _ (unaryIntState) _ _ _ ).
    shelve. shelve. shelve.
    exact (fun (a : A1 * A2) => r a.1 a.2).
  cbn in assoc. specialize (assoc p21).
  cbn. unshelve eapply equal_f in assoc. exact s.
  rewrite [LHS]assoc.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  unfold FreeProbProg.rFree_obligation_2.
  reflexivity.
}
  rewrite θ0_comm. clear θ0_comm.

  (*next we apply bind preservation of θ_dens*)
  unshelve etransitivity.
    cbn. unshelve eapply (ord_relmon_bind SDistr).
    - exact ( prod_choiceType (prod_choiceType A1 A2 ) S ).
    - move=> [x s'].  exact ( θ_dens (θ0 (r x.1 x.2) s' ) ).
    - exact (θ_dens (θ0 p12 s)).
  unfold θ_dens at 1.
  pose utheta_dens_fld :=
@unary_theta_dens.
  unshelve epose (θ_dens_bind :=
@rmm_law2 _ _ _ _ _ _ _ _ _ utheta_dens_fld _ _ _).
  shelve. shelve.
  exact (fun xs' : A1 * A2 * S => let (x, s') := xs' in θ0 (r x.1 x.2) s').
  rewrite /=.
  move: θ_dens_bind => /= θ_dens_bind.
  unshelve eapply equal_f in θ_dens_bind. exact (θ0 p12 s).
  rewrite θ_dens_bind.
  unfold SubDistr.SDistr_obligation_2.
  rewrite  /θ_dens /=.
  assert (contEqu :
( fun x : A1 * A2 * S =>
     Theta_dens.unary_theta_dens_obligation_1 (F_choice_prod_obj ⟨ B, S ⟩)
       (let (x0, s') := x in θ0 (r x0.1 x0.2) s') )
=
( fun trucc : A1 * A2 * S =>
     let (x, s') := trucc in
     Theta_dens.unary_theta_dens_obligation_1 (F_choice_prod_obj ⟨ B, S ⟩)
       (θ0 (r x.1 x.2) s') ) ).
  apply boolp.funext. move=> [[a1 a2] ss]. reflexivity.
  rewrite contEqu. apply f_equal. reflexivity.

  (*p12 is p21 under θ_dens ∘ θ0 *)
  unfold θ_dens at 3.
  pose utheta_dens_fld :=
@unary_theta_dens.
  unshelve epose (θ_dens_bind :=
@rmm_law2 _ _ _ _ _ _ _ _ _ utheta_dens_fld _ _ _).
  shelve. shelve.
  exact (fun xs' : A1 * A2 * S => let (x, s') := xs' in θ0 (r x.1 x.2) s').
  rewrite /=.
  move: θ_dens_bind => /= θ_dens_bind.
  unshelve eapply equal_f in θ_dens_bind. exact (θ0 p21 s).
  rewrite θ_dens_bind.
  assert ( contEqu :
(fun trucc : A1 * A2 * S =>
     let (x, s') := trucc in θ_dens (θ0 (r x.1 x.2) s'))
=
(fun x : A1 * A2 * S =>
     Theta_dens.unary_theta_dens_obligation_1 (F_choice_prod_obj ⟨ B, S ⟩)
       (let (x0, s') := x in θ0 (r x0.1 x0.2) s')) ).
  apply boolp.funext. move=> [[a1 a2] ss]. rewrite /=. reflexivity.
  rewrite contEqu. apply f_equal.
  apply Hcomm.
Qed.


End AuxLemmasSwapRuleR.

Theorem swap_ruleR { A1 A2 B : ord_choiceType } { S : choiceType }
                   { post : B * S -> B * S -> Prop }
                   (r : A1 -> A2 -> FrStP S B) (c1 : FrStP S A1) (c2 : FrStP S A2)
                   (HR    : forall a1  a2, ⊨ ⦃ fun '(s2, s1) => s1 = s2 ⦄ (r a1 a2) ≈ (r a1 a2) ⦃ post ⦄)
                   (post_eq : forall bs bs', bs = bs' -> post bs bs')

                   (*Rem.: "commutativity condition" always satisfied for example by sample o ;; sample o' *)
                   (Hcomm: forall s,  θ_dens (θ0 ((a1 <- c1 ;; a2 <- c2 ;; retF (a1,a2) )) s) =
                                 θ_dens (θ0 ((a2 <- c2 ;; a1 <- c1 ;; retF (a1,a2) )) s) ):

  ⊨ ⦃ fun '(s1, s2) => s1 = s2 ⦄  ( a1 <- c1 ;; a2 <- c2 ;; (r a1 a2) ) ≈ ( a2 <- c2 ;;  a1 <- c1 ;; (r a1 a2)) ⦃ post ⦄ .
Proof.
  unshelve apply: rewrite_eqDistrL.
    exact: ( a <- (a2 <- c2 ;;  a1 <- c1 ;; retF (a1, a2)) ;; r a.1 a.2 ).
  unshelve apply: rewrite_eqDistrR.
    exact: ( a <- (a1 <- c1 ;;  a2 <- c2 ;; retF (a1, a2)) ;; r a.1 a.2 ).
  eapply (seq_rule _ _ _ (fun aa1 aa2 => aa1 = aa2)).
  apply: rewrite_eqDistrL. exact: reflexivity_rule. assumption.
  -  move => [a1 a2] [a1' a2']. apply: pre_hypothesis_rule.
     move => s1 s2 /= [H1 H2 H3]. subst.
     specialize (HR a1' a2' (s2, s2)).
     move => [s s'] /=. move => β [[Heq Heq'] H]. subst. apply: HR.
     simpl. split; auto.
  -  rewrite (@smMonEqu1 A1 A2 B S r c1 c2).
     move=> s.
     unshelve eapply some_commutativity. exact post.
       apply HR.
       apply post_eq.
       apply Hcomm.
  -  rewrite (@smMonEqu2 A1 A2 B S r c1 c2).
     move=> s.
     pose some_commutativity.
     unshelve erewrite <- some_commutativity. exact post.
     reflexivity.
       apply HR.
       apply post_eq.
       apply Hcomm.
Qed.


(*Rem.: a proved variant of the above -- less useful though *)
Lemma swap_ruleR' { A1 A2 B : ord_choiceType } { S : choiceType }
                  { I : S * S -> Prop}
                  { post : B * S -> B * S -> Prop } { Q : A1 * S -> A2 * S -> Prop }
                  (r : FrStP S B) (c1 : FrStP S A1) (c2 : FrStP S A2)
                  (HR    : forall a1  a2, ⊨ ⦃ fun '(s2, s1) => Q (a1, s1) (a2, s2) ⦄ r ≈ r ⦃ post ⦄)
                   (Hinv1 : ⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ )
                   (Hinv2 : ⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a2, s2) '(a1, s1) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ ) :
  ⊨ ⦃ I ⦄  ( c1 ;; c2 ;; r ) ≈ ( c2 ;; c1 ;; r ) ⦃ post ⦄ .
Proof.
  have Hfoo : (c1;; c2 ;; r ) = ( (c1 ;; c2) ;; r ).
  { unfold ";;". by rewrite ord_relmon_law3. } rewrite Hfoo; clear Hfoo.
  have Hfoo : (c2;; c1;; r ) = ((c2 ;; c1) ;; r).
  { unfold ";;". by rewrite ord_relmon_law3. } rewrite Hfoo; clear Hfoo.
  unshelve apply: seq_rule.
  { exact: (fun '(a2, s2) '(a1, s1) => Q (a1, s1) (a2, s2)). }
  apply: post_weaken_rule.
  eapply (swap_rule c1 c2).
  exact: Hinv1.
  exact: Hinv2.
  { move => [a1 s1] [a2 s2] [HI HQ]. auto. }
  move => a2 a1 /=.
  exact: HR a1 a2.
Qed.

(*Rem.: TODO possibly generalize as above *)
Theorem swap_rule_ctx { A1 A2 Bl Br : ord_choiceType } { S : choiceType }
                      { I pre : S * S -> Prop }
                      { post: Br * S -> Br * S -> Prop } { Q : A1 * S -> A2 * S -> Prop }
                      (l : FrStP S Bl) (r : FrStP S Br) (c1 : FrStP S A1) (c2 : FrStP S A2)
                      (HL    : ⊨ ⦃ pre ⦄ l ≈ l ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) ⦄)
                      (HR    : forall a1 a2, ⊨ ⦃ fun '(s2, s1) => Q (a1,s1) (a2,s2) ⦄ r ≈ r ⦃ post ⦄)
                      (Hinv1 : ⊨ ⦃ I ⦄ c1 ≈ c2 ⦃ fun '(a1, s1) '(a2, s2) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ )
                      (Hinv2 : ⊨ ⦃ I ⦄ c2 ≈ c1 ⦃ fun '(a2, s2) '(a1, s1) => I (s1, s2) /\ Q (a1, s1) (a2, s2) ⦄ ):
  ⊨ ⦃ pre ⦄  l ;; c1 ;; c2 ;; r ≈ l ;; c2 ;; c1 ;; r ⦃ post ⦄ .
Proof.
  apply: seq_rule.
   - exact: HL.
   - move => a1 a2 /=.
     apply: swap_ruleR'.
     -- exact: HR.
     -- exact: Hinv1.
     -- exact: Hinv2.
Qed.



Section samplerC_rule.
Notation η M := (ord_relmon_unit M).
Notation dnib M := (ord_relmon_bind M).
(* In this section we prove a rule called samplerC, which tells that *)
(* sampling operations in the monad free monad Fr[St,P] *)
(* (on a  stateful probabilistic signature) commute with other *)
(* operations (for instance 'get' ...) *)

(* More precisely we prove that the semantics of programs *)
(* Fr[St,P] --> StT(Fr[P]) --> StT(SD) *)
(* assigns the same value to *)
(* r <- sample o ;; a <- c ;; ret (a,r) and *)
(* a <- c ;; r <- sample o ;; ret (a,r). *)
(* And this condition is sufficient to prove a rule like the one described *)
(* above *)

(*operations and arities for probabilities*)
Let Op := P_OP.
Let Ar := P_AR.

Context { A : ord_choiceType }  {S : choiceType}.

(*for state + prob*)
Let Opst := (ops_StP S).
Let Arst := (ar_StP S).

Context (o : Op) (c : FrStP S A).

Arguments bindrFree { _ _ _ _ } _ _.
Arguments ropr {_ _ _ } _ _.
Arguments callrFree {_ _} _.
Arguments retrFree {_ _ _} _.

(*the two programs of interest...*)
(*sample_c and c_sample*)
Let splo :=  @callrFree Opst Arst (op_iota o).
Definition sample_c :=
bindrFree splo (fun r =>
bindrFree c (fun a =>
retrFree (a,r))).

Definition c_sample :=
bindrFree c (fun a =>
bindrFree splo (fun r =>
retrFree (a,r))).


Lemma θ0_vs_bind {X Y : choiceType} (m : FrStP S X) (k : X -> FrStP S Y):
θ0 (bindrFree m k) =
(dnib stT_Frp) (fun x:X => θ0 (k x)) (θ0  m).
Proof.
  assert ( to_dnib : bindrFree m k = (dnib (FrStP S)  k) m ).
    reflexivity.
  rewrite to_dnib.
  rewrite /θ0.
  pose bla :=
rmm_law2 _ _ _ _ (@unaryIntState S)
         X Y k.
  rewrite /= in bla.
  unshelve eapply equal_f in bla. exact m.
  rewrite /=. assumption.
Qed.

Lemma θ0_vs_sample_c :
  θ0 sample_c
  =
  dnib stT_Frp
    (fun r : Arst (op_iota o) => dnib stT_Frp (fun a : A => θ0 (retrFree (a, r))) (θ0 c))
    (θ0 splo).
Proof.
  unfold sample_c.
  rewrite θ0_vs_bind.
  eassert (eqCont :
(fun r : Arst (op_iota o) => θ0 (bindrFree c (fun a : choice_incl A => retrFree (a, r))))
=
(fun r => _) ).
  apply boolp.funext. move=> x. rewrite θ0_vs_bind. reflexivity.
  rewrite eqCont. reflexivity.
Qed.

Lemma θ0_vs_c_sample :
  θ0 c_sample
  =
  dnib stT_Frp
    (fun a : A => dnib stT_Frp (fun r : Arst (op_iota o) => θ0 (retrFree (a, r))) (θ0 splo))
    (θ0 c).
Proof.
  unfold c_sample.
  rewrite θ0_vs_bind.
  eapply (f_equal (λ x, dnib stT_Frp x (θ0 c))).
  apply boolp.funext. move=> a.
  rewrite θ0_vs_bind. reflexivity.
Qed.

Lemma θ0_c_sample_vs_s0 (s0 : S) :
θ0 c_sample s0 =
bindrFree (θ0 c s0) (fun asc => let (a, sc) := asc in
bindrFree (θ0 splo sc) (fun rsr => let (r,sr) := rsr in
retrFree (a,r,sr))).
Proof.
  rewrite θ0_vs_c_sample.
  rewrite /=.
  rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite /FreeProbProg.rFree_obligation_2.
  reflexivity.
Qed.

Lemma θ0_sample_c_vs_s0 (s0 : S) :
θ0 sample_c s0 =
bindrFree (θ0 splo s0) (fun rsr => let (r,sr) := rsr in
bindrFree (θ0 c sr) (fun asc => let (a, sc) := asc in
retrFree (a,r,sc))).
Proof.
  rewrite θ0_vs_sample_c.
  rewrite /=.
  rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite /FreeProbProg.rFree_obligation_2.
  reflexivity.
Qed.

Let Frp_fld :=  @Frp.

Lemma bindrFree_and_ret {U:choiceType} (mu : Frp_fld U) :
bindrFree mu (fun u =>
retrFree u)
=
mu.
Proof.
  unfold bindrFree. induction mu.
  reflexivity.
  f_equal. apply boolp.funext. move=> p.
  specialize (H p). rewrite H. reflexivity.
Qed.


Lemma op_outoffree (s0 : S):
UniversalFreeMap.outOfFree sigMap (Arst (op_iota o)) splo
=
@sigMap S (op_iota o).
Proof.
    cbn.
    rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
    apply boolp.funext. move=> s0'.
    rewrite /FreeProbProg.rFree_obligation_2.
    rewrite /FreeProbProg.rFree_obligation_1.
    cbn. rewrite /probopStP. reflexivity.
Qed.

Let sploP := @callrFree Op Ar o.

(* Lemma quick_slice : *)
(* Ar o = Arst (op_iota o). *)
(*   destruct o. cbn. reflexivity. *)
(* Qed. *)

(* Let sploP' :=  @callrFree Op Ar o. *)
(* Program Definition sploP : rFreeF Op Ar (Arst (op_iota o)) := sploP'. *)
(* Next Obligation. *)
(*   apply quick_slice. *)
(* Qed. *)


(* Context (s0 : S). *)
(* Goal True. *)
(*   pose bla := θ0 splo s0. cbn in bla. *)
(*   pose bla' := bindrFree sploP (fun r => *)
(* retrFree (r, s0) ). *)
(*   cbn in bla'. *)
(* rFreeF P_OP P_AR (F_choice_prod_obj ⟨ Arst (op_iota o), S ⟩) *)
(* rFreeF Op   Ar   (prod_choiceType (Ar o) S) *)

Lemma θ0_of_sample (s0 : S) :
θ0 splo s0
=
bindrFree sploP (fun r =>
retrFree (r, s0) ).
Proof.
  unfold θ0. unfold unaryIntState.
  rewrite (op_outoffree s0). rewrite /=.
  rewrite /probopStP.
  destruct o as [X op].
  reflexivity.
Qed.

Lemma θ0_OF_sample_c_s0 (s0 : S) :
θ0 sample_c s0 =
bindrFree sploP (fun r =>
bindrFree (θ0 c s0) (fun asc => let (a, sc) := asc in
retrFree (a,r,sc))).
Proof.
  rewrite θ0_sample_c_vs_s0.
  rewrite θ0_of_sample.
  epose (bind_assoc := ord_relmon_law3 Frp_fld _ _ _ _ _).
  eapply equal_f in bind_assoc.
  cbn in bind_assoc.
  rewrite /FreeProbProg.rFree_obligation_2 in bind_assoc.
  erewrite <- bind_assoc.
  f_equal.
Qed.

Lemma θ0_OF_c_sample_s0 (s0 : S) :
θ0 c_sample s0 =
bindrFree (θ0 c s0) (fun asc => let (a, sc) := asc in
bindrFree sploP (fun r =>
retrFree (a,r,sc))).
Proof.
  rewrite θ0_c_sample_vs_s0.
  f_equal. apply boolp.funext. move=> [a sc].
  rewrite θ0_of_sample.
  epose (bind_assoc := ord_relmon_law3 Frp_fld _ _ _ _ _).
  eapply equal_f in bind_assoc.
  cbn in bind_assoc.
  rewrite /FreeProbProg.rFree_obligation_2 in bind_assoc.
  erewrite <- bind_assoc.
  f_equal.
Qed.

Let utheta_dens_fld :=
(@Theta_dens.unary_theta_dens).

Lemma utheta_dens_vs_bind {X Y : choiceType}
(m : Frp X)
(k : X -> Frp Y) :
utheta_dens_fld _ (bindrFree m k)
=
(dnib SDistr) (fun x => utheta_dens_fld _ (k x))
              (utheta_dens_fld _ m).
Proof.
  assert ( to_dnib : bindrFree m k = (dnib Frp  k) m ).
    reflexivity.
  rewrite to_dnib.
  pose bla :=
rmm_law2 _ _ _ _
(@Theta_dens.unary_theta_dens)
X Y k.
  rewrite /= in bla.
  unshelve eapply equal_f in bla. exact m.
  rewrite /=. assumption.
Qed.

Lemma θ_dens_vs_bind' {X Y : choiceType}
(m : Frp  X )
(k : X -> Frp (prod_choiceType Y S)) :
θ_dens (bindrFree m k) =
(dnib SDistr) (fun xs => θ_dens (k xs)) (utheta_dens_fld _ m).
Proof.
  assert ( to_dnib : bindrFree m k = (dnib Frp  k) m ).
    reflexivity.
  rewrite to_dnib.
  rewrite /θ_dens.
  pose bla :=
rmm_law2 _ _ _ _
(@Theta_dens.unary_theta_dens)
X (prod_choiceType Y S) k.
  rewrite /= in bla.
  unshelve eapply equal_f in bla. exact m.
  rewrite /=. assumption.
Qed.


Let SD_bind
{A B : choiceType}
(m : SDistr_carrier A)
(k : A -> SDistr_carrier B) :=
SDistr_bind A B k m.
Let SD_ret {A : choiceType}
(a : A) :=
SDistr_unit A a.

Lemma θ_dens_OF_θ0_sample_c_s0 (s0:S) :
θ_dens (θ0 sample_c s0)
=
SD_bind (utheta_dens_fld _ sploP) (fun r =>
SD_bind (utheta_dens_fld _ (θ0 c s0)) (fun asc => let (a,sc) := asc in
SDistr_unit _ (a,r,sc))).
Proof.
  rewrite θ0_OF_sample_c_s0.
  rewrite !/θ_dens.
  rewrite utheta_dens_vs_bind.
  rewrite !/SD_bind.
  rewrite /=.
  rewrite /SubDistr.SDistr_obligation_2.
  f_equal.
  apply boolp.funext. move=> r.
  rewrite /Theta_dens.unary_theta_dens_obligation_1.
  epose (hlp := utheta_dens_vs_bind _ _).
  rewrite /= in hlp.
  unfold Theta_dens.unary_theta_dens_obligation_1 in hlp.
  unfold SubDistr.SDistr_obligation_2 in hlp.
  erewrite hlp.
  f_equal.
  apply boolp.funext. move=> [aa ss].
  clear hlp.
  cbn. f_equal.
Qed.



Lemma θ_dens_OF_θ0_c_sample_s0 (s0:S) :
θ_dens (θ0 c_sample s0)
=
SD_bind (utheta_dens_fld _ (θ0 c s0)) (fun asc => let (a,sc) := asc in
SD_bind (utheta_dens_fld _ sploP) (fun r =>
SDistr_unit _ (a,r,sc))).
Proof.
  rewrite θ0_OF_c_sample_s0.
  rewrite !/θ_dens.
  rewrite utheta_dens_vs_bind.
unshelve eassert (eq_cont :
(λ x : choice_incl
             (ord_functor_comp (OrderEnrichedRelativeAdjunctionsExamples.unaryTimesS1 S)
                (OrderEnrichedRelativeAdjunctions.KleisliLeftAdjoint Frp) A),
       utheta_dens_fld
         (F_choice_prod_obj
            ⟨ ord_functor_id ord_choiceType (prod_choiceType A (Arst (op_iota o))),
            OrderEnrichedRelativeAdjunctionsExamples.mkConstFunc ord_choiceType ord_choiceType S
              (prod_choiceType A (Arst (op_iota o))) ⟩)
         (let (a, sc) := x in bindrFree sploP (λ r : choice_incl (Ar o), retrFree (a, r, sc))))
=
fun x => let (a,sc) := x in
SD_bind (utheta_dens_fld _ sploP) (fun r =>
SDistr_unit _ (a,r,sc))).
    apply boolp.funext. move=> [aa ss]. rewrite utheta_dens_vs_bind. reflexivity.
  rewrite eq_cont. rewrite /=.
  rewrite !/SD_bind.
  rewrite /SubDistr.SDistr_obligation_2.
  rewrite /Theta_dens.unary_theta_dens_obligation_1.
  reflexivity.
Qed.


Lemma SD_commutativity {X Y : choiceType}
(p : SDistr X) (q : SDistr Y) :
SD_bind p (fun x =>
SD_bind q (fun y =>
SD_ret (x,y)))
=
SD_bind q (fun y =>
SD_bind p (fun x =>
SD_ret (x,y))).
Proof.
  rewrite !/SD_bind. rewrite !/SDistr_bind.
  rewrite !/SD_ret. rewrite !/SDistr_unit.
  rewrite !/dlet.
  unlock. apply distr_ext. move=> [x y].
  rewrite /mlet /=.
  transitivity
(psum
  (fun x0 : X => psum (fun x1 : Y => p x0 * q x1 * dunit (T:=prod_choiceType X Y) (x0, x1) (x, y)))).
{
  apply eq_psum. move=> x0. rewrite -psumZ /=.
  apply eq_psum. move=> y0 /=.
  rewrite GRing.mulrA. reflexivity.
  destruct p as [pmap p0 p_sum p1]. apply p0.
}
  symmetry.
  transitivity
(psum
  (fun x0 : Y => psum (fun x1 : X => p x1 * q x0 * dunit (T:=prod_choiceType X Y) (x1, x0) (x, y)))).
{
    apply eq_psum. move=> y0. rewrite -psumZ /=.
    apply eq_psum. move=> x0 /=.
    rewrite GRing.mulrA. rewrite[q y0 * _] GRing.mulrC.
    reflexivity.
    destruct q as [qmap q0 q_sum q1]. apply q0.
}
  symmetry.
(*   epose (hlp := psum_pair_swap *)
(* (S:=fun (yx0 : Y * X) => let (y0,x0) := yx0 in *)
(* p x0 * q y0 * dunit (T:=prod_choiceType X Y) (x0,y0) (x,y)) _). *)
(*   rewrite -hlp. *)
(*   rewrite psum_pair. reflexivity. *)
(*   Unshelve<. *)
  apply __admitted__interchange_psum.
{
  move=> x0.
  unshelve eapply eq_summable.
    move=> y0. exact (q y0 * (p x0 * dunit (T:=_) (x0,y0)(x,y))).
    move=> y0. rewrite GRing.mulrA. rewrite [q y0 * _] GRing.mulrC.
    reflexivity.
  apply (
  summable_mu_wgtd (T:=Y)
  (f:=fun y0 => p x0 * dunit (T:=_) (x0,y0) (x,y)) q ).
  move=> y0. unshelve edestruct mulr_cp1.
    exact R.
  clear p1. destruct p0 as [le1 _].
  apply /andP. split.
  apply mulr_ge0.
  destruct p as [pmap p_0 p_sum p_1]. apply p_0.
  destruct (dunit (T:=_) (x0,y0)) as [umap u_0 u_sum u_1]. apply u_0.
  apply le1. destruct p as [pmap p_0 p_sum p_1]. apply p_0.
  destruct (dunit (T:=_) (x0,y0)) as [umap u_0 u_sum u_1]. apply u_0.
  apply le1_mu1. apply le1_mu1.
}
  unshelve eapply eq_summable.
    move=> x0. exact ( p x0 * psum (fun y0 => q y0 * dunit (T:=_) (x0,y0)(x,y))).
  move=> x0. rewrite -psumZ. apply eq_psum. move=> y0 /=. rewrite GRing.mulrA. reflexivity.
  destruct p as [pmap p_0 p_sum p_1]. apply p_0.
  apply (
  summable_mu_wgtd (T:=X)
  (f:=fun x0 => psum (fun y0 : Y => q y0 * dunit (T:=prod_choiceType X Y) (x0, y0) (x, y))) p).
  move=> x0. apply /andP. split.
  apply ge0_psum.
  unshelve eapply Order.POrderTheory.le_trans.
    exact (psum q).
  eapply le_psum.
  move=> y0. apply/andP. split.
  apply mulr_ge0.
  destruct q as [qmap q_0 q_sum q_1]. apply q_0.
  easy.
(* ler_piMr: forall [R : numDomainType] [x y : R], 0 <= y -> x <= 1 -> y * x <= y *)
  apply ler_piMr. destruct q as [qmap q_0 q_sum q_1]. apply q_0.
  apply le1_mu1. easy. destruct q as [qmap q_0 q_sum q_1]. apply q_1.
Qed.

Lemma SD_commutativity' {X Y Z : choiceType}
(p : SDistr X) (q : SDistr Y)
(g : X -> Y -> SDistr Z) :
SD_bind p (fun x =>
SD_bind q (fun y =>
g x y))
=
SD_bind q (fun y =>
SD_bind p (fun x =>
g x y)).
Proof.
  transitivity
(SD_bind (
  SD_bind p (fun x =>
  SD_bind q (fun y =>
  SD_ret (x,y)))
        ) (fun xy => let (x,y) := xy in
g x y)).
{
  epose (bind_bind := (ord_relmon_law3 SDistr) _ _ _ _ _).
  eapply equal_f in bind_bind.
  rewrite /= in bind_bind.
  unfold SubDistr.SDistr_obligation_2 in bind_bind.
  rewrite !/SD_bind.
  erewrite <- bind_bind.
  f_equal. apply boolp.funext. move=> x.
  clear bind_bind.
  epose (bind_bind := (ord_relmon_law3 SDistr) _ _ _ _ _).
  eapply equal_f in bind_bind.
  rewrite /= in bind_bind.
  unfold SubDistr.SDistr_obligation_2 in bind_bind.
  erewrite <- bind_bind. f_equal.
  apply boolp.funext ; move=> y.
  clear bind_bind.
  epose (bind_ret := (ord_relmon_law2 SDistr) _ _ _).
  eapply equal_f in bind_ret. rewrite /= in bind_ret.
  unfold SubDistr.SDistr_obligation_2 in bind_ret.
  unfold SubDistr.SDistr_obligation_1 in bind_ret.
  rewrite /SD_ret. erewrite bind_ret. reflexivity.
}
  rewrite SD_commutativity.
  epose (bind_bind := (ord_relmon_law3 SDistr) _ _ _ _ _).
  eapply equal_f in bind_bind.
  rewrite /= in bind_bind.
  unfold SubDistr.SDistr_obligation_2 in bind_bind.
  rewrite !/SD_bind.
  erewrite <- bind_bind.
  f_equal. apply boolp.funext. move=> y.
  clear bind_bind.
  epose (bind_bind := (ord_relmon_law3 SDistr) _ _ _ _ _).
  eapply equal_f in bind_bind.
  rewrite /= in bind_bind.
  unfold SubDistr.SDistr_obligation_2 in bind_bind.
  erewrite <- bind_bind. f_equal.
  apply boolp.funext ; move=> x.
  clear bind_bind.
  epose (bind_ret := (ord_relmon_law2 SDistr) _ _ _).
  eapply equal_f in bind_ret. rewrite /= in bind_ret.
  unfold SubDistr.SDistr_obligation_2 in bind_ret.
  unfold SubDistr.SDistr_obligation_1 in bind_ret.
  rewrite /SD_ret. erewrite bind_ret. reflexivity.
Qed.


Lemma sample_c_is_c_sample (s0 : S):
θ_dens (θ0 sample_c s0)
=
θ_dens (θ0 c_sample s0).
Proof.
  rewrite (θ_dens_OF_θ0_sample_c_s0 s0).
  rewrite (θ_dens_OF_θ0_c_sample_s0 s0).
  unshelve epose (hlp :=
SD_commutativity'
(utheta_dens_fld (Ar o) sploP)
(utheta_dens_fld _ (θ0 c s0)) _).
    shelve.
    move=> rr /= [aa ss]. exact (SDistr_unit _ (aa,rr,ss)).
  rewrite hlp. f_equal.
  apply boolp.funext. move=> [a sc]. f_equal.
Qed.


End samplerC_rule.
