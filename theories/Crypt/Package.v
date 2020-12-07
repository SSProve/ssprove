From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings Rules
  StateTransfThetaDens StateTransformingLaxMorph FreeProbProg.
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.


From Crypt Require Import pkg_preamble.
From Crypt Require Import pkg_chUniverse.
From Crypt Require Import pkg_core_definition.
From Crypt Require Import pkg_free_module.
From Crypt Require Import pkg_laws.



Module PackageTheory (π : ProbRulesParam).

  Export π.
  Module PKG_TH := (CorePackageTheory π).
  Import PKG_TH.
  Module PKG_FM := (FreeModule π).
  Import PKG_FM.
  Module PKG_LAWS := (PackageLaws π).
  Import PKG_LAWS.


  Section Games.
    Definition Game_import : Interface := fset0.
    Definition Game_Type (Game_export : Interface) : Type :=
      package Game_import Game_export.

    Definition RUN := (0, (chUnit, chBool)).
    Definition A_export : Interface := fset1 RUN.
    Lemma RUN_in_A_export : RUN \in A_export.
      apply in_fset1.
    Qed.

    Definition Adversary4Game (Game_export : Interface) : Type :=
      package Game_export A_export.


    Open Scope fset.
    Let iops_StP := @ops_StP probE rel_choiceTypes chEmb.
    Let iar_StP := @ar_StP probE rel_choiceTypes chEmb.

    Definition dommHeap (s : {fset Location}) := { x : Location | x \in s }.

    Definition makeHeap (s : {fset Location}) :=
      {fmap (dommHeap s) → Value}.

    Definition makeHeap_cT (s : {fset Location}) :=
      [choiceType of (makeHeap s)].

    Definition Game_op_import_S : Type := {_ : ident & void}.
    Definition Game_import_P : Game_op_import_S → choiceType :=
      fun v => match v with existT a b => match b with end end.

    Definition getFromMap
               {locs : {fset Location}}
               (map : {fmap {x : Location | x \in locs} → Value})
               (l : Location) (H : l \in locs) : Value.
    Proof.
      destruct (getm map (exist _ l H)) eqn:Hget.
      + exact s.
      + exact 0.
    Defined.

    Arguments getFromMap {_} _ _ {_}.

    Definition setFromMap
               {locs : {fset Location}}
               (map : {fmap {x : Location | x \in locs} → Value})
               (l : Location) (H : l \in locs) (v : Value) : {fmap {x : Location | x \in locs} → Value}.
    Proof.
      apply (setm map).
      - exists l. exact H.
      - exact v.
    Defined.

    Definition fromEmpty {B} {v : opsig} (H : v \in fset0) : B.
      rewrite in_fset0 in H.
      move: H. move /eqP. move /eqP => H.
      discriminate.
    Defined.
    From Crypt Require Import FreeProbProg.

    Ltac revert_last :=
      match goal with
      | h : _ |- _ => revert h
      end.

    Ltac revert_all :=
      repeat revert_last.

    Ltac abstract_goal :=
      (* revert_all ; *)
      let h := fresh "h" in
      match goal with
      | |- ?G => assert (G) as h ; [
          idtac
        | abstract (apply h)
        ]
      end.

    Arguments retrFree {_ _ _} _.
    Arguments ropr {_ _ _} _ _.

    Set Equations Transparent.

    Equations? FreeTranslate' {B : choiceType} {locs : {fset Location}}
      (p : raw_program B) (h : valid_program locs Game_import p)
    : rFreeF (iops_StP (makeHeap_cT locs)) (iar_StP (makeHeap_cT locs)) B :=
      FreeTranslate' p h with p := {
      | _ret x := retrFree _ ;
      | _opr o x k := False_rect _ _ ;
      | _getr l k := ropr (inl (inl (gett _))) (λ s, let v := getFromMap s l in FreeTranslate' (k v) _) ;
      | _putr l v k :=
        ropr (inl (inl (gett (makeHeap_cT locs)))) (λ s, ropr (inl (inr (putt (makeHeap_cT locs) (setFromMap s l _ v)))) (λ s', FreeTranslate' k _)) ;
      | _sampler op k := ropr (inr op) (λ s, FreeTranslate' (k s) _)
      }.
    Proof.
      - destruct h as [hin _]. eapply fromEmpty. exact hin.
      - cbn in h. intuition auto.
      - cbn in h. destruct h as [ho h]. apply h.
      - cbn in h. intuition auto.
      - cbn in h. destruct h as [ho h]. apply h.
    Defined.

    Definition FreeTranslate {B locs} (p : program locs Game_import B) :=
      let '(exist p h) := p in
      FreeTranslate' p h.

    Let getLocations {I E} (P : package I E) : {fset Location} :=
      let '(locs; PP) := P in locs.

    Definition get_raw_package_op {L} {I E : Interface} (p : raw_package)
               (hp : valid_package L I E p)
               (o : opsig) (ho : o \in E) (arg : src o) : program L I (tgt o).
    Proof.
      (* ER: updated using the same order as TW below *)
      destruct (lookup_op p o) as [f|] eqn:e.
      2:{
        (* TW: Done several times, I should make a lemma. *)
        exfalso.
        destruct o as [n [S T]].
        cbn - [lookup_op] in e.
        specialize (hp _ ho). cbn in hp. destruct hp as [f [ef hf]].
        cbn in e. destruct (p n) as [[St [Tt g]]|] eqn:e2.
        2: discriminate.
        destruct chUniverse_eqP.
        2:{ noconf ef. congruence. }
        destruct chUniverse_eqP.
        2:{ noconf ef. congruence. }
        discriminate.
      }
      exists (f arg).
      destruct o as [n [S T]].
      cbn - [lookup_op] in *.
      eapply lookup_op_valid in hp. 2: eauto.
      cbn - [lookup_op] in hp. destruct hp as [g [eg hg]].
      rewrite e in eg. noconf eg.
      eapply hg.
    Defined.

    Definition get_opackage_op {L} {I E : Interface} (P : opackage L I E)
               (op : opsig) (Hin : op \in E) (arg : src op) : program L I (tgt op).
    Proof.
      exact (get_raw_package_op (projT1 P) (projT2 P) op Hin arg).
    Defined.

    Definition get_package_op {I E : Interface} (P : package I E)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : program (getLocations P) I (tgt op) :=
      let (L, PP) as s return (program (getLocations s) I (tgt op)) := P in
      get_opackage_op PP op Hin arg.

    Definition Pr_raw_program {L} {B}
               (p : raw_program B)
               (p_is_valid : valid_program L Game_import p)
      : makeHeap_cT L -> SDistr (F_choice_prod_obj ⟨ B , makeHeap_cT L ⟩).
    Proof.
      move => s0.
      pose STDIST := thetaFstd B (FreeTranslate (exist _ p p_is_valid)) s0.
      exact (STDIST prob_handler).
    Defined.

    Definition Pr_raw_func_program {L} {A} {B}
               (p : A -> raw_program B)
               (p_is_valid : forall a, valid_program L Game_import (p a))
      : A -> makeHeap_cT L -> SDistr (F_choice_prod_obj ⟨ B , makeHeap_cT L ⟩).
    Proof.
      move => a s0.
      exact (Pr_raw_program (p a) (p_is_valid a) s0).
    Defined.

    Definition Pr_raw_package_op  {E : Interface} {L}
               (p : raw_package)
               (p_is_valid : valid_package L Game_import E p)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : makeHeap_cT L -> SDistr (F_choice_prod_obj ⟨ tgt op , makeHeap_cT L ⟩).
    Proof.
      move => s0.
      pose (get_raw_package_op p p_is_valid op Hin arg) as f.
      exact (Pr_raw_program (f∙1) (f∙2) s0).
    Defined.

    Definition Pr_op  {E : Interface} (P : package Game_import E)
               (op : opsig) (Hin : op \in E) (arg : src op)
      : makeHeap_cT (getLocations P) -> SDistr (F_choice_prod_obj ⟨ tgt op , makeHeap_cT (getLocations P) ⟩).
    Proof.
      move => s0.
      destruct P as [L [PP PP_is_valid]].
      exact (Pr_raw_package_op PP PP_is_valid op Hin arg s0).
    Defined.

    Definition Pr (P : package Game_import A_export) : SDistr (bool_choiceType) :=
      SDistr_bind _ _ (fun '(b, _) => SDistr_unit _ b)
                      (Pr_op P RUN RUN_in_A_export Datatypes.tt emptym).

    Definition get_op {I E : Interface} (p : package I E)
      (o : opsig) (ho : o \in E) (arg : src o) :
      program (p.π1) I (tgt o).
    Proof.
      (* TW: I transformed this definition so that it computes directly. *)
      destruct (lookup_op (p.π2 ∙1) o) as [f|] eqn:e.
      2:{
        (* TW: Done several times, I should make a lemma. *)
        exfalso.
        destruct p as [L [p hp]].
        destruct o as [n [S T]].
        cbn - [lookup_op] in e.
        specialize (hp _ ho). cbn in hp. destruct hp as [f [ef hf]].
        cbn in e. destruct (p n) as [[St [Tt g]]|] eqn:e2.
        2: discriminate.
        destruct chUniverse_eqP.
        2:{ noconf ef. congruence. }
        destruct chUniverse_eqP.
        2:{ noconf ef. congruence. }
        discriminate.
      }
      exists (f arg).
      destruct p as [L [p hp]].
      destruct o as [n [S T]].
      cbn - [lookup_op] in *.
      eapply lookup_op_valid in hp. 2: eauto.
      cbn - [lookup_op] in hp. destruct hp as [g [eg hg]].
      rewrite e in eg. noconf eg.
      eapply hg.
    Defined.

    (* Definition Pr (P : package Game_import A_export) : SDistr (bool_choiceType). *)
    (* Proof. *)
    (*   pose STDIST := thetaFstd _ (FreeTranslate (get_op P RUN RUN_in_A_export Datatypes.tt)). *)
    (*   simpl in STDIST. *)
    (*   pose SSDIST := STDIST prob_handler emptym. *)
    (*   refine (SDistr_bind _ _ (fun '(b, _) => SDistr_unit _ b) SSDIST). *)
    (* Defined. *)

    Section semantic_judgement.
      Context (locsl : {fset Location}).
      Context (locsr : {fset Location}).
      (* morphism *)
      Let θ  := @thetaFstdex probE rel_choiceTypes chEmb (makeHeap_cT locsl) (makeHeap_cT locsr) prob_handler.
      (* spec monad *)
      Let WrelSt  := (rlmm_codomain θ).


      Definition semantic_judgement (A1 A2 : ord_choiceType)
                 (c1 : FrStP (makeHeap_cT locsl) A1) (c2 : FrStP (makeHeap_cT locsr) A2)
                 (w  : Base.dfst (WrelSt ⟨ A1, A2 ⟩)) : Prop :=
        (θ ⟨A1,A2⟩)∙1 ⟨c1,c2⟩ ≤ w.

      Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ c1 c2 w).

      Definition fromPrePost {A1 A2 : ord_choiceType}
                 (pre : (makeHeap_cT locsl * makeHeap_cT locsr) -> Prop)
                 (post : (A1 * makeHeap_cT locsl) -> (A2 * makeHeap_cT locsr) -> Prop)
        :  Base.dfst (WrelSt ⟨ A1, A2 ⟩).
      Proof.
        simpl.
        unshelve econstructor.
        - move=> [is1 is2]. unshelve econstructor.
          + move=> myPost.
             exact (  pre (is1,is2) /\
                      forall as1 as2, (post as1 as2) -> myPost (as1, as2)).
          + move => x y Hxy [H1 H2].
            split.
            * assumption.
            * move => as1 as2 post12. apply: Hxy. by apply: H2.
        - move => x y Heq π.
          by rewrite Heq.
      Defined.

    End semantic_judgement.

    Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
      (semantic_judgement _ _ _ _ c1 c2 (@fromPrePost _ _ _ _ pre post)).

    Import Num.Theory.
    Open Scope ring_scope.
    Open Scope real_scope.

    Definition GamePair (Game_export : Interface) := bool -> Game_Type Game_export.

    Definition Advantage { Game_export : Interface } (G : GamePair Game_export)
               (A : Adversary4Game Game_export) : R :=
      `| (Pr (link A (G false)) true) - (Pr (link A (G true)) true)|.

    Definition AdvantageE { Game_export : Interface }
      : Game_Type Game_export -> Game_Type Game_export -> Adversary4Game Game_export -> R
      := fun G0 G1 A => `| (Pr (link A G0) true) - (Pr (link A G1) true)|.

    Notation "ϵ( GP )" := (fun A => AdvantageE (GP false) (GP true) A) (at level 90).
    Notation " G0 ≈[ R ] G1 " := (AdvantageE G0 G1 = R) (at level 50).

    Ltac fold_FreeTranslate :=
      change (FreeTranslate' ?p ?h) with (FreeTranslate (exist _ p h)).

    Lemma some_lemma_for_prove_relational {export : Interface} {B}
               (P1 : package Game_import export)
               (P2 : package Game_import export)
               (I : makeHeap_cT (getLocations P1) * makeHeap_cT (getLocations P2) -> Prop)
               (Hempty : I (emptym, emptym))
               (H : forall (op : opsig) (Hin : op \in export) (arg : src op),
                   ⊨ ⦃ fun '(s1, s2) => I (s1, s2) ⦄
                     (FreeTranslate (get_package_op P1 op Hin arg))
                     ≈
                     (FreeTranslate (get_package_op P2 op Hin arg))
                     ⦃ fun '(b1, s1) '(b2, s2) => I (s1, s2) /\ b1 = b2 ⦄)
               (A : raw_program B)
               (A_is_valid : valid_program fset0 export A)
               (s1 : makeHeap_cT (P1.π1)) (s2 : makeHeap_cT (P2.π1)) (Hs1s2 : I (s1, s2))
      : dmargin fst (Pr_raw_program (raw_program_link A (P1.π2 ∙1))
                                    (raw_program_link_valid _ _ _ _ _ _ (valid_injectLocations _ fset0 P1.π1 A (fsub0set P1.π1) A_is_valid) (P1.π2 ∙2)) s1) =
        dmargin fst (Pr_raw_program (raw_program_link A (P2.π2 ∙1))
                                    (raw_program_link_valid _ _ _ _ _ _ (valid_injectLocations _ fset0 P2.π1 A (fsub0set P2.π1) A_is_valid) (P2.π2 ∙2)) s2).
      (* ER: for the proof we should have extra information about the second
         component (preserves I), but let's see how the thing behaves so far *)
    Proof.
      destruct P1 as [L1 [P1a P1b]].
      destruct P2 as [L2 [P2a P2b]].
      induction A; intros.
      - cbn. unfold SubDistr.SDistr_obligation_2.
        rewrite !SDistr_rightneutral.
        apply distr_ext. move => x0.
        rewrite !dlet_unit. reflexivity.
      - cbn. unfold SubDistr.SDistr_obligation_2.
        rewrite !SDistr_assoc. admit.
      - unfold Pr_raw_program.
        cbn - [thetaFstd]. fold_FreeTranslate.
        (* TW: I think this is much better now. *)
        (* ER: this is nice, I would like to step a bit with raw_program_link and
               FreeTranslate *)
        simpl.
        (* TW: Now it gets big because of thetaFstd *)
        admit.
      - unfold Pr_raw_program.
        simpl (FreeTranslate ⦑ raw_program_link (_putr l v A) ((L1; ⦑ P1a ⦒).π2) ∙1 ⦒).
        (* PGH: the next two commands break compilation; commented out for now *)
        (* simpl (thetaFstd B (ropr _ _ _ _ _)). *)
        (* destruct (raw_program_link_valid B L1 export Game_import *)
        (*                  (_putr l v A) P1a *)
        (*                  (valid_injectLocations B fset0 L1 (_putr l v A) *)
        (*                                         (fsub0set (T:=nat_ordType) L1) A_is_valid) P1b). *)
        admit.
      - unfold Pr_raw_program in *.
        simpl (FreeTranslate _).
        simpl (thetaFstd).
    Admitted.

    (* ER: How do we connect the package theory with the RHL?
           Something along the following lines should hold? *)
    Definition prove_relational {export : Interface}
               (P1 : package Game_import export)
               (P2 : package Game_import export)
               (I : makeHeap_cT (getLocations P1) * makeHeap_cT (getLocations P2) -> Prop)
               (Hempty : I (emptym, emptym))
               (H : forall (op : opsig) (Hin : op \in export) (arg : src op),
                   ⊨ ⦃ fun '(s1, s2) => I (s1, s2) ⦄
                     (FreeTranslate (get_op P1 op Hin arg))
                     ≈
                     (FreeTranslate (get_op P2 op Hin arg))
                     ⦃ fun '(b1, s1) '(b2, s2) => I (s1, s2) /\ b1 = b2  ⦄)
      : P1 ≈[ fun A => 0 ] P2.
    Proof.
      destruct P1 as [locs1 pp1].
      destruct P2 as [locs2 pp2].
      unfold getLocations in I, H.
      extensionality A.
      unfold semantic_judgement in H.
      unfold AdvantageE, Pr.
      admit.
    Admitted.
  End Games.
End PackageTheory.
