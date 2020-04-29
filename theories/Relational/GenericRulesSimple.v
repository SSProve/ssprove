From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Coq Require Import Relation_Definitions Morphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
(* From Relational Require Import Category RelativeMonads RelativeMonadExamples. *)
From Relational Require Import  OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.

Set Primitive Projections.
Set Universe Polymorphism.

(* We introduce relational program logic rules starting from abstract algebraic structure *)

(* Section RelationalProgramLogicFromBimodule. *)
(*   Context (M1 M2 : Monad) (M12 := compPair M1 M2). *)
(*   Context (W : ord_functor TypeCatSq OrdCat) (rmW : rightModuleStructure M12 W). *)
(*   Context (η : natTrans Jprod W) (σ := point_to_homomorphism Jprod rmW η). *)

(*   Definition mod_semantic_judgement {A1 A2} c1 c2 w := *)
(*     Spr1 (σ ⟨A1,A2⟩) ⟨c1,c2⟩ ≤ w. *)

(*   Notation "⊨ c1 ≈ c2 [{ w }]" := (@mod_semantic_judgement _ _ c1 c2 w). *)

(*   Check (fun A B (c1 : M1 A) (c2: M2 B) w => ⊨ c1 ≈ c2 [{ w }] ). *)

(*   Lemma weaken_rule {A B} {c1 : M1 A} {c2 : M2 B} {w w'} : *)
(*     ⊨ c1 ≈ c2 [{ w }] -> w ≤ w' -> ⊨ c1 ≈ c2 [{ w' }]. *)
(*   Proof. move=> ? ? ; rewrite /mod_semantic_judgement ; estransitivity ; eassumption. Qed. *)

(*   Lemma ret_rule {A B} {a : A} {b : B} : *)
(*     ⊨ ret a ≈ ret b [{ Spr1 (η ⟨A,B⟩) ⟨a,b⟩ }]. *)
(*   Proof. *)
(*     rewrite /mod_semantic_judgement. *)
(*     move: (point_to_homomorphism_to_point Jprod rmW η ⟨A, B⟩ ⟨a,b⟩) => /= ->. *)
(*     sreflexivity. *)
(*   Qed. *)

(*   Definition bindW {A1 A2 B1 B2} *)
(*              (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2) (w : dfst (W ⟨A1,A2⟩)) := *)
(*     Spr1 (rm_bind rmW (to_prod f1 f2)) w. *)

(*   Lemma bind_act_rule {A1 A2 B1 B2} *)
(*         {m1 : M1 A1} {m2 : M2 A2} {w} : *)
(*     ⊨ m1 ≈ m2 [{ w }] -> forall (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2), *)
(*       ⊨ bind m1 f1 ≈ bind m2 f2 [{ bindW f1 f2 w }]. *)
(*   Proof. *)
(*     rewrite /mod_semantic_judgement. *)
(*     move=> H f1 f2. *)
(*     pose (rm_homo _ rmW σ (to_prod f1 f2) ⟨m1, m2⟩) as t. *)
(*     move: t => /= ->. unfold bindW. *)
(*     apply (Spr2 (rm_bind rmW (to_prod f1 f2)))=> //=. *)
(*   Qed. *)

(*   Lemma if_rule {A1 A2} {m1: M1 A1} {m2 : M2 A2} {w w'} (b:bool) : *)
(*       (if b then ⊨ m1 ≈ m2 [{ w }] else ⊨ m1 ≈ m2 [{ w' }]) *)
(*       -> ⊨ m1 ≈ m2 [{ if b then w else w' }]. *)
(*   Proof. destruct b=> //. Qed. *)

(*   Lemma nat_rect_rule {A1 A2} {m1: nat -> M1 A1} {m2 : nat -> M2 A2} {w0 wsuc} *)
(*         (w := nat_rect (fun=> dfst (W ⟨A1, A2⟩)) w0 wsuc) : *)
(*     ⊨ m1 0 ≈ m2 0 [{ w0 }] -> *)
(*     (forall n, ⊨ m1 n ≈ m2 n [{ w n }] -> ⊨ m1 (S n) ≈ m2 (S n) [{ wsuc n (w n) }]) -> *)
(*     forall n, ⊨ m1 n ≈ m2 n [{ w n }]. *)
(*   Proof. induction n => //=. apply H0=> //. Qed. *)

(* End RelationalProgramLogicFromBimodule. *)

(* Generic rules for the simple framework [Section 2.4]*)


Section RelationalProgramLogicFromRelativeMonadZero.
  Context (M1 M2 : Monad)
          (M12 := compPair M1 M2).
  Context (W : RelationalSpecMonad0)
          (θ : RelationalLaxEffectObservation0 M1 M2 W).

  Definition semantic_judgement A1 A2 c1 c2 w := Spr1 (θ ⟨A1,A2⟩) ⟨c1,c2⟩ ≤ w.
  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ c1 c2 w).

  Check (fun A B (c1 : M1 A) (c2: M2 B) w => ⊨ c1 ≈ c2 [{ w }] ).


  Import SPropNotations.
  Lemma seq_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W ⟨B1, B2⟩⦆} :
    ⊨ m1 ≈ m2 [{ wm }] -> (forall a1 a2, ⊨ f1 a1 ≈ f2 a2 [{ wf∙1 ⟨a1, a2⟩ }]) ->
    ⊨ bind m1 f1 ≈ bind m2 f2 [{ wm ≫= wf }].
  Proof.
    intros Hm Hf.
    rewrite /semantic_judgement; etransitivity.
    apply: (rlmm_law2 _ _ M12 W θ _ _ (to_prod f1 f2) ⟨m1, m2⟩).
    set f12 := ((θ _ ∙ _) ∙ _); etransitivity.
    2: apply: (ord_relmon_bind_proper W _ _ f12); move=> [? ?] ; apply Hf.
    apply: ((ord_relmon_bind W f12)∙2 _ _); apply: Hm.
  Qed.

  Lemma weaken_rule2 {A B} {c1 : M1 A} {c2 : M2 B} {w w'} :
    ⊨ c1 ≈ c2 [{ w }] -> w ≤ w' -> ⊨ c1 ≈ c2 [{ w' }].
  Proof.
    rewrite /semantic_judgement. move=> ? ? ; etransitivity ; eassumption.
  Qed.

  Lemma ret_rule2 {A B} {a : A} {b : B} :
    ⊨ ret a ≈ ret b [{ (ord_relmon_unit W ⟨A , B⟩)∙1 ⟨a,b⟩ }].
  Proof.
    apply: (rlmm_law1 _ _ M12 W θ ⟨A , B⟩ ⟨a,b⟩).
  Qed.

  Lemma if_rule {A1 A2} {m1: M1 A1} {m2 : M2 A2} {w w'} (b:bool) :
      (if b then ⊨ m1 ≈ m2 [{ w }] else ⊨ m1 ≈ m2 [{ w' }])
      -> ⊨ m1 ≈ m2 [{ if b then w else w' }].
  Proof. destruct b=> //. Qed.

  Lemma nat_rect_rule {A1 A2} {m1: nat -> M1 A1} {m2 : nat -> M2 A2} {w0 wsuc}
        (w := nat_rect (fun=> dfst (W ⟨A1, A2⟩)) w0 wsuc) :
    ⊨ m1 0 ≈ m2 0 [{ w0 }] ->
    (forall n, ⊨ m1 n ≈ m2 n [{ w n }] -> ⊨ m1 (S n) ≈ m2 (S n) [{ wsuc n (w n) }]) ->
    forall n, ⊨ m1 n ≈ m2 n [{ w n }].
  Proof. induction n => //=. apply H0=> //. Qed.

End RelationalProgramLogicFromRelativeMonadZero.

Notation "θ ⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θ _ _ c1 c2 w) (at level 85).

(* Tailored rules derived from the generic ones *)

Section GoingPractical.
  Context (M1 M2 : Monad) (M12 := compPair M1 M2).
  Context (W : RelationalSpecMonad0) (θ : RelationalLaxEffectObservation0 M1 M2 W).

  Lemma gp_ret_rule {A B a b w} :
    Spr1 (ord_relmon_unit W ⟨A , B⟩) ⟨a,b⟩ ≤ w ->
    θ ⊨ ret a ≈ ret b [{ w }].
  Proof. apply weaken_rule2 ; apply ret_rule2. Qed.

  Lemma gp_seq_rule
        {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W ⟨B1, B2⟩⦆} {w} :
    θ ⊨ m1 ≈ m2 [{ wm }] ->
    (forall a1 a2, θ ⊨ f1 a1 ≈ f2 a2 [{ Spr1 wf ⟨a1, a2⟩ }]) ->
    wm ≫= wf ≤ w ->
    θ ⊨ bind m1 f1 ≈ bind m2 f2 [{ w }].
  Proof. move=> ? ? ; apply weaken_rule2 ; apply seq_rule=> //. Qed.

  Import SPropNotations.
  Program Definition extend_to_Jprod {A1 A2 B1 B2} (wf0 : A1 × A2 -> dfst (W ⟨B1,B2⟩)) : OrdCat⦅Jprod ⟨A1,A2⟩ ; W ⟨B1, B2⟩⦆ :=
    ⦑wf0⦒.
  Next Obligation.
    cbv ; intuition. move: y H => [a1 a2] [Ha1 Ha2]. rewrite Ha1 Ha2.
    reflexivity.
  Qed.


  Definition skip {M:Monad} : M unit := ret tt.
  Notation "m1 ;; m2" := (bind m1 (fun=> m2)) (at level 65).

  Lemma apply_left {A B1 B2} {m1 : M1 A} {c1 : M1 B1} {c2 : M2 B2} {w1 w2 w} :
    θ ⊨ m1 ≈ skip [{ w1 }] ->
    θ ⊨ c1 ≈ c2 [{ w2 }] ->
    w1 ≫= OrdCat_cst w2 ≤ w ->
    θ ⊨ m1 ;; c1 ≈ c2 [{ w }].
  Proof.
    move=> H1 H2 ; apply weaken_rule2.
    enough (c2 = skip ;; c2) as ->.
    apply seq_rule=> //.
    rewrite /bind monad_law1 //.
  Qed.

  Program Definition OrdCat_lift {A B} (f : A -> dfst B) : OrdCat⦅discr A; B⦆ :=
    Sexists _ f _.
  Next Obligation. move=> ? ? H0 ; induction H0; reflexivity. Qed.

  Program Definition OrdCat_lift' {A1 A2 B} (f : A1 -> A2 -> dfst B) : OrdCat⦅Jprod ⟨A1, A2⟩; B⦆ :=
    Sexists _ (fun a => f (nfst a) (nsnd a)) _.
  Next Obligation. move=> ? ? H0 ; induction H0; reflexivity. Qed.

  Lemma apply_left_tot {A1 A2} {c1 : M1 A1} {c2 : M2 A2} {w1 w2 w} :
    θ ⊨ c1 ≈ skip [{ w1 }] ->
    (forall a1, θ ⊨ ret a1 ≈ c2 [{ w2 a1 }]) ->
    w1 ≫= OrdCat_lift' (fun a _ => w2 a) ≤ w ->
    θ ⊨ c1 ≈ c2 [{ w }].
  Proof.
    move=> H1 H2 ; apply weaken_rule2.
    enough (c2 = skip ;; c2) as ->.
    enough (c1 = bind c1 ret) as ->.
    apply seq_rule=> // ? ?; eapply weaken_rule2; [apply H2| cbv ;intuition].
    rewrite /bind monad_law2 //.
    rewrite /bind monad_law1 //.
  Qed.

  Lemma apply_right {A B1 B2} {m2 : M2 A} {c1 : M1 B1} {c2 : M2 B2} {w1 w2 w} :
    θ ⊨ skip ≈ m2 [{ w1 }] ->
    θ ⊨ c1 ≈ c2 [{ w2 }] ->
    w1 ≫= OrdCat_cst w2 ≤ w ->
    θ ⊨ c1 ≈ m2 ;; c2 [{ w }].
  Proof.
    move=> H1 H2 ; apply weaken_rule2.
    enough (c1 = skip ;; c1) as ->.
    apply seq_rule=> //.
    rewrite /bind monad_law1 //.
  Qed.

  Lemma apply_right_tot {A1 A2} {c1 : M1 A1} {c2 : M2 A2} {w1 w2 w} :
    θ ⊨ skip ≈ c2 [{ w1 }] ->
    (forall a2, θ ⊨ c1 ≈ ret a2 [{ w2 a2 }]) ->
    w1 ≫= OrdCat_lift' (fun=>w2) ≤ w ->
    θ ⊨ c1 ≈ c2 [{ w }].
  Proof.
    move=> H1 H2 ; apply weaken_rule2.
    enough (c1 = skip ;; c1) as ->.
    enough (c2 = bind c2 ret) as ->.
    apply seq_rule=> // ? ?; eapply weaken_rule2.
    rewrite /bind monad_law2 //.
    rewrite /bind monad_law1 //.
  Qed.

  (* Let Wmod := rmon_morph_right_module W θ. *)
  (* Let mod_semantic_judgement' {A1 A2} := *)
  (*   @mod_semantic_judgement M1 M2 _ Wmod (rmon_unit W) A1 A2. *)

  (* Import SPropNotations. *)
  (* Lemma to_mod_semantic_judgement {A1 A2} {c1:M1 A1} {c2:M2 A2} w : *)
  (*   θ ⊨ c1 ≈ c2 [{ w }] -> mod_semantic_judgement' c1 c2 w. *)
  (* Proof. *)
  (*   rewrite /mod_semantic_judgement'; unfold mod_semantic_judgement. *)
  (*   unfold semantic_judgement. *)
  (*   enough (θ ⟨ A1, A2 ⟩ ∼ point_to_homomorphism Jprod Wmod (rmon_unit W) ⟨ A1, A2 ⟩) as -> => //. *)
  (*   cbv=> ? ; epose (relmon_law2 W) as t ; cbv in t ; rewrite t=> //. *)
  (* Qed. *)

  (* Lemma from_mod_semantic_judgement {A1 A2} {c1:M1 A1} {c2:M2 A2} w : *)
  (*   mod_semantic_judgement' c1 c2 w -> θ ⊨ c1 ≈ c2 [{ w }]. *)
  (* Proof. *)
  (*   rewrite /mod_semantic_judgement'; unfold mod_semantic_judgement. *)
  (*   unfold semantic_judgement. *)
  (*   enough (θ ⟨ A1, A2 ⟩ ∼ point_to_homomorphism Jprod Wmod (rmon_unit W) ⟨ A1, A2 ⟩) as -> => //. *)
  (*   cbv=> ? ; epose (relmon_law2 W) as t ; cbv in t ; rewrite t=> //. *)
  (* Qed. *)

  (* Let act {A1 A2 B1 B2} := @bindW _ _ _ Wmod A1 A2 B1 B2. *)
  (* Lemma cont_to_spec {A1 A2 B1 B2} *)
  (*       {m1 : M1 A1} {m2 : M2 A2} {w w'} : *)
  (*   θ ⊨ m1 ≈ m2 [{ w }] -> forall (f1 : A1 -> M1 B1) (f2 : A2 -> M2 B2), *)
  (*     act f1 f2 w ≤ w' -> *)
  (*     θ ⊨ bind m1 f1 ≈ bind m2 f2 [{ w' }]. *)
  (* Proof. *)
  (*   move=> ? ? ?; apply weaken_rule2 ; rewrite /act. *)
  (*   apply from_mod_semantic_judgement. *)
  (*   apply bind_act_rule; apply to_mod_semantic_judgement=> //. *)
  (* Qed. *)

  (* (* This rule "shows" completeness of the simple rules using already defined rules *)
  (*    (and not unfolding the judgement which would be trivial, *)
  (*    a safer approach would consist in defining an inductive for ⊢) *)
  (*    assuming the bimodules rules, so not achieving much *) *)
  (* Lemma to_spec {A1 A2} {m1 : M1 A1} {m2 : M2 A2} {w} : *)
  (*   Spr1 (θ ⟨_,_⟩) ⟨m1, m2⟩ ≤ w -> θ ⊨ m1 ≈ m2 [{ w }]. *)
  (* Proof. *)
  (*   enough (m1 = skip ;; m1) as ->. *)
  (*   enough (m2 = skip ;; m2) as ->. *)
  (*   enough (Spr1 (θ ⟨_,_⟩) ⟨skip ;; m1, skip ;; m2⟩ = act (fun=> m1) (fun=> m2) (Spr1 (rmon_unit W ⟨_,_⟩) ⟨tt,tt⟩)) as ->. *)
  (*   apply cont_to_spec. *)
  (*   rewrite /skip ; apply ret_rule2. *)
  (*   move: (rmm_law2 _ _ _ _ θ _ _ (to_prod (fun=> m1) (fun=> m2)) ⟨skip,skip⟩) *)
  (*   => /= ->. *)
  (*   move: (rmm_law1 _ _ _ _ θ ⟨_,_⟩ ⟨tt,tt⟩) => /= -> //. *)
  (*   all:rewrite /bind monad_law1 //. *)
  (* Qed. *)

End GoingPractical.

Ltac apply_seq :=
    refine (gp_seq_rule _ _ _ _ (wf:=extend_to_Jprod _ (fun '⟨a1, a2⟩ => _)) _ _ _).

