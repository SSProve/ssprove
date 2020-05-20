From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple.

Set Primitive Projections.
Set Universe Polymorphism.

Section Erreptions.
  Context (E1 E2 : Type) (Err1 := Exn E1) (Err2 := Exn E2).

  Definition RelErr : RelationalSpecMonad0 :=
    ordmonad_to_relspecmon0 (ExnSpec unit).

  Notation "'raiseP' e" := (@opr _ _ _ (Raise e) _) (at level 60).
  Import SPropNotations.

  Import FunctionalExtensionality.
  Program Definition θErr : RelationalEffectObservation0 Err1 Err2 RelErr :=
    mkRelMonMorph _ _ _ _
                  (fun A =>
                     ⦑fun m12 =>
                        ⦑fun post pexc =>
                           match m12 return Prop with
                           | ⟨retFree _ a1,retFree _ a2⟩ => post ⟨a1, a2⟩
                           | ⟨raiseP _, _⟩ | ⟨_, raiseP _⟩ => pexc tt
                           end⦒⦒) _ _.
  Next Obligation.
    move=> ? ? H ? ? H'; move: m12=> [[?|[?] ?] [?|[?] ?]] /= ; [apply H|..] ; apply H'.
  Qed.
  Next Obligation. induction 1 ; sreflexivity. Qed.
  Next Obligation.
    apply sig_eq=> /= ; extensionality x; apply sig_eq => /=.
    extensionality post ; extensionality pexc.
    move:x => [[?|[?] ?] [?|[?] ?]] //=.
    match goal with [|- match ?d with _ => _ end = _ ] => destruct d as [?|[]]=> // end.
  Qed.

  Program Definition fail_spec {A} : dfst (RelErr A) := ⦑fun _ pexc => pexc tt⦒.
  Next Obligation. cbv; intuition. Qed.

  Lemma raise_l_rule e1 {A2} (a2:A2) :
    θErr ⊨ raise e1 ≈ ret a2 [{ fail_spec }].
  Proof. cbv ; intuition. Qed.

  Lemma raise_r_rule e2 {A1} (a1:A1) :
    θErr ⊨ ret a1 ≈ raise e2 [{ fail_spec }].
  Proof. cbv ; intuition. Qed.

  Definition catch {E A} (c : Exn E A) (cerr : E -> Exn E A) : Exn E A :=
    match c with
    | retFree _ a => ret a
    | raiseP e => cerr e
    end.

  Program Definition catch_spec {A} (w werr: dfst (RelErr A)) : dfst (RelErr A):=
    ⦑fun post pexc => proj1_sig w post (fun _ => proj1_sig werr post pexc) ⦒.
  Next Obligation.
    move=> ? ? ? ? ? ?; apply: w∙2=> //; move=> ? ; apply: werr∙2 => //.
  Qed.

  Lemma catch_rule {A1 A2} (c1 : Err1 A1) cerr1 (c2:Err2 A2) cerr2 w werr :
    θErr ⊨ c1 ≈ c2 [{ w }] ->
    (forall e1 a2, θErr ⊨ cerr1 e1 ≈ ret a2 [{ werr }]) ->
    (forall a1 e2, θErr ⊨ ret a1 ≈ cerr2 e2 [{ werr }]) ->
    (forall e1 e2, θErr ⊨ cerr1 e1 ≈ cerr2 e2 [{ werr }]) ->
    θErr ⊨ catch c1 cerr1 ≈ catch c2 cerr2 [{ catch_spec w werr }].
  Proof.
    move: c1 c2=> [a1|[e1] ?] [a2|[e2] ?] H0 Hl Hr Hlr //=.
    cbv in H0 |- *; intuition; apply: H0; eassumption.
    all:cbv in H0 ; move=> post pexc H ; apply H0 in H.
    cbv in Hr ; move: (Hr a1 e2 post pexc H) ; destruct (cerr2 e2)=> //=.
    cbv in Hl ; move: (Hl e1 a2 post pexc H) ; destruct (cerr1 e1)=> //=.
    cbv in Hlr ; move: (Hlr e1 e2 post pexc H) ; destruct (cerr1 e1) ; destruct (cerr2 e2)=> //=.
  Qed.

  Definition ErrProd A1 A2 := Exn unit (A1 × A2).

  Definition throw {E A} (e:E) : Exn E A :=
    @opr (ExnS E) (@ExnAr _) _ (Raise e) (@False_rect _).

  Inductive exc_rel {A1 A2} : Err1 A1 -> Err2 A2 -> ErrProd A1 A2 -> Prop :=
  | erRet : forall a1 a2, exc_rel (ret a1) (ret a2) (ret ⟨a1,a2⟩)
  | erRaiseLeft : forall e1 c2, exc_rel (throw e1) c2 (throw tt)
  | erRaiseRight : forall c1 e2, exc_rel c1 (throw e2) (throw tt)
  | erCatch : forall c1 c2 cerr1 cerr2 c cerr,
      exc_rel c1 c2 c ->
      (forall e1 e2, exc_rel (cerr1 e1) (cerr2 e2) (cerr tt)) ->
      (forall e1 a2, exc_rel (cerr1 e1) (ret a2) (cerr tt)) ->
      (forall a1 e2, exc_rel (ret a1) (cerr2 e2) (cerr tt)) ->
      exc_rel (catch c1 cerr1) (catch c2 cerr2) (catch c cerr).
  (* The product of catch is a bit crazy : it requires the
  exceptional branch of the product program to be at the
  same time the product of 3 different pair of programs...
  In order to do anything usable, the product should probably have access to
  some more memory cells than the individual programs so that it can
  track the exceptional status of each "projections"... but that looks a bit
  like a hack to get what you would have in the full setting.
  *)

End Erreptions.


Section ErrCollapse.
  Context (E1 E2 E : Type) (Err1 := Exn E1) (Err2 := Exn E2).

  Definition WErr : RelationalSpecMonad0 :=
    ordmonad_to_relspecmon0 (ExnSpec E).

  Context (θErr : RelationalEffectObservation0 Err1 Err2 WErr).
  Context (ϕ1 : (E -> Prop) -> E1 -> Prop)
          (H1 : forall A2 (a2:A2) post e1 pexc,
              proj1_sig (proj1_sig (θErr ⟨_,_⟩) ⟨raise e1, ret a2⟩) post pexc = ϕ1 pexc e1)
          (ϕ2 : (E -> Prop) -> E2 -> Prop)
          (H2 : forall A1 (a1:A1) post e2 pexc,
              proj1_sig (proj1_sig (θErr ⟨_,_⟩) ⟨ret a1, raise e2⟩) post pexc = ϕ2 pexc e2).

  Import SPropNotations.
  (*θErr applied to ⟨raise e1, raise e2⟩ does not depend on e1 or e2 *)
  Lemma collapse : forall pexc e1 e2, ϕ1 pexc e1 = ϕ2 pexc e2.
  Proof.
    move=> pexc e1 e2.
    epose (rmm_law2 _ _ _ _ θErr ⟨_,_⟩ ⟨_,_⟩ ⟨fun (x:False) => ret x, fun (x:unit) => raise e2⟩) as e.
    apply (f_equal (fun h => h∙1 ⟨raise e1, ret tt⟩)) in e.
    apply (f_equal (fun h => proj1_sig h (fun=> True) pexc)) in e.
    cbv in e; rewrite H1 in e; rewrite -e ; clear e.

    epose (rmm_law2 _ _ _ _ θErr ⟨_,_⟩ ⟨_,_⟩ ⟨fun=> raise e1,fun (x:False)=> ret x⟩ ) as e.
    apply (f_equal (fun h => h∙1 ⟨ret tt, raise e2⟩)) in e.
    apply (f_equal (fun h => proj1_sig h (fun=> True) pexc)) in e.
    cbv in e; rewrite H2 in e; rewrite -e ; clear e.
    reflexivity.
  Qed.
End ErrCollapse.

