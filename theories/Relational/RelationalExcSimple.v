From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Mon.SM Require Import SMMonadExamples.
From Mon.Relational Require Import RelativeMonads RelativeMonadExamples GenericRulesSimple.

Set Primitive Projections.
Set Universe Polymorphism.

Section Exceptions.
  Context (E1 E2 : Type) (Exc1 := Exn E1) (Exc2 := Exn E2).

  Definition RelExc : RelationalSpecMonad0 :=
    ordmonad_to_relspecmon0 (ExnSpec unit).

  Notation "'raiseP' e" := (@opr _ _ _ (Raise e) _) (at level 60).
  Import SPropNotations.

  Import FunctionalExtensionality.
  Program Definition θExc : RelationalEffectObservation0 Exc1 Exc2 RelExc :=
    mkRelMonMorph _ _ _ _
                  (fun A =>
                     ⦑fun m12 =>
                        ⦑fun post pexc =>
                           match m12 return SProp with
                           | ⟨retFree _ a1,retFree _ a2⟩ => post ⟨a1, a2⟩
                           | ⟨raiseP _, _⟩ | ⟨_, raiseP _⟩ => pexc tt
                           end⦒⦒) _ _.
  Next Obligation.
    move: m12 H1=> [[?|[?] ?] [?|[?] ?]] /= ; [apply H|..] ; apply H0.
  Qed.
  Next Obligation. induction H=> //. Qed.
  Next Obligation.
    apply Ssig_eq=> /= ;
    extensionality post ; extensionality pexc.
    move:x => [[?|[?] ?] [?|[?] ?]] //=.
    match goal with [|- match ?d with _ => _ end = _ ] => destruct d as [?|[]]=> // end.
  Qed.

  Program Definition fail_spec {A} : dfst (RelExc A) := ⦑fun _ pexc => pexc tt⦒.
  Next Obligation. intuition. Qed.

  Lemma raise_l_rule e1 {A2} (a2:A2) :
    θExc ⊨ raise e1 ≈ ret a2 [{ fail_spec }].
  Proof. cbv ; intuition. Qed.

  Lemma raise_r_rule e2 {A1} (a1:A1) :
    θExc ⊨ ret a1 ≈ raise e2 [{ fail_spec }].
  Proof. cbv ; intuition. Qed.

  Definition catch {E A} (c : Exn E A) (cerr : E -> Exn E A) : Exn E A :=
    match c with
    | retFree _ a => ret a
    | raiseP e => cerr e
    end.

  Program Definition catch_spec {A} (w werr: dfst (RelExc A)) : dfst (RelExc A):=
    ⦑fun post pexc => Spr1 w post (fun _ => Spr1 werr post pexc) ⦒.
  Next Obligation.
    move:H1. apply (Spr2 w)=> // _ /=. exact (Spr2 werr x y H x0 y0 H0).
  Qed.

  Lemma catch_rule {A1 A2} (c1 : Exc1 A1) cerr1 (c2:Exc2 A2) cerr2 w werr :
    θExc ⊨ c1 ≈ c2 [{ w }] ->
    (forall e1 a2, θExc ⊨ cerr1 e1 ≈ ret a2 [{ werr }]) ->
    (forall a1 e2, θExc ⊨ ret a1 ≈ cerr2 e2 [{ werr }]) ->
    (forall e1 e2, θExc ⊨ cerr1 e1 ≈ cerr2 e2 [{ werr }]) ->
    θExc ⊨ catch c1 cerr1 ≈ catch c2 cerr2 [{ catch_spec w werr }].
  Proof.
    move: c1 c2=> [a1|[e1] ?] [a2|[e2] ?] H0 Hl Hr Hlr //=.
    cbv in H0 |- * ; intuition.
    all:cbv in H0 ; move=> post pexc H ; apply H0 in H.
    cbv in Hr ; move: (Hr a1 e2 post pexc H) ; destruct (cerr2 e2)=> //=.
    cbv in Hl ; move: (Hl e1 a2 post pexc H) ; destruct (cerr1 e1)=> //=.
    cbv in Hlr ; move: (Hlr e1 e2 post pexc H) ; destruct (cerr1 e1) ; destruct (cerr2 e2)=> //=.
  Qed.

  Definition ExcProd A1 A2 := Exn unit (A1 × A2).

  Definition throw {E A} (e:E) : Exn E A :=
    @opr (ExnS E) (@ExnAr _) _ (Raise e) (@False_rect _).

  Inductive exc_rel {A1 A2} : Exc1 A1 -> Exc2 A2 -> ExcProd A1 A2 -> SProp :=
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

End Exceptions.


Section ExcCollapse.
  Context (E1 E2 E : Type) (Exc1 := Exn E1) (Exc2 := Exn E2).

  Definition WExc : RelationalSpecMonad0 :=
    ordmonad_to_relspecmon0 (ExnSpec E).

  Context (θExc : RelationalEffectObservation0 Exc1 Exc2 WExc).
  Context (ϕ1 : (E -> SProp) -> E1 -> SProp)
          (H1 : forall A2 (a2:A2) post e1 pexc,
              Spr1 (Spr1 (θExc ⟨_,_⟩) ⟨raise e1, ret a2⟩) post pexc = ϕ1 pexc e1)
          (ϕ2 : (E -> SProp) -> E2 -> SProp)
          (H2 : forall A1 (a1:A1) post e2 pexc,
              Spr1 (Spr1 (θExc ⟨_,_⟩) ⟨ret a1, raise e2⟩) post pexc = ϕ2 pexc e2).

  Import SPropNotations.
  (*θExc applied to ⟨raise e1, raise e2⟩ does not depend on e1 or e2 *)
  Lemma collapse : forall pexc e1 e2, ϕ1 pexc e1 = ϕ2 pexc e2.
  Proof.
    move=> pexc e1 e2.
    epose (rmm_law2 _ _ _ _ θExc ⟨_,_⟩ ⟨_,_⟩ ⟨fun (x:False) => ret x, fun (x:unit) => raise e2⟩ ⟨raise e1, ret tt⟩) as e.
    apply (f_equal (fun h => Spr1 h (fun=> sUnit) pexc)) in e.
    cbv in e; rewrite H1 in e; rewrite -e ; clear e.

    epose (rmm_law2 _ _ _ _ θExc ⟨_,_⟩ ⟨_,_⟩ ⟨fun=> raise e1,fun (x:False)=> ret x⟩ ⟨ret tt, raise e2⟩) as e.
    apply (f_equal (fun h => Spr1 h (fun=> sUnit) pexc)) in e.
    cbv in e; rewrite H2 in e; rewrite -e ; clear e.
    reflexivity.
  Qed.
End ExcCollapse.
