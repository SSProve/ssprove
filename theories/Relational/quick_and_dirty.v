From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Relational Require Import Category RelativeMonads (* RelativeMonadExamples *) Rel.



Definition M1 := Exn unit.
Definition M2 := Identity.
Definition W1 := ExnSpec unit.
Definition W2 := MonoContSProp.

Definition Wrel A1 A2 := MonoContSProp (option A1 × A2).

Import SPropNotations.

Program Definition retWrel {A1 A2} a1 a2 : Wrel A1 A2 :=
  ⦑fun p => p ⟨Some a1, a2⟩⦒.
Next Obligation. cbv ; intuition. Qed.

Program Definition bindWrel
        {A1 A2 B1 B2}
        (wm1 : W1 A1) (wm2 : W2 A2) (wmrel : Wrel A1 A2)
        (wf1 : A1 -> W1 B1) (wf2 : A2 -> W2 B2) (wfrel : A1 × A2 -> Wrel B1 B2)
  : Wrel B1 B2
  :=
    ⦑fun p => wmrel∙1 (fun a12 => match nfst a12 with
                          | Some a1 => (wfrel ⟨a1, nsnd a12⟩)∙1 p
                          | None => (wf2 (nsnd a12))∙1 (fun b2 => p ⟨None, b2⟩)
                               end)⦒.
Next Obligation.
  cbv; move=> p1 p2 Hp; apply wmrel∙2=> [[[?|] ?]];
    [apply: (wfrel _)∙2| apply: (wf2 _)∙2]; move=> ? ; apply: Hp.
Qed.

Import RelNotations.

Definition extends (Γ : Rel) (A1 A2 : Type) : Rel :=
 mkRel (πl Γ × A1) (πr Γ × A2) (fun γa1 γa2 => Γ (nfst γa1) (nfst γa2)).

Check (fun Γ (γ : ⟬Γ⟭) => πl γ) .

Definition extend_point {Γ A1 A2} (γ : ⟬Γ⟭) (a1:A1) (a2:A2) : ⟬extends Γ A1 A2⟭.
Proof. exists ⟨⟨πl γ, a1⟩, ⟨πr γ, a2⟩⟩. exact: πw γ. Defined.

Program Definition bindWrelStrong
        {Γ A1 A2 B1 B2}
        (wm1 : πl Γ -> W1 A1) (wm2 : πr Γ -> W2 A2) (wmrel : ⟬Γ⟭ -> Wrel A1 A2)
        (wf1 : πl Γ × A1 -> W1 B1) (wf2 : πr Γ × A2 -> W2 B2)
        (wfrel : ⟬extends Γ A1 A2⟭ -> Wrel B1 B2)
  : ⟬Γ⟭ -> Wrel B1 B2
  :=
    fun γ =>
      ⦑fun p =>
         let k a12 :=
             match nfst a12 with
             | Some a1 => (wfrel (extend_point γ a1 (nsnd a12)))∙1 p
             | None => (wf2 ⟨πr γ, nsnd a12⟩)∙1 (fun b2 => p ⟨None, b2⟩)
             end
         in (wmrel γ)∙1 k⦒.
Next Obligation.
  cbv; move=> p1 p2 Hp; apply: (wmrel _)∙2=> [[[?|] ?]];
    [apply: (wfrel _)∙2| apply: (wf2 _)∙2]; move=> ? ; apply: Hp.
Qed.

Section StrongBind.
  Context {M:Monad}.
  Context {Γ A B} (m : Γ -> M A) (f : Γ × A -> M B).

  Definition bindStr (γ : Γ) : M B :=
    bind (m γ) (fun a => f ⟨γ,a⟩).
End StrongBind.


Notation "x ⩿ y" := (pointwise_srelation _ (@omon_rel _ _) x y) (at level 70).

Program Definition raise_spec : W1 False :=
  ⦑fun p pexc => pexc tt⦒.
Next Obligation. cbv ; intuition. Qed.

Program Definition rel_raise_spec {A2} (a2:A2) : Wrel False A2 :=
  ⦑fun p => p ⟨None, a2⟩⦒.
Next Obligation. cbv ; intuition. Qed.


Definition catchStr {Γ E A} (m : Γ -> Exn E A) (merr : Γ × E -> Exn E A)
  : Γ -> Exn E A := fun γ => catch (m γ) (fun e => merr ⟨γ,e⟩).

Program Definition catch_spec {A1} (w:W1 A1) (werr : unit -> W1 A1) : W1 A1 :=
  ⦑fun p pexc => w∙1 p (fun u => (werr u)∙1 p pexc)⦒.
Next Obligation.
  cbv ; intuition.
  move: H1; apply: w∙2=> // ?; apply (werr _)∙2 => //.
Qed.


Program Definition catch_spec_str {Γ A1} (w:Γ -> W1 A1) (werr : Γ × unit -> W1 A1)
  : Γ -> W1 A1 :=
  fun γ => ⦑fun p pexc => (w γ)∙1 p (fun u => (werr ⟨γ,u⟩)∙1 p pexc)⦒.
Next Obligation.
  cbv ; intuition.
  move: H1; apply: (w _)∙2=> // ?; apply (werr _)∙2 => //.
Qed.

Program Definition rel_catch_spec {A1 A2} (wmrel : Wrel A1 A2)
           (wmerr : unit -> W1 A1) (* (wmerr_rel : unit -> Wrel A1 A2) *)
  : Wrel A1 A2 :=
  ⦑fun p => wmrel∙1 (fun ae12 => match nfst ae12 with
                           | Some a1 => p ⟨Some a1, nsnd ae12⟩
                           | None => (wmerr tt)∙1 (fun a1 => p ⟨Some a1, nsnd ae12⟩)
                                              (fun u => p ⟨None, nsnd ae12⟩)
                           end)⦒.

Next Obligation.
  cbv. move=> p1 p2 Hp ; apply: (wmrel)∙2=> [[[?|] ?]] ; first by apply: Hp.
  apply: (wmerr _)∙2=> ?; apply: Hp.
Qed.


Program Definition rel_catch_spec_str
        {Γ A1 A2} (wmrel : ⟬Γ⟭ -> Wrel A1 A2)
           (wmerr : πl Γ × unit -> W1 A1) (* (wmerr_rel : unit -> Wrel A1 A2) *)
  : ⟬Γ⟭ -> Wrel A1 A2 :=
  fun γ =>
    ⦑fun p => (wmrel γ)∙1 (fun ae12 => match nfst ae12 with
                             | Some a1 => p ⟨Some a1, nsnd ae12⟩
                             | None => (wmerr ⟨πl γ, tt⟩)∙1 (fun a1 => p ⟨Some a1, nsnd ae12⟩)
                                                (fun u => p ⟨None, nsnd ae12⟩)
                             end)⦒.

Next Obligation.
  cbv. move=> p1 p2 Hp ; apply: (wmrel _)∙2=> [[[?|] ?]] ; first by apply: Hp.
  apply: (wmerr _)∙2=> ?; apply: Hp.
Qed.


Inductive valid :
  forall (Γ : Rel) A1 A2,
    (πl Γ -> M1 A1) -> (πl Γ -> W1 A1) ->
    (πr Γ -> M2 A2) -> (πr Γ -> W2 A2) ->
    (⟬Γ⟭ -> Wrel A1 A2) -> Type :=

| ValidRet : forall Γ A1 A2 a1 a2,
    valid Γ A1 A2 (fun=>ret a1) (fun=>ret a1) (fun=>ret a2) (fun=>ret a2) (fun=>retWrel a1 a2)

| ValidBind :
    forall Γ A1 A2 B1 B2 m1 wm1 m2 wm2 wmrel f1 wf1 f2 wf2 wfrel,
    valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
    valid (extends Γ A1 A2) B1 B2 f1 wf1 f2 wf2 wfrel ->
    valid Γ B1 B2
          (bindStr m1 f1) (bindStr wm1 wf1)
          (bindStr m2 f2) (bindStr wm2 wf2)
          (bindWrelStrong wm1 wm2 wmrel wf1 wf2 wfrel)
| ValidWeaken :
    forall Γ A1 A2 m1 wm1 wm1' m2 wm2 wm2' wmrel wmrel',
      valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
      wm1 ⩿ wm1' -> wm2 ⩿ wm2' -> wmrel ⩿ wmrel' ->
      valid Γ A1 A2 m1 wm1' m2 wm2' wmrel'

| ValidRaise :
    forall Γ A2 a2,
      valid Γ False A2 (fun=> raise tt) (fun=> raise_spec) (fun=> ret a2) (fun=> ret a2)
            (fun=> rel_raise_spec a2)
| ValidCatch :
    forall Γ A1 A2 m1 wm1 m2 wm2 wmrel merr wmerr wmerr_rel,
      valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
      valid (extends Γ unit A2) A1 A2 merr wmerr (fun γa2 => ret (nsnd γa2)) (fun γa2 => ret (nsnd γa2)) wmerr_rel ->
      valid Γ A1 A2
            (catchStr m1 merr) (catch_spec_str wm1 wmerr)
            m2 wm2
            (rel_catch_spec_str wmrel wmerr).
