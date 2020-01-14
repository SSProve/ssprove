From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Lists.List.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Rel GenericRulesComplex.

Set Universe Polymorphism.

Module ExcId.
  Definition M01 := Exn unit.
  Definition M02 := Identity.
  Definition W01 := ExnSpec unit.
  Definition W02 := MonoContSProp.

  Definition M1 := monad_to_relmon M01.
  Definition M2 := monad_to_relmon M02.
  Definition W1 := ordmonad_to_relmon W01.
  Definition W2 := ordmonad_to_relmon W02.

  Import SPropNotations.
  Import RelNotations.

  Program Definition Wrel0 (A : TypeCatSq) : OrdCat :=
    dpair _ (MonoContSProp (option (nfst A) × (nsnd A))) ⦑@omon_rel _ _⦒.
  Next Obligation. apply: MonoCont_order_preorder. Qed.


  Program Definition retWrel0 (A : TypeCatSq) : OrdCat⦅ Jprod A; Wrel0 A⦆ :=
    let f : (typeCat_prod A --> Wrel0 A) :=
        fun a12 => ⦑fun p => p ⟨Some (nfst a12), nsnd a12⟩⦒
    in to_discr f.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition actWrel0 A1 A2 B1 B2 :
    OrdCat ⦅ discr A1; W1 B1 ⦆ ->
    OrdCat ⦅ discr A2; W2 B2 ⦆ ->
    OrdCat ⦅ Jprod ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ ->
    OrdCat ⦅ Wrel0 ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ :=
    fun wf1 wf2 wfrel =>
      ⦑fun wm =>
        ⦑fun p =>
            let k a12 :=
                match nfst a12 with
                | Some a1 => (wfrel∙1 ⟨a1, nsnd a12⟩)∙1 p
                | None => (wf2∙1 (nsnd a12))∙1 (fun b2 => p ⟨None, b2⟩)
                end
            in wm∙1 k⦒⦒.
  Next Obligation.
    move=> ? ? H; apply: wm∙2 => -[[?|] ?] /=;
      by [apply: (wfrel∙1 _)∙2| apply: (wf2∙1 _)∙2].
  Qed.
  Next Obligation. cbv;intuition. Qed.

  Program Definition Wrc : rsm_components W1 W2 :=
    mkRSMComponents _ _ Wrel0 retWrel0 actWrel0 _ _ _ _.
  Next Obligation.
    move=> ? ? H ? ? H1 ? ? H2 w ? /=.
    apply: w∙2=> -[[?|] ?] /=; [apply: H2| apply: H1].
  Qed.
  Next Obligation.
    apply Ssig_eq=> /=.
    extensionality wm. apply Ssig_eq. extensionality p=> /=.
    f_equal. extensionality a; move: a => [[?|] ?] //=.
  Qed.

  Definition Wrel : RelationalSpecMonad := mkRSM W1 W2 Wrc.



  Definition θ01_helper {A} (m : M01 A) (p: A -> SProp) (pexc: unit -> SProp)
    : SProp :=
    match m with
    | retFree _ a => p a
    | opr _ => pexc tt
    end.

  Program Definition θ01 : MonadMorphism M01 W01 :=
    @mkMorphism M01 W01 (fun A m => ⦑θ01_helper m⦒(* ⦑fun p pexc => *)
                                (*    match m with *)
                                (*    | retFree _ a1 => p a1 *)
                                (*    | opr _ => pexc tt *)
                                (*    end⦒ *)) _ _.
  Next Obligation.
    move=> ? ? H ? ? Hexc; move: m=> [?|? ?]; [apply: H| apply: Hexc].
  Qed.
  Next Obligation.
    apply Ssig_eq. extensionality p. extensionality pexc=> /=.
    move: m =>[?|? ?] //=.
  Qed.


  Program Definition θ02 : MonadMorphism M02 W02 :=
    @mkMorphism M02 W02 (fun A m => ret m) _ _.

  Definition θ1 := mmorph_to_rmmorph θ01.
  Definition θ2 := mmorph_to_rmmorph θ02.

  Program Definition θrc : reo_components M1 M2 Wrc θ1 θ2:=
    mkREOComponents M1 M2 Wrc θ1 θ2
                    (fun A =>
                      let f : M1 (nfst A) × M2 (nsnd A) --> Wrc A :=
                          fun m12 => ⦑fun p => match nfst m12 with
                                          | retFree _ a1 => p ⟨Some a1, nsnd m12⟩
                                          | opr _ => p ⟨None, nsnd m12⟩
                                          end⦒
                      in to_discr f) _ _.
  Next Obligation. move: m12 => [[?|? ?] ?] ? ?; apply. Qed.
  Next Obligation.
    apply Ssig_eq; extensionality m12; move: m12 => [[?|??]?] //=.
  Qed.

  Definition θ : relationalEffectObservation M1 M2 Wrel :=
    mkREO _ _ Wrel θ1 θ2 θrc.


  (** FIXME: Copy-paste from GenericRulesComplex *)
  Let valid := valid M01 M02 Wrel θ.
  Let mk_progSpec := mk_progSpec M01 M02 Wrel.

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }] " :=
    (valid Γ _ _ (mk_progSpec Γ _ _ c1 w1 c2 w2 w))
        (at level 85).

  Ltac destruct_valid :=
    unshelve econstructor; [split=> /= γ|move=> /= γl γr γw]; constructor.
  (** FIXME: Copy-paste from GenericRulesComplex *)

  Program Definition raise_spec {Γ} : Γ --> W1 False :=
    fun=>⦑fun p pexc => pexc tt⦒.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition rel_raise_spec {Γ A2} (a2: πr Γ -> A2) : ⟬Γ⟭ --> Wrc ⟨False, A2⟩ :=
    fun γ => ⦑fun p => p ⟨None, a2 (πr γ)⟩⦒.
  Next Obligation. cbv ; intuition. Qed.

  Lemma ValidRaise Γ A2 (a2: _ -> A2) :
    Γ ⊫ fun=> raise tt ≈ ret \o a2 [{raise_spec, retW \o a2, rel_raise_spec a2}].
  Proof. destruct_valid; cbv ; intuition. Qed.


  Definition catchStr {Γ E A} (m : Γ -> Exn E A) (merr : Γ × E -> Exn E A)
    : Γ -> Exn E A := fun γ => catch (m γ) (fun e => merr ⟨γ,e⟩).

  Program Definition catch_spec_str {Γ A1} (w:Γ --> W1 A1)
          (werr : Γ × unit --> W1 A1) : Γ --> W1 A1 :=
    fun γ => ⦑fun p pexc => (w γ)∙1 p (fun u => (werr ⟨γ,u⟩)∙1 p pexc)⦒.
  Next Obligation.
    cbv ; intuition.
    move: H1; apply: (w _)∙2=> // ?; apply (werr _)∙2 => //.
  Qed.

  Program Definition rel_catch_spec_str
          {Γ A1 A2} (wmrel : ⟬Γ⟭ --> Wrc ⟨A1, A2⟩)
          (wmerr_rel : ⟬extends Γ unit A2⟭ --> Wrc ⟨A1, A2⟩)
    : ⟬Γ⟭ --> Wrc ⟨A1, A2⟩ :=
    fun γ =>
      ⦑fun p =>
        let k ae12 :=
            match nfst ae12 with
            | Some a1 => p ⟨Some a1, nsnd ae12⟩
            | None =>
              (wmerr_rel (extend_point γ tt (nsnd ae12)))∙1 p
            end
        in
        (wmrel γ)∙1 k⦒.
  Next Obligation.
    cbv. move=> p1 p2 Hp ; apply: (wmrel _)∙2=> [[[?|] ?]] ; first by apply: Hp.
    apply: (wmerr_rel _)∙2=> ?; apply: Hp.
  Qed.


  Lemma ValidCatch Γ A1 A2 (m1 : _ -> M1 A1) wm1
        (m2: _ -> M2 A2) wm2 wmrel merr wmerr wmerr_rel:
    Γ ⊫ m1 ≈ m2 [{wm1, wm2, wmrel}] ->
    extends Γ unit A2 ⊫ merr ≈ ret \o nsnd [{wmerr, retW \o nsnd, wmerr_rel}] ->
    Γ ⊫ catchStr m1 merr ≈ m2
      [{catch_spec_str wm1 wmerr, wm2, rel_catch_spec_str wmrel wmerr_rel}].
  Proof.
    move=> [[/= H1 H2] H] [[/= He1 He2] He]; destruct_valid.
    - move=> p pexc /=.
      move: (unbox (H1 γ)); unfold θ01_helper, catchStr.
      move: (m1 γ) => [?|[[]]?] /=; first apply.
      set pexc' := (pexc in SProp_op_order _ (_ _ pexc)).
      move=> /(fun f => f p pexc') Htt.
      estransitivity; [apply: (unbox (He1 ⟨γ, tt⟩)) | exact Htt].
    - apply: (unbox (H2 _)).
    - move=> p /=.
      move: (unbox (H γl γr γw)); unfold θ01_helper, catchStr.
      move: (m1 γl) => [?|[[]]?] /=; first apply.
      set p' := (p in SProp_op_order _ (_ p)).
      move=> /(fun f => f p') Htt.
      estransitivity; last exact Htt; apply: (unbox (He _ _ _)).
  Qed.

End ExcId.

Module ExcExc.
  Context (E1 E2 : Type).

  Definition M01 := Exn E1.
  Definition M02 := Exn E2.
  Definition W01 := ExnSpec E1.
  Definition W02 := ExnSpec E2.

  Definition M1 := monad_to_relmon M01.
  Definition M2 := monad_to_relmon M02.
  Definition W1 := ordmonad_to_relmon W01.
  Definition W2 := ordmonad_to_relmon W02.

  Import SPropNotations.
  Import RelNotations.

  Program Definition Wrel0 (A : TypeCatSq) : OrdCat :=
    dpair _ (MonoContSProp ((nfst A + E1) × (nsnd A + E2))) ⦑@omon_rel _ _⦒.
  Next Obligation. apply: MonoCont_order_preorder. Qed.


  Program Definition retWrel0 (A : TypeCatSq) : OrdCat⦅ Jprod A; Wrel0 A⦆ :=
    let f : (typeCat_prod A --> Wrel0 A) :=
        fun a12 => ⦑fun p => p ⟨inl (nfst a12), inl (nsnd a12)⟩⦒
    in to_discr f.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition actWrel0 A1 A2 B1 B2 :
    OrdCat ⦅ discr A1; W1 B1 ⦆ ->
    OrdCat ⦅ discr A2; W2 B2 ⦆ ->
    OrdCat ⦅ Jprod ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ ->
    OrdCat ⦅ Wrel0 ⟨ A1, A2 ⟩; Wrel0 ⟨ B1, B2 ⟩ ⦆ :=
    fun wf1 wf2 wfrel =>
      ⦑fun wm =>
        ⦑fun p =>
            let k a12 :=
                match nfst a12, nsnd a12 with
                | inl a1, inl a2 => (wfrel∙1 ⟨a1, a2⟩)∙1 p
                | inr e1, inl a2 => (wf2∙1 a2)∙1 (fun b2 => p ⟨inr e1, inl b2⟩)
                                             (fun e2 => p ⟨inr e1, inr e2⟩)
                | inl a1, inr e2 => (wf1∙1 a1)∙1 (fun b1 => p ⟨inl b1, inr e2⟩)
                                             (fun e1 => p ⟨inr e1, inr e2⟩)
                | inr e1, inr e2 => p ⟨inr e1, inr e2⟩
                end
            in wm∙1 k⦒⦒.
  Next Obligation.
    move=> ? ? H; apply: wm∙2 => -[[?|?] [?|?]] //=;
      set w := (w in w ∙1); by apply: w∙2.
  Qed.
  Next Obligation. cbv;intuition. Qed.

  Program Definition Wrc : rsm_components W1 W2 :=
    mkRSMComponents _ _ Wrel0 retWrel0 actWrel0 _ _ _ _.
  Next Obligation.
    move=> ? ? H ? ? H1 ? ? H2 w ? /=.
    apply: w∙2=> -[[?|?] [?|?]] //= ; [apply: H2 | apply: H | apply: H1].
  Qed.
  Next Obligation.
    apply Ssig_eq=> /=.
    extensionality wm. apply Ssig_eq. extensionality p=> /=.
    f_equal. extensionality a; move: a => [[?|?] [?|?]] //=.
  Qed.

  Definition Wrel : RelationalSpecMonad := mkRSM W1 W2 Wrc.

End ExcExc.
