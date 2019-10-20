From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Rel.

Set Primitive Projections.
Set Universe Polymorphism.


(* In this file we verify the correctness of the bind rule in the full setting *)

Section RelationalProgramLogicFromRelativeMonad.

  (* The context takes all components of a (full) relational specification monad *)

  (* Basic setup for each side: computational monad, unary specification monad
  and an effect observation relating these *)


  Context (M01 M02 : Monad).
  Definition M1 := (monad_to_relmon M01).
  Definition M2 := (monad_to_relmon M02).

  Context (W : RelationalSpecMonad)
          (θ : relationalEffectObservation M1 M2 W).

  Notation W1 := (rsm_left W).
  Notation W2 := (rsm_right W).
  Notation M12 := (compPair M01 M02).
  Notation θ1 := (reo_left θ).
  Notation θ2 := (reo_right θ).
  Notation Wrel := (rsm_rel W).
  Notation W0 := (rsmc_carrier Wrel).
  Notation η := (rsmc_return Wrel).
  Notation actW := (rsmc_act Wrel).


  Notation θrc := (reo_rel θ).
  Notation θW := (@reoc_carrier _ _ _ _ _ _ _ θrc ⟨_,_⟩).

  Import SPropNotations.
  Import RelNotations.

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    ((forall γ1 : πl Γ, (θ1 _)∙1 (c1 γ1) ≤ Spr1 w1 γ1) s/\
    (forall γ2 : πr Γ, (θ2 _)∙1 (c2 γ2) ≤ Spr1 w2 γ2) s/\
    (forall γ : ⟬Γ⟭, θW∙1 ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ Spr1 w (dfst γ)))
      (at level 85).

  Notation "⋅⊫ c1 ≈ c2 [{ w1 , w2 , w }]" :=
    (Hi unit ⊫ (fun=> c1) ≈ (fun=> c2) [{ @OrdCat_cst (discr unit) _ w1,
                                    @OrdCat_cst (discr unit) _ w2,
                                    @OrdCat_cst (discr (unit × unit)) _ w}]).

  Check (fun A B (c1 : M1 A) (c2: M2 B) (w1:dfst (W1 A)) (w2:dfst (W2 B)) (w3:dfst (W0 ⟨A,B⟩)) => ⋅⊫ c1 ≈ c2 [{ w1, w2, w3 }] ).


  Lemma equal_f {A B} (x:A) (f g : forall x:A, B x) : f = g -> f x = g x.
  Proof. move=> ? ; f_equal=> //. Qed.

  Lemma ordCat_helper {A B} (f g : OrdCat⦅A;B⦆) : f ⪷ g -> forall (x y:dfst A), x ≤ y -> f∙1 x ≤ g∙1 y.
  Proof.
    move=> Hfg x y Hxy; estransitivity.
    apply: (f∙2); exact: Hxy.
    apply: Hfg.
  Qed.

  (* And we prove the rule for binding computations *)

  Lemma full_seq_rule {A1 A2 B1 B2}
        {m1 : M1 A1} {m2 : M2 A2} {wm1 wm2 wm}
        {f1 : A1 -> M1 B1} {f2 : A2 -> M2 B2}
        {wf1 : OrdCat⦅discr A1; W1 B1⦆} {wf2:OrdCat⦅discr A2;W2 B2⦆}
        {wf : OrdCat⦅Jprod ⟨A1,A2⟩ ; W0 ⟨B1, B2⟩⦆} :
    ⋅⊫ m1 ≈ m2 [{ wm1, wm2, wm }] ->
    (⦑A1,A2|fun=>fun=>unit|TyRel⦒ ⊫ f1 ≈ f2 [{ wf1, wf2,  wf }]) ->
    ⋅⊫ bind m1 f1 ≈ bind m2 f2 [{ wm1 ≫= wf1,
                                  wm2 ≫= wf2,
                                  (actW wf1 wf2 wf)∙1 wm }].
  Proof.
    intros [[Hm1 Hm2] Hm] [[Hf1 Hf2] Hf].
    split;[split|]=> ?.
    - move: (rmm_law2 _ _ _ _ θ1 _ _ f1)=> /(f_equal (fun f=> f∙1 m1)) /= ->.
      apply: ordCat_helper; last by apply: Hm1.
      apply: (ord_relmon_bind_proper W1); apply: Hf1.
    - move: (rmm_law2 _ _ _ _ θ2 _ _ f2)=> /(f_equal (fun f=> f∙1 m2)) /= ->.
      apply: ordCat_helper; last by apply: Hm2.
      apply: (ord_relmon_bind_proper W2); apply: Hf2.
    - move: (reoc_law2 _ _ _ _ _ θrc (to_prod f1 f2))
        => /(f_equal (fun f=> f∙1 ⟨m1,m2⟩)) /= ->; estransitivity.
      apply: rsmc_act_proper;
        [apply: Hf1| apply: Hf2| move=> [? ?] /=; eapply (Hf ⦑ _ , _ | tt⦒)].
      eapply ((actW _ _ _)∙2)=> //; apply (Hm ⦑tt,tt|I⦒).
  Qed.

    (* move: (rmm_law2 _ _ M12 (W' W) θ _ _ (to_prod f1 f2))=> /= [[H1 H2] H12]. *)
    (* intuition. *)
    (* move: (f_equal (fun h => h m1) H1)=> /= ->. *)
    (* apply omon_bind=> //; apply (Hm1 tt). *)
    (* move: (f_equal (fun h => h m2) H2)=> /= ->. *)
    (* apply omon_bind=> //; apply (Hm2 tt). *)
    (* move: (f_equal (fun h => h ⟨m1, m2⟩) H12) => /= -> //=. *)
    (* estransitivity. *)
    (* simpl in Hf1. *)
    (* apply: rsmc_act_proper. *)
    (* move=> ? ; apply Hf1. *)
    (* move=> ? ; apply Hf2. *)
    (* move=> [? ?] /=; eapply (Hf ⦑ _ , _ | tt⦒). *)
    (* eapply (Spr2 (actW _ _ _))=> //. *)
    (* apply (Hm ⦑tt,tt|I⦒). *)

  (* Program Definition bindWrelStrong *)
  (*       {Γ A1 A2 B1 B2} *)
  (*       (wm1 : OrdCat⦅discr (πl Γ); W1 A1⦆) *)
  (*       (wm2 : OrdCat⦅discr (πr Γ); W2 A2⦆) *)
  (*       (wmrel : OrdCat⦅discr ⟬Γ⟭; Wrel ⟨A1, A2⟩⦆) *)
  (*       (wf1 : OrdCat⦅discr (πl Γ × A1); W1 B1⦆) *)
  (*       (wf2 : OrdCat⦅discr (πr Γ × A2); W2 B2⦆) *)
  (*       (wfrel : OrdCat⦅discr ⟬extends Γ A1 A2⟭; Wrel ⟨B1, B2⟩⦆) *)
  (*   : OrdCat⦅discr ⟬Γ⟭; Wrel ⟨B1, B2⟩⦆ := *)
  (*   ⦑fun γ => (actW (wf1 ∙ ofmap discr (fun a1 => ⟨πl γ, a1⟩)) *)
  (*                (wf2 ∙ ofmap discr (fun a2 => ⟨πr γ, a2⟩)) *)
  (*                (wfrel ∙ ofmap discr (fun a12 => extend_point γ (nfst a12) (nsnd a12))) ∙ wmrel)∙1 γ ⦒. *)
  (* Next Obligation. *)
  (*   cbv=> ? ?; induction 1 ; apply: rsmc_act_proper; sreflexivity. *)
  (* Qed. *)

  Notation " X --> Y " := (X -> dfst Y) (at level 99).

  Program Definition to_discr {X Y} (f : X --> Y) : OrdCat⦅discr X; Y⦆ := ⦑f⦒.
  Next Obligation. move=> ? ?; induction 1; sreflexivity. Qed.

  Definition bindWrelStrong {Γ A1 A2 B1 B2}
          (wm1 : πl Γ --> W1 A1) (wm2 : πr Γ --> W2 A2)
          (wmrel : ⟬Γ⟭ --> Wrel ⟨A1, A2⟩)
          (wf1 : πl Γ × A1 --> W1 B1) (wf2 : πr Γ × A2 --> W2 B2)
          (wfrel : ⟬extends Γ A1 A2⟭ --> Wrel ⟨B1, B2⟩)
  : ⟬Γ⟭ --> Wrel ⟨B1, B2⟩ :=
    fun γ => (actW (to_discr (fun a1 => wf1 ⟨πl γ, a1⟩))
                (to_discr (fun a2 => wf2 ⟨πr γ, a2⟩))
                (to_discr (fun '⟨a1,a2⟩ => wfrel (extend_point γ a1 a2))))∙1 (wmrel γ).

  Definition MW A1 A2 : Rel :=
    mkRel (M1 A1 × dfst (W1 A1)) (M2 A2 × dfst (W2 A2))
          (fun _ _ => dfst (Wrel ⟨A1,A2⟩)).

  Definition progSpec Γ A1 A2 := Γ R==> MW A1 A2.

  Notation prog1 c := (nfst \o πl c).
  Notation spec1 c := (nsnd \o πl c).
  Notation prog2 c := (nfst \o πr c).
  Notation spec2 c := (nsnd \o πr c).
  Notation specrel c := (πw c).
  (* Definition prog1 {Γ A1 A2} (c : progSpec Γ A1 A2) := nfst \o πl c. *)
  (* Definition spec1 {Γ A1 A2} (c : progSpec Γ A1 A2) := nsnd \o πl c. *)
  (* Definition prog2 {Γ A1 A2} (c : progSpec Γ A1 A2) := nfst \o πr c. *)
  (* Definition spec2 {Γ A1 A2} (c : progSpec Γ A1 A2) := nsnd \o πr c. *)
  (* Definition specrel {Γ A1 A2} (c : progSpec Γ A1 A2) := πw c. *)

  Definition mk_progSpec
             (Γ : Rel) A1 A2
             (c1: πl Γ -> M1 A1) (w1: πl Γ --> W1 A1)
             (c2:πr Γ -> M2 A2) (w2:πr Γ --> W2 A2)
             (wrel: ⟬Γ⟭ --> Wrel ⟨A1, A2⟩) : progSpec Γ A1 A2 :=
    mk_point (Γ R=> MW A1 A2)
             (fun γl => ⟨c1 γl, w1 γl⟩)
             (fun γr => ⟨c2 γr, w2 γr⟩)
             (fun γl γr γw => wrel (mk_point Γ γl γr γw)).

  Definition validity {Γ A1 A2} (c : progSpec Γ A1 A2) : Γ R==> TyRel.
  Proof.
    unshelve econstructor.
    split=> γ /=.
    exact (Box ((θ1 _)∙1 (prog1 c γ) ≤  spec1 c γ)).
    exact (Box ((θ2 _)∙1 (prog2 c γ) ≤  spec2 c γ)).
    move=> /= γl γr γw _ _.
    exact (Box (θW∙1 ⟨prog1 c γl, prog2 c γr⟩ ≤ specrel c γl γr γw)).
  Defined.

  Program Definition dArr {Γ} (A : Γ R==> TyRel) : Rel :=
    mkRel (forall γl : πl Γ, πl A γl) (forall γr : πr Γ, πr A γr)
          (fun fl fr => forall γl γr γw, πw A γl γr γw (fl γl) (fr γr)).

  Definition valid Γ {A1 A2} (c : progSpec Γ A1 A2) := ⟬dArr (validity c)⟭.

  Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }] " :=
    (valid Γ (mk_progSpec Γ _ _ c1 w1 c2 w2 w)).


  Definition retWrel {A1 A2} : A1 -> A2 --> Wrel ⟨A1,A2⟩ :=
    fun a1 a2 => (rsmc_return Wrel ⟨A1,A2⟩)∙1 ⟨a1, a2⟩.

  Definition retW {W : unarySpecMonad} {A} : A --> W A := (ord_relmon_unit W A)∙1.

  Ltac destruct_valid :=
    unshelve econstructor; [split=> /= γ|move=> /= γl γr γw]; constructor.

  Lemma ValidRet Γ A1 A2 (a1: _ -> A1) (a2 : _ -> A2) :
    Γ ⊫ ret \o a1 ≈ ret \o a2 [{retW \o a1, retW \o a2, (fun γ => retWrel (a1 (πl γ)) (a2 (πr γ)))}].
  Proof.
    destruct_valid.
    - move: (rmm_law1 _ _ _ _ θ1 A1) => /(f_equal (fun f=> f∙1 (a1 γ))) /= ->.
      sreflexivity.
    - move: (rmm_law1 _ _ _ _ θ2 A2) => /(f_equal (fun f=> f∙1 (a2 γ))) /= ->.
      sreflexivity.
    - move: (@reoc_law1 _ _ _ _ _ _ _ θrc ⟨A1,A2⟩)
      => /(f_equal (fun f=> f∙1 ⟨a1 γl, a2 γr⟩)) /= ->.
      sreflexivity.
  Qed.

  Definition bindWStr {W : unarySpecMonad} {Γ A B}
             (wm: Γ --> W A) (wf : Γ × A --> W B) : Γ --> W B :=
    fun γ => (ord_relmon_bind W (to_discr (fun a => wf⟨γ, a⟩)))∙1 (wm γ).

  Lemma ValidBind
        Γ A1 A2 B1 B2 m1 wm1 m2 wm2 wmrel
        (f1: _ × A1 -> M1 B1) wf1 (f2: _ × A2 -> M2 B2) wf2 wfrel :
    Γ ⊫ m1 ≈ m2 [{ wm1,  wm2, wmrel }] ->
    extends Γ A1 A2 ⊫ f1 ≈ f2 [{wf1, wf2, wfrel}] ->
    Γ ⊫ bindStr m1 f1 ≈ bindStr m2 f2
      [{bindWStr wm1 wf1,
        bindWStr wm2 wf2,
        bindWrelStrong wm1 wm2 wmrel wf1 wf2 wfrel}].
  Proof.
    move=> [[/= Hm1 Hm2] Hm] [[/= Hf1 Hf2] Hf].
    destruct_valid.
    - move: (rmm_law2 _ _ _ _ θ1 _ _ (fun a => f1 ⟨γ,a⟩))
      => /(f_equal (fun f=> f∙1 (m1 γ))) /= ->.
      apply: ordCat_helper; last by apply: (unbox (Hm1 _)).
      apply: (ord_relmon_bind_proper W1)=> ? ; apply: (unbox (Hf1 _)).
    - move: (rmm_law2 _ _ _ _ θ2 _ _ (fun a=> f2 ⟨γ,a⟩))
      => /(f_equal (fun f=> f∙1 (m2 γ))) /= ->.
      apply: ordCat_helper; last by apply: (unbox (Hm2 _)).
      apply: (ord_relmon_bind_proper W2)=> ?; apply: (unbox (Hf2 _)).
    - move: (reoc_law2 _ _ _ _ _ θrc (to_prod (fun a=> f1 ⟨γl,a⟩) (fun a=> f2 ⟨γr,a⟩))) => /=.
      move=> /(f_equal (fun f=> f∙1 ⟨m1 γl,m2 γr⟩)) /= ->; estransitivity;
              last (eapply ((actW _ _ _)∙2)=> //; apply (unbox (Hm _ _ _))).
      apply: rsmc_act_proper;
        [move=> ? ; apply: (unbox (Hf1 _))| move=> ?; apply: (unbox (Hf2 _))|].
      move=> [? ?] /=; apply: (unbox (Hf _ _ _)).
  Qed.

  Notation "x ⩿ y" := (pointwise_srelation _ (@extract_ord _) x y) (at level 70).

  Lemma ValidWeaken
        Γ A1 A2 (m1 : _ -> M1 A1) wm1 wm1'
        (m2: _ -> M2 A2) wm2 wm2' wmrel wmrel':
    Γ ⊫ m1 ≈ m2 [{ wm1, wm2, wmrel}] ->
    wm1 ⩿ wm1' -> wm2 ⩿ wm2' -> wmrel ⩿ wmrel' ->
    Γ ⊫ m1 ≈ m2 [{ wm1', wm2', wmrel'}].
  Proof.
    move=> [[/= H1 H2] H] Hle1 Hle2 Hle; destruct_valid ; estransitivity.
    apply: (unbox (H1 _)). apply: Hle1.
    apply: (unbox (H2 _)). apply: Hle2.
    apply: (unbox (H _ _ _))=>//. apply: Hle.
  Qed.

  Lemma ValidSubst Γ Δ A1 A2 (m1: _ -> M1 A1) wm1
        (m2: _ -> M2 A2) wm2 wmrel (σ: Δ R==> Γ) :
    Γ ⊫ m1 ≈ m2 [{ wm1, wm2, wmrel}] ->
    Δ ⊫ m1 \o πl σ ≈ m2 \o πr σ
      [{ wm1 \o πl σ, wm2 \o πr σ, wmrel \o applyRel _ _ σ}].
  Proof.
    move=> [[/= H1 H2] H]; destruct_valid.
    apply: (unbox (H1 _)).
    apply: (unbox (H2 _)).
    apply: (unbox (H _ _ _)).
  Qed.

  Definition subst_true {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, true⟩.
  Definition rel_subst_true {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ :=
    applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_true subst_true (fun _ _ γ => ⟨γ, erefl⟩)).
  Definition subst_false {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, false⟩.
  Definition rel_subst_false {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ :=
    applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_false subst_false (fun _ _ γ => ⟨γ, erefl⟩)).

  Definition extend_Lo {Γ A} (γ:⟬Γ⟭) (a1 a2 : A) (H : a1 = a2) : ⟬Γ,∙A⟭ :=
    mk_point (Γ,∙A) ⟨πl γ,a1⟩ ⟨πr γ, a2⟩ ⟨πw γ, H⟩.

  Lemma ValidBoolElim Γ A1 A2 (m1: _ -> M1 A1) wm1 (m2: _ -> M2 A2) wm2 wmrel:
    Γ ⊫ m1 \o subst_true ≈ m2 \o subst_true
      [{wm1 \o subst_true, wm2 \o subst_true, wmrel \o rel_subst_true}] ->
    Γ ⊫ m1 \o subst_false ≈ m2 \o subst_false
      [{wm1 \o subst_false, wm2 \o subst_false, wmrel \o rel_subst_false}] ->
    (Γ,∙ bool) ⊫ m1 ≈ m2 [{ wm1, wm2, wmrel}].
  Proof.
    move=> [[/= Ht1 Ht2] Ht] [[/= Hf1 Hf2] Hf]; destruct_valid.
    move: γ => [γ []]; [apply (unbox (Ht1 _))| apply (unbox (Hf1 _))].
    move: γ => [γ []]; [apply (unbox (Ht2 _))| apply (unbox (Hf2 _))].
    move: γl γr γw => [γ1 []] [γ2 b2] /= [γ b] ;
    pattern b2, b;
    match goal with
    | [|- ?g _ _] =>
      refine (match b as Hb in _ = b' return g b' Hb with | erefl => _ end)
    end;
    [apply: (unbox (Ht _ _ _))| apply: (unbox (Hf _ _ _))].
  Qed.


  Definition subst_nil {Γ A} : Γ -> Γ × list A := fun γ => ⟨γ, nil⟩.

  Definition rel_subst_nil {Γ A} : ⟬Γ⟭ -> ⟬Γ ,∙ list A⟭ :=
    fun γ => mk_point (Γ ,∙ list A) (subst_nil (πl γ)) (subst_nil (πr γ))
                  ⟨πw γ, eq_refl⟩.

  Definition subst_cons {Γ A} : Γ × A × list A -> Γ × list A :=
    fun γal => ⟨nfst (nfst γal), cons (nsnd (nfst γal)) (nsnd γal)⟩.

  Program Definition rel_subst_cons {Γ A} : ⟬Γ,∙A,∙list A⟭ -> ⟬Γ ,∙ list A⟭ :=
    fun γ => mk_point (Γ ,∙ list A) (subst_cons (πl γ)) (subst_cons (πr γ))
                  ⟨nfst (nfst (πw γ)), eq_refl⟩.
  Next Obligation. move: γ=> [? [[?]]] /= -> -> //. Defined.

  Definition ctx_subst_extend {A Γ' Γ} (σ: Γ' R==> Γ) : (Γ' ,∙ A) R==> (Γ ,∙ A)
    :=
      mk_point ((Γ' ,∙ A) R=> (Γ ,∙ A)) (fun e => ⟨(πl σ) (nfst e), nsnd e⟩)
               (fun e => ⟨(πr σ) (nfst e), nsnd e⟩) (fun xl xr X => ⟨(πw σ) (nfst xl) (nfst xr) (nfst X), nsnd X⟩).

  Program Definition weaken_subst {Γ A B} : (Γ,∙A,∙B) R==> (Γ,∙B) :=
    mk_point ((Γ,∙A,∙B) R=> (Γ,∙B))
             (fun '⟨⟨γ,_⟩,b⟩ => ⟨γ,b⟩)
             (fun '⟨⟨γ,_⟩,b⟩ => ⟨γ,b⟩)
             (fun _ _ '⟨⟨γ,_⟩,b⟩ => ⟨γ,b⟩).

  Program Definition dArrCtx {Γ} (A B : Γ R==> TyRel) : Rel :=
    mkRel (forall γl : πl Γ, πl A γl -> πl B γl)
          (forall γr : πr Γ, πr A γr -> πr B γr)
          (fun fl fr => forall γl γr γw al ar,
               πw A γl γr γw al ar ->
               πw B γl γr γw (fl γl al) (fr γr ar)).

  Tactic Notation "destruct_valid_pat"
         simple_intropattern(γl)
         simple_intropattern(γr)
         simple_intropattern(γw) :=
    unshelve econstructor; [split=> /= [γl|γr]|move=> /= γl γr γw]; constructor.

  Lemma ValidListElim Γ A A1 A2 (m1: _ -> M1 A1) wm1 (m2: _ -> M2 A2) wm2 wmrel :
    Γ ⊫ m1 \o subst_nil ≈ m2 \o subst_nil
      [{wm1 \o subst_nil, wm2 \o subst_nil, wmrel \o rel_subst_nil}] ->
    ⟬dArrCtx (compRel weaken_subst
                      (validity (mk_progSpec (Γ,∙list A) _ _ m1 wm1 m2 wm2 wmrel)))
             (validity (mk_progSpec (Γ,∙A,∙list A) _ _
                                    (m1 \o subst_cons) (wm1 \o subst_cons)
                                    (m2 \o subst_cons) (wm2 \o subst_cons)
                                    (wmrel \o rel_subst_cons)))⟭ ->
    (Γ,∙ list A) ⊫ m1 ≈ m2 [{ wm1, wm2, wmrel}].
  Proof.
    move=> [[/= Hnil1 Hnil2] Hnil] [[/= Hcons1 Hcons2] Hcons].
    (* destruct_valid_pat [γl ll] [γr lr] [γw lw]. *)
    destruct_valid.
    - move: γ => [?] ; elim.
      + apply: (unbox (Hnil1 _)).
      + move=> ? ? ?; apply: (unbox (Hcons1 ⟨⟨_, _⟩, _⟩ (box _)))=> //.
    - move: γ => [?] ; elim.
      + apply: (unbox (Hnil2 _)).
      + move=> ? ? ?; apply: (unbox (Hcons2 ⟨⟨_, _⟩, _⟩ (box _)))=> //.
    - match goal with
      | [|- ?G ] =>
        enough ((θ1 _ )∙1 (m1 γl) ≤ wm1 γl s/\
                (θ2 _ )∙1 (m2 γr) ≤ wm2 γr s/\ G) as [[]]=> //
      end.
      move: γl γr γw=> [γl ll] [γr lr] [/= γw] ;
                        elim: ll lr=> [|xl xls /(fun f => f xls erefl) [[? ?] ?]];
      match goal with
      | [|- forall lr lw, @?G lr lw ] =>
        refine (fun lr lw => match lw as Heq in _ = l return G l Heq with
                          | erefl => _ end)
      end; split; try split.
      apply: (unbox (Hnil1 _)).
      apply: (unbox (Hnil2 _)).
      apply: (unbox (Hnil _ _ _)).

      apply: (unbox (Hcons1 ⟨⟨_, _⟩, _⟩ (box _)))=> //.
      apply: (unbox (Hcons2 ⟨⟨_, _⟩, _⟩ (box _)))=> //.
      apply: (unbox (Hcons ⟨⟨γl, xl⟩, xls⟩ ⟨⟨γr, xl⟩, xls⟩ ⟨⟨γw, erefl⟩, erefl⟩ (box _) (box _) (box _)))=> //.
  Qed.



  (* Definition valid {Γ A1 A2} (c : progSpec Γ A1 A2) : Rel := *)
  (*   mkRel (Box (forall γ1 : πl Γ, (θ1 _)∙1 (prog1 c γ1) ≤  spec1 c γ1)) *)
  (*         (Box (forall γ2 : πr Γ, (θ2 _)∙1 (prog2 c γ2) ≤ spec2 c γ2)) *)
  (*         (fun _ _ => Box (forall γ : ⟬Γ⟭, θW∙1 ⟨prog1 c (πl γ), prog2 c (πr γ)⟩ ≤ specrel c (πl γ) (πr γ) (πw γ))). *)

  (* Definition valid (Γ : Rel) A1 A2 *)
  (*            (c1: πl Γ -> M1 A1) (w1: πl Γ --> W1 A1) *)
  (*            (c2:πr Γ -> M2 A2) (w2:πr Γ --> W2 A2) *)
  (*            (wrel: ⟬Γ⟭ --> Wrel ⟨A1, A2⟩) : SProp := *)
  (*   ((forall γ1 : πl Γ, (θ1 _)∙1 (c1 γ1) ≤  w1 γ1) s/\ *)
  (*   (forall γ2 : πr Γ, (θ2 _)∙1 (c2 γ2) ≤ w2 γ2) s/\ *)
  (*   (forall γ : ⟬Γ⟭, θW∙1 ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ wrel γ)). *)

  (* Definition retWrel {A1 A2} : A1 -> A2 --> Wrel ⟨A1,A2⟩ := *)
  (*   fun a1 a2 => (rsmc_return Wrel ⟨A1,A2⟩)∙1 ⟨a1, a2⟩. *)

  (* Definition retW {W : unarySpecMonad} {A} : A --> W A := (ord_relmon_unit W A)∙1. *)

  (* Lemma ValidRet Γ A1 A2 a1 a2: *)
  (*   valid Γ A1 A2  (ret \o a1)  (retW \o a1) (ret \o a2) (retW \o a2) *)
  (*         (fun γ => retWrel (a1 (πl γ)) (a2 (πr γ))). *)
  (* Proof. *)
  (*   split;[split|]=> γ. *)
  (*   - move: (rmm_law1 _ _ _ _ θ1 A1) => /(f_equal (fun f=> f∙1 (a1 γ))) /= ->. *)
  (*     sreflexivity. *)
  (*   - move: (rmm_law1 _ _ _ _ θ2 A2) => /(f_equal (fun f=> f∙1 (a2 γ))) /= ->. *)
  (*     sreflexivity. *)
  (*   - move: (@reoc_law1 _ _ _ _ _ _ _ θrc ⟨A1,A2⟩) *)
  (*     => /(f_equal (fun f=> f∙1 ⟨a1 (πl γ), a2 (πr γ)⟩)) /= ->. *)
  (*     sreflexivity. *)
  (* Qed. *)


  (* Definition bindWStr {W : unarySpecMonad} {Γ A B} *)
  (*            (wm: Γ --> W A) (wf : Γ × A --> W B) : Γ --> W B := *)
  (*   fun γ => (ord_relmon_bind W (to_discr (fun a => wf⟨γ, a⟩)))∙1 (wm γ). *)

  (* Lemma ValidBind *)
  (*       Γ A1 A2 B1 B2 m1 wm1 m2 wm2 wmrel f1 wf1 f2 wf2 wfrel : *)
  (*   valid Γ A1 A2 m1 wm1 m2 wm2 wmrel -> *)
  (*   valid (extends Γ A1 A2) B1 B2 f1 wf1 f2 wf2 wfrel -> *)
  (*   valid Γ B1 B2 *)
  (*         (bindStr m1 f1) (bindWStr wm1 wf1) *)
  (*         (bindStr m2 f2) (bindWStr wm2 wf2) *)
  (*         (bindWrelStrong wm1 wm2 wmrel wf1 wf2 wfrel). *)
  (* Proof. *)
  (*   move=> [[Hm1 Hm2] Hm] [[Hf1 Hf2] Hf]. *)
  (*   split; [split|]=> γ. *)
  (*   - move: (rmm_law2 _ _ _ _ θ1 _ _ (fun a => f1 ⟨γ,a⟩)) *)
  (*     => /(f_equal (fun f=> f∙1 (m1 γ))) /= ->. *)
  (*     apply: ordCat_helper; last by apply: Hm1. *)
  (*     apply: (ord_relmon_bind_proper W1)=> ? ; apply: Hf1. *)
  (*   - move: (rmm_law2 _ _ _ _ θ2 _ _ (fun a=> f2 ⟨γ,a⟩)) *)
  (*     => /(f_equal (fun f=> f∙1 (m2 γ))) /= ->. *)
  (*     apply: ordCat_helper; last by apply: Hm2. *)
  (*     apply: (ord_relmon_bind_proper W2)=> ?; apply: Hf2. *)
  (*   - move: (reoc_law2 _ _ _ _ _ θrc (to_prod (fun a=> f1 ⟨πl γ,a⟩) (fun a=> f2 ⟨πr γ,a⟩))) => /=. *)
  (*     move=> /(f_equal (fun f=> f∙1 ⟨m1 (πl γ),m2 (πr γ)⟩)) /= ->; estransitivity; *)
  (*     last (eapply ((actW _ _ _)∙2)=> //; apply (Hm ⦑tt,tt|I⦒)). *)
  (*     apply: rsmc_act_proper; *)
  (*       [move=> ? ; apply: Hf1| move=> ?; apply: Hf2|]. *)
  (*     move=> [? ?] /=; set γ' := extend_point _ _ _; apply: (Hf γ'). *)
  (* Qed. *)

  (* Notation "x ⩿ y" := (pointwise_srelation _ (@extract_ord _) x y) (at level 70). *)

  (* Lemma ValidWeaken *)
  (*            Γ A1 A2 m1 wm1 wm1' m2 wm2 wm2' wmrel wmrel': *)
  (*   valid Γ A1 A2 m1 wm1 m2 wm2 wmrel -> *)
  (*   wm1 ⩿ wm1' -> wm2 ⩿ wm2' -> wmrel ⩿ wmrel' -> *)
  (*   valid Γ A1 A2 m1 wm1' m2 wm2' wmrel'. *)
  (* Proof. *)
  (*   move=> [[H1 H2] H] Hle1 Hle2 Hle; split; [split|] => ?; estransitivity. *)
  (*   apply: H1. apply: Hle1. *)
  (*   apply: H2. apply: Hle2. *)
  (*   apply: H. apply: Hle. *)
  (* Qed. *)

  (* Lemma ValidSubst Γ Δ A1 A2 m1 wm1 m2 wm2 wmrel (σ: Δ R==> Γ) : *)
  (*   valid Γ A1 A2 m1 wm1 m2 wm2 wmrel -> *)
  (*   valid Δ A1 A2 *)
  (*         (m1 \o πl σ) (wm1 \o πl σ) *)
  (*         (m2 \o πr σ) (wm2 \o πr σ) *)
  (*         (wmrel \o applyRel _ _ σ). *)
  (* Proof. *)
  (*   move=> [[H1 H2] H]; split; [split|]=> γ. *)
  (*   apply: H1. *)
  (*   apply: H2. *)
  (*   set γ' := (σ @R γ); exact: (H γ'). *)
  (* Qed. *)

  (* Definition subst_true {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, true⟩. *)
  (* Definition rel_subst_true {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ := *)
  (*   applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_true subst_true (fun _ _ γ => ⟨γ, erefl⟩)). *)
  (* Definition subst_false {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, false⟩. *)
  (* Definition rel_subst_false {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ := *)
  (*   applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_false subst_false (fun _ _ γ => ⟨γ, erefl⟩)). *)

  (* Definition extend_Lo {Γ A} (γ:⟬Γ⟭) (a1 a2 : A) (H : a1 = a2) : ⟬Γ,∙A⟭ := *)
  (*   mk_point (Γ,∙A) ⟨πl γ,a1⟩ ⟨πr γ, a2⟩ ⟨πw γ, H⟩. *)

  (* Lemma ValidBoolElim Γ A1 A2 m1 wm1 m2 wm2 wmrel: *)
  (*   valid Γ A1 A2 (m1 \o subst_true) (wm1 \o subst_true) *)
  (*         (m2 \o subst_true) (wm2 \o subst_true) (wmrel \o rel_subst_true) -> *)
  (*   valid Γ A1 A2 (m1 \o subst_false) (wm1 \o subst_false) *)
  (*         (m2 \o subst_false) (wm2 \o subst_false) (wmrel \o rel_subst_false) -> *)
  (*     valid (Γ ,∙ bool) A1 A2 m1 wm1 m2 wm2 wmrel. *)
  (* Proof. *)
  (*   move=> [[Ht1 Ht2] Ht] [[Hf1 Hf2] Hf]; split; [split|]. *)
  (*   move=> [γ []]; [apply Ht1| apply Hf1]. *)
  (*   move=> [γ []]; [apply Ht2| apply Hf2]. *)
  (*   move=> [[[γ1 []] [γ2 b2]] [γ b]] /= ; *)
  (*   pattern b2, b; *)
  (*   match goal with *)
  (*   | [|- ?g _ _] => *)
  (*     refine (match b as Hb in _ = b' return g b' Hb with | erefl => _ end) *)
  (*   end; *)
  (*   set γ' := mk_point _ γ1 γ2 γ. *)
  (*   exact: (Ht γ'). *)
  (*   exact: (Hf γ'). *)
  (* Qed. *)

  (* Definition subst_nil {Γ A} : Γ -> Γ × list A := fun γ => ⟨γ, nil⟩. *)

  (* Definition rel_subst_nil {Γ A} : ⟬Γ⟭ -> ⟬Γ ,∙ list A⟭ := *)
  (*   fun γ => mk_point (Γ ,∙ list A) (subst_nil (πl γ)) (subst_nil (πr γ)) *)
  (*                 ⟨πw γ, eq_refl⟩. *)

  (* Definition subst_cons {Γ A} : Γ × A × list A -> Γ × list A := *)
  (*   fun γal => ⟨nfst (nfst γal), cons (nsnd (nfst γal)) (nsnd γal)⟩. *)

  (* Program Definition rel_subst_cons {Γ A} : ⟬Γ,∙A,∙list A⟭ -> ⟬Γ ,∙ list A⟭ := *)
  (*   fun γ => mk_point (Γ ,∙ list A) (subst_cons (πl γ)) (subst_cons (πr γ)) *)
  (*                 ⟨nfst (nfst (πw γ)), eq_refl⟩. *)
  (* Next Obligation. move: γ=> [? [[?]]] /= -> -> //. Qed. *)

  (* Definition ctx_subst_extend {A Γ' Γ} (σ: Γ' R==> Γ) : (Γ' ,∙ A) R==> (Γ ,∙ A) *)
  (*   := *)
  (*     mk_point ((Γ' ,∙ A) R=> (Γ ,∙ A)) (fun e => ⟨(πl σ) (nfst e), nsnd e⟩) *)
  (*              (fun e => ⟨(πr σ) (nfst e), nsnd e⟩) (fun xl xr X => ⟨(πw σ) (nfst xl) (nfst xr) (nfst X), nsnd X⟩). *)

  (* Lemma ValidListElim Γ A A1 A2 m1 wm1 m2 wm2 wmrel : *)
  (*   valid Γ A1 A2 *)
  (*         (m1 \o subst_nil) (wm1 \o subst_nil) *)
  (*         (m2 \o subst_nil) (wm2 \o subst_nil) *)
  (*         (wmrel \o rel_subst_nil) -> *)
  (*   (valid (Γ,∙ list A) A1 A2 m1 wm1 m2 wm2 wmrel -> *)
  (*    valid (Γ,∙ A ,∙ list A) A1 A2 *)
  (*          (m1 \o subst_cons) (wm1 \o subst_cons) *)
  (*          (m2 \o subst_cons) (wm2 \o subst_cons) *)
  (*          (wmrel \o rel_subst_cons)) -> *)
  (*   valid (Γ,∙ list A) A1 A2 m1 wm1 m2 wm2 wmrel. *)
  (* Proof. *)
  (*   move=> [[Hnil1 Hnil2] Hnil] Hcons ; split; [split|]. *)


  (* Definition bindStrongRSM {Γ A1 A2 B1 B2} *)
  (*            (wm1 : πl Γ -> W1 A1) *)
  (*            (wm2 : πr Γ -> W2 A2) *)
  (*            (wmrel : ⟬Γ⟭ -> W A1 A2) *)
  (*            (wf1 : πl Γ × A1 -> W1 B1) *)
  (*            (wf2 : πr Γ × A2 -> W2 B2) *)
  (*            (wfrel : ⟬extends Γ A1 A2⟭ -> W B1 B2) *)
  (* : ⟬Γ⟭ -> Wrel B1 B2 *)

  (* Definition to_ordProd (Γ : ) *)
  (*            (c1 : OrdCat⦅πl Γ;M1 A1⦆) *)
  (*            (c2 : OrdCat⦅πr Γ;M2 A2⦆) *)
  (*            OrdCat⦅⟬Γ⟭; Jprod ⟨M1 A1, M2 A2⟩⦆ *)


  (* Notation " Γ ⊫ c1 ≈ c2 [{ w1 , w2 , w }]" := *)
  (*   ((θ1 _ ∙ c1 ⪷ w1) s/\ (θ2 _ ∙ c2 ⪷ w2) s/\ *)
  (*    (orall γ : ⟬Γ⟭, θW∙1 ⟨c1 (πl γ), c2 (πr γ)⟩ ≤ w∙1 (dfst γ))) *)
  (*     (at level 85). *)


End RelationalProgramLogicFromRelativeMonad.
