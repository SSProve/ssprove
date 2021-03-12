From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Lists.List.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Relational Require Import Category RelativeMonads Rel.


Set Universe Polymorphism.

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

Definition extend_bool_eq
           {Γ A} (b: Γ -> bool)
           (m_true : { γ:Γ ⫳ b γ = true } -> A)
           (m_false: { γ:Γ ⫳ b γ = false } -> A)
           (γ : Γ) : A :=
  (if b γ as b0 return b γ = b0 -> A
   then fun H => m_true (dpair _ γ H)
   else fun H => m_false (dpair _ γ H)) eq_refl.

Lemma trivial_extend_bool_eq {Γ A} (b: Γ -> bool) (a:Γ -> A) :
  a = extend_bool_eq b (fun γ' => a (dfst γ')) (fun γ' => a (dfst γ')).
Proof.
  extensionality γ; rewrite /extend_bool_eq /=; case: (b _)=> //.
Qed.

Definition dep_extend (Γ : Rel) (b : Γ R==> TyRel) : Rel :=
  mkRel {γl : πl Γ ⫳ πl b γl}
        {γr : πr Γ ⫳ πr b γr}
        (fun γbl γbr =>
           { γw : Γ (dfst γbl) (dfst γbr)
           ⫳ πw b (dfst γbl) (dfst γbr) γw (dsnd γbl) (dsnd γbr)  } ).


Definition rel_is_bool (b0 : bool) {Γ} (b : Γ R==> Lo bool) : Γ R==> TyRel :=
  mk_point (Γ R=> TyRel) (fun γl => πl b γl = b0) (fun γr => πr b γr = b0)
           (fun γl γr γw b_eql b_eqr => unit).

Let rel_is_true {Γ} := @rel_is_bool true Γ.
Let rel_is_false {Γ} := @rel_is_bool false Γ.

Definition rel_extend_bool_eq
           {Γ A} (b: Γ R==> Lo bool)
           (m_true : ⟬dep_extend Γ (rel_is_true b)⟭ -> A)
           (m_false: ⟬dep_extend Γ (rel_is_false b)⟭ -> A)
           (γ : ⟬Γ⟭) : A :=
  let bs := b @R γ in
  (if πr bs as b0 return πr bs = b0 -> A
   then fun H => m_true
                (mk_point (dep_extend Γ (rel_is_true b))
                          (dpair _ (πl γ) (eq_trans (πw bs) H))
                          (dpair _ (πr γ) H)
                          (dpair _ (πw γ) tt))
                (* (dpair _ γ (mk_point (rel_is_true b @R γ) (eq_trans (πw bs) H) H tt)) *)
   else fun H => m_false
                (mk_point (dep_extend Γ (rel_is_false b))
                          (dpair _ (πl γ) (eq_trans (πw bs) H))
                          (dpair _ (πr γ) H)
                          (dpair _ (πw γ) tt))
                (* (dpair _ γ (mk_point (rel_is_false b @R γ) (eq_trans (πw bs)) H) H tt) *)
  ) eq_refl.

Definition dep_extend_proj1 {Γ} {R : Γ R==> TyRel} : ⟬dep_extend Γ R⟭ -> ⟬Γ⟭ :=
  fun γ' => mk_point Γ (dfst (πl γ')) (dfst (πr γ')) (dfst (πw γ')).

Lemma trivial_rel_extend_bool_eq {Γ A} (b: Γ R==> Lo bool) (a: ⟬Γ⟭ -> A):
  a = rel_extend_bool_eq b (a \o dep_extend_proj1) (a \o dep_extend_proj1).
Proof.
  extensionality γ ; cbv; case: (nsnd _)=> //.
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
Next Obligation. move: γ=> [? [[?]]] /= -> -> //. Qed.
Definition ctx_subst_extend {A Γ' Γ} (σ: Γ' R==> Γ) : (Γ' ,∙ A) R==> (Γ ,∙ A) :=
  mk_point ((Γ' ,∙ A) R=> (Γ ,∙ A)) (fun e => ⟨(πl σ) (nfst e), nsnd e⟩)
           (fun e => ⟨(πr σ) (nfst e), nsnd e⟩) (fun xl xr X => ⟨(πw σ) (nfst xl) (nfst xr) (nfst X), nsnd X⟩).

Axiom valid : forall (Γ : Rel) A1 A2, (πl Γ -> M1 A1) -> (πl Γ -> W1 A1) -> (πr Γ -> M2 A2) -> (πr Γ -> W2 A2) -> (⟬Γ⟭ -> Wrel A1 A2) -> Type.

Axiom ValidRet : forall Γ A1 A2 a1 a2,
    valid Γ A1 A2  (ret \o a1)  (ret \o a1) (ret \o a2) (ret \o a2) (fun γ => retWrel (a1 (πl γ)) (a2 (πr γ))).

Axiom ValidBind :
    forall Γ A1 A2 B1 B2 m1 wm1 m2 wm2 wmrel f1 wf1 f2 wf2 wfrel,
    valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
    valid (extends Γ A1 A2) B1 B2 f1 wf1 f2 wf2 wfrel ->
    valid Γ B1 B2
          (bindStr m1 f1) (bindStr wm1 wf1)
          (bindStr m2 f2) (bindStr wm2 wf2)
          (bindWrelStrong wm1 wm2 wmrel wf1 wf2 wfrel).

Axiom ValidWeaken :
    forall Γ A1 A2 m1 wm1 wm1' m2 wm2 wm2' wmrel wmrel',
      valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
      wm1 ⩿ wm1' -> wm2 ⩿ wm2' -> wmrel ⩿ wmrel' ->
      valid Γ A1 A2 m1 wm1' m2 wm2' wmrel'.

Axiom ValidRaise :
    forall Γ A2 a2,
      valid Γ False A2 (fun=> raise tt) (fun=> raise_spec) (fun=> ret a2) (fun=> ret a2)
            (fun=> rel_raise_spec a2).

Axiom ValidCatch :
    forall Γ A1 A2 m1 wm1 m2 wm2 wmrel merr wmerr wmerr_rel,
      valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
      valid (extends Γ unit A2) A1 A2 merr wmerr (fun γa2 => ret (nsnd γa2)) (fun γa2 => ret (nsnd γa2)) wmerr_rel ->
      valid Γ A1 A2
            (catchStr m1 merr) (catch_spec_str wm1 wmerr)
            m2 wm2
            (rel_catch_spec_str wmrel wmerr).

Axiom ValidListElim :
  forall Γ A A1 A2 m1 wm1 m2 wm2 wmrel,
      valid Γ A1 A2
            (m1 \o subst_nil) (wm1 \o subst_nil)
            (m2 \o subst_nil) (wm2 \o subst_nil)
            (wmrel \o rel_subst_nil) ->
      (valid (Γ,∙ list A) A1 A2 m1 wm1 m2 wm2 wmrel ->
       valid (Γ,∙ A ,∙ list A) A1 A2
             (m1 \o subst_cons) (wm1 \o subst_cons)
             (m2 \o subst_cons) (wm2 \o subst_cons)
             (wmrel \o rel_subst_cons)) ->
      valid (Γ,∙ list A) A1 A2 m1 wm1 m2 wm2 wmrel.

Axiom ValidSubst : forall Γ Δ A1 A2 m1 wm1 m2 wm2 wmrel (σ: Δ R==> Γ),
    valid Γ A1 A2 m1 wm1 m2 wm2 wmrel ->
    valid Δ A1 A2
          (m1 \o πl σ) (wm1 \o πl σ)
          (m2 \o πr σ) (wm2 \o πr σ)
          (wmrel \o applyRel _ _ σ).

Definition subst_true {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, true⟩.
Definition rel_subst_true {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ :=
  applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_true subst_true (fun _ _ γ => ⟨γ, erefl⟩)).
Definition subst_false {Γ} : Γ -> Γ × bool := fun γ => ⟨γ, false⟩.
Definition rel_subst_false {Γ} : ⟬Γ⟭ -> ⟬Γ,∙bool ⟭ :=
  applyRel _ _ (mk_point (Γ R=> (Γ,∙bool)) subst_false subst_false (fun _ _ γ => ⟨γ, erefl⟩)).

Axiom ValidBoolElim :
  forall Γ A1 A2 m1 wm1 m2 wm2 wmrel,
    valid Γ A1 A2 (m1 \o subst_true) (wm1 \o subst_true)
          (m2 \o subst_true) (wm2 \o subst_true) (wmrel \o rel_subst_true) ->
    valid Γ A1 A2 (m1 \o subst_false) (wm1 \o subst_false)
          (m2 \o subst_false) (wm2 \o subst_false) (wmrel \o rel_subst_false) ->
    valid (Γ ,∙ bool) A1 A2 m1 wm1 m2 wm2 wmrel.

Definition ifp {Γ A} (b : Γ -> bool) (mtrue mfalse : Γ -> A) : Γ -> A :=
  fun γ => if b γ then mtrue γ else mfalse γ.
Definition rel_ifp {Γ A} (b : Γ R==> Lo bool) (mtrue mfalse : ⟬Γ⟭ -> A) : ⟬Γ⟭ -> A :=
  fun γ => if πl (b @R γ) then mtrue γ else mfalse γ.

Definition extend_proj1' {Γ A} : ⟬Γ,∙A⟭ -> ⟬Γ⟭ :=
  applyRel _ _ (mk_point ((Γ,∙A) R=> Γ) nfst nfst (fun _ _ => nfst)).

Definition extend_proj2 {Γ A} : (Γ,∙A) R==> Lo A :=
  mk_point ((Γ,∙A) R=> Lo A) nsnd nsnd (fun _ _ => nsnd).
Definition extend_proj2' {Γ A} : ⟬Γ,∙A⟭ -> ⟬Lo A⟭ :=
  applyRel _ _ extend_proj2.

Lemma valid_bool_elim_extended :
    forall Γ (b : Γ R==> Lo bool) A1 A2
      m1_true wm1_true m2_true wm2_true wmrel_true
      m1_false wm1_false m2_false wm2_false wmrel_false ,
    valid Γ A1 A2 m1_true wm1_true m2_true wm2_true wmrel_true ->
    valid  Γ A1 A2 m1_false wm1_false m2_false wm2_false wmrel_false ->
    valid Γ A1 A2
          (ifp (πl b) m1_true m1_false)
          (ifp (πl b) wm1_true wm1_false)
          (ifp (πr b) m2_true m2_false)
          (ifp (πr b) wm2_true wm2_false)
          (rel_ifp b wmrel_true wmrel_false).
Proof.
  move=> Γ b A1 A2 m1_true wm1_true m2_true wm2_true wmrel_true
      m1_false wm1_false m2_false wm2_false wmrel_false vtrue vfalse.
  set s := mk_point (Γ R=> (Γ,∙bool)) (fun γ => ⟨γ, πl b γ⟩) (fun γ => ⟨γ, πr b γ⟩)
                    (fun xr xl γ => ⟨γ, πw b xr xl γ⟩).
  rewrite {1 2}/ifp.
  change (fun _ => if ?t _ then ?t1 _ else ?t2 _ ) with
      (ifp nsnd (t1 \o nfst) (t2 \o nfst) \o πl s).
  rewrite {3 4}/ifp.
  change (fun _ => if ?t _ then ?t1 _ else ?t2 _ ) with
      (ifp nsnd (t1 \o nfst) (t2 \o nfst) \o πr s).
  change (rel_ifp _ _ _) with
      ((rel_ifp extend_proj2 (wmrel_true \o extend_proj1') (wmrel_false \o extend_proj1')) \o applyRel _ _ s).
  apply (ValidSubst (Γ,∙bool) Γ _ _ _ _ _ _ _ s) .
  apply ValidBoolElim.
  apply vtrue.
  apply vfalse.
Qed.


Lemma trivial_ifp {Γ A} (b: Γ -> bool) (a:Γ -> A) : a = ifp b a a.
Proof. extensionality γ; rewrite /ifp /=; case: (b _)=> //. Qed.

Lemma trivial_rel_ifp {Γ A} (b: Γ R==> Lo bool) (a:⟬Γ⟭ -> A) : a = rel_ifp b a a.
Proof. extensionality γ; cbv. case: (πl b _)=> //. Qed.

Ltac intro_catchStr t x :=
  match t with
  | fun H => catch (@?t1 H) (@?t2 H) =>
    change x with (catchStr t1 (fun H => t2 (nfst H) (nsnd H)))
  end.

Ltac intro_bindStr t x :=
  match t with
  | fun H => bind (@?t1 H) (@?t2 H) =>
    change x with (bindStr t1 (fun H => t2 (nfst H) (nsnd H)))
  end.

Lemma bindStr_law {M: Monad} {A} {Γ} (m : Γ -> M A) : m = bindStr m (fun γ => ret (nsnd γ)).
Proof.
  rewrite /bindStr /bind /ret.
  extensionality γ.
  rewrite monad_law2 => //.
Qed.

Program Definition raise_general_spec {A1} : W1 A1 := ⦑ fun p perr => perr tt ⦒.
Next Obligation.
  cbv; intuition.
Qed.

Program Definition rel_raise_general_spec {A1 A2} (a2 : A2) : Wrel A1 A2 := ⦑ fun p => p ⟨None, a2⟩ ⦒.
Next Obligation.
  cbv; intuition.
Qed.

Lemma valid_raise_anytype : forall Γ A1 A2 a1 a2,
    valid Γ A1 A2 (fun => bind (raise tt) (fun => ret a1)) (fun => raise_general_spec)
          (fun=> ret a2) (fun => ret a2) (fun => rel_raise_general_spec a2).
Proof.
  intros.
  set t := fun => _;
                 intro_bindStr ltac:(eval unfold t in t) t;
                 clear t.
  set w := ret a2.
  change w with (bind w id).
  set y := fun => bind w id.
  intro_bindStr ltac:(eval unfold y in y) y.
  eapply ValidWeaken.
  - apply ValidBind.
    + apply ValidRaise.
    + apply ValidRet.
  - cbv; intuition.
  - cbv; intuition.
  - cbv; intuition.
Qed.

Program Definition null_wp1 {A} : W1 A :=
  ⦑fun (p : A -> SProp) pexc => (forall a, p a) /\ pexc tt⦒.
Next Obligation. cbv ; intuition. Qed.

Program Definition null_wp2 {A} : W2 A :=
  ⦑fun (p : A -> SProp) => forall a, p a⦒.
Next Obligation. cbv ; intuition. Qed.

Program Definition rel_invariant : Wrel unit bool :=
  ⦑fun post => post ⟨None, true⟩ /\ post ⟨Some tt, false⟩⦒.
Next Obligation. cbv; intuition. Qed.

Section ExcPure.
  Notation "m1 ;; m2" := (bind m1 (fun=> m2)) (at level 65).
  Arguments ret: simpl never.
  Arguments raise: simpl never.
  Arguments bind: simpl never.
  Context {A:Type}.
  Definition Γ := EmptyCtx ,∙ (A -> bool) ,∙ (list A).
  Definition Γ' := EmptyCtx ,∙ (A -> bool) ,∙ A,∙ (list A).

  Definition prog1 {A} (l : list A) (pred : A -> bool) : M1 bool :=
    let fix aux (l : list A) : M1 unit (* (fun p pexc => (exists x \in l,
                                          pred x => pexc tt) /\ ((forall x \in l, ~~ pred x) => p tt)) *) :=
        match l with
        | nil => ret tt
        | x :: l => if pred x then (raise tt ;; ret tt) else aux l
        end
    in catch (aux l ;; ret false) (fun => ret true).

  Definition prog2 {A} (l : list A) (pred : A -> bool) : M2 bool :=
    let fix aux (l : list A) : M2 bool :=
        match l with
        | nil => ret false
        | x :: l => if pred x then ret true else aux l
        end
    in aux l.

  Definition prog1' {A} (lp : unit × (A -> bool) × list A) :=
    prog1 (nsnd lp) (nsnd (nfst lp)).

  Definition prog2' {A} (lp : unit × (A -> bool) × list A) :=
    prog2 (nsnd lp) (nsnd (nfst lp)).

  Program Definition prog1_spec : W1 bool :=
    ⦑ fun p _ => forall b, p b ⦒.
  Next Obligation.
    cbv; intuition.
  Qed.

  Program Definition prog2_spec : W2 bool :=
    ⦑ fun p => forall b, p b ⦒.
  Next Obligation.
    cbv; intuition.
  Qed.

  Program Definition prog1_prog2_spec : Wrel bool bool :=
    ⦑ fun p => forall b, p ⟨some b, b⟩ ⦒.
  Next Obligation.
    cbv; intuition.
  Qed.

  Definition b : πl Γ' -> bool :=
    fun h => nsnd (nfst (nfst h)) (nsnd (nfst h)).
  Lemma br : (Γ' R=> Lo bool) b b.
  Proof.
    move => [[[[]]]] ? ? ? [[[[]]]] ? ? ? /= [[[[]]]] -> -> -> //.
  Qed.
  Definition bb : Γ' R==> Lo bool := mk_point (Γ' R=> Lo bool) b b br.

  Lemma prog1_prog2_equiv :
    valid Γ bool bool prog1' (fun => prog1_spec)
          prog2' (fun => prog2_spec) (fun => prog1_prog2_spec).
  Proof with (try (cbv ; intuition)).
    apply: ValidWeaken.
    intro_catchStr ltac:(eval unfold prog1', prog1 in (@prog1' A)) (@prog1' A).
    apply: ValidCatch; last by apply ValidRet.
    {
      rewrite (bindStr_law prog2').
      set t := fun => _; intro_bindStr ltac:(eval unfold t in t) t; clear t.
      apply: ValidBind; last by apply ValidRet.
      refine (ValidListElim (EmptyCtx,∙A -> bool) _ _ _
                            _ (fun=> null_wp1)
                            _ (fun=> null_wp2)
                            (fun=> rel_invariant) _ _).
      all: rewrite /prog2' /prog2 /comp.
      * apply: ValidWeaken; first by apply: ValidRet...
      * move=> IH /= ;
                rewrite (trivial_ifp b (fun=> null_wp1))
                        (trivial_ifp b (fun=> null_wp2))
                        (trivial_rel_ifp bb (fun=> rel_invariant)).
        apply: (valid_bool_elim_extended _ bb).
        apply: ValidWeaken; first by apply valid_raise_anytype...

        have @σ : Γ' R==> Γ by
            simple refine (mk_point (Γ' R=> Γ) _ _ _);
          [move=> [[γ _] l] ; refine ⟨γ,l⟩ |
           move=> [[γ _] l] ; refine ⟨γ,l⟩ |
           move=> /= ? ? [[γ _] l]; refine ⟨γ,l⟩].
        simpl in σ.
        apply (ValidSubst _ _ _ _ _ _ _ _ _ σ) in IH.
        apply: ValidWeaken; first by apply IH...
    }
    all:cbv; intuition.
  Qed.
End ExcPure.
