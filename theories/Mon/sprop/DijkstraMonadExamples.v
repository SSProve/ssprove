From Coq Require Import ssreflect ssrfun ssrbool.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Monoid SpecificationMonads MonadExamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.


(****************************************************************************)
(* Ordered monad algebras yield morphisms into the monotone continuations   *)
(* monad. This gives a general way of generating many effect observations,  *)
(* as described at the end of Section 4.1                                   *)
(****************************************************************************)
Section Algebra.

  Context (M:Monad) (alg:OrderedAlgebra M).

  Existing Instance oalg_order.
  Definition WPSpecMonad := @MonoCont _ (@oalg_rel _ alg) _.

  Program Definition mor_underlying X (m:M X) : WPSpecMonad X :=
    Sexists _ (fun post => alg (bind m (fun x => ret (post x)))) _.
  Next Obligation.
    move=> ? ? H. apply oalg_mono ; assumption.
  Qed.

  Import FunctionalExtensionality.
  Program Definition mor : MonadMorphism M WPSpecMonad :=
    @mkMorphism _ _ mor_underlying _ _.
  Next Obligation.
    apply Ssig_eq; extensionality post; cbv ; rewrite monad_law1 malg_ret //.
  Qed.
  Next Obligation.
    apply Ssig_eq ; extensionality post; cbv; rewrite monad_law3 malg_bind //.
  Defined.

  Definition D_wp := @Dθ _ _ mor.

  Definition underlying {A spec} : D_wp A spec -> M A := Spr1.

End Algebra.


Section UpdateMonadEffectObservation.
  Context (M:monoid) (X : monoid_action M).
  Let UpdX := Upd X.
  Let WUpdX := UpdSpec X.

  Program Definition UpdEffObs : MonadMorphism UpdX WUpdX :=
    @mkMorphism _ _ (fun A m => Sexists _ (fun p x => let mx := m x in p (nfst mx) (nsnd mx)) _) _ _.
  Next Obligation.
    move=> ? ? H ? ; apply H.
  Qed.

End UpdateMonadEffectObservation.


Section Option.
  Program Definition Opt : Monad :=
    @mkMonad option (@Some) (fun _ _ m f => Option.bind f m) _ _ _.
  (* TODO : report this error of Solve Obligations *)
  (* Solve Obligations with move: c => [?|] //=. *)
  Next Obligation. move: c => [?|] //=. Qed.
  Next Obligation. move: c => [?|] //=. Qed.

  Program Definition TotAlg : OrderedAlgebra Opt :=
    let alg := @mkMonadAlgebra Opt SProp
                               (fun c => match c with
                                      | Some p => p
                                      | None => sEmpty end) _ _ in
    @mkOrderedAlgebra _ alg SProp_op_order _ _.
  Next Obligation. move: m => [?|] //=. Qed.
  Next Obligation. typeclasses eauto. Qed.
  Next Obligation. move=> ? ? ? [?|] //= ; intuition. Qed.

  Definition morWpTot := mor TotAlg.

  Program Definition PartAlg : OrderedAlgebra Opt :=
    let alg := @mkMonadAlgebra Opt SProp
                               (fun c => match c with
                                      | Some p => p
                                      | None => sUnit end) _ _ in
    @mkOrderedAlgebra _ alg SProp_op_order _ _.
  Next Obligation. move: m => [?|] //=. Qed.
  Next Obligation. typeclasses eauto. Qed.
  Next Obligation. move=> ? ? ? [?|] //= ; intuition. Qed.

  Definition morWpPart := mor PartAlg.

  Import StrongestPostcondition.
  Let SP := ForwardPredTransformer.


  Import FunctionalExtensionality.
  Import SPropNotations.

  Section TotalSPNotExactlyMorphism.
    Program Definition θSP A (m : Opt A) : SP A :=
      match m with
      | Some a => ret a
      | None => Sexists _ (fun pre a => @mkOver _ pre _) _
      end.

    Lemma θSP_ret A (a:A) : θSP (ret a) = ret a.
    Proof. reflexivity. Qed.

    Lemma θSP_bind A B (m:Opt A) (f : A -> Opt B) :
      bind (θSP m) (fun b => θSP (f b)) ≤ θSP (bind m f).
    Proof.
      move: m => [a|] //=.
      change SP_bind with (@monad_bind SP).
      change SP_ret with (@monad_ret SP).
      erewrite monad_law1.
      move:(f a) => [?|] //=.

      move=> pre b /= [a H] ; exact (over H).
    Qed.

  End TotalSPNotExactlyMorphism.



  Program Definition morSpPart : MonadMorphism Opt SP :=
    @mkMorphism Opt SP (fun A c => match c with
                             | Some a => ret a
                             | None => Sexists _ (fun pre a => @mkOver _ sEmpty _) _
                             end) _ _.
  Next Obligation. destruct H. Qed.
  Next Obligation.
    move: m => [a|] //=.
    change SP_bind with (@monad_bind SP).
    change SP_ret with (@monad_ret SP).
    erewrite monad_law1.
    move:(f a) => [?|] //=.
    apply Ssig_eq=> //=.
    extensionality pre ; extensionality y.
    apply SPropOver_eq.
    split.
    move=> H ; destruct H.
    move=> [? H] ; move: (over H) => H0 ; destruct H0.
  Qed.

  Lemma part_pairing A m : wpsp_pairing (morWpPart A m) (morSpPart A m).
  Proof.
    cbv ; destruct m as [?|]; split ; try intuition ; subst_sEq ; intuition.
  Qed.


  Program Definition ranTotDiv A B (f : B -> Opt A)  w
    (H : morWpTot A (bind (None : Opt B) f) ≤ w) :
    ran w (morWpTot B None) :=
    Sexists _ (fun _ => Sexists _ (fun _ => sEmpty) _) _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; split. cbv in H. assumption. intuition. Qed.

End Option.


Section FreeMonadEffectObservation.

  Context (S : Type) (P: S -> Type).
  Context (W : OrderedMonad).
  Context (OpContSpecs : forall s, W (P s)).

  Let Free := Free P.

  Fixpoint OpSpec_mor A (m : Free A) : W A :=
    match m with
    | retFree _ a => ret a
    | @opr _ _ _ s k => bind (OpContSpecs s) (fun ps => OpSpec_mor (k ps))
    end.

  Import FunctionalExtensionality.
  Program Definition OpSpecEffObs : MonadMorphism Free W :=
    @mkMorphism _ _ OpSpec_mor _ _.
  Next Obligation.
    elim m=> [?|? ? IH] //=.
    rewrite /bind /ret monad_law1 //.
    rewrite /bind monad_law3 ; f_equal. extensionality ps ; apply IH.
  Qed.

  Definition OpSpecWP : Dijkstra W := Dθ OpSpecEffObs.

  Program Definition cont_perform : forall s, OpSpecWP (P s) (@OpContSpecs s) :=
    fun s => Sexists _ (@opr _ _ _ s (@retFree _ _ _)) _.
  Next Obligation.
    cbv ; rewrite monad_law2 ; sreflexivity.
  Qed.

  Inductive ObsFree A : W A -> Type :=
  | OFRet : forall a w, ret a ≤ w -> ObsFree w
  | OFOp : forall s w w',
      bind (OpContSpecs s) w' ≤ w ->
      (forall x : P s, OpSpecWP A (w' x)) ->
      ObsFree w.

  Definition observeθ A w (m:OpSpecWP A w) : ObsFree w.
  Proof.
    destruct m as [[|] H].
    exact (OFRet H).
    apply (OFOp H)=> a. exists (f a). sreflexivity.
  Defined.

  Context (OpPartialRan : forall s C (w : W C) w0,
              bind (OpContSpecs s) w0 ≤ w -> ran w (OpContSpecs s)).
  Definition observeRan A w (m:OpSpecWP A w) : ObsFree w.
  Proof.
    destruct m as [[|] H] ; simpl in H.
    exact (OFRet H).
    pose (OpPartialRan H) as H'.
    destruct H' as [w0 H'].
    simple refine (OFOp _ _).
    exact s. exact w0. destruct H' ; assumption.
    move=> a. exists (f a). destruct H' as [H1 H2].
    apply (H2 (fun a => OpSpecEffObs A (f a))). assumption.
  Defined.

End FreeMonadEffectObservation.


Section FreeDijkstraMonads.
  Context (S : Type) (P: S -> Type).
  Context (W : OrderedMonad).
  Context (OpSpecs : forall s, W (P s)).
  Context (OpPartialRan : forall s C (w : W C) w0,
              bind (OpSpecs s) w0 ≤ w -> ran w (OpSpecs s)).

  Inductive FreeD (A:Type) : W A -> Type :=
  | FDRet : forall (a:A) (w:W A), ret a ≤ w -> FreeD w
  | FDop : forall s w (w':ran w (OpSpecs s)),
      (forall x:P s, FreeD (Spr1 w' x)) -> FreeD w.

  Definition fd_dret A (a:A) : FreeD (ret a) :=
    @FDRet _ a (ret a) ltac:(sreflexivity).

  Definition fd_weaken A {w1 w2} (m : @FreeD A w1) (Hw : w1 ≤ w2)
    : FreeD w2.
  Proof.
    revert w2 Hw ; induction m=> w2 Hw.
    simple refine (@FDRet _ a _ _). estransitivity ; eassumption.
    simple refine (@FDop _ s _ _ (fun x => _)).
    apply (OpPartialRan (w0:=Spr1 w')).
    destruct w' as [? [? ?]] ; estransitivity ; eassumption.
    simpl.
    apply (X x).
    apply ran_mono. assumption. sreflexivity.
  Defined.

  Definition fd_bind A B wm wf (m:@FreeD A wm) (f:forall a, @FreeD B (wf a))
    : FreeD (bind wm wf).
  Proof.
    revert wf f; induction m => wf0 f0.
    apply (fd_weaken (f0 a)). rewrite -monad_law1;
                               apply omon_bind; [assumption| sreflexivity].
    simple refine (@FDop _ s  _ _ (fun x => _)).
    apply (OpPartialRan (w0:=fun x => bind (Spr1 w' x) wf0)).
    rewrite /bind -monad_law3.
    apply omon_bind ; [|sreflexivity].
    destruct w' as [? [? ?]] ; assumption.


    simpl.
    apply (fd_weaken (X x wf0 f0)).
    match goal with
    | [|- _≤ Spr1 ?X _] => destruct X as [w'' [H1 H2]]
    end ; simpl in *.
    apply (H2 (fun x => bind (Spr1 w' x) wf0)).
    rewrite /bind -monad_law3. apply omon_bind ; [|sreflexivity].
    destruct w' as [? [? ?]] ; assumption.
  Defined.

  (* So far, so good, we have a carrier type with return,
     bind and weaken operations defined *)
  (* The problems arise when trying to prove anything by induction
     because right kan extension need not to be equal on the nose *)
  (* Assuming that the preorder on W is actually an order should
     be enough to go forward but that looks quite annoying to prove... *)

  (* Import FunctionalExtensionality. *)
  (* Import SPropNotations. *)
  (* Notation "w1 ≃ w2" := (w1 ≤ w2 s/\ w2 ≤ w1) (at level 65). *)
  (* Context (Wantisym : forall A (w1 w2 : W A), w1 ≃ w2 -> w1 = w2). *)
  (* Lemma kleisli_antisym A B (w1 w2 : A -> W B) : (forall a, w1 a ≃ w2 a) -> w1 = w2.  *)
  (* Proof. *)
  (*   move=> H ; extensionality a ; apply Wantisym ; apply H. *)
  (* Qed. *)

  (* Lemma fd_weaken_refl A w1 (m:@FreeD A w1) (H : w1 ≤ w1) : *)
  (*   fd_weaken m H = m. *)
  (* Proof. *)
  (*   induction m=> //=. *)
  (*   Set Printing Implicit. *)
  (*   match goal with *)
  (*   | [|- FDop ?f1 = FDop ?f2] => enough (f1 = f2) as -> ; [reflexivity|] *)
  (*   end. *)

End FreeDijkstraMonads.

Section SumOfTheories.
  Context (S1 S2 : Type) (P1: S1 -> Type) (P2: S2 -> Type).
  Context (W : OrderedMonad).
  Context (OpSpecs1 : forall s, W (P1 s)) (OpSpecs2 : forall s, W (P2 s)).

  Definition sumS : Type := S1 + S2.
  Definition sumP (s:sumS) : Type :=
    match s with
    | inl s1 => P1 s1
    | inr s2 => P2 s2
    end.
  Definition sumOpSpecs (s:sumS) : W (sumP s) :=
    match s with
    | inl s1 => OpSpecs1 s1
    | inr s2 => OpSpecs2 s2
    end.
End SumOfTheories.

(****************************************************************************)
(* We use the approach of McBride'15, Turing completeness totally free,     *)
(* in order to extend a Dijkstra monad on a free monad with an operation    *)
(* corresponding to a recursive call. Then we provide a fix operation       *)
(* (some kind of handler) to recover a function in the original Dijkstra    *)
(* monad.                                                                   *)
(****************************************************************************)

From Equations Require Import Equations.
From Mon.sprop Require Import WellFounded.

Derive NoConfusion for FreeF.
Derive Subterm for FreeF.

Section GeneralRecursion.
  Context (S : Type) (P: S -> Type).

  Context (W : OrderedMonad).

  Context (OpSpecs : forall s, W (P s))
          (Hran_s : forall s C (w : W C) w0, bind (OpSpecs s) w0 ≤ w ->
                                        ran w (OpSpecs s)).

  Context `{forall A, aa (@omon_rel W A)}.

  Context (DBase : Dijkstra W)
          (perform_s : forall s, DBase (P s) (OpSpecs s))
          (intro_assume:forall A (pre:SProp) (w:W A),
              (pre -> DBase A w) -> DBase A (assume_p pre w)).

  Context (Dom:Type) (prec : Dom -> Dom -> Prop) `{WellFounded _ prec}
          (Hsquash_prec : forall d1 d2, Squash (prec d1 d2) -> prec d1 d2).
  Context (Cod : Dom -> Type) (inv : forall d:Dom, W (Cod d)).

  Definition inv' d0 d := assume_p (Squash (prec d d0)) (inv d).

  Context (Hran_inv : forall d0 d C (w : W C) w0,
              bind (inv' d0 d) w0 ≤ w ->
              ran w (inv' d0 d)).

  Import SPropNotations.

  Definition GenRecExtS : Type := sumS S Dom.
  Definition GenRecExtP (s:GenRecExtS) : Type := sumP P Cod s.
  Definition GenRecExtSpecs (d0:Dom) (s:GenRecExtS) : W (GenRecExtP s) :=
    sumOpSpecs OpSpecs (fun d => assume_p (Squash (prec d d0)) (inv d)) s.

  Definition GenRecExt d0 := OpSpecWP (GenRecExtSpecs d0).

  Section GenRecTelescopes.
    Import Telescopes.
    Definition GenRecTele :=
      ext Dom (fun d => ext Type (fun C => ext (W C) (fun w => tip (GenRecExt d C w)))).

    Let T C := (FreeF GenRecExtP C).
    Definition GenRec_to_FreeF : tele_fn GenRecTele {C : Type & T C}.
    Proof. intros ? C ? [m] ; exists C ; exact m. Defined.
    Definition GenRec_measure :=
      tele_measure GenRecTele {C : Type & T C} GenRec_to_FreeF
                   (lexdepprod Type T (empty_rel Type)
                               (@FreeF_subterm _ GenRecExtP)).
    Definition to_tele C w d c : GenRecTele :=
      sigmaI _ d (sigmaI _ C (sigmaI _ w c)).

  End GenRecTelescopes.


  Import FunctionalExtensionality.

  Context (f : forall (d:Dom), GenRecExt d (Cod d) (inv d)).
  Equations(noind) eval {C w d} (c : GenRecExt d C w) : DBase C w
    by wf (d, to_tele c)
          (Subterm.lexprod Dom _ prec GenRec_measure)
    :=
    eval (Sexists _ (retFree _ z) _) := wkn (dm_ret DBase z) _ ;
    eval (Sexists _ (@opr _ _ _ (inl s) k) w) :=
      wkn (dm_bind (perform_s s)
                    (fun ps => @eval _ (Spr1 (Hran_s w) ps) d (Sexists _ (k ps) _))) _ ;


    eval (Sexists _ (@opr _ _ _ (inr d') k) w) :=
      let m (pre : Squash (prec d' d)) := @eval _ _ d' (f d') in
      wkn (dm_bind (intro_assume m) (fun ps => @eval C (Spr1 (Hran_inv w) ps) d (Sexists _ (k ps) _))) _.
  Next Obligation.
    match goal with
    | [|- context [Spr1 ?T]] =>
      let H0 := fresh "H" in
      move: (Spr2 T) => /= [_ H0] ; apply (H0 _ w ps)
    end.
  Qed.
  Next Obligation.
    do 2 right. do 2 constructor.
  Qed.
  Next Obligation.
    match goal with
    | [|- context [Spr1 ?T]] =>
      let H0 := fresh "H" in
      move: (Spr2 T) => /= [H0 _] ; apply H0
    end.
  Qed.
  Next Obligation.
    match goal with
    | [|- context [Spr1 ?T]] =>
      let H0 := fresh "H" in
      move: (Spr2 T) => /= [_ H0] ; apply (H0 _ w ps)
    end.
  Qed.
  Next Obligation.
    do 2 right. do 2 constructor.
  Qed.
  Next Obligation.
    match goal with
    | [|- context [Spr1 ?T]] =>
      let H0 := fresh "H" in
      move: (Spr2 T) => /= [H0 _] ; apply H0
    end.
  Qed.

  Next Obligation.
    unfold eval.
    rewrite Subterm.FixWf_unfold_ext.
    destruct c as [[?|[?|?]] ?] ; try reflexivity.
  Defined.

  Definition ffix (d:Dom) : DBase (Cod d) (inv d) := eval (f d).

  Definition call {d0} d : GenRecExt d0 (Cod d) (inv' d0 d) :=
    cont_perform (GenRecExtSpecs d0) (inr d).

End GeneralRecursion.

Section NatLtSProp.

  Inductive leS : nat -> nat -> SProp :=
  | leSZ : forall n, leS 0 n
  | leSS : forall n m, leS n m -> leS (S n) (S m).

  Lemma leS_diag : forall n, leS n n.
  Proof. elim=> [|] ; constructor. assumption. Qed.

  Lemma leS_to_le : forall m n, leS n m -> le n m.
  Proof.
    induction m. move=> [|n H] //=.
    assert (HF:sEmpty) by inversion H ; inversion HF.
    move=> [?|n H]. exact (PeanoNat.Nat.le_0_l _).
    apply Le.le_n_S ; apply IHm. inversion H ; assumption.
  Qed.

  Goal forall (p:SProp), Squash (Box p) -> p.
  Proof. move=> p [[H]] ; exact H. Qed.

  Lemma sq_le_to_leS : forall m n, Squash (le n m) -> leS n m.
  Proof.
    elim=> [|m IHm] [|n IHn].
    move=> ? ; constructor.
    destruct IHn as [H] ; inversion H.
    move=> ? ; constructor.
    destruct IHn as [H] ; inversion H.
    apply leS_diag.
    constructor. apply IHm.
    constructor. apply Le.le_Sn_le ; assumption.
  Qed.

End NatLtSProp.

Section EmptySignature.

  Definition EmptyS : Type := False.
  Definition EmptyP : EmptyS -> Type := False_rect Type.
  Definition EmptyOpSpecs (W: OrderedMonad) (s : EmptyS) : W (EmptyP s) :=
    match s with end.
  Definition EmptyRan (W:OrderedMonad) (s:EmptyS) :
    forall (C : Type) (w : W C), ran w (EmptyOpSpecs W s) :=
    match s with end.
  Definition EmptyRan' (W:OrderedMonad) (s:EmptyS) :
    forall (C : Type) (w : W C) w0,
      bind (EmptyOpSpecs W s) w0 ≤ w -> ran w (EmptyOpSpecs W s) :=
    match s with end.

End EmptySignature.

(****************************************************************************)
(* Dijkstra monad for Pure computations                                     *)
(****************************************************************************)

(* TODO : there seems to be something funny to encode non-decidable partial maps
   from A to B using A -> { p : SProp & p -> B }
   This looks a bit like a Dijkstra monad, or maybe a graded monad (since the precondition
   does not look like a spec monad but rather a monoid)
 *)

Section Pure.
  Let W := MonoContSProp.
  Import SPropNotations.
  Import FunctionalExtensionality.

  Definition Pure_car A (w:W A) : Type :=
    { f : forall p, Spr1 w p -> { a : A ≫ p a }
    ≫ forall p p' (H : Pred_op_order p' p) Hwp Hwp',
          Squash (Spr1 (f p Hwp) = Spr1 (f p' Hwp')) }.

  Program Definition Pure_ret A (a:A) : Pure_car (ret a) :=
    ⦑fun p Hpre => Sexists _ a Hpre⦒.
  Next Obligation. constructor ; reflexivity. Qed.

  Import EqNotations.
  Lemma sprop_app_irr
    : forall {p:SProp} {Z : Type} (f : p -> Z) (x1 x2 : p), f x1 = f x2.
  Proof. reflexivity. Defined.

  Program Definition Pure_bind A B wm wf (m:@Pure_car A wm)
          (f: forall a, @Pure_car B (wf a)) : @Pure_car B (bind wm wf) :=
    ⦑fun p Hpre =>
      let m0 := Spr1 m _ Hpre in
      Spr1 (f (Spr1 m0)) p (Spr2 m0)⦒.
  Next Obligation.
    unshelve epose (Hm := Spr2 m _ _ _ Hwp Hwp').
    cbv ; intuition.
    destruct Hm as [Hm].
    unshelve epose (Hf := Spr2 (f (Spr1 (Spr1 m (fun a : A => Spr1 (wf a) p) Hwp))) p p' H _ _).
    exact (Spr2 (Spr1 m (fun a : A => Spr1 (wf a) p) Hwp)).
    unshelve eapply (Spr2 (wf _) _ _).
    exact p.
    exact H.
    exact (Spr2 (Spr1 m (fun a : A => Spr1 (wf a) p) Hwp)).
    destruct Hf as [Hf].
    constructor.
    rewrite Hf.
    assert (forall a a' p Hp Hp' (Ha:a = a'), Spr1 (f a) p Hp = Spr1 (f a') p Hp').
    intros.
    refine (match Ha as H0 in _ = a0 return
                  forall (H:a' = a0),
                    Spr1 (f a) p0 Hp = Spr1 (f a0) p0 (eq_sind (fun a => Spr1 (wf a) p0) Hp' H)
            with
            | eq_refl => _
            end eq_refl).
    intros. apply sprop_app_irr.

    erewrite (H0 _ _ p' _ _ Hm).
    reflexivity.
  Qed.

  Program Definition Pure_wkn A w w' (m:@Pure_car A w) (Hww':w ≤ w')
    : @Pure_car A w'
    := ⦑fun p Hpre => Spr1 m p (Hww' p Hpre)⦒.
  Next Obligation. apply (Spr2 m)=> //. Qed.

  Lemma sprop_app_irr'
    : forall {p:SProp} {Z : Type} (f : p -> Z) (x1 x2 : p), f x1 ≡ f x2.
  Proof. reflexivity. Defined.

  Import SPropAxioms.

  Program Definition Pure : Dijkstra W :=
    {| dm_tyop := Pure_car
    ; dm_ret := Pure_ret
    ; dm_bind := Pure_bind
    ; dm_wkn := Pure_wkn
    |}.
  Next Obligation. hnf ; reflexivity. Qed.
  Next Obligation. hnf ; reflexivity. Qed.
  Next Obligation. hnf ; reflexivity. Qed.
  Next Obligation.
    cbv.
    apply Monoid.Ssig_sEq.
    simpl ;  funext p ; funext_s Hpre.
    assert (forall a a' p Hp Hp' (Ha:a ≡ a'), Spr1 (f a) p Hp ≡ Spr1 (f a') p Hp').
    intros.
    refine (match Ha as H0 in _ ≡ a0 return
                  forall (H:a' ≡ a0),
                    Spr1 (f a) p0 Hp ≡ Spr1 (f a0) p0 (sEq_sind _ _ (fun a _ => Spr1 (wf a) p0) Hp' _ H)
            with
            | sEq_refl _ => _
            end (sEq_refl _)).
    intros. apply sprop_app_irr'.
    apply H.
    epose (Spr2 m (fun a : A => Spr1 (wf' a) p) _ _ _ _).
    destruct s as [s].
    rewrite s.
    reflexivity.
    Unshelve.
    cbv in Hf |- *; move=> ? ; apply Hf.
    cbv in Hm |- * ; apply Hm=> //.
  Qed.

  Program Definition pure_intro_assume A (pre:SProp) w (f : pre -> Pure A w)
    : Pure A (assume_p pre w) :=
    ⦑fun p Hpre => Spr1 (f _) p _⦒.
  Next Obligation. destruct Hpre ; assumption. Qed.
  Next Obligation. destruct Hpre ; assumption. Qed.
  Next Obligation. apply (Spr2 (f _))=> //. Qed.
End Pure.

(****************************************************************************)
(* We implement the fibonnacci function on top of Pure using General Recursion *)
(****************************************************************************)

Section Fibonnacci.
  Let W := MonoContSProp.
  Definition fib_trivial_inv : W nat := PrePostSpec sUnit (fun _ => sUnit).
  Let GenRecNatNat :=
    GenRecExt (EmptyOpSpecs W) lt (fun _ => fib_trivial_inv).
  Let call {n0} (n:nat) : GenRecNatNat n0 nat _ := call _ _ _ n.
  Import DijkstraMonadNotations.
  Program Definition fib0 (n:nat) : GenRecNatNat n nat fib_trivial_inv :=
    match n with
    | 0 | 1 => wkn (dret 1) _
    | S (S n) => wkn (r1 <- call (S n) ; r2 <- call n ; dret (r1 + r2)) _
    end.
  Next Obligation. destruct H; cbv; auto. Qed.
  Next Obligation. destruct H; cbv; auto. Qed.
  Next Obligation. cbv ; intuition ; constructor. reflexivity.
                   constructor ; reflexivity. Qed.

  Definition Empty_perform W (D: Dijkstra W) (s:EmptyS) : D (EmptyP s) (EmptyOpSpecs W s) := match s with end.
  Program Definition fib := @ffix _ _ W _ (@EmptyRan' W) _ Pure (Empty_perform  Pure) pure_intro_assume _ _ _ _ _ _ _ fib0.
  Next Obligation.
    apply leS_to_le. apply (sq_le_to_leS H).
  Qed.
  Next Obligation.
    unshelve eapply (ran_iso (@MonoContAlongPrePost_ran _ _ w (Squash (S d <= d0)) (fun _ => sUnit)  _)).
    cbv in H.
    move=> Hw ; destruct (H _ Hw) ; assumption.
    split ; sreflexivity.
    cbv ; intuition.
  Qed.

  Program Definition fib' n := Spr1 (@fib n) (fun _ => sUnit) _.
  Next Obligation. intuition. Qed.

  (* Goal exists x, x = Spr1 (fib' 2). *)
  (* Proof. *)
  (*   eexists. *)
  (*   rewrite /fib' /fib /ffix. *)
  (*   time repeat (simp eval ; simpl). *)
  (*   (* Tactic call ran for 15.526 secs (15.437u,0.026s) (success) *) *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Goal exists x, x = Spr1 (fib' 0). *)
  (* Proof. *)
  (*   eexists. *)
  (*   rewrite /fib' /fib /ffix. *)
  (*   time repeat (simp eval ; simpl). *)
  (*   (* Tactic call ran for 1.12 secs (1.115u,0.003s) (success) *) *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Goal exists x, x = Spr1 (fib' 3). *)
  (* Proof. *)
  (*   eexists. *)
  (*   rewrite /fib' /fib /ffix. *)
  (*   time repeat (simp eval ; simpl). *)
  (*   (* Tactic call ran for 296.109 secs (295.803u,0.029s) (success) *) *)
  (*   reflexivity. *)
  (* Qed. *)

End Fibonnacci.