From Coq Require Import ssreflect ssrfun ssrbool.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.
Set Universe Polymorphism.

(***************************************************************)
(* The main useful example of a specification monad:           *)
(*    the monotone continuations monad.                        *)
(* This is especially useful because the monad laws hold       *)
(* definitionally in Coq.                                      *)
(***************************************************************)
Section MonotoneContinuationsMonad.
  Import SPropNotations.

  Context {R: Type} (Rrel : srelation R) `{PreOrder _ Rrel}.
  Notation "x ≼ y" := (Rrel x y) (at level 70).

  Definition MonoContCarrier (X: Type) : Type :=
    { f : (X -> R) -> R ≫ SProper (pointwise_srelation X Rrel s==> Rrel) f}.

  Program Definition MonoCont_ret A (a:A) : MonoContCarrier A :=
    Sexists _ (fun k => k a) _.
  Next Obligation. cbv; auto. Qed.

  Program Definition MonoCont_bind A B (m : MonoContCarrier A)
          (f : A -> MonoContCarrier B) : MonoContCarrier B :=
    Sexists _ (fun k => Spr1 m (fun a => Spr1 (f a) k)) _.
  Next Obligation.
    cbv ; intuition. apply (Spr2 m).
    intros a ; apply (Spr2 (f a)) ; assumption.
  Qed.

  Program Definition MonoContU : Monad :=
    @mkMonad MonoContCarrier MonoCont_ret MonoCont_bind _ _ _.

  Program Definition MonoCont_order A : srelation (MonoContU A) :=
    fun m1 m2 => pointwise_srelation (A -> R) Rrel (Spr1 m1) (Spr1 m2).
  Instance MonoCont_order_preorder A : PreOrder (@MonoCont_order A).
  Proof.
    constructor ; cbv ; intuition ;
      eauto using PreOrder_Transitive.
  Qed.

  Program Definition MonoCont : OrderedMonad :=
    @mkOrderedMonad MonoContU MonoCont_order _ _.
  Next Obligation.
    cbv ; intuition.
    repeat lazymatch goal with | [H : Ssig _ |- _] => destruct H end.
    match goal with
    |[|- Rrel (?X ?F) (?Y ?G)] => stransitivity (X G) ; auto
    end.
  Qed.

End MonotoneContinuationsMonad.

Section MonoContSProp.
  Definition MonoContSProp := @MonoCont SProp (SProp_op_order) _.
  Import SPropNotations.

  Global Program Instance MonoContSProp_aa A : aa (@omon_rel MonoContSProp A)
    :=
      @mkAa _ _
            (fun pre w => Sexists _ (fun p => pre -> Spr1 w p) _)
            (fun pre w => Sexists _ (fun p => pre s/\ Spr1 w p) _)
            _ _ _.
  Solve All Obligations with cbv ; intuition ; try (eapply (Spr2 w) ; eauto).

End MonoContSProp.


Section PrePostSpec.
  Import SPropNotations.

  (* Generic pre-/post-conditions for the W^Pure specification monad. *)
  Program Definition PrePostSpec {A} (P : SProp) (Q : A -> SProp) :
    MonoContSProp A :=
    Sexists _ (fun (Z : A -> SProp) => P s/\ forall a, Q a -> Z a) _.
  Next Obligation. cbv ; intuition eauto. Qed.

  Section Ran.
    Context (B C : Type) (w : MonoContSProp C)
            (pre : SProp) (post : B -> SProp).
    Context (Hpre : Spr1 w (fun _ => sUnit) -> pre).

    Definition MonoContAlongPrePost_ran : ran w (PrePostSpec pre post).
    Proof.
      unshelve econstructor.
      refine (fun b => Sexists _ (fun p => post b s/\ Spr1 w p) _).
      cbv ; intuition ; eapply (Spr2 w _) ; eauto.
      split.
      cbv. intros ; split.
      apply Hpre. eapply (Spr2 w _) ; eauto.
      cbv ; intuition. cbv ; intuition.
      cbv ; intuition.
      destruct (H a q). apply s ; assumption.
   Qed.
  End Ran.
End PrePostSpec.

Section ExceptionSpec.
  Context (E:Type).
  Import SPropNotations.

  Definition ExnSpecCarrier : Type -> Type :=
    fun X => { f : (X -> SProp) -> (E -> SProp) -> SProp
          ≫ SProper ((X ⇢ SProp_op_order) s==> (E ⇢ SProp_op_order) s==> SProp_op_order) f}.

  Program Definition ExnSpec_ret : forall A, A -> ExnSpecCarrier A :=
    fun A a => ⦑ fun p pexc => p a ⦒.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition ExnSpec_bind :
    forall A B, ExnSpecCarrier A -> (A -> ExnSpecCarrier B) -> ExnSpecCarrier B :=
    fun A B m f =>
      ⦑ fun p pexc => Spr1 m (fun a => Spr1 (f a) p pexc) pexc ⦒.
  Next Obligation.
    move=> ? ? ? ? ? ?.
    eapply (Spr2 m) ; try eassumption.
    move=> /= ? ; apply (Spr2 (f _)) ; assumption.
  Qed.

  Program Definition ExnSpecU : Monad :=
    @mkMonad ExnSpecCarrier ExnSpec_ret ExnSpec_bind _ _ _.

  Definition ExnSpec_rel A : srelation (ExnSpecU A) :=
    fun m1 m2 => ((A -> SProp) ⇢ ((E -> SProp) ⇢ SProp_op_order)) (Spr1 m1) (Spr1 m2).

  Instance ExnSpec_order A : PreOrder (@ExnSpec_rel A).
  Proof. constructor ; cbv ; intuition. Qed.

  Program Definition ExnSpec : OrderedMonad :=
    @mkOrderedMonad ExnSpecU ExnSpec_rel _ _.
  Next Obligation.
    cbv; move=> ? y H ? ? ? ? ? H1 ; apply H.
    move: H1 ; apply (Spr2 y) ; cbv ; intuition.
  Qed.
End ExceptionSpec.

(***************************************************************)
(* A variation on continuations for update monads              *)
(***************************************************************)

Section UpdateSpecMonad.
  Context (M : monoid) (X : monoid_action M).

  Definition dom_rel A : srelation (A -> M -> SProp) :=
    pointwise_srelation A (pointwise_srelation M SProp_op_order).
  Definition cod_rel : srelation (X -> SProp) :=
    pointwise_srelation X SProp_op_order.

  Instance dom_rel_ord A : PreOrder (@dom_rel A).
  Proof. constructor ; cbv ; intuition. Qed.
  Instance cod_rel_ord : PreOrder cod_rel.
  Proof. constructor ; cbv ; intuition. Qed.

  Import SPropNotations.

  Definition WUpd A :=
    { f : (A -> M -> SProp) -> X -> SProp ≫
      SProper (@dom_rel A s==> cod_rel) f}.
  Program Definition retWUpd A (a : A) : WUpd A :=
    Sexists _ (fun p xx => p a (e M)) _.
  Next Obligation. move=> ? ? H ? ; apply H. Qed.

  Program Definition bindWUpd A1 A2
          (wm : WUpd A1) (wf : A1 -> WUpd A2)
    : WUpd A2 :=
    Sexists _
            (fun p x => Spr1 wm (fun a m => Spr1 (wf a)
                                              (fun a m' => p a (m'⋅m))
                                              (m ⧕  x)) x) _.
  Next Obligation.
    move=> ? ? H ? ; apply (Spr2 wm)=> a m ; apply (Spr2 (wf a))=> ? ? ; apply H.
  Qed.

  Definition WUpd_rel A : srelation (WUpd A) :=
    fun m1 m2 => forall p, cod_rel (Spr1 m1 p) (Spr1 m2 p).
  Instance WUpd_ord A : PreOrder (@WUpd_rel A).
  Proof. constructor ; cbv ; intuition. Qed.

  (* We do not prove the monadic laws since they would
   rely on funext. Instead we let them be proved on a case
   by case basis, which should be trivial when both the monoid
   and action laws hold definitionally *)
  Program Definition UpdSpecFromLaws pf1 pf2 pf3 : OrderedMonad :=
    let upd_spec_monad := @mkMonad WUpd retWUpd bindWUpd pf1 pf2 pf3 in
    @mkOrderedMonad upd_spec_monad WUpd_rel WUpd_ord _.
  Next Obligation.
    cbv ; move=> x ? Hm ? ? Hf ? ? H. move: (Hm _ _ H).
    apply (Spr2 x) => ? ? ; apply Hf.
  Qed.

  Import FunctionalExtensionality.

  Program Definition UpdSpec := UpdSpecFromLaws _ _ _.
  Next Obligation.
    apply Ssig_eq. extensionality p0 ; extensionality x.
    cbv. f_equal.
    extensionality a0 ; extensionality m' ; rewrite !monoid_law2 //.
    rewrite !monact_unit //.
  Qed.

  Next Obligation.
    apply Ssig_eq. extensionality p.
    cbv. extensionality a ; f_equal. extensionality a0 ; extensionality m'.
    rewrite !monoid_law1 //.
  Qed.

  Next Obligation.
    apply Ssig_eq; extensionality p ; extensionality x.
    cbv.
    let t :=
        f_equal ; [let Hab := fresh "ab" in
        let Hmm := fresh "mm" in
        extensionality Hab ; extensionality Hmm |..] in
    do 3 t.
    rewrite !monoid_law3 //.
    rewrite !monact_mult //.
  Qed.

  Section AssertAssume.
    Context pf1 pf2 pf3 (UpdSpec := UpdSpecFromLaws pf1 pf2 pf3).
    Global Program Instance UpdSpecFromLaws_aa A : aa (@omon_rel UpdSpec A)
      :=
        @mkAa _ _
              (fun pre w => Sexists _ (fun p x => pre -> Spr1 w p x) _)
              (fun pre w => Sexists _ (fun p x => pre s/\ Spr1 w p x) _)
              _ _ _.
    Solve All Obligations with cbv ; intuition ; try (eapply (Spr2 w) ; eauto).

  End AssertAssume.

  Global Instance UpdSpec_aa A : aa (@omon_rel UpdSpec A).
  Proof. eapply UpdSpecFromLaws_aa. Defined.

End UpdateSpecMonad.



(*****************************************************************)
(* Some less useful specification monads, covered in Section 4.1 *)
(*****************************************************************)

(* Fat monotone relation-based specification monad *)
Section MonotonicRelations.
  Import SPropNotations.
  Import SPropAxioms.

  Definition SPropAssuming (pre : SProp) :=
    { q : SProp ≫ q s<-> (pre -> q) }.

  Definition MR_base X :=
    forall (pre:SProp), (X -> SPropAssuming pre) -> SPropAssuming pre.

  Definition MR_base_rel X : srelation (MR_base X) :=
    fun r1 r2 =>
    forall (pre1 pre2:SProp) (Hpre : pre1 -> pre2) (post1 : X -> SPropAssuming pre1)
      (post2 : X -> SPropAssuming pre2)
      (Hpost : forall x, Spr1 (post2 x) -> Spr1 (post1 x)), Spr1 (r2 pre2 post2) -> Spr1 (r1 pre1 post1).

  Definition MR X := { r : MR_base X ≫ SProper (@MR_base_rel X) r }.

  Program Definition retMR A a : MR A :=
    Sexists _ (fun pre post => Sexists _ (pre -> Spr1 (post a)) _) _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition bindMR A B (m:MR A) (f: A -> MR B) : MR B :=
      Sexists _ (fun pre post =>
                   Sexists _ (Spr1 (Spr1 m pre (fun a => Sexists _ (Spr1 (Spr1 (f a) pre post)) _))) _) _.
  Next Obligation.
    split ; move=> ? //=.
    match goal with | [|- _ ?X] => apply (Spr2 X) ;assumption end.
  Qed.
  Next Obligation.
    cbv ; intuition.
    match goal with | [|- ?X ?Y] => apply (Spr2 Y) ; assumption end.
  Qed.
  Next Obligation.
    cbv ; intuition.
    simple refine (Spr2 m _ _ _ _ _ _ H).
    assumption.
    cbv ; move=> a. apply (Spr2 (f a)). assumption. auto.
  Qed.

  Import FunctionalExtensionality.

  Program Definition MR_monad : Monad :=
    @mkMonad MR retMR bindMR _ _ _.
  Next Obligation.
    apply Ssig_eq ; extensionality pre ; extensionality post ; apply Ssig_eq ; apply sprop_ext.
    do 2 split ; cbv.
    move=> ?; match goal with
               | [|- _ ?X] => apply (Spr2 X) ; assumption
              end.
    move=> ? ? //=.
  Qed.
  Next Obligation.
    apply Ssig_eq ; extensionality pre ; extensionality post ; apply Ssig_eq ; apply sprop_ext.
    do 2 split ; cbv.
    apply (Spr2 c) => //=.
    move=> ? ? ; apply (Spr2 (post _)) ; assumption.
    apply (Spr2 c) => //=.
  Qed.

  Definition MR_rel X : srelation (MR X) :=
    fun w1 w2 => forall pre post, Spr1 (Spr1 w2 pre post) -> Spr1 (Spr1 w1 pre post).

  Instance MR_preorder X : PreOrder (@MR_rel X).
  Proof.
    constructor ; cbv ; intuition.
  Qed.

  Program Definition MRSpec : OrderedMonad :=
    @mkOrderedMonad MR_monad MR_rel _ _.
  Next Obligation.
    cbv ; intuition.
    simple refine (H _ _ _).
    move:H1 ; apply (Spr2 y); auto.
  Qed.

End MonotonicRelations.



From Coq Require FunctionalExtensionality.

Section Pred.
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Definition Pred X := X -> SProp.
  Definition Pred_ret : forall A, A -> Pred A := fun _ x y => y ≡ x.
  Definition Pred_bind
    : forall A B, Pred A -> (A -> Pred B) -> Pred B :=
    fun A B m f y => s∃ x, m x s/\ (f x) y.

  Program Definition PredM : Monad :=
    @mkMonad Pred Pred_ret Pred_bind _ _ _.
  Next Obligation.
    cbv ; extensionality y ; apply sprop_ext ; do 2 constructor.
    move=> [? [H ?]] ; induction H=> //.
    move=> ? ; eexists ; split=> //.
  Qed.
  Next Obligation.
    cbv ; extensionality y ; apply sprop_ext ; do 2 constructor.
    move=> [? [? H]] ; induction H=> //.
    move=> ? ; eexists ; split=> // ; by [].
  Qed.
  Next Obligation.
    cbv ; extensionality y ; apply sprop_ext ; do 2 constructor.
    move=> [? [[? [? ?]] ?]] ; eexists ; split ; [|eexists; split] ; eassumption.
    move=> [? [? [? [? ?]]]] ; eexists ; split ; [eexists; split|] ; eassumption.
  Qed.

  Program Definition PredOM : OrderedMonad :=
    @mkOrderedMonad PredM (fun X => X ⇢ SProp_order) _ _.
  Next Obligation.
    cbv=> ? ? ? ? ? ? ? [a [? ?]]; exists a ; split ; auto.
  Qed.
End Pred.

Module PrePost.
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Definition PP X := SProp  × (X -> SProp).

  Definition PP_ret : forall A, A -> PP A := fun _ x => ⟨ sUnit, fun y => y ≡ x ⟩.

  Definition PP_bind
    : forall A B, PP A -> (A -> PP B) -> PP B :=
    fun A B m f =>
      ⟨ (nfst m s/\ forall x, nsnd m x -> nfst (f x)),
        fun y => s∃ x, nsnd m x s/\ nsnd (f x) y ⟩.

  Program Definition PP_monad : Monad :=
    @mkMonad PP PP_ret PP_bind _ _ _.

  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ; apply sprop_ext => //=.
    dintuition ; subst_sEq ; assumption.
    do 2 split.
    intros [? []]; subst_sEq ; assumption.
    eexists ; split ; [| eassumption] ; reflexivity.
  Qed.

  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ;
      apply sprop_ext => //= ; try by dintuition.
    do 2 split.
    move=> [? [? ?]] ; subst_sEq ; eassumption.
    move=> ? ; eexists ; split. eassumption. reflexivity.
  Qed.

  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ; apply sprop_ext => //=.
    - dintuition. eapply q ; eexists ; split ; eassumption.
      destruct (q x H) ; assumption.
      destruct H as [?[n ?]]. destruct (q _ n) ; auto.
    - do 2 split.
    intros [? [[? []]]] ; eexists ; split ; [|eexists;split] ;eassumption.
    intros [? [? [? []]]] ; eexists ; split ; [eexists; split|] ; eassumption.
  Qed.

  Program Definition PP_rel A : srelation (PP A) :=
    fun m1 m2 => (nfst m2 -> nfst m1) s/\ forall x, nsnd m1 x -> nsnd m2 x.
  Instance PP_rel_preorder A : PreOrder (@PP_rel A).
  Proof. constructor ; cbv ; dintuition. Qed.

  Program Definition PPSpecMonad : OrderedMonad :=
    @mkOrderedMonad PP_monad PP_rel _ _.
  Next Obligation.
    cbv ; dintuition. destruct (H x0) ; auto.
    destruct H0 as [x1 []]. destruct (H x1) ; eexists ; split ; auto.
    auto.
  Qed.

  Section RightKanExtension.
    Context A B (w : PPSpecMonad A) (w' : PPSpecMonad B).

    (*    1 -- w --> A
          |         /
          w' <=   /
          |     /  Ran_w w'
          v   /
          B <
   *)

    Context (Hpre : nfst w' -> nfst w).

    Local Definition PPSpec_ran : A -> PPSpecMonad B :=
      fun (a:A) => ⟨nsnd w a s/\ nfst w', fun b => nsnd w a -> nsnd w' b⟩.

    Lemma PPSpec_ran_valid : bind w PPSpec_ran ≤[PPSpecMonad] w'.
    Proof.
      cbv ; split.
      intuition.
      move=> b [a [? ?]] ; intuition.
    Qed.

    Lemma PPSpec_ran_universal : forall (w'' : A -> PPSpecMonad B),
        bind w w'' ≤[PPSpecMonad] w' -> forall a, w'' a ≤[PPSpecMonad] PPSpec_ran a.
    Proof.
      cbv. move=> ? [? H] a ; intuition.
      apply H. exists a ; intuition.
    Qed.

    Program Definition PPSpecRan : ran w' w :=
      Sexists _ PPSpec_ran _.
    Next Obligation.
      split ; [exact PPSpec_ran_valid | exact PPSpec_ran_universal].
    Qed.
  End RightKanExtension.

  Global Program Instance PP_aa A : aa (@omon_rel PPSpecMonad A)
    :=
      @mkAa _ _
            (fun pre w => ⟨pre -> nfst w, nsnd w⟩)
            (fun pre w => ⟨pre s/\ nfst w, nsnd w⟩)
            _ _ _.
  Solve All Obligations with cbv ; intuition.

End PrePost.



Module  StrongestPostcondition.
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Record SPropOver (p:SProp) := mkOver { base :> SProp ; over : base -> p }.

  Definition SP X := { f : forall p:SProp, X -> SPropOver p ≫
                       forall (p1 p2 : SProp) x, (p1 -> p2) -> f p1 x -> f p2 x}.

  Program Definition SP_ret A (a:A) : SP A :=
    Sexists _ (fun p y => @mkOver _ (p s/\ a ≡ y) _) _.
  Next Obligation. destruct H ; assumption. Qed.
  Next Obligation. destruct H0 ; split ; auto. Qed.

  Program Definition SP_bind A B (m:SP A) (f : A -> SP B) : SP B :=
    Sexists _ (fun p y => @mkOver _ (s∃ x, Spr1 (f x) (Spr1 m p x) y) _) _.
  Next Obligation.
    destruct H as [x0 H0].
    exact (@over _ (Spr1 m p x0) (@over _ (Spr1 (f _) _ _) H0)).
  Qed.

  Next Obligation.
    destruct H0 as [x0 H1].
    exists x0 ; apply (Spr2 (f x0) _ _ _ (Spr2 m _ _ x0 H)) ; assumption.
  Qed.

  Lemma trivial_eq (p:SProp) {A} (x:A) : p = (p s/\ x ≡ x).
  Proof. apply sprop_ext ; split ; dintuition. Qed.

  Lemma SPropOver_eq p (q1 q2 : SPropOver p) :
    (base q1 s<-> base q2) -> q1 = q2.
  Proof.
    intros .
    assert (H0 : base q1 = base q2) by (apply sprop_ext ; constructor ; assumption).
    destruct q1 ; destruct q2 ; simpl in *.
    induction H0.
    reflexivity.
  Qed.

  Program Definition SP_monad : Monad := @mkMonad SP SP_ret SP_bind _ _ _.

  Next Obligation.
    apply Ssig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;
      simpl ; split.
    intros [x H] ; move: (over H) => [_?] ; subst_sEq ;
      move: H ; apply (Spr2 (f a)) ; intuition.
    intros H ; exists a; rewrite <- trivial_eq ; assumption.
  Qed.

  Next Obligation.
    apply Ssig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;  simpl ; split.
    intros [? []] ; subst_sEq ; assumption.
    intros H ; eexists ; intuition ; eassumption.
  Qed.

  Next Obligation.
    apply Ssig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;  simpl ; split.

    intros [x0 H].
    move: (over H) => [x1 H1]; exists x1 ; exists x0; move: H.
    apply (Spr2 (g x0)) => ? //=.

    intros [x0 [x1 H]] ; exists x1 ; move: H ; apply (Spr2 (g x1)) => ?.
    exists x0 ; assumption.
  Qed.

  Definition SP_rel A : srelation (SP A) :=
    fun m1 m2 => forall p x, Spr1 m1 p x -> Spr1 m2 p x.
  Instance SP_rel_preorder A : PreOrder (@SP_rel A).
  Proof. constructor ; cbv ; intuition. Qed.

  Program Definition ForwardPredTransformer : OrderedMonad :=
    @mkOrderedMonad SP_monad SP_rel _ _.
  Next Obligation.
    cbv; move=> ? ? ? ? f H ? ? [x H0].
    exists x. move : (H _ _ _ H0) ; eapply (Spr2 (f x)) ; auto.
  Qed.

End StrongestPostcondition.

Section Adjunctions.
  Import PrePost.
  Import SPropNotations.

  Definition pred2pp A (post:PredOM A) : PPSpecMonad A :=
    ⟨sUnit, post⟩.
  Definition pp2pred A (pp:PPSpecMonad A) : PredOM A :=
    fun a => nsnd pp a.

  Lemma pred_pp_adjunction : forall A post (pp : PPSpecMonad A),
   pred2pp post ≤[PPSpecMonad] pp  s<-> post ≤[PredOM] pp2pred pp.
  Proof.
    move=> A post pp ; cbv ; split ; intuition.
  Qed.

  Let MonoCont := MonoContSProp.

  Definition wp2pp A (w : MonoCont A) : PPSpecMonad A :=
    ⟨Spr1 w (fun _ => sUnit), fun x =>  forall p, Spr1 w p -> p x⟩.
  Program Definition pp2wp A (pp : PPSpecMonad A) : MonoCont A :=
    Sexists _ (fun post => nfst pp s/\ (forall x, nsnd pp x -> post x)) _.
  Next Obligation. cbv ; intuition. Qed.

  Lemma wp_pp_adjunction : forall A pp (w : MonoCont A),
   pp ≤[PPSpecMonad] wp2pp w s<-> pp2wp pp ≤[MonoCont] w.
  Proof.
    intros A pp w ; cbv ; split.
    - move=> [Hpre Hpost] a H1 ; split.
      apply Hpre. move:H1. apply (Spr2 w). cbv ; dintuition.
      intros ; apply Hpost ; assumption.
    - intros Hpp ; split.
      move=> H1 ; move: (Hpp _ H1) ; dintuition.
      intros x Hp post Hpost ; move: (Hpp _ Hpost) ; move=> [_ H1].
      apply H1 ; assumption.
  Qed.


  Program Definition wp2mr A (w : MonoCont A) : MRSpec A :=
    Sexists _ (fun pre post => Sexists _ (pre -> Spr1 w (fun a => Spr1 (post a))) _ ) _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation.
    cbv ; intuition.
    move: H2 ; apply (Spr2 w). cbv ; auto.
  Qed.

  Program Definition assuming (pre : SProp) A (post : A -> SProp) (x:A) :
    SPropAssuming pre :=
    Sexists _ (pre -> post x) _.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition mr2wp A (mr:MRSpec A) : MonoCont A :=
    Sexists _ (fun p => s∃ (pre:SProp), Spr1 (Spr1 mr pre (assuming pre p)) s/\ pre) _.
  Next Obligation.
    cbv ; intuition.
    move: H0 => [pre [Hmr ?]] ; exists pre ; intuition.
    move: Hmr ; apply (Spr2 mr) ; cbv ; auto.
  Qed.

  Lemma wp_mr_adjunction : forall A (w : MonoCont A) r,
   w ≤ mr2wp r s<-> wp2mr w ≤ r.
  Proof.
   cbv ; intuition.
   apply H. exists pre ; intuition.
   move: H0 ; apply (Spr2 r) ; auto.

   move: H0 => [pre [Hr Hpre]].
   move: (H _ _ Hr Hpre). apply (Spr2 w). auto.
  Qed.


   Import StrongestPostcondition.


  Definition sp2pp A (sp:ForwardPredTransformer A) : PPSpecMonad A :=
    let post := fun x => forall (pre : SProp), pre -> Spr1 sp pre x in
    let pre := s∃ pre, (forall x, post x -> Spr1 sp pre x) s/\ pre in
    ⟨pre, post⟩.

  Program Definition pp2sp0 A (pp : PPSpecMonad A) : ForwardPredTransformer A :=
    let sp pre x := pre s/\ (nfst pp -> nsnd pp x) in
    Sexists _ (fun pre x => @mkOver _ (sp pre x) _) _.
  Next Obligation. destruct H ; assumption. Qed.
  Next Obligation. move: H0 => [Hpre Hpost] ; split ; auto. Qed.

  Program Definition pp2sp A (pp : PPSpecMonad A) : ForwardPredTransformer A :=
    let sp pre x : SProp :=
        forall (sp: ForwardPredTransformer A),
          (forall x pre', pre' s/\ nsnd pp x -> Spr1 sp pre' x) ->
              Spr1 sp pre x in
    Sexists _ (fun pre x => @mkOver _ (sp pre x) _) _.
  Next Obligation.
    move: (H (pp2sp0 pp)) => H0.
    apply (fun f => over (H0 f)).
    cbv ; intuition.
  Qed.
  Next Obligation.
    move: (H0 sp H1). apply (Spr2 sp). assumption.
  Qed.

  Lemma pp2sp01 A (pp:PPSpecMonad A) :
    pp2sp pp ≤[ForwardPredTransformer] pp2sp0 pp.
  Proof.
    cbv.
    move=> p x H.
    move: (H (pp2sp0 pp)) => H0.
    apply H0.
    cbv ; intuition.
  Qed.

  Lemma sp2pp_pp2sp_loop A (pp:PPSpecMonad A) :
    sp2pp (pp2sp pp) ≤[PPSpecMonad] pp.
  Proof.
    cbv.
    split.
    - move=> ?; exists sUnit;split.
      move=> ? H ? ?; apply H.
      all:intuition.
    - move=> x H.
      simple refine (_ (H sUnit stt (pp2sp0 ⟨sUnit, nsnd pp⟩) _)); cbv ; intuition.
  Qed.

  Lemma pp2sp_sp2pp_loop A (sp:ForwardPredTransformer A) :
    sp ≤[ForwardPredTransformer] pp2sp (sp2pp sp).
  Proof.
    cbv.
    intuition.
    specialize (H0 x).
    apply H0.
    split. exact (over H).
    intros ; move: H ; apply (Spr2 sp) ; intuition.
  Qed.

  Lemma sp_pp_adjunction A pp (sp : ForwardPredTransformer A) :
    sp2pp sp ≤[PPSpecMonad] pp s<-> sp ≤[ForwardPredTransformer] pp2sp pp.
  Proof.
    cbv ; split.
    - dintuition. apply H0.
      split. exact (over H).
      apply q. intros ; move:H ; apply (Spr2 sp) ; intuition.
    - dintuition.
      exists sUnit. split ; intuition.
      apply H1 ; constructor.
      simple refine (_ (H sUnit x (H0 sUnit stt)(pp2sp0 ⟨sUnit, nsnd pp⟩) _)); cbv ; intuition.
  Qed.

  Program Definition sp2mr A (sp : ForwardPredTransformer A)
    : MRSpec A :=
    Sexists _ (fun pre post => Sexists _ (forall a, Spr1 sp pre a -> Spr1 (post a)) _) _.
  Next Obligation.
    cbv ; intuition.
    apply (Spr2 (post a)).
    auto.
  Qed.
  Next Obligation.
    cbv ; intuition.
    apply Hpost. apply H. move: H0 ; apply (Spr2 sp) ; auto.
  Qed.

  Program Definition mr2sp A (mr : MRSpec A)
    : ForwardPredTransformer A :=
    Sexists _ (fun pre a => @mkOver _ (pre s/\ forall post, Spr1 (Spr1 mr pre post) -> Spr1 (post a)) _)_.
  Next Obligation. destruct H ; assumption. Qed.
  Next Obligation.
    move: H0 => [Hpre Hmr] ; split ; [auto|].
    move=> post Hpost. simple refine (Hmr (fun a => Sexists _ (Spr1 (post a)) _) _). cbv ; intuition.
    move: Hpost ; apply (Spr2 mr) ; cbv ; intuition.
  Qed.

  Lemma sp_mr_adjunction A (sp : ForwardPredTransformer A) (mr:MRSpec A) :
     sp2mr sp ≤ mr s<-> sp  ≤ mr2sp mr.
  Proof.
    cbv ; intuition.
    exact (over H0).
    move: (H _ _ H1) => [? Hpost].
    apply Hpost ; assumption.
  Qed.

End Adjunctions.


Section WpSpRightKanExtension.
  Let MonoCont := @MonoCont SProp (SProp_op_order) _.
  Import PrePost.
  Import StrongestPostcondition.
  Import SPropNotations.

  Definition ppwp_pairing A (pp : PPSpecMonad A) (w : MonoCont A) : SProp :=
    nfst pp -> Spr1 w (nsnd pp).

  Definition ppsp_pairing A (pp : PPSpecMonad A) (sp : ForwardPredTransformer A) : SProp :=
    forall a, Spr1 sp (nfst pp) a -> nsnd pp a.

  Definition wpsp_pairing A (wp: MonoCont A) (sp:ForwardPredTransformer A) : SProp :=
    (forall pre post, let pp := ⟨pre, post⟩ in ppwp_pairing pp wp -> ppsp_pairing pp sp) s/\
    (forall pre post, let pp := ⟨pre, post⟩ in ppsp_pairing pp sp -> ppwp_pairing pp wp).

  Context (M : Monad) (θwp : MonadMorphism M MonoCont)
          (θsp : MonadMorphism M ForwardPredTransformer).
  Context (Hadj : forall A m, wpsp_pairing (θwp A m) (θsp A m)).

  Program Definition wp_ran A B (w: MonoCont B) (m: M A) : ran w (θwp A m) :=
    Sexists _ (fun a => Sexists _ (fun p => Spr1 (θsp A m) (Spr1 w p) a) _) _.
  Next Obligation.
    cbv. move=> ? ? H ; apply (Spr2 (θsp A m)) ; apply (Spr2 w)=> //=.
  Qed.
  Next Obligation.
    move: (Hadj m) ; move => [H1 H2]; cbv ; split.
    - move=> p ; apply H2 => //=.
    - move=> w' Hw' a p.
      refine (H1 _ (fun a => Spr1 (w' a) p) _ a).
      cbv ; apply Hw'.
   Qed.

End WpSpRightKanExtension.