From Coq Require Import ssreflect.
From Mon Require Export Base.
From Coq Require Import Relation_Definitions Morphisms.
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

  Context {R: Type} (Rrel : relation R) `{PreOrder _ Rrel}.
  Notation "x ≼ y" := (Rrel x y) (at level 70).

  Definition MonoContCarrier (X: Type) : Type :=
    { f : (X -> R) -> R | Proper (pointwise_relation X Rrel ==> Rrel) f}.

  Program Definition MonoCont_ret A (a:A) : MonoContCarrier A :=
    exist _ (fun k => k a) _.
  Next Obligation. cbv; auto. Qed.

  Program Definition MonoCont_bind A B (m : MonoContCarrier A)
          (f : A -> MonoContCarrier B) : MonoContCarrier B :=
    exist _ (fun k => proj1_sig m (fun a => proj1_sig (f a) k)) _.
  Next Obligation.
    cbv ; intuition. apply (proj2_sig m).
    intros a ; apply (proj2_sig (f a)) ; assumption.
  Qed.

  Program Definition MonoContU : Monad :=
    @mkMonad MonoContCarrier MonoCont_ret MonoCont_bind _ _ _.
  Next Obligation. apply sig_eq. compute.
    rewrite -FunctionalExtensionality.eta_expansion. reflexivity.
  Qed.
  Next Obligation. apply sig_eq. compute. reflexivity. Qed.
  Next Obligation. apply sig_eq. simpl. reflexivity. Qed.



  Program Definition MonoCont_order A : relation (MonoContU A) :=
    fun m1 m2 => pointwise_relation (A -> R) Rrel (proj1_sig m1) (proj1_sig m2).
  Instance MonoCont_order_preorder A : PreOrder (@MonoCont_order A).
  Proof.
    constructor ; cbv ; intuition ;
      eauto using PreOrder_Transitive.
  Qed.

  Program Definition MonoCont : OrderedMonad :=
    @mkOrderedMonad MonoContU MonoCont_order _ _.
  Next Obligation. cbv. intuition.
    destruct x as [fx ex]. destruct y as [fy ey].
    destruct H as (Hrefl , Htrans). unfold Transitive in Htrans.
    pose lleft := (fun a0 : A => (let (w, _) := x0 a0 in w) a).
    pose rright := (fun a0 : A => (let (w, _) := y0 a0 in w) a).
    apply: (Htrans (fx lleft) (fy lleft) (fy rright)).
     by apply: (H0 lleft).
    apply ey. intro a0. compute. apply H1.
  Qed.

End MonotoneContinuationsMonad.

Section MonoContProp.
  Definition MonoContSProp := @MonoCont Prop (SProp_op_order) _.
  Import SPropNotations.

  Global Program Instance MonoContSProp_aa A : aa (@omon_rel MonoContSProp A)
    :=
      @mkAa _ _
            (fun pre w => exist _ (fun p => pre -> proj1_sig w p) _)
            (fun pre w => exist _ (fun p => pre s/\ proj1_sig w p) _)
            _ _ _.
  Solve All Obligations with cbv ; intuition ; try (eapply (proj2_sig w) ; eauto).
  Next Obligation. compute. split ; intuition.
    apply H ; trivial.
    apply H. split ; assumption.
  Qed.

End MonoContProp.

Definition STCont S := @MonoCont (S -> Prop) (pointwise_relation S SProp_op_order) _.


Section PrePostSpec.
  Import SPropNotations.

  (* Generic pre-/post-conditions for the W^Pure specification monad. *)
  Program Definition PrePostSpec {A} (P : Prop) (Q : A -> Prop) :
    MonoContSProp A :=
    exist _ (fun (Z : A -> Prop) => P s/\ forall a, Q a -> Z a) _.
  Next Obligation. cbv ; intuition eauto. Qed.

  Section Ran.
    Context (B C : Type) (w : MonoContSProp C)
            (pre : Prop) (post : B -> Prop).
    Context (Hpre : proj1_sig w (fun _ => True) -> pre).

    Definition MonoContAlongPrePost_ran : ran w (PrePostSpec pre post).
    Proof.
      unshelve econstructor.
      refine (fun b => exist _ (fun p => post b s/\ proj1_sig w p) _).
      cbv ; intuition ; eapply (proj2_sig w _) ; eauto.
      split.
      cbv. intros ; split.
      apply Hpre. eapply (proj2_sig w _) ; eauto.
      cbv ; intuition. cbv ; intuition.
      cbv ; intuition.
      destruct (H a H2). apply H3 ; assumption.
   Qed.
  End Ran.
End PrePostSpec.

Section ExceptionSpec.
  Context (E:Type).
  Import SPropNotations.

  Definition ExnSpecCarrier : Type -> Type :=
    fun X => { f : (X -> Prop) -> (E -> Prop) -> Prop
          | Proper ((pointwise_relation X SProp_op_order) ==> (pointwise_relation E SProp_op_order) ==> SProp_op_order) f}.

  Program Definition ExnSpec_ret : forall A, A -> ExnSpecCarrier A :=
    fun A a => ⦑ fun p pexc => p a ⦒.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition ExnSpec_bind :
    forall A B, ExnSpecCarrier A -> (A -> ExnSpecCarrier B) -> ExnSpecCarrier B :=
    fun A B m f =>
      ⦑ fun p pexc => proj1_sig m (fun a => proj1_sig (f a) p pexc) pexc ⦒.
  Next Obligation.
    move=> ? ? ? ? ? ?.
    eapply (proj2_sig m) ; try eassumption.
    move=> /= ? ; apply (proj2_sig (f _)) ; assumption.
  Qed.

  Program Definition ExnSpecU : Monad :=
    @mkMonad ExnSpecCarrier ExnSpec_ret ExnSpec_bind _ _ _.
  Next Obligation. compute.
    apply sig_eq. compute.
    rewrite -FunctionalExtensionality.eta_expansion.
    reflexivity.
  Qed.
  Next Obligation. compute. apply sig_eq ; compute.
    rewrite -FunctionalExtensionality.eta_expansion.
    reflexivity.
  Qed.
  Next Obligation. compute. apply sig_eq ; compute. reflexivity. Qed.


  Definition ExnSpec_rel A : relation (ExnSpecU A) :=
    fun m1 m2 => (pointwise_relation (A -> Prop) (pointwise_relation (E -> Prop) SProp_op_order)) (proj1_sig m1) (proj1_sig m2).

  Global Instance ExnSpec_order A : PreOrder (@ExnSpec_rel A).
  Proof. constructor ; cbv ; intuition. apply H. apply H0.
    assumption.
  Qed.

  Program Definition ExnSpec : OrderedMonad :=
    @mkOrderedMonad ExnSpecU ExnSpec_rel _ _.
  Next Obligation.
    cbv; move=> ? y H ? ? G ? ? H1 ; apply H.
    move: H1 ; apply (proj2_sig y) ; cbv ; intuition.
    apply G. assumption.
  Qed.
End ExceptionSpec.

(***************************************************************)
(* A variation on continuations for update monads              *)
(***************************************************************)

Section UpdateSpecMonad.
  Context (M : monoid) (X : monoid_action M).

  Definition dom_rel A : relation (A -> M -> Prop) :=
    pointwise_relation A (pointwise_relation M SProp_op_order).
  Definition cod_rel : relation (X -> Prop) :=
    pointwise_relation X SProp_op_order.

  Instance dom_rel_ord A : PreOrder (@dom_rel A).
  Proof. constructor ; cbv ; intuition. Qed.
  Instance cod_rel_ord : PreOrder cod_rel.
  Proof. constructor ; cbv ; intuition. Qed.

  Import SPropNotations.

  Definition WUpd A :=
    { f : (A -> M -> Prop) -> X -> Prop |
      Proper (@dom_rel A ==> cod_rel) f}.
  Program Definition retWUpd A (a : A) : WUpd A :=
    exist _ (fun p xx => p a (e M)) _.
  Next Obligation. move=> ? ? H ? ; apply H. Qed.

  Program Definition bindWUpd A1 A2
          (wm : WUpd A1) (wf : A1 -> WUpd A2)
    : WUpd A2 :=
    exist _
            (fun p x => proj1_sig wm (fun a m => proj1_sig (wf a)
                                              (fun a m' => p a (m'⋅m))
                                              (m ⧕  x)) x) _.
  Next Obligation.
    move=> ? ? H ? ; apply (proj2_sig wm)=> a m ; apply (proj2_sig (wf a))=> ? ? ; apply H.
  Qed.

  Definition WUpd_rel A : relation (WUpd A) :=
    fun m1 m2 => forall p, cod_rel (proj1_sig m1 p) (proj1_sig m2 p).
  Instance WUpd_ord A : PreOrder (@WUpd_rel A).
  Proof. constructor ; cbv ; intuition. apply H. apply H0. assumption. Qed.

  (* We do not prove the monadic laws since they would
   rely on funext. Instead we let them be proved on a case
   by case basis, which should be trivial when both the monoid
   and action laws hold definitionally *)
  Program Definition UpdSpecFromLaws pf1 pf2 pf3 : OrderedMonad :=
    let upd_spec_monad := @mkMonad WUpd retWUpd bindWUpd pf1 pf2 pf3 in
    @mkOrderedMonad upd_spec_monad WUpd_rel WUpd_ord _.
  Next Obligation.
    cbv ; move=> x ? Hm ? ? Hf ? ? H. move: (Hm _ _ H).
    apply (proj2_sig x) => ? ? ; apply Hf.
  Qed.

  Import FunctionalExtensionality.

  Program Definition UpdSpec := UpdSpecFromLaws _ _ _.
  Next Obligation.
    apply sig_eq. extensionality p0 ; extensionality x.
    cbv. f_equal.
    extensionality a0 ; extensionality m' ; rewrite !monoid_law2 //.
    rewrite !monact_unit //.
  Qed.

  Next Obligation.
    apply sig_eq. extensionality p.
    cbv. extensionality a ; f_equal. extensionality a0 ; extensionality m'.
    rewrite !monoid_law1 //.
  Qed.

  Next Obligation.
    apply sig_eq; extensionality p ; extensionality x.
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
              (fun pre w => exist _ (fun p x => pre -> proj1_sig w p x) _)
              (fun pre w => exist _ (fun p x => pre s/\ proj1_sig w p x) _)
              _ _ _.
    Solve All Obligations with cbv ; intuition ; try (eapply (proj2_sig w) ; eauto).
    Next Obligation. compute. split ; intuition.
      all: apply H ; trivial. split ; trivial.
    Qed.

  End AssertAssume.

  Global Instance UpdSpec_aa A : aa (@omon_rel UpdSpec A).
  Proof. eapply UpdSpecFromLaws_aa. Defined.

End UpdateSpecMonad.



(*****************************************************************)
(* Some less useful specification monads, covered in Section 4.1 *)
(*****************************************************************)

(* Fat monotone relation-based specification monad *)
Section MonotonicRelations.
(*--------------------a forgotten section ----------------
  Import SPropNotations.
  Import SPropAxioms.

  Definition SPropAssuming (pre : Prop) :=
    { q : Prop | q <-> (pre -> q) }.

  Definition MR_base X :=
    forall (pre:Prop), (X -> SPropAssuming pre) -> SPropAssuming pre.

  Definition MR_base_rel X : srelation (MR_base X) :=
    fun r1 r2 =>
    forall (pre1 pre2:Prop) (Hpre : pre1 -> pre2) (post1 : X -> SPropAssuming pre1)
      (post2 : X -> SPropAssuming pre2)
      (Hpost : forall x, proj1_sig (post2 x) -> proj1_sig (post1 x)), proj1_sig (r2 pre2 post2) -> proj1_sig (r1 pre1 post1).

  Definition MR X := { r : MR_base X | SProper (@MR_base_rel X) r }.

  Program Definition retMR A a : MR A :=
    exist _
            (fun pre (post : A -> SPropAssuming pre)  =>
              exist _ (pre -> proj1_sig (post a)) _)
            _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; intuition. apply Hpost. assumption. Qed.

  Program Definition bindMR A B (m:MR A) (f: A -> MR B) : MR B :=
      exist _ (fun pre post =>
                   exist _ (proj1_sig (proj1_sig m pre (fun a => exist _ (proj1_sig (proj1_sig (f a) pre post)) _))) _) _.
  Next Obligation.
    split ; move=> ? //=.
    match goal with | [|- _ ?X] => apply (proj2_sig X) ;assumption end.
  Qed.
  Next Obligation. destruct m as [r propr]. simpl.
    destruct (r pre (fun a : A => ⦑ ((f a) ∙1 pre post) ∙1 ⦒)).
    compute. compute in s. assumption.
  Qed.
  Next Obligation.
    cbv ; intuition.
    simple refine (proj2_sig m _ _ _ _ _ _ H).
    assumption.
    cbv ; move=> a. apply (proj2_sig (f a)). assumption. auto.
  Qed.

  Import FunctionalExtensionality.

  Program Definition MR_monad : Monad :=
    @mkMonad MR retMR bindMR _ _ _.
  Next Obligation.
    apply sig_eq ; extensionality pre ; extensionality post ; apply sig_eq.
    simpl. destruct ((f a) ∙1 pre post) as [q eq]. compute.
    compute in eq. destruct eq as [eq1 eq2]. apply sprop_ext. apply box.
    split ; assumption.
  Qed.
  Next Obligation.
    apply sig_eq ; extensionality pre ; extensionality post ; apply sig_eq ; apply sprop_ext.
    do 2 split ; cbv.
    apply (proj2_sig c) => //=.
    move=> ? ? ; apply (proj2_sig (post _)) ; assumption.
    apply (proj2_sig c) => //=.
  Qed.
  Next Obligation.

  Qed.

  Definition MR_rel X : srelation (MR X) :=
    fun w1 w2 => forall pre post, proj1_sig (proj1_sig w2 pre post) -> proj1_sig (proj1_sig w1 pre post).

  Instance MR_preorder X : PreOrder (@MR_rel X).
  Proof.
    constructor ; cbv ; intuition.
  Qed.

  Program Definition MRSpec : OrderedMonad :=
    @mkOrderedMonad MR_monad MR_rel _ _.
  Next Obligation.
    cbv ; intuition.
    simple refine (H _ _ _).
    move:H1 ; apply (proj2_sig y); auto.
  Qed.

------------end of forgotten section *)
End MonotonicRelations.


Section Pred.
(*-----------------------a forgotten section
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Definition Pred X := X -> Prop.
  Definition Pred_ret : forall A, A -> Pred A := fun _ x y => y = x.
  Definition Pred_bind
    : forall A B, Pred A -> (A -> Pred B) -> Pred B :=
    fun A B m f y => exists x, m x s/\ (f x) y.

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
-------------------end of forgotten section *)
End Pred.

Module PrePost.
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Definition PP X := Prop  × (X -> Prop).

  Definition PP_ret : forall A, A -> PP A := fun _ x => ⟨ True, fun y => y = x ⟩.

  Definition PP_bind
    : forall A B, PP A -> (A -> PP B) -> PP B :=
    fun A B m f =>
      ⟨ (nfst m s/\ forall x, nsnd m x -> nfst (f x)),
        fun y => exists x, nsnd m x s/\ nsnd (f x) y ⟩.

  Program Definition PP_monad : Monad :=
    @mkMonad PP PP_ret PP_bind _ _ _.

  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ; apply sprop_ext => //=.
    dintuition ; subst. compute. intuition. rewrite H0. assumption.
    do 2 split.
    intros [? []]. subst. assumption.
    eexists ; split ; [| eassumption] ; reflexivity.
  Qed.
  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ;
      apply sprop_ext => //= ; try by dintuition.
    compute. apply box. intuition.
    do 2 split.
    move=> [? [? ?]] ; subst ; eassumption.
    move=> ? ; eexists ; split. eassumption. reflexivity.
  Qed.
  Next Obligation.
    apply nprod_eq =>//= ; [|extensionality y] ; apply sprop_ext => //=.
    compute. apply box. intuition. apply H1. exists x. intuition.
    apply H1. assumption.
    destruct H as [x0 [pf_nsnd_f pf_nsnd_c]].
    apply (H1 x0 pf_nsnd_f). assumption.
    - do 2 split.
    intros [? [[? []]]] ; eexists ; split ; [|eexists;split] ;eassumption.
    intros [? [? [? []]]] ; eexists ; split ; [eexists; split|] ; eassumption.
  Qed.

  Program Definition PP_rel A : relation (PP A) :=
    fun m1 m2 => (nfst m2 -> nfst m1) s/\ forall x, nsnd m1 x -> nsnd m2 x.
  Instance PP_rel_preorder A : PreOrder (@PP_rel A).
  Proof. constructor ; cbv ; dintuition. Qed.

  Program Definition PPSpecMonad : OrderedMonad :=
    @mkOrderedMonad PP_monad PP_rel _ _.
  Next Obligation.
    cbv ; dintuition. destruct (H x0) ; auto.
    destruct H2 as [x1 []]. destruct (H x1) ; eexists ; split ; auto.
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

    Import SPropMonadicStructuresNotation.

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
      exist _ PPSpec_ran _.
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
(*---------------------------------- a forgotten module
  Import SPropNotations.
  Import SPropAxioms.
  Import FunctionalExtensionality.

  Record SPropOver (p:Prop) := mkOver { base :> Prop ; over : base -> p }.

  Definition SP X := { f : forall p:SProp, X -> SPropOver p |
                       forall (p1 p2 : Prop) x, (p1 -> p2) -> f p1 x -> f p2 x}.

  Program Definition SP_ret A (a:A) : SP A :=
    exist _ (fun p y => @mkOver _ (p s/\ a = y) _) _.
  Next Obligation. destruct H ; assumption. Qed.
  Next Obligation. destruct H0 ; split ; auto. Qed.

  Program Definition SP_bind A B (m:SP A) (f : A -> SP B) : SP B :=
    exist _ (fun p y => @mkOver _ (exists x, proj1_sig (f x) (proj1_sig m p x) y) _) _.
  Next Obligation.
    destruct H as [x0 H0].
    exact (@over _ (proj1_sig m p x0) (@over _ (proj1_sig (f _) _ _) H0)).
  Qed.

  Next Obligation.
    destruct H0 as [x0 H1].
    exists x0 ; apply (proj2_sig (f x0) _ _ _ (proj2_sig m _ _ x0 H)) ; assumption.
  Qed.

  Lemma trivial_eq (p:Prop) {A} (x:A) : p = (p s/\ x = x).
  Proof. apply sprop_ext ; split ; dintuition. Qed.

  Lemma SPropOver_eq p (q1 q2 : SPropOver p) :
    (base q1 <-> base q2) -> q1 = q2.
  Proof.
    intros .
    assert (H0 : base q1 = base q2) by (apply sprop_ext ; constructor ; assumption).
    destruct q1 ; destruct q2 ; simpl in *.
    induction H0.
    reflexivity.
  Qed.

  Program Definition SP_monad : Monad := @mkMonad SP SP_ret SP_bind _ _ _.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;
      simpl ; split.
    intros [x H] ; move: (over H) => [_?] ; subst ;
      move: H ; apply (proj2_sig (f a)) ; intuition.
    intros H ; exists a; rewrite <- trivial_eq ; assumption.
  Qed.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;  simpl ; split.
    intros [? []] ; subst ; assumption.
    intros H ; eexists ; intuition ; eassumption.
  Qed.

  Next Obligation.
    apply sig_eq ; extensionality p ; extensionality y ; apply SPropOver_eq ;  simpl ; split.

    intros [x0 H].
    move: (over H) => [x1 H1]; exists x1 ; exists x0; move: H.
    apply (proj2_sig (g x0)) => ? //=.

    intros [x0 [x1 H]] ; exists x1 ; move: H ; apply (proj2_sig (g x1)) => ?.
    exists x0 ; assumption.
  Qed.

  Definition SP_rel A : srelation (SP A) :=
    fun m1 m2 => forall p x, proj1_sig m1 p x -> proj1_sig m2 p x.
  Instance SP_rel_preorder A : PreOrder (@SP_rel A).
  Proof. constructor ; cbv ; intuition. Qed.

  Program Definition ForwardPredTransformer : OrderedMonad :=
    @mkOrderedMonad SP_monad SP_rel _ _.
  Next Obligation.
    cbv; move=> ? ? ? ? f H ? ? [x H0].
    exists x. move : (H _ _ _ H0) ; eapply (proj2_sig (f x)) ; auto.
  Qed.
-------------------end of forgotten module*)
End StrongestPostcondition.

Section Adjunctions.
(*----------------------------a forgotten section
  Import PrePost.
  Import SPropNotations.

  Definition pred2pp A (post:PredOM A) : PPSpecMonad A :=
    ⟨True, post⟩.
  Definition pp2pred A (pp:PPSpecMonad A) : PredOM A :=
    fun a => nsnd pp a.

  Lemma pred_pp_adjunction : forall A post (pp : PPSpecMonad A),
   pred2pp post ≤[PPSpecMonad] pp  <-> post ≤[PredOM] pp2pred pp.
  Proof.
    move=> A post pp ; cbv ; split ; intuition.
  Qed.

  Let MonoCont := MonoContProp.

  Definition wp2pp A (w : MonoCont A) : PPSpecMonad A :=
    ⟨proj1_sig w (fun _ => True), fun x =>  forall p, proj1_sig w p -> p x⟩.
  Program Definition pp2wp A (pp : PPSpecMonad A) : MonoCont A :=
    exist _ (fun post => nfst pp s/\ (forall x, nsnd pp x -> post x)) _.
  Next Obligation. cbv ; intuition. Qed.

  Lemma wp_pp_adjunction : forall A pp (w : MonoCont A),
   pp ≤[PPSpecMonad] wp2pp w <-> pp2wp pp ≤[MonoCont] w.
  Proof.
    intros A pp w ; cbv ; split.
    - move=> [Hpre Hpost] a H1 ; split.
      apply Hpre. move:H1. apply (proj2_sig w). cbv ; dintuition.
      intros ; apply Hpost ; assumption.
    - intros Hpp ; split.
      move=> H1 ; move: (Hpp _ H1) ; dintuition.
      intros x Hp post Hpost ; move: (Hpp _ Hpost) ; move=> [_ H1].
      apply H1 ; assumption.
  Qed.


  Program Definition wp2mr A (w : MonoCont A) : MRSpec A :=
    exist _ (fun pre post => exist _ (pre -> proj1_sig w (fun a => proj1_sig (post a))) _ ) _.
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation.
    cbv ; intuition.
    move: H2 ; apply (proj2_sig w). cbv ; auto.
  Qed.

  Program Definition assuming (pre : Prop) A (post : A -> Prop) (x:A) :
    SPropAssuming pre :=
    exist _ (pre -> post x) _.
  Next Obligation. cbv ; intuition. Qed.

  Program Definition mr2wp A (mr:MRSpec A) : MonoCont A :=
    exist _ (fun p => exists (pre:Prop), proj1_sig (proj1_sig mr pre (assuming pre p)) s/\ pre) _.
  Next Obligation.
    cbv ; intuition.
    move: H0 => [pre [Hmr ?]] ; exists pre ; intuition.
    move: Hmr ; apply (proj2_sig mr) ; cbv ; auto.
  Qed.

  Lemma wp_mr_adjunction : forall A (w : MonoCont A) r,
   w ≤ mr2wp r <-> wp2mr w ≤ r.
  Proof.
   cbv ; intuition.
   apply H. exists pre ; intuition.
   move: H0 ; apply (proj2_sig r) ; auto.

   move: H0 => [pre [Hr Hpre]].
   move: (H _ _ Hr Hpre). apply (proj2_sig w). auto.
  Qed.


   Import StrongestPostcondition.

   Definition sp2pred A (sp:ForwardPredTransformer A) : PredOM A :=
     fun r => proj1_sig sp True r.

   Program Definition pred2sp A (post : PredOM A) : ForwardPredTransformer A :=
     ⦑fun pre r => @mkOver _ (pre s/\ post r) _⦒.
   Next Obligation. destruct H ; assumption. Qed.
   Next Obligation. destruct H0; split ; auto. Qed.

   Import FunctionalExtensionality.
   Lemma sp2pred2sp_id : forall A (sp : ForwardPredTransformer A),
       pred2sp (sp2pred sp) = sp.
   Proof.
     move=> A sp. apply sig_eq. extensionality p. extensionality r.
     apply SPropOver_eq. split; cbv.
     move=> [Hp]. apply (sp∙2). trivial.
     move=> H; split. exact (over H). move:H ;apply (sp∙2)=> //.
   Qed.

   Lemma pred2sp2pred_id : forall A (p : PredOM A), sp2pred (pred2sp p) = p.
   Proof.
     move=> A p; rewrite /sp2pred /pred2sp /= ; extensionality r.
     apply SPropAxioms.sprop_ext; do 2 split; move=> // [_ ?] //.
   Qed.

  (** Previous convoluted definition that's secretly "equivalent" to the one above *)
  (*  Definition sp2pp A (sp:ForwardPredTransformer A) : PPSpecMonad A := *)
  (*    let post := fun x => forall (pre : Prop), pre -> proj1_sig sp pre x in *)
  (*    let pre := exists pre, (forall x, post x -> proj1_sig sp pre x) s/\ pre in *)
  (*    ⟨pre, post⟩. *)

  (* Program Definition pp2sp0 A (pp : PPSpecMonad A) : ForwardPredTransformer A := *)
  (*   let sp pre x := pre s/\ (nfst pp -> nsnd pp x) in *)
  (*   exist _ (fun pre x => @mkOver _ (sp pre x) _) _. *)
  (* Next Obligation. destruct H ; assumption. Qed. *)
  (* Next Obligation. move: H0 => [Hpre Hpost] ; split ; auto. Qed. *)

  (* Program Definition pp2sp A (pp : PPSpecMonad A) : ForwardPredTransformer A := *)
  (*   let sp pre x : Prop := *)
  (*       forall (sp: ForwardPredTransformer A), *)
  (*         (forall x pre', pre' s/\ nsnd pp x -> proj1_sig sp pre' x) -> *)
  (*             proj1_sig sp pre x in *)
  (*   exist _ (fun pre x => @mkOver _ (sp pre x) _) _. *)
  (* Next Obligation. *)
  (*   move: (H (pp2sp0 pp)) => H0. *)
  (*   apply (fun f => over (H0 f)).  *)
  (*   cbv ; intuition. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   move: (H0 sp H1). apply (proj2_sig sp). assumption. *)
  (* Qed. *)

  (* Lemma pp2sp01 A (pp:PPSpecMonad A) : *)
  (*   pp2sp pp ≤[ForwardPredTransformer] pp2sp0 pp. *)
  (* Proof. *)
  (*   cbv. *)
  (*   move=> p x H. *)
  (*   move: (H (pp2sp0 pp)) => H0. *)
  (*   apply H0. *)
  (*   cbv ; intuition. *)
  (* Qed. *)

  (* Lemma sp2pp_pp2sp_loop A (pp:PPSpecMonad A) : *)
  (*   sp2pp (pp2sp pp) ≤[PPSpecMonad] pp. *)
  (* Proof. *)
  (*   cbv. *)
  (*   split. *)
  (*   - move=> ?; exists True;split. *)
  (*     move=> ? H ? ?; apply H. *)
  (*     all:intuition. *)
  (*   - move=> x H. *)
  (*     simple refine (_ (H True stt (pp2sp0 ⟨True, nsnd pp⟩) _)); cbv ; intuition. *)
  (* Qed. *)

  (* Lemma pp2sp_sp2pp_loop A (sp:ForwardPredTransformer A) : *)
  (*   sp ≤[ForwardPredTransformer] pp2sp (sp2pp sp). *)
  (* Proof. *)
  (*   cbv. *)
  (*   intuition. *)
  (*   specialize (H0 x). *)
  (*   apply H0. *)
  (*   split. exact (over H). *)
  (*   intros ; move: H ; apply (proj2_sig sp) ; intuition. *)
  (* Qed. *)

  (* Lemma sp_pp_adjunction A pp (sp : ForwardPredTransformer A) : *)
  (*   sp2pp sp ≤[PPSpecMonad] pp <-> sp ≤[ForwardPredTransformer] pp2sp pp. *)
  (* Proof. *)
  (*   cbv ; split. *)
  (*   - dintuition. apply H0. *)
  (*     split. exact (over H). *)
  (*     apply q. intros ; move:H ; apply (proj2_sig sp) ; intuition. *)
  (*   - dintuition. *)
  (*     exists True. split ; intuition. *)
  (*     apply H1 ; constructor. *)
  (*     simple refine (_ (H True x (H0 True stt)(pp2sp0 ⟨True, nsnd pp⟩) _)); cbv ; intuition. *)
  (* Qed. *)

  Program Definition sp2mr A (sp : ForwardPredTransformer A)
    : MRSpec A :=
    exist _ (fun pre post => exist _ (forall a, proj1_sig sp pre a -> proj1_sig (post a)) _) _.
  Next Obligation.
    cbv ; intuition.
    apply (proj2_sig (post a)).
    auto.
  Qed.
  Next Obligation.
    cbv ; intuition.
    apply Hpost. apply H. move: H0 ; apply (proj2_sig sp) ; auto.
  Qed.

  Program Definition mr2sp A (mr : MRSpec A)
    : ForwardPredTransformer A :=
    exist _ (fun pre a => @mkOver _ (pre s/\ forall post, proj1_sig (proj1_sig mr pre post) -> proj1_sig (post a)) _)_.
  Next Obligation. destruct H ; assumption. Qed.
  Next Obligation.
    move: H0 => [Hpre Hmr] ; split ; [auto|].
    move=> post Hpost. simple refine (Hmr (fun a => exist _ (proj1_sig (post a)) _) _). cbv ; intuition.
    move: Hpost ; apply (proj2_sig mr) ; cbv ; intuition.
  Qed.

  Lemma sp_mr_adjunction A (sp : ForwardPredTransformer A) (mr:MRSpec A) :
     sp2mr sp ≤ mr <-> sp  ≤ mr2sp mr.
  Proof.
    cbv ; intuition.
    exact (over H0).
    move: (H _ _ H1) => [? Hpost].
    apply Hpost ; assumption.
  Qed.
-------------------------end of forgotten section*)
End Adjunctions.


Section WpSpRightKanExtension.
(*-----------------------------a forgotten section
  Let MonoCont := @MonoCont Prop (SProp_op_order) _.
  Import PrePost.
  Import StrongestPostcondition.
  Import SPropNotations.

  Definition ppwp_pairing A (pp : PPSpecMonad A) (w : MonoCont A) : Prop :=
    nfst pp -> proj1_sig w (nsnd pp).

  Definition ppsp_pairing A (pp : PPSpecMonad A) (sp : ForwardPredTransformer A) : Prop :=
    forall a, proj1_sig sp (nfst pp) a -> nsnd pp a.

  Definition wpsp_pairing A (wp: MonoCont A) (sp:ForwardPredTransformer A) : Prop :=
    (forall pre post, let pp := ⟨pre, post⟩ in ppwp_pairing pp wp -> ppsp_pairing pp sp) s/\
    (forall pre post, let pp := ⟨pre, post⟩ in ppsp_pairing pp sp -> ppwp_pairing pp wp).

  Context (M : Monad) (θwp : MonadMorphism M MonoCont)
          (θsp : MonadMorphism M ForwardPredTransformer).
  Context (Hadj : forall A m, wpsp_pairing (θwp A m) (θsp A m)).

  Program Definition wp_ran A B (w: MonoCont B) (m: M A) : ran w (θwp A m) :=
    exist _ (fun a => exist _ (fun p => proj1_sig (θsp A m) (proj1_sig w p) a) _) _.
  Next Obligation.
    cbv. move=> ? ? H ; apply (proj2_sig (θsp A m)) ; apply (proj2_sig w)=> //=.
  Qed.
  Next Obligation.
    move: (Hadj m) ; move => [H1 H2]; cbv ; split.
    - move=> p ; apply H2 => //=.
    - move=> w' Hw' a p.
      refine (H1 _ (fun a => proj1_sig (w' a) p) _ a).
      cbv ; apply Hw'.
   Qed.
---------------------------end of forgotten section*)
End WpSpRightKanExtension.

