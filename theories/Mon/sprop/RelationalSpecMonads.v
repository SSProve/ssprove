From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Relational Monoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Section UpdateRelationalSpecMonad.
  Context (M1 M2 : monoid) (X1 : monoid_action M1) (X2 : monoid_action M2).

  Definition dom_rel A B : srelation (A × B -> M1 × M2 -> SProp) :=
    pointwise_srelation (A × B) (pointwise_srelation (M1 × M2) SProp_op_order).
  Definition cod_rel : srelation (X1 × X2 -> SProp) :=
    pointwise_srelation (X1 × X2) SProp_op_order.

  Instance dom_rel_ord A B : PreOrder (@dom_rel A B).
  Proof. constructor ; cbv ; intuition. Qed.
  Instance cod_rel_ord : PreOrder cod_rel.
  Proof. constructor ; cbv ; intuition. Qed.

  Import SPropNotations.

  Definition WUpd A B :=
    { f : (A × B -> M1 × M2 -> SProp) -> X1 × X2 -> SProp ≫
      SProper (@dom_rel A B s==> cod_rel) f}. 
  Program Definition retWUpd A B (ab : A × B) : WUpd A B:=
    exist _ (fun p xx => p ab ⟨e M1, e M2⟩) _.
  Next Obligation.
   move=> ? ? H ? ; apply H.
  Qed.

  Program Definition bindWUpd A1 B1 A2 B2
          (wm : WUpd A1 B1) (wf : A1 × B1 -> WUpd A2 B2)
    : WUpd A2 B2 :=
    exist _
            (fun p xx => proj1_sig wm (fun ab mm => proj1_sig (wf ab)
                                              (fun ab mm' => p ab
                                                           ⟨nfst mm' ⋅ nfst mm, nsnd mm' ⋅ nsnd mm⟩) 
                                              ⟨nfst mm ⧕ nfst xx ,
                                               nsnd mm ⧕ nsnd xx⟩) xx) _.
  Next Obligation.
    move=> ? ? H ? ; apply (proj2_sig wm).
    cbv ; intros ab mm ; apply (proj2_sig (wf ab)).
    cbv ; intros ? ? ; apply H.
  Qed.

  Definition WUpd_rel A B : srelation (WUpd A B) :=
    fun m1 m2 => forall p, cod_rel (proj1_sig m1 p) (proj1_sig m2 p).
  Instance WUpd_ord A B : PreOrder (@WUpd_rel A B).
  Proof. constructor ; cbv ; intuition. Qed.

  (* We do not prove the monadic laws since they would
   rely on funext. Instead we let them be proved on a case
   by case basis, which should be trivial when both the monoid
   and action laws hold definitionally *)
  Program Definition UpdRelSpecFromLaws pf1 pf2 pf3 : RelationalSpecMonad :=
    @mkRSM WUpd retWUpd bindWUpd pf1 pf2 pf3 WUpd_rel WUpd_ord _.
  Next Obligation.
    cbv ; move=> x ? Hm ? ? Hf ? ? H. move: (Hm _ _ H).
    apply (proj2_sig x) => ? ? ; apply Hf.
  Qed.

  Import FunctionalExtensionality.

  Program Definition UpdRelSpec := UpdRelSpecFromLaws _ _ _.
  Next Obligation.
    apply sig_eq. extensionality p0 ; extensionality xx.
    cbv. f_equal.
    extensionality ab ; extensionality mm' ; rewrite !monoid_law2 //.
    rewrite !monact_unit //.
  Qed.

  Next Obligation.
    apply sig_eq. extensionality p.
    cbv. extensionality ab ; f_equal. extensionality ab0 ; extensionality mm'.
    rewrite !monoid_law1 //.
  Qed.

  Next Obligation.
    apply sig_eq; extensionality p ; extensionality xx.
    cbv.
    let t :=
        f_equal ; [let Hab := fresh "ab" in
        let Hmm := fresh "mm" in
        extensionality Hab ; extensionality Hmm |..] in
    do 3 t.
    rewrite !monoid_law3 //.
    rewrite !monact_mult //.
  Qed.

End UpdateRelationalSpecMonad.


Section ReaderRelationalSpecMonad.
  Context (S : Type).

  Program Definition ReaderRSM : RelationalSpecMonad :=
    @UpdRelSpecFromLaws _ _ (oneAction S) (oneAction S) _ _ _.

End ReaderRelationalSpecMonad.

Section WriterRelationalSpecMonad.
  Context (O : Type).

  Let trivAct := trivialAction (strict_monoid (listMonoid O)).
  Program Definition WriteRSM : RelationalSpecMonad :=
    @UpdRelSpecFromLaws _ _ trivAct trivAct _ _ _.
End WriterRelationalSpecMonad.


Section UpdateMonad.
  Context (M: monoid) (X : monoid_action M).

  Definition UpdMonadCarrier (A:Type) : Type := X -> A × M.
  Definition UpdMonadRet A (a:A) : UpdMonadCarrier A := fun x => ⟨a, e M⟩.
  Definition UpdMonadBind A B (m:UpdMonadCarrier A)
             (f : A -> UpdMonadCarrier B) : UpdMonadCarrier B :=
    fun x =>
      let mx := m x in
      let fx := f (nfst mx) (nsnd mx ⧕ x) in
      ⟨nfst fx, nsnd fx ⋅ nsnd mx⟩.

  Definition UpdateMonadFromLaws pf1 pf2 pf3 : Monad :=
    @mkMonad UpdMonadCarrier UpdMonadRet UpdMonadBind pf1 pf2 pf3.

  Import FunctionalExtensionality.
  Program Definition UpdateMonad : Monad := UpdateMonadFromLaws _ _ _.
  Next Obligation.
    cbv ; extensionality x. rewrite !monact_unit monoid_law2 //.
  Qed.

  Next Obligation.
    cbv ; extensionality x ; rewrite monoid_law1 //.
  Qed.

  Next Obligation.
    cbv ; extensionality x. rewrite - !monact_mult !monoid_law3 //.
  Qed.
End UpdateMonad.


Section UpdateRelationalEffectObservation.
  Context (M1 M2 : monoid) (X1 : monoid_action M1) (X2 : monoid_action M2).
  Let MM := MonadsToRCM (UpdateMonad X1) (UpdateMonad X2).
  Let W := UpdRelSpec X1 X2.

  Program Definition UpdateREO : RelationalEffectObservation MM W :=
    @mkREO _ _ (fun A B ff =>
                  exist _
                          (fun p xx =>
                             let yy := apply_prod (dfst ff) xx in
                             let yl := nfst yy in
                             let yr := nsnd yy in
                             p ⟨nfst yl, nfst yr⟩ ⟨nsnd yl, nsnd yr⟩) _
               ) _ _.
  Next Obligation. move=> ? ? H ? ; apply H. Qed.
End UpdateRelationalEffectObservation.

Section HeapSmallFootprint.
  Context (Loc Val : Type).
  Program Definition Heap :=
    @pointwiseActionFromLaws Loc _ (overwriteAction Val) _ _.

  Definition StHeap := UpdateMonad Heap.
  Definition StHeapRCM := DiagonalRCM StHeap.
  Program Definition WHeapRSM :=
    @UpdRelSpecFromLaws _ _ Heap Heap _ _ _.
  Program Definition θHeapREO :=
    UpdateREO Heap Heap.
End HeapSmallFootprint.



(* Section ContinuationRelationalSpecMonad. *)
(*   Context (A B Ans : Type) (ϕ : A × B -> Ans) (ψ : Ans -> A × B) *)
(*           (Ans_rel : srelation Ans) `{PreOrder _ Ans_rel}. *)
(*   Context (M : RelationalComputationMonad) (AB := topRel A B) *)
(*           (α : forall Xl Xr, (topRel Xl Xr R==> AB) -> (M Xl Xr R==> AB)). *)

(*   (* potential variations with A × B instead of Ans ? *) *)
(*   Definition W Xl Xr := (Xl × Xr -> Ans) -> Ans. *)

(*   Definition retW Xl Xr (x : Xl × Xr) : W Xl Xr := *)
(*     fun p => p x. *)
(*   Definition bindW Xl Xr Yl Yr (wm : W Xl Xr) (wf : Xl × Xr -> W Yl Yr) *)
(*     : W Yl Yr := *)
(*     fun p => wm (fun x => wf x p). *)

(*   Definition MM Xl Xr := let MX := M Xl Xr in tleft MX × tright MX. *)
(*   (* Definition θ Xl Xr (m : MM Xl Xr) : W Xl Xr := *) *)
(*   (*   fun p =>  *) *)

(* End ContinuationRelationalSpecMonad. *)

Section StateRelationalSpecMonad.

  Context (S:Type).
  Definition WSt A B := (A × B -> S × S -> Prop) -> S × S -> Prop.
  Definition retWSt A B (x : A × B) : WSt A B := fun p s => p x s.
  Definition bindWSt A1 B1 A2 B2
             (wm : WSt A1 B1) (f : A1 × B1 -> WSt A2 B2) : WSt A2 B2 :=
    fun p => wm (fun x1 s => f x1 p s).

  Definition θSt A B (m : (S -> A × S) × (S -> B × S)) : WSt A B :=
    fun p ss => let r := apply_prod m ss in
             let r1 := nfst r in
             let r2 := nsnd r in
             p ⟨nfst r1, nfst r2⟩ ⟨nsnd r1, nsnd r2⟩. 

  (* (S -> Prop) × (S -> Prop) --> S × S -> Prop  *)

End StateRelationalSpecMonad.