From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Section Monoid.
  Record monoid :=
    mkMonoid
      { monoid_carrier :> Type
      ; monoid_unit : monoid_carrier
      ; monoid_mult : monoid_carrier -> monoid_carrier -> monoid_carrier
      ; monoid_law1 : forall m, monoid_mult monoid_unit m = m
      ; monoid_law2 : forall m, monoid_mult m monoid_unit = m
      ; monoid_law3 : forall m1 m2 m3,
          monoid_mult (monoid_mult m1 m2) m3 = monoid_mult m1 (monoid_mult m2 m3)
      }.

  Definition e := monoid_unit.
End Monoid.

Notation "x ⋅ y" := (monoid_mult x y) (at level 55).

Section MonoidAction.
  
  Record monoid_action (M : monoid) :=
    mkAction
      { monact_carrier :> Type
      ; monact_action : M -> monact_carrier -> monact_carrier
      ; monact_unit : forall x, monact_action (e M) x = x
      ; monact_mult : forall m1 m2 x, monact_action (m1 ⋅ m2) x = monact_action m1 (monact_action m2 x)
      }.
End MonoidAction.

Notation "m ⧕ x" := (monact_action m x) (at level 55).


Section MonoidExamples.
  Program Definition endMonoid (X : Type) : monoid :=
    @mkMonoid (X -> X) id (fun f g x => f (g x)) _ _ _.

  Program Definition unitMonoid : monoid :=
    @mkMonoid unit tt (fun _ _ => tt) _ _ _.
  (* This does not solve the goal but the latter does ??? *)
  Solve Obligations with move: m => [] //.
  Solve Obligations with destruct m ; reflexivity.

  Program Definition oneMonoid : monoid := endMonoid False.

  Import FunctionalExtensionality.
  Program Definition pointwiseMonoid (X:Type) (M:monoid) : monoid :=
    @mkMonoid (X -> M) (fun _ => e M) (fun f g x => f x ⋅ g x) _ _ _.
  Next Obligation. extensionality y ; rewrite monoid_law1 //. Qed.
  Next Obligation. extensionality y ; rewrite monoid_law2 //. Qed.
  Next Obligation. extensionality y ; rewrite monoid_law3 //. Qed.

  Program Definition listMonoid (X:Type) : monoid :=
    @mkMonoid (list X) nil (@app _) _ (@List.app_nil_r _) (@List.app_assoc_reverse _).

  Program Definition prodMonoid (M1 M2:monoid) : monoid :=
    @mkMonoid (M1 × M2) ⟨e M1, e M2⟩ (fun x y => ⟨nfst x ⋅ nfst y, nsnd x ⋅ nsnd y⟩)
              _ _ _.
  Next Obligation. rewrite !monoid_law1 //. Qed.
  Next Obligation. rewrite !monoid_law2 //. Qed.
  Next Obligation. rewrite !monoid_law3 //. Qed.

  Program Definition optionMonoid (X:Type) : monoid :=
    @mkMonoid (option X) None (fun m1 m2 => match m1 with
                                         | None => m2
                                         | Some x => Some x end) _ _ _.
  Next Obligation. move: m => [] //. Qed.
  Next Obligation. move: m1 m2 m3 => [?|] [?|] [?|] //. Qed.

  Import SPropNotations.
  Program Definition overwriteMonoid (X:Type) : monoid :=
    @mkMonoid { f : X -> X ≫ s∃ (m: optionMonoid X), forall x, Some (f x) ≡ m⋅(Some x)}
              (Sexists _ id _)
              (fun f g => Sexists _ (Spr1 f \o Spr1 g) _) _ _ _.
  Next Obligation. exists None. move=> ? //. Qed.
  Next Obligation.
    move: f g => [? [mf Hf]] [? [mg Hg]].
    exists (@monoid_mult (optionMonoid X) mf mg).
    move=> ? ; move: mf mg Hf Hg => [?|] [?|] Hf Hg /= ; try by apply Hf.
    all: eapply (sEq_trans (Hf _)); apply Hg.
  Qed.
  Next Obligation. destruct m as [f [m e]]. compute. f_equal.
    apply ax_proof_irrel.
  Qed.
  Next Obligation. destruct m as [f [m e]]. compute. f_equal.
    apply ax_proof_irrel.
  Qed.
  Next Obligation. compute. f_equal. apply ax_proof_irrel. Qed.

End MonoidExamples.

Section ActionExamples.
  Program Definition multAction (M:monoid) : monoid_action M :=
    @mkAction M M (fun m1 m2 => m1 ⋅ m2) _ _.
  Next Obligation. rewrite monoid_law1 //. Defined.
  Next Obligation. rewrite monoid_law3 //. Defined.

  Program Definition trivialAction (M : monoid) : monoid_action M :=
    @mkAction M unit (fun _ x => x) _ _.

  Program Definition endAction (X:Type) : monoid_action (endMonoid X) :=
    @mkAction _ X (fun f x => f x) _ _. 

  Program Definition unitAction (X:Type) : monoid_action unitMonoid :=
   @mkAction _ X (fun _ x => x) _ _.

  Program Definition oneAction (X:Type) : monoid_action oneMonoid :=
    @mkAction _ X (fun _ x => x) _ _.

  Section PointwiseAction.
    Context (A:Type) (M:monoid) (X:monoid_action M).
    Let AM := pointwiseMonoid A M.
    Definition pointwise_action (m:AM) (x : A -> X) (a:A) := m a ⧕ x a.

    Definition pointwiseActionFromLaws pf1 pf2 :=
      @mkAction AM (A -> X) pointwise_action pf1 pf2.

    Import FunctionalExtensionality.
    Program Definition pointwiseAction := pointwiseActionFromLaws _ _.
    Next Obligation. cbv ; extensionality a ; rewrite monact_unit //. Qed.
    Next Obligation. cbv ; extensionality a ; rewrite monact_mult //. Qed.

  End PointwiseAction.

  Section ProdAction.
    Context (M1 M2: monoid) (X1: monoid_action M1) (X2: monoid_action M2).
    Let M12 := prodMonoid M1 M2.
    Let X12 := X1 × X2.
    Definition product_action (m12 : M12) (x12:X12) :=
      ⟨nfst m12 ⧕ nfst x12, nsnd m12 ⧕ nsnd x12⟩.
    Definition prodActionFromLaws pf1 pf2 :=
      @mkAction M12 (X1 × X2) product_action pf1 pf2.
    Program Definition prodAction := prodActionFromLaws _ _.
    Next Obligation. rewrite /product_action 2!monact_unit //. Qed.
    Next Obligation. rewrite /product_action 2!monact_mult //. Qed.
  End ProdAction.

  Program Definition optionAction (X:Type) : monoid_action (optionMonoid X):=
    @mkAction _ X (fun m x => match m with None => x | Some x' => x' end) _ _.
  Next Obligation. move: m1 m2 => [?|] [?|] //. Qed.

  Program Definition overwriteAction (X:Type)
    : monoid_action (overwriteMonoid X) :=
    @mkAction _ X (fun f x => Spr1 f x) _ _.
End ActionExamples.

Section MonoidStrictification.
  (* Given any monoid with monoid laws holding propositionally,
     we can turn it into one where the laws hold definitionally *)
  Context (M : monoid).
  Import SPropNotations.

  Definition SM := { f : M -> M ≫ s∃ m, forall m', f m' ≡ m ⋅ m'}.
  Program Definition se : SM := Sexists _ id _.
  Next Obligation.
    exists (e M). intros ; rewrite monoid_law1 //.
  Qed.

  Program Definition smult (sm1 sm2 : SM) : SM :=
    Sexists _ (Spr1 sm1 \o Spr1 sm2) _.
  Next Obligation.
    move:sm1 sm2=> [? [m1 H1]] [? [m2 H2]].
    exists (m1 ⋅ m2) ; move=> m /=.
    rewrite monoid_law3. eelim (H2 _). eelim (H1 _) => //.
  Qed.

  Program Definition strict_monoid := @mkMonoid SM se smult _ _ _.

  Program Definition embed (m:M) : SM := Sexists _ (monoid_mult m) _.
  Next Obligation. exists m ; move=> ? //. Qed.

  Definition project (sm : SM) : M := Spr1 sm (e M).

  Lemma embed_project_id : forall m, project (embed m) = m.
  Proof. intro. cbv. rewrite monoid_law2 //. Qed.

  Lemma Ssig_sEq : forall (A : Type) (P : A -> SProp) (mx my : {x : A ≫ P x}),
       Spr1 mx ≡ Spr1 my -> mx ≡ my.
  Proof.
    intros A P [mx ?] [my ?] H. simpl in H.
    induction H. compute. f_equal. apply ax_proof_irrel.
  Qed.

  Import SPropAxioms.
  Lemma project_embed_id : forall sm, embed (project sm) ≡ sm.
  Proof.
    intro sm. apply Ssig_sEq ; funext m0.
    cbv. move: (Spr2 sm) => [m Hm].
    pose (H0 := Hm m0).
    apply sEq_sym in H0.
    unshelve eapply (sEq_trans _ H0).
    f_equiv. pose (He := Hm (e M)).
    apply (sEq_trans He).
    rewrite monoid_law2 //.
   Qed.
  Next Obligation. compute. destruct m. f_equal. apply ax_proof_irrel. Qed.
  Next Obligation. compute. destruct m. f_equal. apply ax_proof_irrel. Qed.
  Next Obligation. compute. f_equal. apply ax_proof_irrel. Qed.

End MonoidStrictification.

(* A strictified version of the free monoid on a type O *)
(* Useful to obtain update monads satisfying definitional monad laws *)
Section StrictList.
  Context (O:Type).
  Definition strict_list_monoid : monoid := strict_monoid (listMonoid O).
  Import SPropNotations.
  Definition inject (o:O) : strict_list_monoid :=
    @embed (listMonoid O) (cons o nil).
  Definition snil : strict_list_monoid :=
    @embed (listMonoid O) nil.
End StrictList.
