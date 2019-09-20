From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads DijkstraMonadExamples.
From Relational Require Import RelativeMonads RelativeMonadExamples.

Section Commutations.
  Context {M:Monad}.

  Definition commute {A B} (ma : M A) (mb : M B) :=
    bind ma (fun a => bind mb (fun b => ret ⟨a,b⟩)) =
    bind mb (fun b => bind ma (fun a => ret ⟨a,b⟩)).

  Definition swap {A B} (ab : A × B) : B × A := ⟨nsnd ab, nfst ab⟩.

  Lemma eq_bind {A B} (m : M A) :
    forall (f1 f2 : A -> M B), (forall a, f1 a = f2 a) -> bind m f1 = bind m f2.
  Proof. move=> ? ? /funext -> //. Qed.

  Lemma map_ret {A B} (f : A -> B) (a : A) : f <$> ret a = @ret M _ (f a).
  Proof. rewrite /map /bind monad_law1 //. Qed.

  Lemma commute_elim {A B C} (f : A × B -> M C) (ma : M A) (mb : M B) :
    commute ma mb ->
    bind ma (fun a=> bind mb (fun b => f ⟨a,b⟩)) = bind mb (fun b=> bind ma (fun a=> f ⟨a,b⟩)).
  Proof.
    rewrite /commute=> /(f_equal (fun t => bind t f)).
    rewrite /bind !monad_law3. repeat rewrite -/bind.
    under eq_bind => a do (rewrite /bind !monad_law3 -/bind ; under eq_bind => b do rewrite monad_law1).
    under (@eq_bind B _) => a do (rewrite /bind !monad_law3 -/bind ; under eq_bind => b do rewrite monad_law1).
    done.
  Qed.

  Lemma commute_sym {A B} (ma : M A) (mb : M B)
    : commute ma mb -> commute mb ma.
  Proof.
    move=> /(commute_elim (fun p => ret (swap p))) //=.
  Qed.

  Import FunctionalExtensionality.
  Lemma commute_ret {A B} (a : A) (mb : M B) : commute (ret a) mb.
  Proof.
    rewrite /commute /bind monad_law1 ; f_equal.
    extensionality a2; rewrite monad_law1 //.
  Qed.

  Ltac apply_commute_elim H :=
    match goal with
    | [|- context c [bind ?m1 (fun a1 => bind ?m2 (fun a2 => @?f a1 a2))]] =>
      move: (commute_elim (fun p => f (nfst p) (nsnd p)) m1 m2 H) => /= ->
    end.


  Lemma commute_bind {A1 A2 B} (m1 : M A1) (f1 : A1 -> M A2) (m2:M B)
    : commute m1 m2 -> (forall a1, commute (f1 a1) m2) -> commute (bind m1 f1) m2.
  Proof.
    move=> Hm Hf ; rewrite /commute /bind monad_law3. repeat rewrite -/bind.
    under eq_bind => a1 do rewrite (Hf a1).
    apply_commute_elim Hm.
    under eq_bind => b do rewrite /bind -monad_law3.
    done.
  Qed.
End Commutations.

Ltac apply_commute_elim H :=
  match goal with
  | [|- context c [bind ?m1 (fun a1 => bind ?m2 (fun a2 => @?f a1 a2))]] =>
    move: (commute_elim (fun p => f (nfst p) (nsnd p)) m1 m2 H) => /= ->
  end.

Section FromFreeCommute.
  Context (W : OrderedMonad).
  Context {S1:Type} {P1:S1 -> Type} (wop1 : forall s1, W (P1 s1)).
  Context {S2:Type} {P2:S2 -> Type} (wop2 : forall s2, W (P2 s2)).
  Context (Hcom : forall s1 s2, commute (wop1 s1) (wop2 s2)).

  Let θ1 := OpSpecEffObs wop1.
  Let θ2 := OpSpecEffObs wop2.

  Import FunctionalExtensionality.
  Lemma fromFreeCommute A1 A2 : forall c1 c2, commute (θ1 A1 c1) (θ2 A2 c2).
  Proof.
    move=> c1.
    elim: c1 A2 => [a1|s1 k1 IH1] A2 c2; first by apply commute_ret.
    simpl; apply commute_bind ; last by move=> a1; apply: IH1.
    elim: c2 => [a2| s2 k2 IH2] ; first by apply commute_sym, commute_ret.
    simpl ; apply commute_sym, commute_bind; first by apply commute_sym, Hcom.
    move=> a2; apply commute_sym, IH2.
  Qed.

End FromFreeCommute.

Section CommuteEffectObs.
  Context (W : OrderedMonad) (M1 M2:Monad).
  Context (θ1 : MonadMorphism M1 W) (θ2 : MonadMorphism M2 W).
  Context (Hcom : forall A1 A2 c1 c2, commute (θ1 A1 c1) (θ2 A2 c2)).

  Definition Wrel : RelationalSpecMonad0 :=
    relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon W).

  Import SPropNotations.
  Import FunctionalExtensionality.
  Program Definition commute_effObs : RelationalEffectObservation0 M1 M2 Wrel
    :=
      mkREO0 M1 M2 Wrel
             (fun '⟨A1,A2⟩ => ⦑fun '⟨c1,c2⟩ => bind (θ1 A1 c1) (fun a1=> bind (θ2 A2 c2)
                                               (fun a2=> ret ⟨a1,a2⟩))⦒) _ _.
  Next Obligation. elim: H ; sreflexivity. Qed.
  Next Obligation. do 2 rewrite mon_morph_ret /bind monad_law1; done. Qed.
  Next Obligation.
    rewrite mon_morph_bind {1 2}/bind monad_law3; repeat rewrite -/bind.
    under eq_bind => a.
      under eq_bind => b.
        rewrite mon_morph_bind /bind monad_law3 ; repeat rewrite -/bind.
        over.
      apply_commute_elim (Hcom _ _ (nfst f a) (nsnd x)).
      over.
    rewrite /bind monad_law3; repeat rewrite -/bind.
    f_equal ; extensionality a1.
    rewrite /bind monad_law3; repeat rewrite -/bind.
    f_equal ; extensionality a2.
    rewrite /bind monad_law1 //.
  Qed.

End CommuteEffectObs.
