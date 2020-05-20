From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.

From Mon Require Export Base.
From Coq Require Import Relation_Definitions Morphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads DijkstraMonadExamples.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.


Section Commutations.
  Context {M:Monad}.

  Definition commute {A B} (ma : M A) (mb : M B) :=
    bind ma (fun a => bind mb (fun b => ret ⟨a,b⟩)) =
    bind mb (fun b => bind ma (fun a => ret ⟨a,b⟩)).

  Definition swap {A B} (ab : A × B) : B × A := ⟨nsnd ab, nfst ab⟩.

  Import FunctionalExtensionality.
  Lemma eq_bind {A B} (m : M A) :
    forall (f1 f2 : A -> M B), (forall a, f1 a = f2 a) -> bind m f1 = bind m f2.
  Proof. move=> ? ? /functional_extensionality -> //. Qed.

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
  Next Obligation. move=> ? ? H ; induction H; sreflexivity. Qed.
  Next Obligation.
    apply sig_eq=> /= ; extensionality a=> /=.
    now do 2 rewrite mon_morph_ret /bind monad_law1.
  Qed.
  Next Obligation.
    apply sig_eq=> /= ; extensionality x=> /=.
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

Section ConverseCommute.
  Context (M1 M2 : Monad).
  Context (W : OrderedMonad).
  Let Wrel := relativeMonad_precomposition typeCat_prod (ordmonad_to_relmon W).

  Context (θ : RelationalEffectObservation0 M1 M2 Wrel).

  Let θapp (A B : Type) := proj1_sig (θ ⟨A , B⟩).

  Definition unitt : Type := unit.

  Require Import Coq.Logic.FunctionalExtensionality.

  Lemma θret (A B : Type) (a : A) (b : B) : θapp A B ⟨ ret a, ret b ⟩ = ret ⟨ a, b ⟩.
    move: (rmm_law1 _ _ _ _ θ ⟨A,B⟩) => /(f_equal proj1_sig) e.
    apply (equal_f e ⟨a, b ⟩).
  Qed.

  Lemma θbind (A1 A2 B1 B2 : Type) (m1 : M1 A1) (f1 : A1 -> M1 B1) (m2 : M2 A2) (f2 : A2 -> M2 B2) : θapp B1 B2 ⟨ bind m1 f1 ,  bind m2 f2 ⟩ = bind (θapp A1 A2 ⟨m1, m2⟩) (fun p => θapp B1 B2 ⟨ f1 (nfst p), f2 (nsnd p) ⟩).
    move: (rmm_law2 _ _ _ _ θ ⟨A1,A2⟩ ⟨B1, B2⟩ (⟨f1, f2⟩)) => /(f_equal proj1_sig) e.
    apply (equal_f e ⟨m1, m2⟩).
  Qed.

  Lemma bind_comm : forall (M : Monad) A1 A2 A3 (f : A1 -> A2) (m : M A1) (k : A2 -> M A3), bind (f <$> m) k = bind m (fun a => k (f a)).
    move=> M A1 A2 A3 f m k //=.
    rewrite /bind (monad_law3 m).
    f_equal; extensionality a; rewrite (monad_law1); reflexivity.
  Qed.

  Program Definition effobs_from_releffobs1 : MonadMorphism M1 W := @mkMorphism _ _ (fun A v => nfst <$> θapp A unitt ⟨ v, ret tt ⟩) _ _.
  Next Obligation.
    rewrite /map θret.
    rewrite /bind /ret monad_law1. reflexivity.
  Qed.
  Next Obligation.
    rewrite bind_comm.
    rewrite <- (monad_law2 (ret tt)) at 1.
    rewrite θbind //.
    rewrite /map /bind monad_law3. f_equal; extensionality a; destruct a as [a []].
    reflexivity.
  Qed.

  Let θ1 := effobs_from_releffobs1.
  
  Program Definition effobs_from_releffobs2 : MonadMorphism M2 W := @mkMorphism _ _ (fun A v => nsnd <$> θapp unitt A ⟨ ret tt, v ⟩) _ _.
  Next Obligation.
    rewrite /map θret.
    rewrite /bind /ret monad_law1. reflexivity.
  Qed.
  Next Obligation.
    rewrite bind_comm.
    rewrite <- (monad_law2 (ret tt)) at 1.
    rewrite θbind //.
    rewrite /map /bind monad_law3. f_equal; extensionality a; destruct a as [[] a]. reflexivity.
  Qed.

  Let θ2 := effobs_from_releffobs2.

  Lemma releffobs_eq_effobs1 : forall A1 A2 c1 c2, θapp A1 A2 ⟨c1, c2⟩ = bind (θ1 A1 c1) (fun a : A1 => bind (θ2 A2 c2) (fun b : A2 => ret ⟨ a, b ⟩)).
    move=> A1 A //= c1 c2.
    rewrite <- (monad_law2 c1) at 1.
    rewrite <- (monad_law1 tt (fun _ => c2)) at 1.
    rewrite θbind /=. rewrite bind_comm.
    f_equal; extensionality a; destruct a as [a1 []].
    rewrite bind_comm //=.
    rewrite <- (monad_law2 c2) at 1. rewrite <- (monad_law1 tt (fun _ => monad_ret M1 a1)).
    rewrite θbind. f_equal; extensionality b; destruct b as [[] a2].
    apply θret.
  Qed.

  Lemma releffobs_eq_effobs2 : forall A1 A2 c1 c2, θapp A1 A2 ⟨c1, c2⟩ = bind (θ2 A2 c2) (fun b : A2 => bind (θ1 A1 c1) (fun a : A1 => ret ⟨ a, b ⟩)).
    move=> A1 A2 //= c1 c2.
    rewrite <- (monad_law2 c2) at 1.
    rewrite <- (monad_law1 tt (fun _ => c1)) at 1.
    rewrite θbind /=. rewrite bind_comm.
    f_equal; extensionality a; destruct a as [[] a2].
    rewrite bind_comm //=.
    rewrite <- (monad_law2 c1) at 1. rewrite <- (monad_law1 tt (fun _ => monad_ret M2 a2)).
    rewrite θbind. f_equal; extensionality b; destruct b as [a1 []].
    apply θret.
  Qed.

  Lemma effobs12_commute : forall A1 A2 c1 c2, commute (θ1 A1 c1) (θ2 A2 c2).
    move=> A1 A2 c1 c2. unfold commute.
    rewrite /commute -releffobs_eq_effobs1 -releffobs_eq_effobs2. reflexivity.
  Qed.

  Let θ' : RelationalEffectObservation0 M1 M2 Wrel := commute_effObs _ _ _ θ1 θ2 effobs12_commute.

  Theorem converse_to_commute_effObs : forall A1 A2 c1 c2,
      proj1_sig (θ ⟨ A1, A2 ⟩) ⟨ c1, c2 ⟩  = proj1_sig (θ' ⟨ A1, A2 ⟩) ⟨ c1, c2 ⟩.
    move=> A1 A2 //= c1 c2. apply releffobs_eq_effobs1.
  Qed.
End ConverseCommute.
