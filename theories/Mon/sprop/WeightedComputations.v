From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality List.

From Mon Require Export Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads Monoid DijkstraMonadExamples.

Section WeightedComputations.
  Import List.

  Context (I:monoid).

  Context (Hcomm : forall (x y: I), x ⋅ y = y ⋅ x).

  Import ListNotations.

  Lemma flat_map_app {A B} l1 : forall l2 (f : A -> list B),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    induction l1 as [|? ? IHl] ; intros;
      [|simpl; rewrite <- app_assoc; f_equal ; rewrite IHl]; reflexivity.
  Qed.

  Program Definition Wc : Monad :=
    @mkMonad (fun X => list (I × X))
            (fun X x => [⟨e I, x⟩])
            (fun A B m0 f => flat_map (fun p1 => map (fun p2 => ⟨nfst p1 ⋅ nfst p2, nsnd p2⟩) (f (nsnd p1))) m0)
            _ _ _.
  Next Obligation.
    under map_ext => p2 do rewrite monoid_law1 ; rewrite map_id app_nil_r //.
  Qed.
  Next Obligation.
    elim: c => [//| ? ? /= ->] ; by rewrite monoid_law2.
  Qed.

  Next Obligation.
    elim: c => [//| /= ? ? IH].

    rewrite flat_map_app; f_equal ; last exact IH.
    rewrite !flat_map_concat_map !concat_map ; f_equal.
    rewrite !map_map.
    apply map_ext=> x; rewrite /= map_map.
    apply map_ext=> y /= ; rewrite monoid_law3 //.
  Qed.

  (** Old dev *)

  (* Lemma Forall_app {A} (f: A -> Prop) l1 : *)
  (*   forall l2, Forall f (l1 ++ l2) <-> Forall f l1 /\ Forall f l2. *)
  (* Proof. *)
  (*   induction l1 as [|? ? IH]. *)
  (*   intros ; simpl ; intuition. *)
  (*   intros ; simpl ; split. *)
  (*   intros H ; inversion H. apply IH in H3. destruct H3. *)
  (*   split ; [constructor|] ; assumption. *)
  (*   intros [H1 H2] ; inversion H1. *)
  (*   constructor; [|apply IH; split] ; assumption. *)
  (* Qed. *)

  (* Lemma Forall_map {A B} (f : A -> B) (p : B -> Prop) l : *)
  (*   Forall p (map f l) <-> Forall (fun x => p (f x)) l. *)
  (* Proof. *)
  (*   induction l as [|? ? IH]. *)
  (*   split ; constructor. *)
  (*   simpl ; split ; intros H ; inversion H ; constructor ; try (apply IH) ; assumption. *)
  (* Qed. *)

  (* Lemma in_flat_map {A B} (f : A -> list B) y l : In y (flat_map f l) -> exists x, In x l /\ In y (f x). *)
  (* Proof. *)
  (*   induction l. *)
  (*   intros []. *)
  (*   simpl ; intros H%in_app_or. destruct H. exists a ; split ; [left ; reflexivity | *)
  (*   assumption]. *)
  (*   specialize (IHl H). destruct IHl as [x0 []]. *)
  (*   exists x0 ; split ; [right|] ; assumption. *)
  (* Qed. *)

  (* Lemma Forall_flat_map {A B} (f : A -> list B) (p : B -> Prop) l : *)
  (*   Forall p (flat_map f l) <-> (forall x y, In x l -> In y (f x) -> p y). *)
  (* Proof. *)
  (*   induction l. *)
  (*   simpl ; split. intros ? ? ? []. constructor. *)
  (*   simpl ; split. *)
  (*   + intros H%Forall_app. destruct H. *)
  (*     intros ? ? []. rewrite Forall_forall in H. subst ; apply H. *)
  (*     rewrite IHl in H0. apply H0. assumption. *)

  (*   + intros. apply Forall_forall. *)
  (*     intros y Hy. apply in_app_or in Hy ; destruct Hy.  *)
  (*     apply (H a). left ; reflexivity. assumption. *)
  (*     apply in_flat_map in H0. destruct H0 as [x0 []]. *)
  (*     apply (H x0) ; [right|] ; assumption. *)
  (* Qed. *)

  (* Program Definition WcProp_alg : MonadAlgebra Wc := *)
  (* mkMonadAlgebra Wc (I -> Prop) *)
  (*                 (fun m r => Forall (fun x => snd x (fst x ∗ r)) m) _ _. *)

  (* Next Obligation. *)
  (*   extensionality x. apply prop_ext ; split. *)
  (*   intros H ; apply Forall_inv in H ; simpl in H. rewrite lunit in H. assumption. *)
  (*   constructor. *)
  (*   simpl. rewrite lunit ; assumption. *)
  (*   constructor. *)
  (* Qed. *)

  (* Next Obligation. *)
  (*   extensionality r. apply prop_ext. rewrite !Forall_flat_map. *)
  (*   simpl. split. intros. *)
  (*   apply in_map_iff in H1. *)
  (*   destruct y. *)
  (*   destruct H1 as [? []].  subst . *)
  (*   simpl. *)
  (*   injection H1 ; intros ; subst. *)
  (*   rewrite (comm (fst x)). rewrite <- assoc. *)
  (*   enough (forall x0, In x0 (f (snd x)) -> snd x0 (fst x0 ∗ (fst x ∗ r))). *)
  (*   exact (H3 x0 H2). *)
  (*   apply (H x (fst x, fun r => forall x1, In x1 (f (snd x)) -> snd x1 (fst x1 ∗ r))). assumption. *)
  (*   left. f_equal. rewrite runit. reflexivity. *)
  (*   extensionality r0. apply prop_ext ; split ; intros Hall. *)
  (*   rewrite Forall_forall in Hall. *)
  (*   assumption. *)
  (*   rewrite Forall_forall. *)
  (*   assumption. *)

  (*   intros H x y Hx [H1 | H1]. subst. simpl. *)
  (*   rewrite Forall_forall. intros. *)
  (*   rewrite runit. rewrite assoc. rewrite (comm (fst x0)). *)
  (*   apply (H x (fst x ∗ fst x0, snd x0)). *)
  (*   assumption. *)
  (*   change (In _ (map ?f ?l)) with (In (f x0) (map f l)). *)
  (*   apply in_map. *)
  (*   assumption. *)
  (*   contradiction. *)
  (* Qed. *)

  (* Program Definition WcProp_oalg : OrderedAlgebra Wc := *)
  (*   mkOrderedAlgebra WcProp_alg (PredOP_order I) _. *)
  (* Next Obligation. *)
  (*  rewrite Forall_flat_map in H0 |- *. *)
  (*  intros [] [] Hx [Hy|[]]. injection Hy ; intros ; subst ; simpl. *)
  (*  apply H. apply (H0 (i,a0) (i ∗ e, k' a0) Hx). *)
  (*  left ; reflexivity. *)
  (* Qed. *)

  (* Definition WcSpec := WPSpecMonad WcProp_oalg. *)

  (* Definition WcWP : Dijkstra WcSpec := D_wp _ _. *)

End WeightedComputations.