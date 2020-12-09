(*
  This file defines an inductive type [chUniverse] and a total order on that type, which
  is then used to show that [chUniverse] forms a [choiceType].
 *)


From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings Rules
  StateTransfThetaDens StateTransformingLaxMorph FreeProbProg.
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.

(* Basic structure *)

Inductive chUniverse :=
| chZero
| chUnit
| chNat
| chBool
| chProd (A B : chUniverse).

Fixpoint chElement (U : chUniverse) : choiceType :=
  match U with
  | chZero => void_choiceType
  | chUnit => unit_choiceType
  | chNat => nat_choiceType
  | chBool => bool_choiceType
  | chProd U1 U2 => prod_choiceType (chElement U1) (chElement U2)
  end.

Coercion chElement : chUniverse >-> choiceType.

Section chUniverseTypes.

  Fixpoint chUniverse_test (u v : chUniverse) : bool :=
    match u, v with
    | chZero , chZero => true
    | chNat , chNat => true
    | chUnit , chUnit => true
    | chBool , chBool => true
    | chProd a b , chProd a' b' => chUniverse_test a a' && chUniverse_test b b'
    | _ , _ => false
    end.

  Definition chUniverse_eq : rel chUniverse :=
    fun u v => chUniverse_test u v.

  Lemma chUniverse_eqP : Equality.axiom chUniverse_eq.
  Proof.
    move=> x y.
    induction x as [ | | | | x1 ih1 x2 ih2] in y |- *.
    all: destruct y as [ | | | | y1 y2].
    all: simpl.
    all: try solve [ right ; discriminate ].
    all: try solve [ left ; reflexivity ].
    destruct (ih1 y1), (ih2 y2).
    all: simpl.
    all: subst.
    all: try solve [ right ; congruence ].
    left. reflexivity.
  Qed.

  Lemma chUniverse_refl :
    ∀ u, chUniverse_eq u u.
  Proof.
    intros u. destruct chUniverse_eq eqn:e.
    - constructor.
    - move: e => /chUniverse_eqP []. reflexivity.
  Qed.

  Canonical chUniverse_eqMixin := EqMixin chUniverse_eqP.
  Canonical chUniverse_eqType :=
    Eval hnf in EqType chUniverse chUniverse_eqMixin.

  Fixpoint chUniverse_lt (t1 t2 : chUniverse) :=
  match t1, t2 with
  | chZero, chZero   => false
  | chZero, _ => true
  | chUnit, chZero => false
  | chUnit, chUnit => false
  | chUnit, _ => true
  | chBool, chZero => false
  | chBool, chUnit => false
  | chBool, chBool => false
  | chBool, _ => true
  | chNat, chZero => false
  | chNat, chUnit => false
  | chNat, chBool => false
  | chNat, chNat => false
  | chNat, _ => true
  | chProd u1 u2, chProd w1 w2 =>
    (chUniverse_lt u1 w1) ||
    (chUniverse_eq u1 w1 && chUniverse_lt u2 w2)
  | chProd _ _, _ => false
  end.


  Definition chUniverse_leq (t1 t2 : chUniverse) :=
    chUniverse_eq t1 t2 || chUniverse_lt t1 t2.

  Lemma chUniverse_lt_transitive : transitive (T:=chUniverse) chUniverse_lt.
  Proof.
    intros v u w h1 h2.
    induction u as [ | | | | u1 ih1 u2 ih2] in v, w, h1, h2 |- *.
    - destruct w. all: try reflexivity.
      destruct v. all: discriminate.
    - destruct v. all: try discriminate.
      + destruct w. all: try discriminate.
        reflexivity.
      + destruct w. all: try discriminate.
        all: reflexivity.
      + destruct w. all: try discriminate.
        reflexivity.
    - destruct w. all: try reflexivity.
      + destruct v. all: discriminate.
      + destruct v. all: discriminate.
      + destruct v. all: discriminate.
      + destruct v. all: discriminate.
    - destruct v. all: try discriminate.
      + destruct w. all: try discriminate.
        reflexivity.
      + destruct w. all: try discriminate.
        reflexivity.
    - destruct w. all: try discriminate; destruct v; try discriminate.
      simpl.
      apply/orP.
      simpl in h1, h2.
      move: h1. move/orP => h1.
      move: h2. move/orP => h2.
      destruct h1 as [h1|h1], h2 as [h2|h2].
      + left.
        apply (ih1 v1). all: assumption.
      + move: h2. move /andP => [h2 h2'].
        move: h2. move /eqP => h2. destruct h2.
        left. assumption.
      + move: h1. move /andP => [h1 h1'].
        move: h1. move /eqP => h1. destruct h1.
        left. assumption.
      + move: h1 => /andP [/eqP ? h1].
        move: h2 => /andP [/eqP ? h2]. subst.
        right. apply/andP. split.
        * apply/eqP. reflexivity.
        * apply (ih2 v2). all: auto.
  Qed.

  Lemma chUniverse_lt_areflexive :
    ∀ x, ~~ chUniverse_lt x x.
  Proof.
    intros x.
    induction x as [ | | | | x1 ih1 x2 ih2] in |- *.
    all: intuition.
    simpl.
    apply/norP; split.
    - apply ih1.
    - apply/nandP.
      right. apply ih2.
  Qed.

  Lemma chUniverse_lt_total_holds :
    ∀ x y,
      ~~ (chUniverse_test x y) ==> (chUniverse_lt x y || chUniverse_lt y x).
  Proof.
    intros x y.
    induction x as [ | | | | x1 ih1 x2 ih2] in y |- *.
    all: try solve [ destruct y ; intuition ; reflexivity ].
    destruct y. all: try (intuition; reflexivity).
    cbn. intuition.
    specialize (ih1 y1). specialize (ih2 y2).
    apply/implyP.
    move /nandP => H.
    apply/orP.
    destruct (chUniverse_test x1 y1) eqn:Heq.
    - destruct H. 1: discriminate.
      move: ih2. move /implyP => ih2.
      specialize (ih2 H).
      move: ih2. move /orP => ih2.
      destruct ih2.
      + left. apply/orP. right. apply/andP; split.
        all: intuition auto.
      + right. apply/orP. right. apply/andP; intuition.
        move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
    - destruct H.
      + move: ih1. move /implyP => ih1.
        specialize (ih1 H).
        move: ih1. move /orP => ih1.
        destruct ih1.
        * left. apply/orP. left. assumption.
        * right. apply/orP. left. assumption.
      + move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * simpl in ih1.  move: ih1. move /orP => ih1.
          destruct ih1.
          -- left. apply/orP. left. assumption.
          -- right. apply/orP. left. assumption.
        * simpl in ih1.  move: ih1. move /orP => ih1.
          destruct ih1.
          -- left. apply/orP. left. assumption.
          -- right. apply/orP. left. assumption.
  Qed.

  Lemma chUniverse_lt_asymmetric :
    ∀ x y,
      (chUniverse_lt x y ==> ~~ chUniverse_lt y x).
  Proof.
    intros x y.
    apply /implyP. move => H.
    destruct (~~ chUniverse_lt y x) eqn:Heq.
    - intuition.
    - move: Heq. move /negP /negP => Heq.
      pose  (chUniverse_lt_areflexive x) as Harefl.
      move: Harefl. apply /implyP. rewrite implyNb.
      apply /orP. left.
      apply (chUniverse_lt_transitive _ _ _ H Heq).
  Qed.

  Lemma chUniverse_lt_total_not_holds :
    ∀ x y,
      ~~ (chUniverse_test x y) ==> (~~ (chUniverse_lt x y && chUniverse_lt y x)).
  Proof.
    intros x y. apply /implyP. intros Hneq.
    pose (chUniverse_lt_total_holds x y) as Htot.
    move: Htot. move /implyP => Htot. specialize (Htot Hneq).
    move: Htot. move /orP => Htot. apply /nandP. destruct Htot.
    - right. pose (chUniverse_lt_asymmetric x y) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
    - left. pose (chUniverse_lt_asymmetric y x) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
  Qed.

  Lemma chUniverse_lt_tot :
    ∀ x y,
      (chUniverse_lt x y || chUniverse_lt y x || chUniverse_eq x y).
  Proof.
    intros x y.
    destruct (chUniverse_eq x y) eqn:H.
    - intuition.
    - apply/orP.
      left.
      unfold chUniverse_eq in H.
      pose (chUniverse_lt_total_holds x y).
      move: i. move /implyP => i.
      apply i. apply/negP.
      intuition. move: H0. rewrite H. intuition.
  Qed.

  Lemma chUniverse_leqP : Ord.axioms chUniverse_leq.
  Proof.
    split => //.
    - intro x. unfold chUniverse_leq.
      apply/orP. left. apply /eqP. reflexivity.
    - intros v u w h1 h2.
      move: h1 h2. unfold chUniverse_leq.
      move /orP => h1. move /orP => h2.
      destruct h1.
      + move: H. move /eqP => H. destruct H.
        apply/orP. assumption.
      + destruct h2.
        * move: H0. move /eqP => H0. destruct H0.
          apply/orP. right. assumption.
        * apply/orP. right. exact (chUniverse_lt_transitive _ _ _ H H0).
    - unfold antisymmetric.
      move => x y. unfold chUniverse_leq. move/andP => [h1 h2].
      move: h1 h2. unfold chUniverse_leq.
      move /orP => h1. move /orP => h2.
      destruct h1.
      1:{ move: H. move /eqP. intuition auto. }
      destruct h2.
      1:{ move: H0. move /eqP. intuition auto. }
      destruct (~~ (chUniverse_test x y)) eqn:Heq.
      + move: Heq. move /idP => Heq.
        pose (chUniverse_lt_total_not_holds x y) as Hp.
        move: Hp. move /implyP => Hp. specialize (Hp Heq).
        move: Hp. move /nandP => Hp.
        destruct Hp.
        * move: H. move /eqP /eqP => H. rewrite H in H1. simpl in H1.
          discriminate.
        * move: H0. move /eqP /eqP => H0. rewrite H0 in H1. simpl in H1.
          discriminate.
      + move: Heq. move /eqP. auto.
    - unfold total.
      intros x y. unfold chUniverse_leq.
      pose (chUniverse_lt_tot x y).
      move: i. move /orP => H.
      destruct H.
      + move: H. move /orP => H.
        destruct H.
        * apply/orP. left. apply/orP. right. assumption.
        * apply/orP. right. apply/orP. right. assumption.
      + apply/orP. left. apply/orP. left. assumption.
  Qed.


  Fixpoint encode (t : chUniverse) : GenTree.tree nat :=
  match t with
  | chZero => GenTree.Leaf 0
  | chUnit => GenTree.Leaf 1
  | chBool => GenTree.Leaf 2
  | chNat => GenTree.Leaf 3
  | chProd l r => GenTree.Node 1 [:: encode l ; encode r]
  end.

  Fixpoint decode (t : GenTree.tree nat) : option chUniverse :=
    match t with
    | GenTree.Leaf 0 => Some chZero
    | GenTree.Leaf 1 => Some chUnit
    | GenTree.Leaf 2 => Some chBool
    | GenTree.Leaf 3 => Some chNat
    | GenTree.Node 1 [:: l ; r] =>
      match decode l, decode r with
      | Some l, Some r => Some (chProd l r)
      | _, _ => None
      end
    | _ => None
    end.

  Lemma codeK : pcancel encode decode.
  Proof.
    move=> t. induction t; intuition.
    simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  Defined.

  Definition chUniverse_choiceMixin := PcanChoiceMixin codeK.
  Canonical chUniverse_choiceType := ChoiceType chUniverse chUniverse_choiceMixin.

  Definition chUniverse_ordMixin := OrdMixin chUniverse_leqP.
  Canonical chUniverse_ordType :=
    Eval hnf in OrdType chUniverse chUniverse_ordMixin.

End chUniverseTypes.
