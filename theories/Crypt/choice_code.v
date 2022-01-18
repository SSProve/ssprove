(**
  This file defines an inductive type [choice_code] corresponding to codes for
  choice types.
  We give a total order on this type, which is then used to show that
  [choice_code] forms a [choiceType].
 *)


From Coq Require Import Utf8 Lia.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra fintype.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Crypt Require Import Prelude Axioms.
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

Inductive choice_code :=
| chUnit
| chNat
| chBool
| chProd (A B : choice_code)
| chMap (A B : choice_code)
| chOption (A : choice_code)
| chFin (n : positive).

Derive NoConfusion NoConfusionHom for choice_code.

(* Definition void_leq (x y : void) := true. *)

(* Lemma void_leqP : Ord.axioms void_leq. *)
(* Proof. split; by do ![case]. Qed. *)

(* Definition void_ordMixin := OrdMixin void_leqP. *)
(* Canonical void_ordType := Eval hnf in OrdType void void_ordMixin. *)

Fixpoint chElement_ordType (U : choice_code) : ordType :=
  match U with
  | chUnit => unit_ordType
  | chNat => nat_ordType
  | chBool => bool_ordType
  | chProd U1 U2 => prod_ordType (chElement_ordType U1) (chElement_ordType U2)
  | chMap U1 U2 => fmap_ordType (chElement_ordType U1) (chElement_ordType U2)
  | chOption U => option_ordType (chElement_ordType U)
  | chFin n => [ordType of ordinal n.(pos) ]
  end.

Fixpoint chElement (U : choice_code) : choiceType :=
  match U with
  | chUnit => unit_choiceType
  | chNat => nat_choiceType
  | chBool => bool_choiceType
  | chProd U1 U2 => prod_choiceType (chElement U1) (chElement U2)
  | chMap U1 U2 => fmap_choiceType (chElement_ordType U1) (chElement U2)
  | chOption U => option_choiceType (chElement U)
  | chFin n => [choiceType of ordinal n.(pos) ]
  end.

Coercion chElement : choice_code >-> choiceType.

(* Canonical element in a type of the choice_code *)
#[program] Fixpoint chCanonical (T : choice_code) : T :=
  match T with
  | chUnit => Datatypes.tt
  | chNat => 0
  | chBool => false
  | chProd A B => (chCanonical A, chCanonical B)
  | chMap A B => _
  | chOption A => None
  | chFin n => _
  end.
Next Obligation.
  eapply fmap_of_fmap. apply emptym.
Defined.
Next Obligation.
  exists 0. destruct n as [p h]. simpl.
  unfold Positive in h. auto.
Defined.

Section choice_codeTypes.

  Fixpoint choice_code_test (u v : choice_code) : bool :=
    match u, v with
    | chNat , chNat => true
    | chUnit , chUnit => true
    | chBool , chBool => true
    | chProd a b , chProd a' b' => choice_code_test a a' && choice_code_test b b'
    | chMap a b , chMap a' b' => choice_code_test a a' && choice_code_test b b'
    | chOption a, chOption a' => choice_code_test a a'
    | chFin n, chFin n' => n == n'
    | _ , _ => false
    end.

  Definition choice_code_eq : rel choice_code :=
    fun u v => choice_code_test u v.

  Lemma choice_code_eqP : Equality.axiom choice_code_eq.
  Proof.
    move=> x y.
    induction x as [ | | | x1 ih1 x2 ih2 | x1 ih1 x2 ih2 | x1 ih1 | x1]
    in y |- *.
    all: destruct y as [ | | | y1 y2 | y1 y2 | y1 | y1].
    all: simpl.
    all: try solve [ right ; discriminate ].
    all: try solve [ left ; reflexivity ].
    - destruct (ih1 y1), (ih2 y2).
      all: simpl.
      all: subst.
      all: try solve [ right ; congruence ].
      left. reflexivity.
    - destruct (ih1 y1), (ih2 y2).
      all: simpl.
      all: subst.
      all: try solve [ right ; congruence ].
      left. reflexivity.
    - destruct (ih1 y1).
      all: subst.
      + left. reflexivity.
      + right. congruence.
    - destruct (x1 == y1) eqn:e.
      + move: e => /eqP e. subst. left. reflexivity.
      + move: e => /eqP e. right. intro h.
        apply e. inversion h. reflexivity.
  Qed.

  Lemma choice_code_refl :
    ∀ u, choice_code_eq u u.
  Proof.
    intros u. destruct choice_code_eq eqn:e.
    - constructor.
    - move: e => /choice_code_eqP []. reflexivity.
  Qed.

  Canonical choice_code_eqMixin := EqMixin choice_code_eqP.
  Canonical choice_code_eqType :=
    Eval hnf in EqType choice_code choice_code_eqMixin.

  Fixpoint choice_code_lt (t1 t2 : choice_code) :=
  match t1, t2 with
  | chUnit, chUnit => false
  | chUnit, _ => true
  | chBool, chUnit => false
  | chBool, chBool => false
  | chBool, _ => true
  | chNat, chUnit => false
  | chNat, chBool => false
  | chNat, chNat => false
  | chNat, _ => true
  | chProd _ _, chUnit => false
  | chProd _ _, chBool => false
  | chProd _ _, chNat => false
  | chProd u1 u2, chProd w1 w2 =>
    (choice_code_lt u1 w1) ||
    (choice_code_eq u1 w1 && choice_code_lt u2 w2)
  | chProd _ _, _ => true
  | chMap _ _, chUnit => false
  | chMap _ _, chBool => false
  | chMap _ _, chNat => false
  | chMap _ _, chProd _ _ => false
  | chMap u1 u2, chMap w1 w2 =>
    (choice_code_lt u1 w1) ||
    (choice_code_eq u1 w1 && choice_code_lt u2 w2)
  | chMap _ _, _ => true
  | chOption _, chUnit => false
  | chOption _, chBool => false
  | chOption _, chNat => false
  | chOption _, chProd _ _ => false
  | chOption _, chMap _ _ => false
  | chOption u, chOption w => choice_code_lt u w
  | chOption _, _ => true
  | chFin n, chUnit => false
  | chFin n, chBool => false
  | chFin n, chNat => false
  | chFin n, chProd _ _ => false
  | chFin n, chMap _ _ => false
  | chFin n, chOption _ => false
  | chFin n, chFin n' => n < n'
  end.

  Definition choice_code_leq (t1 t2 : choice_code) :=
    choice_code_eq t1 t2 || choice_code_lt t1 t2.

  Lemma choice_code_lt_transitive : transitive (T:=choice_code) choice_code_lt.
  Proof.
    intros v u w h1 h2.
    induction u as [ | | | u1 ih1 u2 ih2 | u1 ih1 u2 ih2 | u ih | u]
    in v, w, h1, h2 |- *.
    - destruct w. all: try auto.
      destruct v. all: discriminate.
    - destruct w. all: try auto.
      all: destruct v. all: discriminate.
    - destruct w. all: try auto.
      all: destruct v. all: discriminate.
    - destruct v. all: try discriminate.
      all: destruct w. all: try discriminate. all: try reflexivity.
      cbn in *.
      move: h1 => /orP h1.
      move: h2 => /orP h2.
      apply/orP.
      destruct h1 as [h1|h1], h2 as [h2|h2].
      + left. eapply ih1. all: eauto.
      + left. move: h2 => /andP [/eqP e h2]. subst. auto.
      + left. move: h1 => /andP [/eqP e h1]. subst. auto.
      + right. move: h1 => /andP [/eqP e1 h1].
        move: h2 => /andP [/eqP e2 h2].
        apply/andP. subst. split.
        * apply/eqP. reflexivity.
        * eapply ih2. all: eauto.
    - destruct v. all: try discriminate.
      all: destruct w. all: try discriminate. all: try reflexivity.
      simpl in *.
      move: h1 => /orP h1.
      move: h2 => /orP h2.
      apply/orP.
      destruct h1 as [h1|h1], h2 as [h2|h2].
      + left. eapply ih1. all: eauto.
      + left. move: h2 => /andP [/eqP e h2]. subst. auto.
      + left. move: h1 => /andP [/eqP e h1]. subst. auto.
      + right. move: h1 => /andP [/eqP e1 h1].
        move: h2 => /andP [/eqP e2 h2].
        apply/andP. subst. split.
        * apply/eqP. reflexivity.
        * eapply ih2. all: eauto.
    - destruct v. all: try discriminate.
      all: destruct w. all: try reflexivity. all: try discriminate.
      simpl in *.
      eapply ih. all: eauto.
    - destruct v. all: try discriminate.
      destruct w. all: try discriminate.
      simpl in *.
      eapply ltn_trans. all: eauto.
  Qed.

  Lemma choice_code_lt_areflexive :
    ∀ x, ~~ choice_code_lt x x.
  Proof.
    intros x.
    induction x as [ | | | x1 ih1 x2 ih2 | x1 ih1 x2 ih2 | x ih | x] in |- *.
    all: intuition; simpl.
    - simpl.
      apply/norP. split.
      + apply ih1.
      + apply/nandP.
        right. apply ih2.
    - simpl.
      apply/norP. split.
      + apply ih1.
      + apply/nandP.
        right. apply ih2.
    - rewrite ltnn. auto.
  Qed.

  Lemma choice_code_lt_total_holds :
    ∀ x y,
      ~~ (choice_code_test x y) ==> (choice_code_lt x y || choice_code_lt y x).
  Proof.
    intros x y.
    induction x as [ | | | x1 ih1 x2 ih2| x1 ih1 x2 ih2| x ih| x]
    in y |- *.
    all: try solve [ destruct y ; intuition ; reflexivity ].
    - destruct y. all: try (intuition; reflexivity).
      cbn.
      specialize (ih1 y1). specialize (ih2 y2).
      apply/implyP.
      move /nandP => H.
      apply/orP.
      destruct (choice_code_test x1 y1) eqn:Heq.
      + destruct H. 1: discriminate.
        move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * left. apply/orP. right. apply/andP. split.
          all: intuition auto.
        * right. apply/orP. right. apply/andP. intuition.
          move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
      + destruct H.
        * move: ih1. move /implyP => ih1.
          specialize (ih1 H).
          move: ih1. move /orP => ih1.
          destruct ih1.
          -- left. apply/orP. left. assumption.
          -- right. apply/orP. left. assumption.
        * move: ih2. move /implyP => ih2.
          specialize (ih2 H).
          move: ih2. move /orP => ih2.
          destruct ih2.
          --- simpl in ih1.  move: ih1. move /orP => ih1.
              destruct ih1.
              +++ left. apply/orP. left. assumption.
              +++ right. apply/orP. left. assumption.
          --- simpl in ih1.  move: ih1. move /orP => ih1.
              destruct ih1.
              +++ left. apply/orP. left. assumption.
              +++ right. apply/orP. left. assumption.
    - destruct y. all: try (intuition; reflexivity).
      cbn.
      specialize (ih1 y1). specialize (ih2 y2).
      apply/implyP.
      move /nandP => H.
      apply/orP.
      destruct (choice_code_test x1 y1) eqn:Heq.
      + destruct H. 1: discriminate.
        move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * left. apply/orP. right. apply/andP. split.
          all: intuition auto.
        * right. apply/orP. right. apply/andP. intuition.
          move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
      + destruct H.
        * move: ih1. move /implyP => ih1.
          specialize (ih1 H).
          move: ih1. move /orP => ih1.
          destruct ih1.
          -- left. apply/orP. left. assumption.
          -- right. apply/orP. left. assumption.
        * move: ih2. move /implyP => ih2.
          specialize (ih2 H).
          move: ih2. move /orP => ih2.
          destruct ih2.
          --- simpl in ih1. move: ih1. move /orP => ih1.
              destruct ih1.
              +++ left. apply/orP. left. assumption.
              +++ right. apply/orP. left. assumption.
          --- simpl in ih1. move: ih1. move /orP => ih1.
              destruct ih1.
              +++ left. apply/orP. left. assumption.
              +++ right. apply/orP. left. assumption.
    - destruct y. all: try (intuition; reflexivity).
      unfold choice_code_lt.
      unfold choice_code_test.
      rewrite -neq_ltn.
      apply /implyP. auto.
  Qed.

  Lemma choice_code_lt_asymmetric :
    ∀ x y,
      (choice_code_lt x y ==> ~~ choice_code_lt y x).
  Proof.
    intros x y.
    apply /implyP. move => H.
    destruct (~~ choice_code_lt y x) eqn:Heq.
    - intuition.
    - move: Heq. move /negP /negP => Heq.
      pose  (choice_code_lt_areflexive x) as Harefl.
      move: Harefl. apply /implyP. rewrite implyNb.
      apply /orP. left.
      apply (choice_code_lt_transitive _ _ _ H Heq).
  Qed.

  Lemma choice_code_lt_total_not_holds :
    ∀ x y,
      ~~ (choice_code_test x y) ==> (~~ (choice_code_lt x y && choice_code_lt y x)).
  Proof.
    intros x y. apply /implyP. intros Hneq.
    pose (choice_code_lt_total_holds x y) as Htot.
    move: Htot. move /implyP => Htot. specialize (Htot Hneq).
    move: Htot. move /orP => Htot. apply /nandP. destruct Htot.
    - right. pose (choice_code_lt_asymmetric x y) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
    - left. pose (choice_code_lt_asymmetric y x) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
  Qed.

  Lemma choice_code_lt_tot :
    ∀ x y,
      (choice_code_lt x y || choice_code_lt y x || choice_code_eq x y).
  Proof.
    intros x y.
    destruct (choice_code_eq x y) eqn:H.
    - intuition.
    - apply/orP.
      left.
      unfold choice_code_eq in H.
      pose (choice_code_lt_total_holds x y).
      move: i. move /implyP => i.
      apply i. apply/negP.
      intuition. move: H0. rewrite H. intuition.
  Qed.

  Lemma choice_code_leqP : Ord.axioms choice_code_leq.
  Proof.
    split => //.
    - intro x. unfold choice_code_leq.
      apply/orP. left. apply /eqP. reflexivity.
    - intros v u w h1 h2.
      move: h1 h2. unfold choice_code_leq.
      move /orP => h1. move /orP => h2.
      destruct h1.
      + move: H. move /eqP => H. destruct H.
        apply/orP. assumption.
      + destruct h2.
        * move: H0. move /eqP => H0. destruct H0.
          apply/orP. right. assumption.
        * apply/orP. right. exact (choice_code_lt_transitive _ _ _ H H0).
    - unfold antisymmetric.
      move => x y. unfold choice_code_leq. move/andP => [h1 h2].
      move: h1 h2. unfold choice_code_leq.
      move /orP => h1. move /orP => h2.
      destruct h1.
      1:{ move: H. move /eqP. intuition auto. }
      destruct h2.
      1:{ move: H0. move /eqP. intuition auto. }
      destruct (~~ (choice_code_test x y)) eqn:Heq.
      + move: Heq. move /idP => Heq.
        pose (choice_code_lt_total_not_holds x y) as Hp.
        move: Hp. move /implyP => Hp. specialize (Hp Heq).
        move: Hp. move /nandP => Hp.
        destruct Hp.
        * move: H. move /eqP /eqP => H. rewrite H in H1. simpl in H1.
          discriminate.
        * move: H0. move /eqP /eqP => H0. rewrite H0 in H1. simpl in H1.
          discriminate.
      + move: Heq. move /eqP. auto.
    - unfold total.
      intros x y. unfold choice_code_leq.
      pose (choice_code_lt_tot x y).
      move: i. move /orP => H.
      destruct H.
      + move: H. move /orP => H.
        destruct H.
        * apply/orP. left. apply/orP. right. assumption.
        * apply/orP. right. apply/orP. right. assumption.
      + apply/orP. left. apply/orP. left. assumption.
  Qed.


  Fixpoint encode (t : choice_code) : GenTree.tree nat :=
  match t with
  | chUnit => GenTree.Leaf 1
  | chBool => GenTree.Leaf 2
  | chNat => GenTree.Leaf 3
  | chProd l r => GenTree.Node 1 [:: encode l ; encode r]
  | chMap l r => GenTree.Node 2 [:: encode l ; encode r]
  | chOption u => GenTree.Node 3 [:: encode u]
  | chFin n => GenTree.Leaf ((4 + n) - 1)%N
  end.

  Fixpoint decode (t : GenTree.tree nat) : option choice_code :=
    match t with
    | GenTree.Leaf 1 => Some chUnit
    | GenTree.Leaf 2 => Some chBool
    | GenTree.Leaf 3 => Some chNat
    | GenTree.Leaf n =>
      Some ( chFin (mkpos ((n - 4).+1)%N) )
    | GenTree.Node 1 [:: l ; r] =>
      match decode l, decode r with
      | Some l, Some r => Some (chProd l r)
      | _, _ => None
      end
    | GenTree.Node 2 [:: l ; r] =>
      match decode l, decode r with
      | Some l, Some r => Some (chMap l r)
      | _, _ => None
      end
    | GenTree.Node 3 [:: l] =>
      match decode l with
      | Some l => Some (chOption l)
      | _ => None
      end
    | _ => None
    end.

  Lemma codeK : pcancel encode decode.
  Proof.
    intro t. induction t.
    all: intuition.
    all: simpl.
    - rewrite IHt1. rewrite IHt2. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
    - rewrite IHt. reflexivity.
    - destruct n as [n npos]. cbn.
      destruct n.
      + discriminate.
      + cbn.
        rewrite -subnE subn0. repeat f_equal. apply eq_irrelevance.
  Defined.

  Definition choice_code_choiceMixin := PcanChoiceMixin codeK.
  Canonical choice_code_choiceType :=
    ChoiceType choice_code choice_code_choiceMixin.

  Definition choice_code_ordMixin := OrdMixin choice_code_leqP.
  Canonical choice_code_ordType :=
    Eval hnf in OrdType choice_code choice_code_ordMixin.

End choice_codeTypes.
