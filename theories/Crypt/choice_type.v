(**
  This file defines an inductive type [choice_type] corresponding to codes for
  choice types.
  We give a total order on this type, which is then used to show that
  [choice_type] forms a [choiceType].
 *)


From Coq Require Import Utf8 Lia.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.

(* !!! Import before mathcomp, to avoid overriding instances !!! *)
(* specifically, importing after mathcomp results in conflicting instances for
   Z_choiceType. *)
From deriving Require Import deriving.

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra fintype.
From mathcomp Require Import word_ssrZ word.
(* From Jasmin Require Import utils word. *)
From SSProve.Crypt Require Import jasmin_word jasmin_util.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

From SSProve.Crypt Require Import Prelude Axioms Casts.
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
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

Inductive choice_type :=
| chUnit
| chNat
| chInt
| chBool
| chProd (A B : choice_type)
| chMap (A B : choice_type)
| chOption (A : choice_type)
| chFin (n : positive)
| chWord (nbits : wsize)
| chList (A : choice_type)
| chSum (A B : choice_type).

Derive NoConfusion NoConfusionHom for choice_type.

Fixpoint chElement_ordType (U : choice_type) : ordType :=
  match U with
  | chUnit => unit_ordType
  | chNat => nat_ordType
  | chInt => int_ordType
  | chBool => bool_ordType
  | chProd U1 U2 => prod_ordType (chElement_ordType U1) (chElement_ordType U2)
  | chMap U1 U2 => fmap_ordType (chElement_ordType U1) (chElement_ordType U2)
  | chOption U => option_ordType (chElement_ordType U)
  | chFin n => fin_ordType n
  | chWord nbits => word_ordType nbits
  | chList U => list_ordType (chElement_ordType U)
  | chSum U1 U2 => sum_ordType (chElement_ordType U1) (chElement_ordType U2)
  end.

Fixpoint chElement (U : choice_type) : choiceType :=
  match U with
  | chUnit => unit_choiceType
  | chNat => nat_choiceType
  | chInt => int_choiceType
  | chBool => bool_choiceType
  | chProd U1 U2 => prod_choiceType (chElement U1) (chElement U2)
  | chMap U1 U2 => fmap_choiceType (chElement_ordType U1) (chElement U2)
  | chOption U => option_choiceType (chElement U)
  | chFin n => fin_choiceType n
  | chWord nbits => word_choiceType nbits
  | chList U => list_choiceType (chElement U)
  | chSum U1 U2 => sum_choiceType (chElement U1) (chElement U2)
  end.

Coercion chElement : choice_type >-> choiceType.

(*
#[short(type="ord_countType")]
HB.structure Definition OrdCountType :=
  { A of Countable A & hasOrd A & Choice A }.

HB.instance Definition _ (A : ord_countType) (B : countType) :=
  [Countable of {fmap A → B} by <:].

Lemma can_unit : cancel (λ tt, true) (λ _, tt).
Proof. by intros []. Qed.

HB.instance Definition _ := CanIsCountable can_unit.

Check (nat : countType).
HB.instance Definition _ (T : countType)
  := PcanHasOrd (@pickleK T).

 *)


(*
Fixpoint choice_countType (U : choice_type) : countType :=
  match U with
  | chUnit => unit
  | chNat => nat
  | chInt => int
  | chBool => bool
  | chProd U1 U2 => choice_countType U1 * choice_countType U2
  | chMap U1 U2 => {fmap choice_countType U1 → choice_countType U2}
  | chOption U => option (choice_countType U)
  | chFin n => fin_choiceType n
  | chWord nbits => word_choiceType nbits
  | chList U => list (choice_countType U)
  | chSum U1 U2 => choice_countType U1 + choice_countType U2
  end.
 *)

(* Canonical element in a type of the choice_type *)
#[program] Fixpoint chCanonical (T : choice_type) : T :=
  match T with
  | chUnit => tt
  | chNat => 0
  | chInt => 0
  | chBool => false
  | chProd A B => (chCanonical A, chCanonical B)
  | chMap A B => emptym
  | chOption A => None
  | chFin n => fintype.Ordinal n.(cond_pos)
  | chWord nbits => word0
  | chList A => [::]
  | chSum A B => inl (chCanonical A)
  end.

(* Temporary replacement for countType on choice_type *)
Definition cucumber {U : choice_type} : U → nat.
Admitted.

Definition uncucumber {U : choice_type} : nat → option U.
Admitted.

Lemma cucumberK {U : choice_type} : @pcancel nat U cucumber uncucumber.
Admitted.

Definition coerce {A B : choice_type} : A → B
  := λ x, odflt (chCanonical B) (uncucumber (cucumber x)).

Lemma coerceE {A : choice_type} (a : A) : coerce a = a.
Proof. rewrite /coerce cucumberK //. Qed.


Section choice_typeTypes.

  Fixpoint choice_type_test (u v : choice_type) : bool :=
    match u, v with
    | chNat , chNat => true
    | chInt , chInt => true
    | chUnit , chUnit => true
    | chBool , chBool => true
    | chProd a b , chProd a' b' => choice_type_test a a' && choice_type_test b b'
    | chMap a b , chMap a' b' => choice_type_test a a' && choice_type_test b b'
    | chOption a, chOption a' => choice_type_test a a'
    | chFin n, chFin n' => n == n'
    | chWord nbits, chWord nbits' =>
        nbits == nbits'
    | chList a, chList b => choice_type_test a b
    | chSum a b, chSum a' b' =>  choice_type_test a a' && choice_type_test b b'
    | _ , _ => false
    end.

  Definition choice_type_eq : rel choice_type :=
    fun u v => choice_type_test u v.

  Lemma choice_type_eqP : Equality.axiom choice_type_eq.
  Proof.
    move=> x y.
    induction x as [ | | | | x1 ih1 x2 ih2 | x1 ih1 x2 ih2 | x1 ih1 | x1 | x1 | x1 ih1 | x1 ih1 x2 ih2 ]
    in y |- *.
    all: destruct y as [ | | | | y1 y2 | y1 y2 | y1 | y1 | y1 | y1 | y1 y2 ].
    all: simpl.
    all: try solve [ right ; discriminate ].
    all: try solve [ left ; reflexivity ].
    (* chProd *)
    - destruct (ih1 y1), (ih2 y2).
      all: simpl.
      all: subst.
      all: try solve [ right ; congruence ].
      left. reflexivity.
    (* chMap *)
    - destruct (ih1 y1), (ih2 y2).
      all: simpl.
      all: subst.
      all: try solve [ right ; congruence ].
      left. reflexivity.
    (* chOption *)
    - destruct (ih1 y1).
      all: subst.
      + left. reflexivity.
      + right. congruence.
    (* chFin *)
    - destruct (x1 == y1) eqn:e.
      + move: e => /eqP e. subst. left.  reflexivity.
      + move: e => /eqP e. right. intro h.
        apply e. inversion h. reflexivity.
    (* chWord *)
    - destruct (x1 == y1) eqn:e.
      + move: e => /eqP e. subst. left. reflexivity.
      + move: e => /eqP e. right. intro h.
        apply e. inversion h. reflexivity.
    (* chList *)
    - destruct (ih1 y1).
      all: subst.
      + left. reflexivity.
      + right. congruence.
    (* chSum *)
    - destruct (ih1 y1), (ih2 y2).
      all: simpl.
      all: subst.
      all: try solve [right ; congruence].
      left. reflexivity.
  Qed.

  Lemma choice_type_refl :
    ∀ u, choice_type_eq u u.
  Proof.
    intros u. destruct choice_type_eq eqn:e.
    - constructor.
    - move: e => /choice_type_eqP []. reflexivity.
  Qed.

  Definition choice_type_indDef := [indDef for choice_type_rect].
  Canonical choice_type_indType := IndType choice_type choice_type_indDef.
  (* The unfolding became a problem in [pkg_composition]. So I follow the advice on
     https://github.com/arthuraa/deriving
   *)

  (*
    This
    [Definition choice_type_hasDecEq := [derive hasDecEq for choice_type].]
    did work well up until [pkg_composition].
    The unfolding there was too much.
    The [nored] version then did not provide enough reduction.
   *)
  Definition choice_type_hasDecEq := hasDecEq.Build choice_type choice_type_eqP.
  HB.instance Definition _ := choice_type_hasDecEq.

  Fixpoint choice_type_lt (t1 t2 : choice_type) :=
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
  | chInt, chUnit => false
  | chInt, chBool => false
  | chInt, chNat => false
  | chInt, chInt => false
  | chInt, _ => true
  | chProd _ _, chUnit => false
  | chProd _ _, chBool => false
  | chProd _ _, chNat => false
  | chProd _ _, chInt => false
  | chProd u1 u2, chProd w1 w2 =>
    (choice_type_lt u1 w1) ||
    (eq_op u1 w1 && choice_type_lt u2 w2)
  | chProd _ _, _ => true
  | chMap _ _, chUnit => false
  | chMap _ _, chBool => false
  | chMap _ _, chNat => false
  | chMap _ _, chInt => false
  | chMap _ _, chProd _ _ => false
  | chMap u1 u2, chMap w1 w2 =>
    (choice_type_lt u1 w1) ||
    (eq_op u1 w1 && choice_type_lt u2 w2)
  | chMap _ _, _ => true
  | chOption _, chUnit => false
  | chOption _, chBool => false
  | chOption _, chNat => false
  | chOption _, chInt => false
  | chOption _, chProd _ _ => false
  | chOption _, chMap _ _ => false
  | chOption u, chOption w => choice_type_lt u w
  | chOption _, _ => true
  | chFin _, chUnit => false
  | chFin _, chBool => false
  | chFin _, chNat => false
  | chFin _, chInt => false
  | chFin _, chProd _ _ => false
  | chFin _, chMap _ _ => false
  | chFin _, chOption _ => false
  | chFin n, chFin n' => n < n'
  | chFin _, _ => true
  | chWord _, chUnit => false
  | chWord _, chBool => false
  | chWord _, chNat => false
  | chWord _, chInt => false
  | chWord _, chProd _ _ => false
  | chWord _, chMap _ _ => false
  | chWord _, chOption _ => false
  | chWord _, chFin _ => false
  | chWord n, chWord n' => (n < n')%CMP
  | chWord _, _ => true
  | chList _, chUnit => false
  | chList _, chBool => false
  | chList _, chNat => false
  | chList _, chInt => false
  | chList _, chProd _ _ => false
  | chList _, chMap _ _ => false
  | chList _, chOption _ => false
  | chList _, chFin _ => false
  | chList _, chWord _ => false
  | chList u, chList w => choice_type_lt u w
  | chList _, _ => true
  | chSum _ _, chUnit => false
  | chSum _ _, chBool => false
  | chSum _ _, chNat => false
  | chSum _ _, chInt => false
  | chSum _ _, chProd _ _ => false
  | chSum _ _, chMap _ _ => false
  | chSum _ _, chOption _ => false
  | chSum _ _, chFin _ => false
  | chSum _ _, chWord _ => false
  | chSum _ _, chList _ => false
  | chSum u1 u2, chSum w1 w2 =>
    (choice_type_lt u1 w1) ||
    (eq_op u1 w1 && choice_type_lt u2 w2)
  end.

  Definition choice_type_leq (t1 t2 : choice_type) :=
    eq_op t1 t2 || choice_type_lt t1 t2.

  Lemma choice_type_lt_transitive : transitive (T:=choice_type) choice_type_lt.
  Proof.
    intros v u w h1 h2.
    induction u as [ | | | | u1 ih1 u2 ih2 | u1 ih1 u2 ih2 | u ih | u | u | u ih | u1 ih1 u2 ih2 ]
    in v, w, h1, h2 |- *.
    (* chUnit *)
    - destruct w. all: try auto.
      destruct v. all: discriminate.
    (* chNat *)
    - destruct w. all: try auto.
      all: destruct v. all: discriminate.
    (* chInt *)
    - destruct w. all: try auto.
      all: destruct v. all: discriminate.
    (* chBool *)
    - destruct w. all: try auto.
      all: destruct v. all: discriminate.
    (* chProd *)
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
    (* chMap *)
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
    (* chOption *)
    - destruct v. all: try discriminate.
      all: destruct w. all: try reflexivity. all: try discriminate.
      simpl in *.
      eapply ih. all: eauto.
    (* chFin *)
    - destruct v. all: try discriminate.
      all: destruct w; try discriminate; auto.
      simpl in *.
      eapply ltn_trans. all: eauto.
    (* chWord *)
    - destruct v. all: try discriminate.
      all: destruct w; try discriminate; auto.
      simpl in *.
      eapply cmp_lt_trans. all: eauto.
    (* chList *)
    - destruct v. all: try discriminate.
      all: destruct w. all: try reflexivity. all: try discriminate.
      simpl in *.
      eapply ih. all: eauto.
    (* chSum *)
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
  Qed.

  Lemma choice_type_lt_areflexive :
    ∀ x, ~~ choice_type_lt x x.
  Proof.
    intros x.
    induction x as [ | | | | x1 ih1 x2 ih2 | x1 ih1 x2 ih2 | x ih | x | x | x ih | x1 ih1 x2 ih2] in |- *.
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
    - rewrite cmp_nlt_le.
      apply cmp_le_refl.
    - simpl.
      apply/norP. split.
      + apply ih1.
      + apply/nandP.
        right. apply ih2.
  Qed.

  Lemma choice_type_lt_total_holds :
    ∀ x y,
      ~~ (eq_op x y) ==> (choice_type_lt x y || choice_type_lt y x).
  Proof.
    intros x.
    induction x as [ | | | | x1 ih1 x2 ih2| x1 ih1 x2 ih2| x ih| x | x | x ih | x1 ih1 x2 ih2].
    all: try solve [ destruct y ; auto with solve_subterm ; reflexivity ].
    (* chProd *)
    - destruct y. all: try (intuition; reflexivity).
      specialize (ih1 y1). specialize (ih2 y2).
      apply/implyP.
      move /nandP => H.
      apply/orP.
      destruct (eq_op x1 y1) eqn:Heq.
      + destruct H. 1:  now setoid_rewrite Heq in H.
        move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * left. apply/orP. right. apply/andP. split.
          all: intuition.
        * right. apply/orP. right. apply/andP. intuition.
          move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
      + destruct H.
        * move: ih1. rewrite -Heq; move /implyP => ih1.
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
    (* chMap *)
    - destruct y. all: try (intuition; reflexivity).
      cbn.
      specialize (ih1 y1). specialize (ih2 y2).
      apply/implyP.
      move /nandP => H.
      apply/orP.
      destruct (eq_op x1 y1) eqn:Heq.
      + destruct H. 1: now setoid_rewrite Heq in H.
        move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * left. apply/orP. right. apply/andP. split.
          all: intuition.
        * right. apply/orP. right. apply/andP. intuition.
          move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
      + destruct H.
        * move: ih1. move /implyP => ih1.
          specialize (ih1 isT).
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
    (* chFin *)
    - destruct y. all: try (intuition; reflexivity).
      unfold choice_type_lt.
      rewrite -neq_ltn.
      apply /implyP. auto.
    (* chWord *)
    - destruct y. all: try (intuition; reflexivity).
      unfold choice_type_lt.
      apply /implyP.
      move => H. apply /orP.
      destruct (gcmp x nbits) eqn:E.
      + by move: E H => /cmp_eq -> /negP.
      + left. by apply /eqP.
      + right. unfold cmp_lt. rewrite cmp_sym. by move: E => ->.
    (* chSum *)
    - destruct y. all: try (intuition; reflexivity).
      cbn.
      specialize (ih1 y1). specialize (ih2 y2).
      apply/implyP.
      move /nandP => H.
      apply/orP.
      destruct (eq_op x1 y1) eqn:Heq.
      + destruct H. 1: now setoid_rewrite Heq in H.
        move: ih2. move /implyP => ih2.
        specialize (ih2 H).
        move: ih2. move /orP => ih2.
        destruct ih2.
        * left. apply/orP. right. apply/andP. split.
          all: intuition.
        * right. apply/orP. right. apply/andP. intuition.
          move: Heq. move /eqP => Heq. rewrite Heq. apply/eqP. reflexivity.
      + destruct H.
        * move: ih1. move /implyP => ih1.
          specialize (ih1 isT).
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
  Qed.

  Lemma choice_type_lt_asymmetric :
    ∀ x y,
      (choice_type_lt x y ==> ~~ choice_type_lt y x).
  Proof.
    intros x y.
    apply /implyP. move => H.
    destruct (~~ choice_type_lt y x) eqn:Heq.
    - intuition.
    - move: Heq. move /negP /negP => Heq.
      pose  (choice_type_lt_areflexive x) as Harefl.
      move: Harefl. apply /implyP. rewrite implyNb.
      apply /orP. left.
      apply (choice_type_lt_transitive _ _ _ H Heq).
  Qed.

  Lemma choice_type_lt_total_not_holds :
    ∀ x y,
      ~~ (eq_op x y) ==> (~~ (choice_type_lt x y && choice_type_lt y x)).
  Proof.
    intros x y. apply /implyP. intros Hneq.
    pose (choice_type_lt_total_holds x y) as Htot.
    move: Htot. move /implyP => Htot. specialize (Htot Hneq).
    move: Htot. move /orP => Htot. apply /nandP. destruct Htot.
    - right. pose (choice_type_lt_asymmetric x y) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
    - left. pose (choice_type_lt_asymmetric y x) as Hasym.
      move: Hasym. move /implyP => Hasym. specialize (Hasym H). assumption.
  Qed.

  Lemma choice_type_lt_tot :
    ∀ x y,
      (choice_type_lt x y || choice_type_lt y x || eq_op x y).
  Proof.
    intros x y.
    destruct (eq_op x y) eqn:H.
    - apply/orP. by right.
    - apply/orP.
      left.
      pose (choice_type_lt_total_holds x y).
      move: i. move /implyP => i.
      apply i. apply/negP.
      intuition. move: H0. rewrite H. intuition.
  Qed.

  Lemma choice_type_leqxx : reflexive choice_type_leq.
  Proof.
    intro x. unfold choice_type_leq.
    apply/orP. left. apply /eqP. reflexivity.
  Qed.

  Lemma choice_type_leq_trans : transitive choice_type_leq.
  Proof.
    intros v u w h1 h2.
    move: h1 h2. unfold choice_type_leq.
    move /orP => h1. move /orP => h2.
    destruct h1.
    + move: H. move /eqP => H. destruct H.
      apply/orP. assumption.
    + destruct h2.
      * move: H0. move /eqP => H0. destruct H0.
        apply/orP. right. assumption.
      * apply/orP. right. exact (choice_type_lt_transitive _ _ _ H H0).
  Qed.

  Lemma choice_type_leq_asym : antisymmetric choice_type_leq.
  Proof.
    unfold antisymmetric.
    move => x y. unfold choice_type_leq. move/andP => [h1 h2].
    move: h1 h2. unfold choice_type_leq.
    move /orP => h1. move /orP => h2.
    destruct h1.
    1:{ move: H. move /eqP. intuition. }
    destruct h2.
    1:{ move: H0. move /eqP. intuition. }
    destruct (~~ (eq_op x y)) eqn:Heq.
    + move: Heq. move /idP => Heq.
      pose (choice_type_lt_total_not_holds x y) as Hp.
      move: Hp. move /implyP => Hp. specialize (Hp Heq).
      move: Hp. move /nandP => Hp.
      destruct Hp.
      * move: H. move /eqP /eqP => H. rewrite H in H1. simpl in H1.
        discriminate.
      * move: H0. move /eqP /eqP => H0. rewrite H0 in H1. simpl in H1.
        discriminate.
    + move: Heq. move /eqP. auto.
  Qed.

  Lemma choice_type_leq_total : total choice_type_leq.
    unfold total.
    intros x y. unfold choice_type_leq.
    pose (choice_type_lt_tot x y).
    move: i. move /orP => H.
    destruct H.
    + move: H. move /orP => H.
      destruct H.
      * apply/orP. left. apply/orP. right. assumption.
      * apply/orP. right. apply/orP. right. assumption.
    + apply/orP. left. apply/orP. left. assumption.
  Qed.

  Fixpoint encode (t : choice_type) : GenTree.tree nat :=
  match t with
  | chUnit => GenTree.Leaf 1
  | chBool => GenTree.Leaf 2
  | chNat => GenTree.Leaf 3
  | chInt => GenTree.Leaf 4
  | chProd l r => GenTree.Node 1 [:: encode l ; encode r]
  | chMap l r => GenTree.Node 2 [:: encode l ; encode r]
  | chOption u => GenTree.Node 3 [:: encode u]
  | chFin n => GenTree.Node 4 [:: GenTree.Leaf (pos n)]
  | chWord n => GenTree.Node 5 [:: GenTree.Leaf (wsize_log2 n)]
  | chList u => GenTree.Node 6 [:: encode u]
  | chSum l r => GenTree.Node 7 [:: encode l ; encode r]
  end.

  Fixpoint decode (t : GenTree.tree nat) : option choice_type :=
    match t with
    | GenTree.Leaf 1 => Some chUnit
    | GenTree.Leaf 2 => Some chBool
    | GenTree.Leaf 3 => Some chNat
    | GenTree.Leaf 4 => Some chInt
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
    | GenTree.Node 4 [:: GenTree.Leaf (S n)] => Some (chFin (mkpos (S n)))
    | GenTree.Node 5 [:: GenTree.Leaf n] => Some (chWord (nth U8 wsizes n))
    | GenTree.Node 6 [:: l] =>
      match decode l with
      | Some l => Some (chList l)
      | _ => None
      end
    | GenTree.Node 7 [:: l ; r] =>
      match decode l, decode r with
      | Some l, Some r => Some (chSum l r)
      | _, _ => None
      end
    | _ => None
    end.

  Lemma codeK : pcancel encode decode.
  Proof.
    intro t. induction t.
    all: intuition eauto.
    all: simpl.
    - rewrite IHt1. rewrite IHt2. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
    - rewrite IHt. reflexivity.
    - destruct n as [n npos]. cbn.
      destruct n.
      + discriminate.
      + cbn. repeat f_equal. apply eq_irrelevance.
    - repeat f_equal. unfold wsizes.
      destruct nbits; reflexivity.
    - rewrite IHt. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

  #[short(type="choice_type_choiceMixin")]
    HB.instance Definition _ := PCanHasChoice codeK.

  HB.instance Definition _ :=
    hasOrd.Build choice_type
      (choice_type_leqxx)
      (choice_type_leq_trans)
      (choice_type_leq_asym)
      (choice_type_leq_total).
End choice_typeTypes.
