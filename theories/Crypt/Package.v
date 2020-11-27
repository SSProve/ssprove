From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra.
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

(* General definitions *)

Definition transport {A : Type} {x y : A} (P : A → Type) (eq : x = y) (t : P x) : P y :=
  eq_rect x P t y eq.

Notation "p ⋅ t" := (transport (fun x => _) p t) (at level 20).

Lemma fsetU_coproduct {T : ordType} (x : T) s1 s2 :
  (x \in s1 :|: s2) → ((x \in s1) + (x \in s2)).
Proof.
  rewrite in_fsetU. unfold is_true.
  case (x \in s1) ; case (x \in s2); move => h.
  - left. exact h.
  - left. exact h.
  - right. exact h.
  - left. exact h.
Defined.

Fact disjoint_in_both {T : ordType} (s1 s2 : {fset T}) :
  fdisjoint s1 s2 → ∀ x, x \in s1 → x \in s2 → False.
Proof.
  move => Hdisjoint x x_in_s1 x_in_s2.
  assert (x \notin s2) as H by exact (fdisjointP s1 s2 Hdisjoint x x_in_s1).
  rewrite x_in_s2 in H. by [].
Qed.

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

Definition ident := nat.

(* Signature of an operation, including the identifier *)
Definition opsig := ident * (chUniverse * chUniverse).
(* Record opsig := mkop {
  ident : nat ;
  src : chUniverse ;
  tgt : chUniverse
}. *)

Definition Location := nat.
Definition Value := nat_choiceType.

Module PackageTheory (π : ProbRulesParam).

  Export π.

  Definition Interface := {fset opsig}.

  Definition ide (v : opsig) : ident :=
    let '(n, (s, t)) := v in n.

  Definition chsrc (v : opsig) : chUniverse :=
      let '(n, (s, t)) := v in s.

  Definition src (v : opsig) : choiceType :=
    chsrc v.

  Definition chtgt (v : opsig) : chUniverse :=
    let '(n, (s, t)) := v in t.

  Definition tgt (v : opsig) : choiceType :=
    chtgt v.

  Section Translation.

    Context (probE : Type → Type).
    Context (rel_choiceTypes : Type) (*the "small" type of relevant choiceTypes*)
            (chEmb : rel_choiceTypes → choiceType).

    Definition Prob_ops_collection :=
      ∑ rchT : rel_choiceTypes, probE (chEmb rchT).

    Definition Prob_arities : Prob_ops_collection → choiceType :=
      fun '(envType ; opp) => chEmb envType.

  End Translation.

  Definition Op := (Prob_ops_collection probE rel_choiceTypes chEmb).
  Definition Arit := (Prob_arities probE rel_choiceTypes chEmb).

  Section FreeModule.

    Context (Loc : {fset Location}).
    Context (import : Interface).

    Inductive raw_program (A : choiceType) : Type :=
    | _ret (x : A)
    | _opr (o : opsig) (x : src o) (k : tgt o → raw_program A)
    | _getr (l : Location) (k : Value → raw_program A)
    | _putr (l : Location) (v : Value) (k : raw_program A)
    | _sampler (op : Op) (k : Arit op → raw_program A).

    Arguments _ret [A] _.
    Arguments _opr [A] _ _.
    Arguments _getr [A] _.
    Arguments _putr [A] _.
    Arguments _sampler [A] _ _.

    (* TODO Investigate if we can have rules rather than such a function.
      I see no reason why not. Would we gain something from it?
      Maybe we would then have type checker (or the like).
    *)
    Fixpoint valid_program {A} (v : raw_program A) :=
      match v with
      | _ret x => True
      | _opr o x k => o \in import ∧ ∀ v, valid_program (k v)
      | _getr l k => l \in Loc ∧ ∀ v, valid_program (k v)
      | _putr l v k => l \in Loc ∧ valid_program k
      | _sampler op k => ∀ v, valid_program (k v)
      end.

    Definition program A :=
      { v : raw_program A | valid_program v }.

    Lemma program_ext :
      ∀ A (u v : program A),
        u ∙1 = v ∙1 →
        u = v.
    Proof.
      intros A u v h.
      destruct u as [u hu], v as [v hv].
      cbn in h. subst.
      f_equal. apply proof_irrelevance.
    Qed.

    Definition ret [A : choiceType] (x : A) : program A.
    Proof.
      exists (_ret x).
      cbn. auto.
    Defined.

    Definition opr [A : choiceType] (o : opsig) (h : o \in import)
      (x : src o) (k : tgt o → program A) : program A.
    Proof.
      pose k' := λ x, (k x) ∙1.
      exists (_opr o x k').
      cbn. intuition auto.
      subst k'. cbn.
      exact ((k v) ∙2).
    Defined.

    Definition getr [A : choiceType] l (h : l \in Loc) (k : Value → program A) :
      program A.
    Proof.
      pose k' := λ x, (k x) ∙1.
      exists (_getr l k').
      subst k'. cbn. intuition auto.
      exact ((k v) ∙2).
    Defined.

    Definition putr [A : choiceType] l (h : l \in Loc) (v : Value)
      (k : program A) : program A.
    Proof.
      exists (_putr l v (k ∙1)).
      cbn. intuition auto.
      exact (k ∙2).
    Defined.

    Definition sampler [A : choiceType] (op : Op) (k : Arit op → program A) :
      program A.
    Proof.
      pose k' := λ x, (k x) ∙1.
      exists (_sampler op k').
      cbn. subst k'.
      intro. cbn.
      exact ((k v) ∙2).
    Defined.

    Fixpoint bind_ {A B : choiceType}
      (c : raw_program A) (k : TypeCat ⦅ choice_incl A ; raw_program B ⦆ ) :
      raw_program B :=
      match c with
      | _ret a => k a
      | _opr o x k'  => _opr o x (λ p, bind_ (k' p) k)
      | _getr l k' => _getr l (λ v, bind_ (k' v) k)
      | _putr l v k' => _putr l v (bind_ k' k)
      | _sampler op k' => _sampler op (λ a, bind_ (k' a) k)
      end.

    Lemma bind_valid :
      ∀ A B c k,
        valid_program c →
        (∀ x, valid_program (k x)) →
        valid_program (@bind_ A B c k).
    Proof.
      intros A B c k hc hk.
      induction c in hc |- *.
      all: solve [ cbn ; cbn in hc ; intuition auto ].
    Qed.

    Definition bind {A B : choiceType} (c : program A)
      (k : TypeCat ⦅ choice_incl A ; program B ⦆ ) :
      program B.
    Proof.
      exists (bind_ (c ∙1) (λ x, (k x) ∙1)).
      destruct c as [c h]. cbn.
      apply bind_valid.
      - auto.
      - intro x. exact ((k x) ∙2).
    Defined.

    Import SPropAxioms. Import FunctionalExtensionality.

    Program Definition rFree : ord_relativeMonad choice_incl :=
      @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl program _ _ _ _ _ _.
    Next Obligation. apply ret. auto. Defined.
    Next Obligation. eapply bind. all: eauto. Defined.
    Next Obligation.
      f_equal. apply functional_extensionality. auto.
    Qed.
    Next Obligation.
      apply functional_extensionality.
      intro c. apply program_ext.
      destruct c as [c h]. cbn.
      induction c.
      all: solve [
        simpl in * ; try reflexivity ;
        f_equal ; try apply functional_extensionality ; intuition auto
      ].
    Qed.
    Next Obligation.
      extensionality x. apply program_ext.
      cbn. reflexivity.
    Qed.
    Next Obligation.
      apply functional_extensionality. intros [c h].
      apply program_ext. cbn.
      induction c in h |- *.
      all: solve [
        simpl in * ; try reflexivity ;
        f_equal ; try apply functional_extensionality ; intuition auto
      ].
    Qed.

    Fixpoint mapFree_ {A B : choiceType} (f : A → B) (m : raw_program A) :
      raw_program B :=
      match m with
      | _ret x => _ret (f x)
      | _opr o x k => _opr o x (λ r, mapFree_ f (k r))
      | _getr l k' => _getr l (λ v, mapFree_ f (k' v))
      | _putr l v k' => _putr l v (mapFree_ f k')
      | _sampler op k' => _sampler op (λ a, mapFree_ f (k' a))
      end.

    Definition mapFree {A B : choiceType} (f : A → B) (m : program A) :
      program B.
    Proof.
      exists (mapFree_ f (m ∙1)).
      destruct m as [m h]. cbn.
      induction m in h |- *.
      all: solve [ cbn in * ; intuition auto ].
    Defined.

  End FreeModule.

  Arguments _ret [A] _.
  Arguments _opr [A] _ _.
  Arguments _getr [A] _.
  Arguments _putr [A] _.
  Arguments _sampler [A] _ _.

  Arguments ret [Loc] [import] [A] _.
  Arguments opr [Loc] [import] [A] _ _.
  Arguments getr [Loc] [import] [A] _ _.
  Arguments putr [Loc] [import] [A] _ _.
  Arguments sampler [Loc] [import] [A] _ _.

  Section FreeLocations.

    Context {import : Interface}.

    Lemma injectSubset :
      ∀ {locs1 locs2 : {fset Location}} {l : Location},
        fsubset locs1 locs2 →
        l \in locs1 →
        l \in locs2.
    Proof.
      intros locs1 locs2 l Hfsubset H.
      unfold fsubset in Hfsubset.
      move: Hfsubset.
      move /eqP => Q.
      rewrite -Q.
      rewrite in_fsetU.
      intuition.
    Defined.

    Let programI locs := program locs import.

    Lemma valid_injectLocations :
      ∀ A L1 L2 (v : raw_program A),
        fsubset L1 L2 →
        valid_program L1 import v →
        valid_program L2 import v.
    Proof.
      intros A L1 L2 v h p.
      cbn. induction v in p |- *.
      all: try solve [ cbn ; cbn in p ; intuition auto ].
      - cbn. cbn in p. intuition auto. eapply injectSubset. all: eauto.
      - cbn. cbn in p. intuition auto. eapply injectSubset. all: eauto.
    Qed.

    Definition injectLocations {A : choiceType} {loc1 loc2 : {fset Location}}
      (h : fsubset loc1 loc2) (v : programI loc1 A) : programI loc2 A.
    Proof.
      exists v ∙1.
      destruct v as [v p].
      cbn. eapply valid_injectLocations. all: eauto.
    Defined.

    Lemma injectLocationsInjective :
      ∀ {A : choiceType} {locs1 locs2 : {fset Location}}
        (Hfsubset1 Hfsubset2 : fsubset locs1 locs2)
        (v : programI locs1 A),
        injectLocations Hfsubset1 v = injectLocations Hfsubset2 v.
    Proof.
      intros A locs1 locs2 h1 h2 v.
      f_equal. apply bool_irrelevance.
    Qed.

    Lemma injectLocationsMerge :
      ∀ {A : choiceType} {locs1 locs2 locs3 : {fset Location}}
        (h1 : fsubset locs1 locs2)
        (h2 : fsubset locs2 locs3)
        (v : programI locs1 A),
        (injectLocations h2 (injectLocations h1 v)) =
        injectLocations (fsubset_trans h1 h2) v.
    Proof.
      intros A locs1 locs2 locs3 h1 h2 v.
      destruct v as [v h]. cbn.
      apply program_ext. cbn. reflexivity.
    Qed.

  End FreeLocations.

  Section FreeMap.

    Context {Locs : {fset Location}}.

    Lemma in_fsubset :
      ∀ {e} {S1 S2 : Interface},
        fsubset S1 S2 →
        e \in S1 →
        e \in S2.
    Proof.
      intros e S1 S2 hs h.
      unfold fsubset in hs.
      move: hs. move /eqP => hs. rewrite -hs.
      rewrite in_fsetU.
      intuition.
    Defined.

    Let programL I := program Locs I.

    Lemma valid_injectMap :
      ∀ {A I1 I2} (v : raw_program A),
        fsubset I1 I2 →
        valid_program Locs I1 v →
        valid_program Locs I2 v.
    Proof.
      intros A I1 I2 v h p.
      induction v in p |- *.
      all: try solve [ cbn ; cbn in p ; intuition auto ].
      cbn. cbn in p. intuition auto. eapply in_fsubset. all: eauto.
    Qed.

    Definition injectMap {A : choiceType} {I1 I2 : Interface}
      (h : fsubset I1 I2) (v : programL I1 A) : programL I2 A.
    Proof.
      exists v ∙1.
      destruct v as [v p]. cbn.
      eapply valid_injectMap. all: eauto.
    Defined.

    Lemma injectMapInjective {A : choiceType} {I1 I2 : Interface}
          (Hfsubset1 Hfsubset2 : fsubset I1 I2)
          (v : programL I1 A) :
      injectMap Hfsubset1 v = injectMap Hfsubset2 v.
    Proof.
      f_equal. apply bool_irrelevance.
    Qed.

  End FreeMap.

  Section commuteMapLocations.

    Context {locs1 locs2 : {fset Location}}.
    Context {I1 I2 : Interface}.

    Lemma commuteMapLocations :
      ∀ {A : choiceType}
        (h1 : fsubset locs1 locs2) (h2 : fsubset I1 I2)
        (v : program locs1 I1 A),
        injectMap h2 (injectLocations h1 v) =
        injectLocations h1 (injectMap h2 v).
    Proof.
      intros A h1 h2 v.
      apply program_ext. cbn. reflexivity.
    Qed.

  End commuteMapLocations.

  Section commuteBindLocations.

    Context {locs1 locs2 : {fset Location}}.
    Context {I : Interface}.

    Lemma commuteBindLocations :
      ∀ {A B : choiceType} (h : fsubset locs1 locs2)
        (v : program locs1 I A) (f : A → program locs1 I B),
        bind _ _ (injectLocations h v) (fun w => injectLocations h (f w)) =
        injectLocations h (bind _ _ v f).
    Proof.
      intros A B h v f.
      apply program_ext. cbn. reflexivity.
    Qed.

  End commuteBindLocations.

  Section PackageModule.

    Definition pointed_program :=
      ∑ (S T : chUniverse), S → raw_program T.

    (* Can't use opsig as index because maps aren't dependent. *)
    Definition raw_package :=
      {fmap ident -> pointed_program}.

    Definition valid_package L I (E : Interface) (p : raw_package) :=
      ∀ o, o \in E →
        let '(id, (src, tgt)) := o in
        ∃ (f : src → raw_program tgt),
          p id = Some (src ; tgt ; f) ∧ ∀ x, valid_program L I (f x).

    (* Open packages *)
    Definition opackage L I E :=
      { p : raw_package | valid_package L I E p }.

    Definition package I E :=
      ∑ L, opackage L I E.

    Record bundle := mkbundle {
      locs : {fset Location} ;
      import : Interface ;
      export : Interface ;
      pack : opackage locs import export
    }.

  Section Link.

    Definition cast_fun {So To St Tt : chUniverse}
      (hS : St = So) (hT : Tt = To) (f : St → raw_program Tt) :
      So → raw_program To.
    Proof.
      subst. auto.
    Defined.

    Definition lookup_op (p: raw_package) (o : opsig) :
      option (src o → raw_program (tgt o)) :=
      let '(n, (So, To)) := o in
      match p n with
      | Some (St ; Tt ; f) =>
        match chUniverse_eqP St So, chUniverse_eqP Tt To with
        | ReflectT hS, ReflectT hT => Some (cast_fun hS hT f)
        | _,_ => None
        end
      | None => None
      end.

    Derive NoConfusion NoConfusionHom EqDec for chUniverse.
    Derive NoConfusion NoConfusionHom for sigT.
    Derive NoConfusion NoConfusionHom for option.

    Lemma lookup_op_valid :
      ∀ L I E p o,
        valid_package L I E p →
        o \in E →
        ∃ f,
          lookup_op p o = Some f ∧
          ∀ x, valid_program L I (f x).
    Proof.
      intros L I E p o hp ho.
      specialize (hp o ho).
      destruct o as [n [So To]].
      destruct hp as [f [ef hf]].
      exists f. intuition auto. cbn.
      destruct (p n) as [[St [Tt ft]]|] eqn:e. 2: discriminate.
      destruct chUniverse_eqP.
      2:{ inversion ef. congruence. }
      destruct chUniverse_eqP.
      2:{ inversion ef. congruence. }
      subst. cbn. noconf ef.
      reflexivity.
    Qed.

    Lemma lookup_op_map :
      ∀ p o f,
        lookup_op (@mapm _ pointed_program _ (λ '(So ; To ; g), (So ; To ; f So To g)) p) o =
        omap (f (chsrc o) (chtgt o)) (lookup_op p o).
    Proof.
      intros p [n [So To]] f. unfold lookup_op.
      rewrite mapmE. destruct (p n) as [[St [Tt ft]]|] eqn:e.
      2:{ cbn. reflexivity. }
      cbn. destruct chUniverse_eqP. 2: reflexivity.
      destruct chUniverse_eqP. 2: reflexivity.
      cbn. subst. cbn. reflexivity.
    Qed.

    Fixpoint raw_program_link {A} (v : raw_program A) (p : raw_package) :
      raw_program A :=
      match v with
      | _ret a => _ret a
      | _opr o a k =>
        match lookup_op p o with
        | Some f => bind_ (f a) (λ x, raw_program_link (k x) p)
        | None => _opr o a (λ x, raw_program_link (k x) p) (* Should not happen in practice *)
        end
      | _getr l k => _getr l (λ x, raw_program_link (k x) p)
      | _putr l v k => _putr l v (raw_program_link k p)
      | _sampler op k => _sampler op (λ x, raw_program_link (k x) p)
      end.

    Lemma raw_program_link_valid :
      ∀ A L Im Ir (v : raw_program A) p,
        valid_program L Im v →
        valid_package L Ir Im p →
        valid_program L Ir (raw_program_link v p).
    Proof.
      intros A L Im Ir v p hv hp.
      induction v in hv |- *.
      all: try solve [ cbn ; cbn in hv ; intuition auto ].
      cbn. cbn in hv.
      eapply lookup_op_valid in hp as hf. 2: intuition eauto.
      destruct hf as [f [ef hf]].
      rewrite ef.
      apply bind_valid.
      - intuition auto.
      - intuition auto.
    Qed.

    Definition program_link {A L Im Ir}
      (v : program L Im A) (p : opackage L Ir Im) :
      program L Ir A.
    Proof.
      exists (raw_program_link (v ∙1) (p ∙1)).
      destruct v as [v hv], p as [p hp]. cbn.
      eapply raw_program_link_valid. all: eauto.
    Defined.

    Definition raw_link (p1 p2 : raw_package) : raw_package :=
      @mapm _ pointed_program _
        (λ '(So ; To ; f), (So ; To ; λ x, raw_program_link (f x) p2)) p1.

    Definition olink {L I E I'}
      (p1 : opackage L I E) (p2 : opackage L I' I) : opackage L I' E.
    Proof.
      exists (raw_link p1 ∙1 p2 ∙1).
      destruct p1 as [p1 h1], p2 as [p2 h2]. cbn.
      intros [n [So To]] ho.
      unfold raw_link. rewrite mapmE.
      specialize (h1 _ ho) as h1'. cbn in h1'.
      destruct h1' as [f [ef hf]]. rewrite ef. cbn.
      eexists. split. 1: reflexivity.
      intro x.
      eapply raw_program_link_valid. all: eauto.
    Defined.

    Lemma bind_assoc :
      ∀ {A B C : choiceType} (v : raw_program A)
        (k1 : TypeCat ⦅ choice_incl A ; raw_program B ⦆)
        (k2 : TypeCat ⦅ choice_incl B ; raw_program C ⦆),
        bind_ (bind_ v k1) k2 =
        bind_ v (λ x, bind_ (k1 x) k2).
    Proof.
      intros A B C v k1 k2.
      induction v in k1, k2 |- *.
      - cbn. reflexivity.
      - cbn. f_equal. apply functional_extensionality. auto.
      - cbn. f_equal. extensionality z. auto.
      - cbn. f_equal. auto.
      - cbn. f_equal. extensionality z. auto.
    Qed.

    Lemma raw_program_link_bind :
      ∀ {A B : choiceType} (v : raw_program A)
        (k : TypeCat ⦅ choice_incl A ; raw_program B ⦆)
        (p : raw_package),
        raw_program_link (bind_ v k) p =
        bind_ (raw_program_link v p) (λ x, raw_program_link (k x) p).
    Proof.
      intros A B v k p.
      induction v.
      - cbn. reflexivity.
      - cbn. destruct lookup_op.
        + rewrite bind_assoc. f_equal.
          apply functional_extensionality. auto.
        + cbn. f_equal. apply functional_extensionality. auto.
      - cbn. f_equal. apply functional_extensionality. auto.
      - cbn. f_equal. auto.
      - cbn. f_equal. apply functional_extensionality. auto.
    Qed.

    (* For associativity we need to know that all operations in the program
      are indeed provided by the package.
      [provides p v] states that p provides everything that v imports.
      Alternatively we could compare with a set.
    *)
    Fixpoint provides {A} (p : raw_package) (v : raw_program A) :=
      match v with
      | _ret a => True
      | _opr o a k =>
        match lookup_op p o with
        | Some f => ∀ x, provides p (k x)
        | None => False
        end
      | _getr l k => ∀ x, provides p (k x)
      | _putr l v k => provides p k
      | _sampler op k => ∀ x, provides p (k x)
      end.

    Lemma raw_program_link_assoc :
      ∀ A (v : raw_program A) f g,
        provides f v →
        raw_program_link (raw_program_link v f) g =
        raw_program_link v (raw_link f g).
    Proof.
      intros A v f g h.
      induction v in f, g, h |- *.
      - cbn. reflexivity.
      - cbn. unfold raw_link in *.
        rewrite lookup_op_map. cbn in h.
        destruct lookup_op eqn:e. 2: exfalso ; auto.
        cbn. rewrite raw_program_link_bind. f_equal.
        apply functional_extensionality. auto.
      - cbn. f_equal. apply functional_extensionality. auto.
      - cbn. f_equal. auto.
      - cbn. f_equal. apply functional_extensionality. auto.
    Qed.

    Lemma valid_provides :
      ∀ A (v : raw_program A) (p : raw_package) L I E,
        valid_program L E v →
        valid_package L I E p →
        provides p v.
    Proof.
      intros A v p L I E hv hp.
      induction v in hv |- *.
      - cbn. auto.
      - cbn. cbn in hv. destruct hv as [ho hv].
        destruct lookup_op eqn:e.
        2:{
          specialize (hp _ ho) as hp'.
          destruct o as [n [So To]]. cbn in *.
          destruct hp' as [f [ef hf]].
          destruct (p n) as [[St [Tt ft]]|] eqn:et. 2: discriminate.
          destruct chUniverse_eqP.
          2:{ inversion ef. congruence. }
          destruct chUniverse_eqP.
          2:{ inversion ef. congruence. }
          discriminate.
        }
        intuition eauto.
      - cbn. cbn in hv. intuition auto.
      - cbn. cbn in hv. intuition auto.
      - cbn. cbn in hv. intuition auto.
    Qed.

    Lemma program_link_assoc :
      ∀ {A L Im Ir Il}
        (v : program L Im A)
        (f : opackage L Ir Im)
        (g : opackage L Il Ir),
        program_link (program_link v f) g =
        program_link v (olink f g).
    Proof.
      intros A L Im Ir Il [v hv] [f hf] [g hg].
      apply program_ext. cbn.
      apply raw_program_link_assoc.
      eapply valid_provides. all: eauto.
    Qed.

    Lemma valid_package_inject_locations :
      ∀ I E L1 L2 p,
        fsubset L1 L2 →
        valid_package L1 I E p →
        valid_package L2 I E p.
    Proof.
      intros I E L1 L2 p hL h.
      intros [n [S T]] ho. specialize (h _ ho). cbn in h.
      destruct h as [f [ef hf]].
      exists f. intuition auto.
      eapply valid_injectLocations. all: eauto.
    Qed.

    Lemma valid_package_inject_export :
      ∀ L I E1 E2 p,
        fsubset E1 E2 →
        valid_package L I E2 p →
        valid_package L I E1 p.
    Proof.
      intros L I E1 E2 p hE h.
      intros o ho. specialize (h o).
      destruct o as [o [So To]].
      forward h.
      { eapply in_fsubset. all: eauto. }
      destruct h as [f [ef hf]].
      exists f. intuition auto.
    Qed.

    (* TODO Probably useless? *)
    Definition opackage_inject_locations {I E L1 L2}
      (hL : fsubset L1 L2) (p : opackage L1 I E) :
      opackage L2 I E.
    Proof.
      exists (p ∙1).
      destruct p as [p h]. cbn.
      eapply valid_package_inject_locations. all: eauto.
    Defined.

    Definition program_link' {A L1 L2 I M}
      (v : program L1 M A) (p : opackage L2 I M) :
      program (L1 :|: L2) I A.
    Proof.
      exists (raw_program_link (v ∙1) (p ∙1)).
      destruct v as [v hv], p as [p hp]. cbn.
      eapply raw_program_link_valid.
      - eapply valid_injectLocations. 2: eauto.
        apply fsubsetUl.
      - eapply valid_package_inject_locations. 2: eauto.
        apply fsubsetUr.
    Defined.

    (* Remove unexported functions from a raw package *)
    Definition trim (E : Interface) (p : raw_package) :=
      filterm (λ n '(So ; To ; f), (n, (So, To)) \in E) p.

    Lemma trim_get :
      ∀ E (p : raw_package) n So To f,
        p n = Some (So ; To ; f) →
        (n, (So, To)) \in E →
        trim E p n = Some (So ; To ; f).
    Proof.
      intros E p n So To f e h.
      unfold trim. rewrite filtermE. rewrite e. cbn.
      rewrite h. reflexivity.
    Qed.

    Lemma valid_trim :
      ∀ L I E p,
        valid_package L I E p →
        valid_package L I E (trim E p).
    Proof.
      intros L I E p h.
      intros [n [So To]] ho.
      specialize (h _ ho). cbn in h. destruct h as [f [ef hf]].
      exists f. intuition auto.
      apply trim_get. all: auto.
    Qed.

    Lemma link_valid :
      ∀ L1 L2 I M E p1 p2,
        valid_package L1 M E p1 →
        valid_package L2 I M p2 →
        valid_package (L1 :|: L2) I E (raw_link (trim E p1) p2).
    Proof.
      intros L1 L2 I M E p1 p2 h1 h2.
      intros [n [So To]] ho. unfold raw_link.
      rewrite mapmE.
      specialize (h1 _ ho) as h1'. cbn in h1'.
      destruct h1' as [f [ef hf]].
      erewrite trim_get. 2-3: eauto.
      cbn.
      eexists. split. 1: reflexivity.
      intro x.
      eapply raw_program_link_valid.
      - eapply valid_injectLocations.
        + apply fsubsetUl.
        + eapply hf.
      - eapply valid_package_inject_locations.
        + apply fsubsetUr.
        + auto.
    Qed.

    (* Sequential composition p1 ∘ p2 *)
    (* link_ is raw_link *)
    Definition link {I M E} (p1 : package M E) (p2 : package I M) : package I E.
    Proof.
      exists (p1.π1 :|: p2.π1).
      exists (raw_link (trim E (p1.π2 ∙1)) (p2.π2 ∙1)).
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]]. cbn.
      eapply link_valid. all: eauto.
    Defined.

    Definition link' {I M1 M2 E} (p1 : package M1 E) (p2 : package I M2)
      (h : fsubset M1 M2) : package I E.
    Proof.
      exists (p1.π1 :|: p2.π1).
      exists (raw_link (trim E (p1.π2 ∙1)) (p2.π2 ∙1)).
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]]. cbn.
      eapply link_valid.
      - eauto.
      - eapply valid_package_inject_export. all: eauto.
    Defined.

    Lemma package_ext :
      ∀ {I E} (p1 p2 : package I E),
        p1.π1 = p2.π1 →
        p1.π2 ∙1 =1 p2.π2 ∙1 →
        p1 = p2.
    Proof.
      intros I E p1 p2 e1 e2.
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]].
      apply eq_fmap in e2.
      cbn in *. subst.
      f_equal. f_equal. apply proof_irrelevance.
    Qed.

    (* Technical lemma before proving assoc *)
    Lemma raw_link_trim_commut :
      ∀ E p1 p2,
        raw_link (trim E p1) p2 =
        trim E (raw_link p1 p2).
    Proof.
      intros E p1 p2.
      apply eq_fmap. intro n.
      unfold raw_link. unfold trim.
      repeat rewrite ?filtermE ?mapmE.
      destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
      cbn.
      destruct ((n, (S1, T1)) \in E) eqn:e1.
      2:{ rewrite e1. cbn. reflexivity. }
      rewrite e1. cbn. reflexivity.
    Qed.

    Lemma trim_invol :
      ∀ E p,
        trim E (trim E p) = trim E p.
    Proof.
      intros E p.
      apply eq_fmap. intro n.
      unfold trim. rewrite !filtermE.
      destruct (p n) as [[S1 [T1 f1]]|] eqn:e.
      2:{ rewrite e. cbn. reflexivity. }
      rewrite e. cbn.
      destruct ((n, (S1, T1)) \in E) eqn:e1.
      2:{ rewrite e1. cbn. reflexivity. }
      rewrite e1. cbn. rewrite e1. reflexivity.
    Qed.

    Lemma lookup_op_trim :
      ∀ E o p,
        lookup_op (trim E p) o =
        obind (λ f, if o \in E then Some f else None) (lookup_op p o).
    Proof.
      intros E [n [So To]] p.
      unfold lookup_op, trim.
      rewrite filtermE.
      destruct (p n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
      cbn.
      destruct ((n, (S1, T1)) \in E) eqn:e1.
      - rewrite e1. destruct chUniverse_eqP. 2: reflexivity.
        destruct chUniverse_eqP. 2: reflexivity.
        cbn. subst. cbn. rewrite e1. reflexivity.
      - rewrite e1.
        destruct chUniverse_eqP. 2: reflexivity.
        destruct chUniverse_eqP. 2: reflexivity.
        subst. rewrite e1. cbn. reflexivity.
    Qed.

    Lemma raw_program_link_trim_right :
      ∀ A L E (v : raw_program A) p,
        valid_program L E v →
        raw_program_link v (trim E p) = raw_program_link v p.
    Proof.
      intros A L E v p h.
      induction v in p, h |- *.
      - cbn. reflexivity.
      - cbn. cbn in h. rewrite lookup_op_trim.
        destruct h as [ho h].
        destruct lookup_op eqn:e.
        + cbn. rewrite ho. f_equal. apply functional_extensionality.
          intuition auto.
        + cbn. f_equal. apply functional_extensionality.
          intuition auto.
      - cbn. cbn in h. f_equal. apply functional_extensionality.
        intuition auto.
      - cbn. cbn in h. f_equal. intuition auto.
      - cbn. cbn in h. f_equal. apply functional_extensionality.
        intuition auto.
    Qed.

    Lemma trim_get_inv :
      ∀ E p n So To f,
        trim E p n = Some (So ; To ; f) →
        p n = Some (So ; To ; f) ∧ (n, (So, To)) \in E.
    Proof.
      intros E p n So To f e.
      unfold trim in e. rewrite filtermE in e. cbn in e.
      destruct (p n) as [[S1 [T1 f1]]|] eqn:e1.
      2:{ rewrite e1 in e. cbn in e. discriminate. }
      rewrite e1 in e. cbn in e.
      destruct ((n, (S1, T1)) \in E) eqn:e2.
      2:{ rewrite e2 in e. discriminate. }
      rewrite e2 in e. noconf e.
      intuition auto.
    Qed.

    Lemma raw_link_trim_right :
      ∀ L I E p1 p2,
        valid_package L I E p1 →
        raw_link (trim E p1) (trim I p2) =
        raw_link (trim E p1) p2.
    Proof.
      intros L I E p1 p2 h.
      apply eq_fmap. intro n.
      unfold raw_link.
      rewrite !mapmE.
      destruct (trim E p1 n) as [[S1 [T1 f1]]|] eqn:e.
      2:{ rewrite e. reflexivity. }
      rewrite e. cbn.
      f_equal. f_equal. f_equal.
      extensionality x.
      apply trim_get_inv in e as [e he].
      specialize (h _ he). cbn in h.
      destruct h as [f [ef h]].
      rewrite ef in e. noconf e.
      eapply raw_program_link_trim_right.
      apply h.
    Qed.

    Lemma raw_link_assoc :
      ∀ L1 L2 E M1 M2 p1 p2 p3,
        valid_package L1 M1 E p1 →
        valid_package L2 M2 M1 p2 →
        raw_link (trim E p1) (raw_link (trim M1 p2) p3) =1
        raw_link (trim E (raw_link (trim E p1) p2)) p3.
    Proof.
      intros L1 L2 E M1 M2 p1 p2 p3 h1 h2.
      rewrite (raw_link_trim_commut M1).
      rewrite (raw_link_trim_commut _ _ p2).
      rewrite trim_invol.
      erewrite raw_link_trim_right. 2: eauto.
      unfold raw_link. unfold trim.
      intro n. repeat rewrite ?filtermE ?mapmE.
      destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
      cbn.
      destruct ((n, (S1, T1)) \in E) eqn:e1.
      2:{ rewrite e1. cbn. reflexivity. }
      rewrite e1. cbn.
      f_equal. f_equal. f_equal.
      extensionality x.
      rewrite raw_program_link_assoc.
      + reflexivity.
      + specialize (h1 _ e1). cbn in h1.
        destruct h1 as [g [eg hg]].
        rewrite eg in e. noconf e.
        eapply valid_provides.
        * eapply valid_injectLocations.
          -- eapply fsubsetUl.
          -- eapply hg.
        * eapply valid_package_inject_locations.
          -- eapply fsubsetUr.
          -- eauto.
    Qed.

    Lemma link_assoc :
      ∀ {E M1 M2 I}
        (p1 : package M1 E)
        (p2 : package M2 M1)
        (p3 : package I M2),
        link p1 (link p2 p3) = link (link p1 p2) p3.
    Proof.
      intros E M1 M2 I [l1 [p1 h1]] [l2 [p2 h2]] [l3 [p3 h3]].
      apply package_ext.
      - cbn. apply fsetUA.
      - cbn. eapply raw_link_assoc. all: eauto.
    Qed.

    (* bundled versions *)
    Definition blink p1 p2 (h : import p1 = export p2) : bundle.
    Proof.
      unshelve econstructor.
      - exact (locs p1 :|: locs p2).
      - exact (import p2).
      - exact (export p1).
      - exists (raw_link (trim (export p1) ((pack p1) ∙1)) ((pack p2) ∙1)).
        destruct p1 as [L1 I1 E1 [p1 h1]], p2 as [L2 I2 E2 [p2 h2]].
        cbn in h. subst. cbn.
        eapply link_valid. all: eauto.
    Defined.

    Lemma blink_export :
      ∀ p1 p2 (h : import p1 = export p2),
        export p1 = export (blink p1 p2 h).
    Proof.
      intros p1 p2 h.
      reflexivity.
    Defined.

    Lemma blink_import :
      ∀ p1 p2 h,
        import p2 = import (blink p1 p2 h).
    Proof.
      intros p1 p2 h.
      reflexivity.
    Defined.

    Lemma bundle_ext :
      ∀ (b1 b2 : bundle),
        locs b1 = locs b2 →
        import b1 = import b2 →
        export b1 = export b2 →
        (pack b1) ∙1 =1 (pack b2) ∙1 →
        b1 = b2.
    Proof.
      intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] el ei ee ep.
      cbn in *. apply eq_fmap in ep. subst. f_equal. f_equal.
      apply proof_irrelevance.
    Qed.

    Lemma blink_assoc :
      ∀ p1 p2 p3 (h12 : import p1 = export p2) (h23 : import p2 = export p3),
        blink p1 (blink p2 p3 h23) h12 =
        blink (blink p1 p2 h12) p3 h23.
    Proof.
      intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] [L3 I3 E3 [p3 h3]] h12 h23.
      cbn in *. subst.
      apply bundle_ext. all: cbn. 2,3: auto.
      - apply fsetUA.
      - eapply raw_link_assoc. all: eauto.
    Qed.

  End Link.

  Notation "p1 ∘ p2" := (link p1 p2) (right associativity, at level 80).

  Section Par.

    (** Because p1 and p2 might implement more than prescribed by their
        interface and in particular overlap, we trim them first.
    *)
    Definition raw_par (E1 E2 : Interface) (p1 p2 : raw_package) :=
      unionm (trim E1 p1) (trim E2 p2).

    (** When comparing export interfaces, since we disallow overloading
        we need to have only the identifier parts disjoint.
    *)
    Definition idents (E : Interface) : {fset ident} :=
      (λ '(n, _), n) @: E.

    Definition parable (E1 E2 : Interface) :=
      fdisjoint (idents E1) (idents E2).

    Lemma parable_sym :
      ∀ {E1 E2},
        parable E1 E2 →
        parable E2 E1.
    Proof.
      intros E1 E2 h.
      unfold parable.
      rewrite fdisjointC.
      auto.
    Qed.

    Lemma valid_par :
      ∀ {L1 L2 I1 I2 E1 E2 p1 p2},
        valid_package L1 I1 E1 p1 →
        valid_package L2 I2 E2 p2 →
        parable E1 E2 →
        valid_package (L1 :|: L2) (I1 :|: I2) (E1 :|: E2) (raw_par E1 E2 p1 p2).
    Proof.
      intros L1 L2 I1 I2 E1 E2 p1 p2 h1 h2 h.
      intros [n [So To]] ho.
      unfold raw_par. rewrite unionmE.
      destruct (trim E1 p1 n) as [[S1 [T1 f1]]|] eqn:e.
      - rewrite e. cbn.
        apply trim_get_inv in e as [e he].
        specialize (h1 _ he) as h1e. cbn in h1e.
        destruct h1e as [f [ef hf]].
        rewrite ef in e. noconf e.
        rewrite in_fsetU in ho. move: ho => /orP [ho|ho].
        2:{
          eapply mem_imfset with (f := λ '(n, _), n) in he.
          eapply mem_imfset with (f := λ '(n, _), n) in ho.
          exfalso. eapply disjoint_in_both. all: eauto.
        }
        specialize (h1 _ ho) as h1e. cbn in h1e.
        destruct h1e as [g [eg _]].
        rewrite ef in eg. noconf eg.
        exists f. split. 1: reflexivity.
        intro.
        eapply valid_injectLocations. 1: apply fsubsetUl.
        eapply valid_injectMap. 1: apply fsubsetUl.
        auto.
      - rewrite e. simpl.
        rewrite in_fsetU in ho. move: ho => /orP [ho|ho].
        1:{
          specialize (h1 _ ho). cbn in h1.
          destruct h1 as [f [ef hf]].
          eapply trim_get in ef. 2: eauto.
          rewrite ef in e. discriminate.
        }
        specialize (h2 _ ho). cbn in h2.
        destruct h2 as [f [ef hf]].
        eapply trim_get in ef as etf. 2: eauto.
        exists f. intuition auto.
        eapply valid_injectLocations. 1: apply fsubsetUr.
        eapply valid_injectMap. 1: apply fsubsetUr.
        auto.
    Qed.

    Definition bpar (p1 p2 : bundle) (h : parable (export p1) (export p2)) :
      bundle.
    Proof.
      unshelve econstructor.
      - exact (locs p1 :|: locs p2).
      - exact (import p1 :|: import p2).
      - exact (export p1 :|: export p2).
      - exists (raw_par (export p1) (export p2) (pack p1) ∙1 (pack p2) ∙1).
        destruct p1 as [L1 I1 E1 [p1 h1]], p2 as [L2 I2 E2 [p2 h2]].
        cbn - [raw_par fdisjoint] in *.
        apply valid_par. all: auto.
    Defined.

    Lemma fsubset_ext :
      ∀ (A : ordType) (s1 s2 : {fset A}),
        (∀ x, x \in s1 → x \in s2) →
        fsubset s1 s2.
    Proof.
      intros A s1 s2 h.
      cbn. apply/eqP. pose proof (eq_fset (s1 :|: s2) s2) as [h1 h2].
      forward h1.
      { intro x. rewrite in_fsetU.
        destruct (x \in s1) eqn:e.
        - cbn. symmetry. apply h. auto.
        - cbn. reflexivity.
      }
      rewrite h1. reflexivity.
    Qed.

    Lemma trim_domm_subset :
      ∀ E p,
        fsubset (domm (trim E p)) (idents E).
    Proof.
      intros E p.
      apply fsubset_ext. intros x h.
      rewrite mem_domm in h.
      destruct (trim E p x) as [[So [To f]]|] eqn:e. 2: discriminate.
      apply trim_get_inv in e as [? e].
      eapply mem_imfset with (f := λ '(n, _), n) in e.
      auto.
    Qed.

    (** To circumvent the very annoying lemmata that conclude on equality
        of coerced arguments when it is the same as concluding global equality!
    *)
    Lemma fsval_eq :
      ∀ (A : ordType) (u v : {fset A}),
        FSet.fsval u = FSet.fsval v →
        u = v.
    Proof.
      intros A [u hu] [v hv] e.
      cbn in e. subst. f_equal.
      apply bool_irrelevance.
    Qed.

    Lemma raw_par_commut :
      ∀ E1 E2 p1 p2,
        parable E1 E2 →
        raw_par E1 E2 p1 p2 = raw_par E2 E1 p2 p1.
    Proof.
      intros E1 E2 p1 p2 h.
      apply eq_fmap.
      intro n. unfold raw_par. f_equal.
      apply unionmC.
      unfold parable in h.
      pose proof (trim_domm_subset E1 p1) as s1.
      pose proof (trim_domm_subset E2 p2) as s2.
      cbn in s1. cbn in s2.
      move: s1 => /eqP s1. move: s2 => /eqP s2.
      apply fsval_eq in s1. apply fsval_eq in s2.
      rewrite <- s1 in h. rewrite <- s2 in h.
      rewrite !fdisjointUr !fdisjointUl in h.
      move: h => /andP [h _]. move: h => /andP [h _].
      auto.
    Qed.

    Lemma bpar_commut :
      ∀ p1 p2 (h : parable (export p1) (export p2)),
        bpar p1 p2 h = bpar p2 p1 (parable_sym h).
    Proof.
      intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] h.
      simpl in *.
      apply bundle_ext. all: simpl.
      1-3: apply fsetUC.
      intro. f_equal.
      apply raw_par_commut. assumption.
    Qed.

    Definition par {I1 I2 E1 E2} (p1 : package I1 E1) (p2 : package I2 E2)
      (h : parable E1 E2) : package (I1 :|: I2) (E1 :|: E2).
    Proof.
      exists (p1.π1 :|: p2.π1).
      exists (raw_par E1 E2 p1.π2 ∙1 p2.π2 ∙1).
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]]. simpl.
      apply valid_par. all: auto.
    Defined.

    Definition opackage_transport {L I1 I2 E1 E2} (eI : I1 = I2) (eE : E1 = E2)
      (p : opackage L I1 E1) : opackage L I2 E2.
      (* exist (valid_package L I2 E2) (p ∙1) (eI ⋅ eE ⋅ (p ∙2)). *)
    Proof.
      exists (p ∙1).
      destruct p as [p h]. cbn.
      subst. auto.
    Defined.

    Definition package_transport {I1 I2 E1 E2} (eI : I1 = I2) (eE : E1 = E2)
      (p : package I1 E1) : package I2 E2 :=
      (p.π1 ; opackage_transport eI eE p.π2).

    Lemma par_commut :
      ∀ {I1 I2 E1 E2} (p1 : package I1 E1) (p2 : package I2 E2)
        (h : parable E1 E2),
        par p1 p2 h =
        package_transport (fsetUC I2 I1) (fsetUC E2 E1) (par p2 p1 (parable_sym h)).
    Proof.
      intros I1 I2 E1 E2 [L1 p1] [L2 p2] h.
      apply package_ext.
      - cbn. apply fsetUC.
      - simpl. destruct p1 as [p1 h1], p2 as [p2 h2].
        simpl. intro. f_equal. apply raw_par_commut. assumption.
    Qed.

    Lemma trim_raw_par :
      ∀ E1 E2 p1 p2,
        trim (E1 :|: E2) (raw_par E1 E2 p1 p2) = raw_par E1 E2 p1 p2.
    Proof.
      intros E1 E2 p1 p2.
      unfold raw_par. apply eq_fmap.
      intro n. rewrite unionmE.
      destruct (trim E1 p1 n) as [[S1 [T1 f1]]|] eqn:e1.
      - simpl. unfold trim at 1. rewrite filtermE.
        rewrite unionmE. rewrite e1. simpl.
        apply trim_get_inv in e1. destruct e1 as [? e].
        rewrite in_fsetU. rewrite e. reflexivity.
      - simpl. unfold trim at 1. rewrite filtermE.
        rewrite unionmE. rewrite e1. simpl.
        destruct (trim E2 p2 n) as [[S2 [T2 f2]]|] eqn:e2.
        + rewrite e2. simpl.
          apply trim_get_inv in e2. destruct e2 as [? e].
          rewrite in_fsetU. rewrite e. rewrite orbT. reflexivity.
        + rewrite e2. simpl. reflexivity.
    Qed.

    Lemma raw_link_unionm :
      ∀ p1 p2 p3,
        raw_link (unionm p1 p2) p3 =
        unionm (raw_link p1 p3) (raw_link p2 p3).
    Proof.
      intros p1 p2 p3.
      apply eq_fmap. intro n.
      rewrite unionmE. unfold raw_link at 1.
      rewrite mapmE. rewrite unionmE.
      unfold raw_link at 1.
      rewrite mapmE.
      destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e1.
      - simpl. reflexivity.
      - simpl. destruct (p2 n) as [[S2 [T2 f2]]|] eqn:e2.
        + simpl. unfold raw_link.
          rewrite mapmE. rewrite e2. simpl. reflexivity.
        + simpl. unfold raw_link.
          rewrite mapmE. rewrite e2. simpl. reflexivity.
    Qed.

    Lemma lookup_op_unionm :
      ∀ p1 p2 o,
        lookup_op (unionm p1 p2) o =
        if isSome (p1 (fst o)) then lookup_op p1 o else lookup_op p2 o.
    Proof.
      intros p1 p2 [n [So To]].
      cbn. rewrite unionmE.
      destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e1. all: reflexivity.
    Qed.

    Lemma raw_program_link_raw_par_left :
      ∀ A I L L' E1 E2 (v : raw_program A) p1 p2,
        valid_program L E1 v →
        valid_package L' I E1 p1 →
        raw_program_link v (raw_par E1 E2 p1 p2) =
        raw_program_link v p1.
    Proof.
      intros A I L L' E1 E2 v p1 p2 hv h.
      induction v in hv |- *.
      - cbn. reflexivity.
      - simpl. cbn in hv. destruct hv as [ho hv].
        rewrite lookup_op_unionm.
        pose proof (lookup_op_trim E1 o p1) as e1.
        pose proof (lookup_op_trim E2 o p2) as e2.
        rewrite e1. rewrite e2. clear e1 e2.
        eapply lookup_op_valid in h as hf. 2: eauto.
        destruct hf as [f [ef hf]].
        rewrite ef.
        simpl. rewrite ho.
        destruct (trim E1 p1 o.1) eqn:e1.
        2:{
          exfalso. destruct o as [n [So To]]. cbn - [lookup_op trim] in *.
          unfold trim in e1. rewrite filtermE in e1.
          destruct (p1 n) as [[St [Tt g]]|] eqn:e2.
          2:{ clear e1. cbn in ef. rewrite e2 in ef. discriminate. }
          rewrite e2 in e1. cbn in e1.
          cbn in ef. rewrite e2 in ef.
          destruct chUniverse_eqP. 2: discriminate.
          destruct chUniverse_eqP. 2: discriminate.
          subst. rewrite ho in e1. discriminate.
        }
        rewrite e1. simpl. f_equal. apply functional_extensionality.
        intuition auto.
      - simpl. cbn in hv. f_equal. apply functional_extensionality.
        intuition auto.
      - simpl. cbn in hv. f_equal.
        intuition auto.
      - simpl. cbn in hv. f_equal. apply functional_extensionality.
        intuition auto.
    Qed.

    Lemma import_raw_par_left :
      ∀ {E1 E2 E3 L L' I} p1 p2 p3,
        valid_package L E2 E1 p1 →
        valid_package L' I E2 p2 →
        raw_link (trim E1 p1) (raw_par E2 E3 p2 p3) =
        raw_link (trim E1 p1) p2.
    Proof.
      intros E1 E2 E3 L L' I p1 p2 p3 h1 h2.
      apply eq_fmap. intro n.
      unfold raw_link. rewrite !mapmE.
      destruct (trim E1 p1 n) as [[S1 [T1 f1]]|] eqn:e1.
      - rewrite e1. simpl. f_equal. f_equal. f_equal.
        apply trim_get_inv in e1 as e2.
        destruct e2 as [e2 hh].
        specialize (h1 _ hh). cbn in h1.
        destruct h1 as [f [ef hf]].
        rewrite ef in e2. noconf e2.
        extensionality x. eapply raw_program_link_raw_par_left. all: eauto.
      - rewrite e1. simpl. reflexivity.
    Qed.

    Lemma import_raw_par_right :
      ∀ {E1 E2 E3 L L' I} p1 p2 p3,
        parable E2 E3 →
        valid_package L E3 E1 p1 →
        valid_package L' I E3 p3 →
        raw_link (trim E1 p1) (raw_par E2 E3 p2 p3) =
        raw_link (trim E1 p1) p3.
    Proof.
      intros E1 E2 E3 L L' I p1 p2 p3 hE h1 h2.
      rewrite raw_par_commut. 2: auto.
      erewrite import_raw_par_left. all: eauto.
    Qed.

    Lemma interchange :
      ∀ A B C D E F c1 c2
        (p1 : package B A)
        (p2 : package E D)
        (p3 : package C B)
        (p4 : package F E),
        par (link p1 p3) (link p2 p4) c1 =
        link (par p1 p2 c1) (par p3 p4 c2).
    Proof.
      intros A B C D E F c1 c2.
      intros [L1 [p1 h1]] [L2 [p2 h2]] [L3 [p3 h3]] [L4 [p4 h4]].
      apply package_ext.
      - cbn. rewrite !fsetUA. f_equal. rewrite fsetUC. rewrite fsetUA. f_equal.
        apply fsetUC.
      - simpl. unfold raw_par.
        rewrite <- raw_link_trim_commut. rewrite trim_invol.
        rewrite <- raw_link_trim_commut. rewrite trim_invol.
        rewrite trim_raw_par. unfold raw_par.
        rewrite raw_link_unionm.
        erewrite <- import_raw_par_left. 2-3: eauto.
        erewrite <- (import_raw_par_right p2 _ p4). 2-4: eauto.
        intro. reflexivity.
    Qed.

  End Par.

  (** Package builder

    The same way we have constructors for program, we provide constructors
    for packages that are correct by construction.
  *)
  Definition pointed_vprogram L I :=
    ∑ (S T : chUniverse), S → program L I T.

  Definition export_interface {L I} (p : {fmap ident -> pointed_vprogram L I})
    : Interface :=
    fset (mapm (λ '(So ; To ; f), (So, To)) p).

  Definition mkpack {L I} (p : {fmap ident -> pointed_vprogram L I}) :
    opackage L I (export_interface p).
  Proof.
    exists (@mapm _ (pointed_vprogram L I) pointed_program
      (λ '(So ; To ; f), (So ; To ; λ x, (f x) ∙1)) p).
    intros [n [So To]] ho.
    rewrite mapmE. unfold export_interface in ho.
    rewrite in_fset in ho.
    move: ho => /getmP ho. rewrite mapmE in ho.
    destruct (p n) as [[S [T f]]|] eqn:e.
    2:{ rewrite e in ho. cbn in ho. discriminate. }
    rewrite e in ho. cbn in ho. noconf ho.
    exists (λ x, (f x) ∙1). simpl. intuition auto.
    exact ((f x) ∙2).
  Defined.

  (* Alternative from a function *)
  Equations? map_interface (I : seq opsig) {A} (f : ∀ x, x \in I → A) : seq A :=
      map_interface (a :: I') f := f a _ :: map_interface I' (λ x h, f x _) ;
      map_interface [::] f := [::].
    Proof.
      - rewrite in_cons. apply/orP. left. apply/eqP. reflexivity.
      - rewrite in_cons. apply/orP. right. auto.
    Qed.

  Notation "[ 'interface' e | h # x ∈ I ]" := (map_interface I (λ x h, e)).

  (* Lemma getm_def_map_interface :
    ∀ A I (f : ∀ x, x \in I → A) n,
      getm_def [interface (ide x, f x h) | h # x ∈ I] n =
      omap (λ x, f (n, x) _) (getm_def I n). *)

  Lemma getm_def_map_interface_Some :
    ∀ A (I : seq opsig) (f : ∀ x, x \in I → A) n y,
      getm_def [interface (ide x, f x h) | h # x ∈ I] n = Some y →
      ∃ z h, getm_def I n = Some z ∧ y = f (n, z) h.
  Proof.
    cbn. intros A I f n y e.
    induction I in f, n, y, e |- *.
    - simp map_interface in e. discriminate.
    - simp map_interface in e. cbn in e.
      destruct eqn eqn:e1.
      + noconf e. cbn. replace (ide a) with a.1 in e1.
        2:{ destruct a as [? [? ?]]. cbn. reflexivity. }
        rewrite e1. move: e1 => /eqP e1. subst.
        exists a.2. unshelve eexists.
        { destruct a. cbn. rewrite in_cons.
          apply/orP. left. apply/eqP. reflexivity.
        }
        split. 1: reflexivity.
        destruct a. cbn. f_equal.
        apply bool_irrelevance.
      + replace (ide a) with a.1 in e1.
        2:{ destruct a as [? [? ?]]. cbn. reflexivity. }
        cbn. rewrite e1.
        specialize IHI with (1 := e).
        destruct IHI as [z [h [h1 h2]]].
        exists z. unshelve eexists.
        { rewrite in_cons. apply/orP. right. auto. }
        intuition auto. subst. f_equal.
        apply bool_irrelevance.
  Qed.

  Definition funmkpack {L I} {E : Interface}
    (f : ∀ (o : opsig), o \in E → src o → program L I (tgt o)) :
    opackage L I E.
  Proof.
    pose foo : seq (nat * pointed_vprogram L I) :=
      [interface (ide o, (chsrc o ; chtgt o ; f o h)) | h # o ∈ E].
    pose bar := mkfmap foo.
    exists (@mapm _ (pointed_vprogram L I) pointed_program
      (λ '(So ; To ; f), (So ; To ; λ x, (f x) ∙1)) bar).
    intros [n [So To]] ho.
    rewrite mapmE. subst bar foo.
    rewrite mkfmapE.
  Abort.

  Section ID.

    Definition preid_prog {L I} (o : opsig) (h : o \in I) :
      ident * pointed_vprogram L I :=
      (let '(n, (So, To)) := o in
      λ h, (n, (So ; To ; λ s, opr (n, (So, To)) h s (λ x, ret x)))) h.

    Definition preid L I : {fmap ident -> pointed_vprogram L I} :=
      mkfmap [interface preid_prog x h | h # x ∈ I].

    Lemma fset_ext :
      ∀ (A : ordType) (s1 s2 : {fset A}),
        (∀ x, x \in s1 ↔ x \in s2) →
        s1 = s2.
    Proof.
      intros A s1 s2 h.
      apply/eqP. rewrite eqEfsubset.
      apply/andP. split.
      - apply fsubset_ext. intros. eapply h. auto.
      - apply fsubset_ext. intros. eapply h. auto.
    Qed.

    (* Maybe specialise even further to producing packages *)
    Lemma get_map_interface_Some_inv :
      ∀ {A} (I : seq opsig) (f : ∀ x, x \in I → nat * A) n (x : A),
        getm_def (map_interface I f) n = Some x →
        ∃ y h, getm_def I n = Some y ∧ (n, x) = f (n, y) h.
    Proof.
      cbn. intros A I f n x e.
      induction I in n, x, f, e |- *.
      - simp map_interface in e. cbn in e. discriminate.
      - simp map_interface in e. cbn in e. cbn.
        destruct eqn eqn:e1.
        + noconf e. move: e1 => /eqP e1. subst.
          cbn.
    Abort.

    Lemma export_id :
      ∀ L I, export_interface (preid L I) = I.
    Proof.
      intros L I. apply fset_ext.
      cbn. intros [n [S T]].
      unfold export_interface. rewrite in_fset.
      split.
      - move/getmP => h. rewrite mapmE in h.
        unfold preid in h. rewrite mkfmapE in h.
        destruct getm_def as [[? [? f]]|] eqn:e. 2: discriminate.
        simpl in h. noconf h.
    Abort.

    Definition id L I := mkpack (preid L I).

    Definition make_proxy (op : opsig) : ident * pointed_program :=
      let '(n, (So, To)) := op in
      (n, (So ; To ; λ s, _opr (n, (So, To)) s (λ k, _ret k))).

    Definition ID (I : Interface) : package I I.
    Proof.
      exists fset0.
      exists (mkfmap [seq make_proxy x | x <- I]).
      intros [n [So To]] ho.
      rewrite mkfmapE.
    Admitted.

  End ID.

  End PackageModule.

  Section Games.
    Definition Game_import : Interface := fset0.
    Definition Game_Type (Game_export : Interface) : Type :=
      package Game_import Game_export.

    Definition RUN := (0, (chUnit, chBool)).
    Definition A_export : Interface := fset1 RUN.
    Lemma RUN_in_A_export : RUN \in A_export.
      apply in_fset1.
    Qed.

    Definition Adversary4Game (Game_export : Interface) : Type :=
      package Game_export A_export.


    Open Scope fset.
    Let iops_StP := @ops_StP probE rel_choiceTypes chEmb.
    Let iar_StP := @ar_StP probE rel_choiceTypes chEmb.

    Definition dommHeap (s : {fset Location}) := { x : Location | x \in s }.

    Definition makeHeap (s : {fset Location}) :=
      {fmap (dommHeap s) → Value}.

    Definition makeHeap_cT (s : {fset Location}) :=
      [choiceType of (makeHeap s)].

    Definition Game_op_import_S : Type := {_ : ident & void}.
    Definition Game_import_P : Game_op_import_S → choiceType :=
      fun v => match v with existT a b => match b with end end.

    Definition getFromMap
               {locs : {fset Location}}
               (map : {fmap {x : Location | x \in locs} → Value})
               (l : Location) (H : l \in locs) : Value.
    Proof.
      destruct (getm map (exist _ l H)) eqn:Hget.
      + exact s.
      + exact 0.
    Defined.

    Definition setFromMap
               {locs : {fset Location}}
               (map : {fmap {x : Location | x \in locs} → Value})
               (l : Location) (H : l \in locs) (v : Value) : {fmap {x : Location | x \in locs} → Value}.
    Proof.
      apply (setm map).
      - exists l. exact H.
      - exact v.
    Defined.

    Definition fromEmpty {B} {v : opsig} (H : v \in fset0) : B.
      rewrite in_fset0 in H.
      move: H. move /eqP. move /eqP => H.
      discriminate.
    Defined.
    From Crypt Require Import FreeProbProg.

    Definition FreeTranslate {B : choiceType} {locs : {fset Location}} (v : raw_program B)
               (v_is_valid : valid_program locs Game_import v)
      : rFreeF (iops_StP (makeHeap_cT locs)) (iar_StP (makeHeap_cT locs)) B.
    Proof.
      induction v.
      - apply FreeProbProg.retrFree. exact x.
      - inversion v_is_valid as [Habs _].
        apply (fromEmpty Habs).
      - apply (FreeProbProg.ropr _ _ _ (inl (inl (gett _)))).
        inversion v_is_valid as [Hin Hk].
        move => s0. apply (X (getFromMap s0 l Hin)).
        apply Hk.
      - apply (FreeProbProg.ropr _ _ _ (inl (inl (gett (makeHeap_cT locs))))).
        simpl. move => s0. inversion v_is_valid as [Hin Hk].
        apply (FreeProbProg.ropr _ _ _ (inl (inr (putt (makeHeap_cT locs) (setFromMap s0 l Hin v))))).
        move => s1.
        apply IHv.
        exact Hk.
      - apply (FreeProbProg.ropr _ _ _ (inr op)).
        move => s0. apply (X s0). simpl in v_is_valid.
        apply v_is_valid.
    Defined.

    Definition Pr (P : package Game_import A_export) : SDistr (bool_choiceType).
    Proof.
      destruct P as [locs [PP PP_is_valid]].
      destruct (lookup_op PP RUN) eqn:eq_PP0.
      - pose V := FreeTranslate (r Datatypes.tt).
        pose (lookup_op_valid locs Game_import A_export PP RUN PP_is_valid RUN_in_A_export).
        assert (valid_program locs Game_import (r Datatypes.tt)).
        { destruct e. inversion H. symmetry in eq_PP0. induction eq_PP0.
          inversion H0. apply H1. }
        pose V' := (V locs H).
        pose STDIST := thetaFstd _ V'.
        simpl in STDIST.
        pose SSDIST := STDIST prob_handler emptym.
        refine (SDistr_bind _ _ (fun '(b, _) => SDistr_unit _ b) SSDIST).
      - assert False.
        { pose (lookup_op_valid locs Game_import A_export PP RUN PP_is_valid RUN_in_A_export).
          destruct e. inversion H. symmetry in eq_PP0. destruct eq_PP0. discriminate. }
        contradiction.
    Defined.
  End Games.
End PackageTheory.
