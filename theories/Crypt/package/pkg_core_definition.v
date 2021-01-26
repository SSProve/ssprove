(*
  This file defines "packages" of stateful probabilistic computation.
  It should not be directly required but instead used via Package.v.

  * raw_package (computational part of a package without validity conditions)


 *)

From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd RulesStateProb StateTransformingLaxMorph
     pkg_chUniverse.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


(* General definitions *)

Declare Scope package_scope.
Delimit Scope package_scope with pack.


Module CorePackageTheory (π : RulesParam).

  Local Open Scope fset.
  Local Open Scope fset_scope.
  Local Open Scope type_scope.

  Import π.

  Definition ident := nat.

  (* Signature of an operation, including the identifier *)
  Definition opsig := ident * (chUniverse * chUniverse).
  (* Record opsig := mkop {
  ident : nat ;
  src : chUniverse ;
  tgt : chUniverse
  }. *)

  Definition Location := ∑ (t : chUniverse), nat.
  Definition Value (t : chUniverse) := chElement t.

  Definition Interface := {fset opsig}.

  Definition ide (v : opsig) : ident :=
    let '(n, _) := v in n.

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
    | _getr (l : Location) (k : Value l.π1 → raw_program A)
    | _putr (l : Location) (v : Value l.π1) (k : raw_program A)
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

    Definition getr [A : choiceType] l (h : l \in Loc) (k : Value l.π1 → program A) :
      program A.
    Proof.
      pose k' := λ x, (k x) ∙1.
      exists (_getr l k').
      subst k'. cbn. intuition auto.
      exact ((k v) ∙2).
    Defined.

    Definition putr [A : choiceType] l (h : l \in Loc) (v : Value l.π1)
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

    Lemma prove_program :
      ∀ {A} (P : program A → Type) p q,
        P p →
        p ∙1 = q ∙1 →
        P q.
    Proof.
      intros A P p q h e.
      apply program_ext in e. subst. auto.
    Defined.

    Lemma program_rect :
      ∀ (A : choiceType) (P : program A → Type),
        (∀ x : A, P (ret x)) →
        (∀ (o : opsig) (h : o \in import) (x : src o) (k : tgt o → program A),
          (∀ s : tgt o, P (k s)) → P (opr o h x k)
        ) →
        (∀ (l : Location) (h : l \in Loc) (k : Value l.π1 → program A),
          (∀ s : Value l.π1, P (k s)) → P (getr l h k)
        ) →
        (∀ (l : Location) (h : l \in Loc) (v : Value l.π1) (k : program A),
          P k → P (putr l h v k)
        ) →
        (∀ (op : Op) (k : Arit op → program A),
          (∀ s : Arit op, P (k s)) → P (sampler op k)
        ) →
        ∀ p : program A, P p.
    Proof.
      intros A P hret hop hget hput hsamp.
      intros [p h]. revert p h. fix aux 1.
      intros p h. destruct p.
      - eapply prove_program. 1: eapply hret.
        reflexivity.
      - cbn in h.
        eapply prove_program.
        + unshelve eapply hop.
          5:{
            intro s. unshelve eapply aux.
            - eapply (k s).
            - destruct h as [ho hk]. auto.
          }
          * destruct h as [ho hk]. auto.
          * auto.
        + reflexivity.
      - cbn in h.
        eapply prove_program.
        + unshelve eapply hget.
          4:{
            intros s. unshelve eapply aux.
            - eapply (k s).
            - destruct h as [ho hk]. auto.
          }
          * destruct h as [ho hk]. auto.
        + reflexivity.
      - cbn in h.
        eapply prove_program.
        + unshelve eapply hput.
          5:{
            unshelve eapply aux.
            - eapply p.
            - destruct h as [ho hk]. auto.
          }
          * auto.
          * destruct h as [ho hk]. auto.
          * auto.
        + reflexivity.
      - cbn in h.
        eapply prove_program.
        + unshelve eapply hsamp.
          3:{
            intro s. unshelve eapply aux.
            - eapply (k s).
            - auto.
          }
        + reflexivity.
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
  Arguments bind [Loc] [import] [A] [B] _ _.


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
        bind (injectLocations h v) (fun w => injectLocations h (f w)) =
        injectLocations h (bind v f).
    Proof.
      intros A B h v f.
      apply program_ext. cbn. reflexivity.
    Qed.

  End commuteBindLocations.

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

End CorePackageTheory.
