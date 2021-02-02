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

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

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
    (* The "small" type of relevant choiceTypes *)
    Context (rel_choiceTypes : Type).
    Context (chEmb : rel_choiceTypes → choiceType).

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
    | ret (x : A)
    | opr (o : opsig) (x : src o) (k : tgt o → raw_program A)
    | getr (l : Location) (k : Value l.π1 → raw_program A)
    | putr (l : Location) (v : Value l.π1) (k : raw_program A)
    | sampler (op : Op) (k : Arit op → raw_program A).

    Arguments ret [A] _.
    Arguments opr [A] _ _.
    Arguments getr [A] _.
    Arguments putr [A] _.
    Arguments sampler [A] _ _.

    Inductive valid_program {A} : raw_program A → Prop :=
    | valid_ret :
        ∀ x,
          valid_program (ret x)

    | valid_opr :
        ∀ o x k,
          o \in import →
          (∀ v, valid_program (k v)) →
          valid_program (opr o x k)

    | valid_getr :
        ∀ l k,
          l \in Loc →
          (∀ v, valid_program (k v)) →
          valid_program (getr l k)

    | valid_putr :
        ∀ l v k,
          l \in Loc →
          valid_program k →
          valid_program (putr l v k)

    | valid_sampler :
        ∀ op k,
          (∀ v, valid_program (k v)) →
          valid_program (sampler op k)
    .

    Derive NoConfusion NoConfusionHom for chUniverse.
    Derive NoConfusion NoConfusionHom EqDec for nat.
    Derive NoConfusion NoConfusionHom for raw_program.
    Derive Signature for valid_program.

    (* Inversion lemmata *)

    Lemma inversion_valid_opr :
      ∀ {A o x k},
        @valid_program A (opr o x k) →
        (o \in import) *
        (∀ v, valid_program (k v)).
    Proof.
      intros A o x k h.
      dependent destruction h.
      intuition auto.
    Qed.

    Lemma inversion_valid_getr :
      ∀ {A l k},
        @valid_program A (getr l k) →
        (l \in Loc) *
        (∀ v, valid_program (k v)).
    Proof.
      intros A l k h.
      dependent destruction h.
      intuition auto.
    Qed.

    Lemma inversion_valid_putr :
      ∀ {A l v k},
        @valid_program A (putr l v k) →
        (l \in Loc) *
        (valid_program k).
    Proof.
      intros A l v k h.
      dependent destruction h.
      intuition auto.
    Qed.

    Lemma inversion_valid_sampler :
      ∀ {A op k},
        @valid_program A (sampler op k) →
        ∀ v, valid_program (k v).
    Proof.
      intros A op k h.
      dependent destruction h.
      auto.
    Qed.

    Class ValidProgram {A} (p : raw_program A) :=
      is_valid_program : valid_program p.

    (* Instance ValidProgram_ret (A : choiceType) (x : A) : ValidProgram (ret x).
    Proof.
      apply valid_ret.
    Qed. *)

    Lemma valid_program_from_class :
      ∀ A (p : raw_program A),
        ValidProgram p →
        valid_program p.
    Proof.
      intros A p h. auto.
    Defined.

    (* Hint Extern 1 (ValidProgram (opr ?o ?x ?k)) =>
      apply valid_opr ; [
        eauto
      | intro ; apply valid_program_from_class
      ] : typeclass_instances.

    Hint Extern 1 (ValidProgram (getr ?o ?x ?k)) =>
      apply valid_getr ; [
        eauto
      | intro ; apply valid_program_from_class
      ] : typeclass_instances.

    Hint Extern 1 (ValidProgram (putr ?o ?x ?k)) =>
      apply valid_putr ; [
        eauto
      | apply valid_program_from_class
      ] : typeclass_instances.

    Hint Extern 1 (ValidProgram (sampler ?op ?k)) =>
      apply valid_sampler ;
      intro ; apply valid_program_from_class
      : typeclass_instances. *)

    Record program A := mkprog {
      prog : raw_program A ;
      prog_valid : ValidProgram prog
    }.

    Arguments mkprog {_} _.
    Arguments prog {_} _.
    Arguments prog_valid {_} _.

    (* Notation "{ 'program' p }" :=
      (mkprog p _)
      (format "{ program  p  }") : package_scope. *)

    Lemma program_ext :
      ∀ A (u v : program A),
        u.(prog) = v.(prog) →
        u = v.
    Proof.
      intros A u v h.
      destruct u as [u hu], v as [v hv].
      cbn in h. subst.
      f_equal. apply proof_irrelevance.
    Qed.

    Fixpoint bind {A B} (c : raw_program A) (k : A → raw_program B) :
      raw_program B :=
      match c with
      | ret a => k a
      | opr o x k'  => opr o x (λ p, bind (k' p) k)
      | getr l k' => getr l (λ v, bind (k' v) k)
      | putr l v k' => putr l v (bind k' k)
      | sampler op k' => sampler op (λ a, bind (k' a) k)
      end.

    Lemma valid_bind :
      ∀ A B c k,
        valid_program c →
        (∀ x, valid_program (k x)) →
        valid_program (@bind A B c k).
    Proof.
      intros A B c k hc hk.
      induction hc. all: simpl.
      all: solve [ try constructor ; eauto ].
    Qed.

    Lemma prove_program :
      ∀ {A} (P : program A → Type) p q,
        P p →
        p.(prog) = q.(prog) →
        P q.
    Proof.
      intros A P p q h e.
      apply program_ext in e. subst. auto.
    Defined.

    (* TODO: Do we need it? *)
    (* Lemma program_rect :
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
    Defined. *)

    Open Scope package_scope.

    Import SPropAxioms. Import FunctionalExtensionality.

    (* TODO: NEEDED? *)
    (* Program Definition rFree : ord_relativeMonad choice_incl :=
      @mkOrdRelativeMonad ord_choiceType TypeCat choice_incl program _ _ _ _ _ _.
    Next Obligation.
      simple refine {program ret _ }.
      auto.
    Defined.
    Next Obligation.
      eapply bind. all: eauto. Defined.
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
    Qed. *)

    Fixpoint mapFree {A B : choiceType} (f : A → B) (m : raw_program A) :
      raw_program B :=
      match m with
      | ret x => ret (f x)
      | opr o x k => opr o x (λ r, mapFree f (k r))
      | getr l k' => getr l (λ v, mapFree f (k' v))
      | putr l v k' => putr l v (mapFree f k')
      | sampler op k' => sampler op (λ a, mapFree f (k' a))
      end.

    (* Definition mapFree {A B : choiceType} (f : A → B) (m : program A) :
      program B.
    Proof.
      exists (mapFree_ f (m ∙1)).
      destruct m as [m h]. cbn.
      induction m in h |- *.
      all: solve [ cbn in * ; intuition auto ].
    Defined. *)

  End FreeModule.

  Arguments ret [A] _.
  Arguments opr [A] _ _.
  Arguments getr [A] _.
  Arguments putr [A] _.
  Arguments sampler [A] _ _.

  Arguments mkprog [_ _ _] _.
  Arguments prog [_ _ _] _.
  Arguments prog_valid [_ _ _] _.

  Notation "{ 'program' p }" :=
    (mkprog p _)
    (format "{ program  p  }") : package_scope.

  Notation "{ 'program' p '#with' h }" :=
    (mkprog p h)
    (only parsing) : package_scope.

  Instance ValidProgram_ret (A : choiceType) (x : A) L I :
    ValidProgram L I (ret x).
  Proof.
    apply valid_ret.
  Qed.

  (* TODO Replace the eautos in the tactics by in_fset stuff
    This means moving them from pkg_tactics.
    Can reorganise later.
  *)

  Hint Extern 1 (ValidProgram ?L ?I (opr ?o ?x ?k)) =>
    apply valid_opr ; [
      eauto
    | intro ; apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (getr ?o ?k)) =>
    apply valid_getr ; [
      eauto
    | intro ; apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (putr ?o ?x ?k)) =>
    apply valid_putr ; [
      eauto
    | apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (sampler ?op ?k)) =>
    apply valid_sampler ;
    intro ; apply valid_program_from_class
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (bind ?p ?k)) =>
    apply valid_bind ; [
      apply valid_program_from_class
    | intro ; apply valid_program_from_class
    ]
    : typeclass_instances.

  Coercion prog : program >-> raw_program.

  Hint Extern 1 (ValidProgram ?L ?I (?p.(prog))) =>
    apply p.(prog_valid)
    : typeclass_instances.

  (* Section Test.

    Open Scope package_scope.

    Definition foo L I : program L I _ :=
      {program ret 0 }.

    (* Obligation Tactic := idtac. *)

    Definition bar L I o (h : o \in I) x op : program L I _ :=
      {program
        sampler op (λ z, opr o x (λ y, ret y))
      }.

    Context (L : {fset Location}) (I : Interface).
    Context (o : opsig).

    Axiom h : o \in I.

    Fail Definition toto x op : program L I _ :=
      {program
        sampler op (λ z, opr o x (λ y, ret y))
      }.

    Definition toto x op : program L I _ :=
      {program
        sampler op (λ z, opr o x (λ y, ret y))
        #with let z := h in _
      }.

    Definition toto' x op : program L I _ :=
      {program
        sampler op (λ z, opr o x (λ y, ret y))
        #with [hints h]
      }.

    Context (l : Location).
    Axiom h' : l \in L.

    Fail Definition baba x op : program L I _ :=
      {program
        getr l (λ u, sampler op (λ z, opr o x (λ y, ret y)))
      }.

    Definition baba x op : program L I _ :=
      {program
        getr l (λ u, sampler op (λ z, opr o x (λ y, ret y)))
        #with [hints h ; h' ]
      }.

  End Test. *)

  Section FreeLocations.

    Context {import : Interface}.

    (* TODO Make this lemma more general? *)
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
      induction p.
      all: try solve [ constructor ; eauto ].
      - constructor. 2: eauto.
        eapply injectSubset. all: eauto.
      - constructor. 2: eauto.
        eapply injectSubset. all: eauto.
    Qed.

    Open Scope package_scope.

    (** Ideally we should need those.
      Injections should be hanlded behind the scenes.
      That's the point of using subset types. Maybe we can tweak the
      typeclasses hints to use fsubset when needed.
    *)
    (* Definition injectLocations {A : choiceType} {loc1 loc2 : {fset Location}}
      (h : fsubset loc1 loc2) (v : programI loc1 A) : programI loc2 A.
    Proof.
      refine {program v.(prog)}.
      destruct v as [v p].
      cbn. eapply valid_injectLocations. all: eauto.
    Defined. *)

    (* Lemma injectLocationsInjective :
      ∀ {A : choiceType} {locs1 locs2 : {fset Location}}
        (Hfsubset1 Hfsubset2 : fsubset locs1 locs2)
        (v : programI locs1 A),
        injectLocations Hfsubset1 v = injectLocations Hfsubset2 v.
    Proof.
      intros A locs1 locs2 h1 h2 v.
      f_equal. apply bool_irrelevance.
    Qed. *)

    (* Lemma injectLocationsMerge :
      ∀ {A : choiceType} {locs1 locs2 locs3 : {fset Location}}
        (h1 : fsubset locs1 locs2)
        (h2 : fsubset locs2 locs3)
        (v : programI locs1 A),
        (injectLocations h2 (injectLocations h1 v)) =
        injectLocations (fsubset_trans h1 h2) v.
    Proof.
      intros A locs1 locs2 locs3 h1 h2 v.
      destruct v as [v h].
      apply program_ext. cbn. reflexivity.
    Qed. *)

  End FreeLocations.

  Section FreeMap.

    Context {Locs : {fset Location}}.

    (* TODO Factorise with lemma above. *)
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
      induction p.
      all: try solve [ constructor ; auto ].
      constructor. 2: eauto.
      eapply in_fsubset. all: eauto.
    Qed.

    Open Scope package_scope.

    (* Definition injectMap {A : choiceType} {I1 I2 : Interface}
      (h : fsubset I1 I2) (v : programL I1 A) : programL I2 A.
    Proof.
      refine {program v.(prog) }.
      destruct v as [v p]. cbn.
      eapply valid_injectMap. all: eauto.
    Defined.

    Lemma injectMapInjective {A : choiceType} {I1 I2 : Interface}
          (Hfsubset1 Hfsubset2 : fsubset I1 I2)
          (v : programL I1 A) :
      injectMap Hfsubset1 v = injectMap Hfsubset2 v.
    Proof.
      f_equal. apply bool_irrelevance.
    Qed. *)

  End FreeMap.

  (* Section commuteMapLocations.

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

  End commuteMapLocations. *)

  (* TODO NEEDED? *)
  (* Section commuteBindLocations.

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

  End commuteBindLocations. *)

  Definition typed_raw_function :=
    ∑ (S T : chUniverse), S → raw_program T.

  Definition raw_package :=
    {fmap ident -> typed_raw_function}.

  Definition valid_package L I (E : Interface) (p : raw_package) :=
    ∀ o, o \in E →
      let '(id, (src, tgt)) := o in
      ∃ (f : src → raw_program tgt),
        p id = Some (src ; tgt ; f) ∧ ∀ x, valid_program L I (f x).

  Class ValidPackage L I E p :=
    is_valid_package : valid_package L I E p.

  (* Packages *)
  Record package L I E := mkpackage {
    pack : raw_package ;
    pack_valid : ValidPackage L I E pack
  }.

  Arguments mkpackage [_ _ _] _ _.
  Arguments pack [_ _ _] _.
  Arguments pack_valid [_ _ _] _.

  (* Packages coming with their set of locations *)
  Record loc_package I E := mkloc_package {
    locs : {fset Location} ;
    locs_pack : package locs I E
  }.

  Arguments mkloc_package [_ _] _ _.
  Arguments locs [_ _] _.
  Arguments locs_pack [_ _] _.

  (* Definition loc_package I E :=
    ∑ L, package L I E. *)

  Coercion locs_pack : loc_package >-> package.

  Lemma loc_package_ext :
    ∀ {I E} (p1 p2 : loc_package I E),
      p1.(locs) = p2.(locs) →
      p1.(locs_pack).(pack) =1 p2.(locs_pack).(pack) →
      p1 = p2.
  Proof.
    intros I E p1 p2 e1 e2.
    destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]].
    apply eq_fmap in e2.
    cbn in *. subst.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.

  (* Record bundle := mkbundle {
    locs : {fset Location} ;
    import : Interface ;
    export : Interface ;
    pack : opackage locs import export
  }. *)

  Notation "{ 'package' p }" :=
    (mkpackage p _)
    (format "{ package  p  }") : package_scope.

  Notation "{ 'package' p '#with' h }" :=
    (mkpackage p h)
    (only parsing) : package_scope.

  Coercion pack : package >-> raw_package.

  Hint Extern 1 (ValidPackage ?L ?I ?E (?p.(pack))) =>
    apply p.(pack_valid)
    : typeclass_instances.

  Lemma valid_package_from_class :
    ∀ L I E (p : raw_package),
      ValidPackage L I E p →
      valid_package L I E p.
  Proof.
    intros A p h. auto.
  Defined.

End CorePackageTheory.
