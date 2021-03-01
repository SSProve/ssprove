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

  Definition loc_type (l : Location) := l.π1.

  Coercion loc_type : Location >-> chUniverse.

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
    | getr (l : Location) (k : l → raw_program A)
    | putr (l : Location) (v : l) (k : raw_program A)
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

    Lemma valid_program_from_class :
      ∀ A (p : raw_program A),
        ValidProgram p →
        valid_program p.
    Proof.
      intros A p h. auto.
    Defined.

    Record program A := mkprog {
      prog : raw_program A ;
      prog_valid : ValidProgram prog
    }.

    Arguments mkprog {_} _.
    Arguments prog {_} _.
    Arguments prog_valid {_} _.

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

    Lemma inversion_valid_bind :
      ∀ {A B} {c : raw_program A} {k : A → raw_program B},
        valid_program (bind c k) →
        valid_program c.
    Proof.
      intros A B c k h.
      induction c.
      - constructor.
      - simpl in h. apply inversion_valid_opr in h. destruct h as [h1 h2].
        constructor. all: eauto.
      - simpl in h. apply inversion_valid_getr in h.
        constructor. all: intuition eauto.
      - simpl in h. apply inversion_valid_putr in h.
        constructor. all: intuition eauto.
      - simpl in h.
        constructor. intro.
        eapply inversion_valid_sampler in h.
        eauto.
    Qed.

    (* Alternative to bind *)
    Inductive command : choiceType → Type :=
    | cmd_op o (x : src o) : command (tgt o)
    | cmd_get (ℓ : Location) : command (Value ℓ.π1)
    | cmd_put (ℓ : Location) (v : Value ℓ.π1) : command unit_choiceType
    | cmd_sample op : command (Arit op).

    Definition cmd_bind {A B} (c : command A) (k : A → raw_program B) :=
      match c in command A return (A → raw_program B) → raw_program B with
      | cmd_op o x => opr o x
      | cmd_get ℓ => getr ℓ
      | cmd_put ℓ v => λ k, putr ℓ v (k Datatypes.tt)
      | cmd_sample op => sampler op
      end k.

    Inductive valid_command : ∀ A, command A → Prop :=
    | valid_cmd_op :
        ∀ o x,
          o \in import →
          valid_command _ (cmd_op o x)

    | valid_cmd_get :
        ∀ ℓ,
          ℓ \in Loc →
          valid_command _ (cmd_get ℓ)

    | valid_cmd_put :
        ∀ ℓ v,
          ℓ \in Loc →
          valid_command _ (cmd_put ℓ v)

    | valid_cmd_sample :
        ∀ op,
          valid_command _ (cmd_sample op).

    Arguments valid_command [_] _.

    Class ValidCommand {A} (c : command A) :=
      is_valid_command : valid_command c.

    Lemma valid_command_from_class :
      ∀ A (c : command A),
        ValidCommand c →
        valid_command c.
    Proof.
      auto.
    Qed.

    Lemma valid_cmd_bind :
      ∀ {A B} (c : command A) (k : A → raw_program B),
        valid_command c →
        (∀ x, valid_program (k x)) →
        valid_program (cmd_bind c k).
    Proof.
      intros A B c k hc hk.
      induction hc.
      - cbn. constructor. all: auto.
      - cbn. constructor. all: auto.
      - cbn. constructor. all: auto.
      - cbn. constructor. auto.
    Qed.

    Lemma inversion_valid_cmd_bind :
      ∀ {A B} (c : command A) (k : A → raw_program B),
        valid_program (cmd_bind c k) →
        valid_command c ∧ (∀ x, valid_program (k x)).
    Proof.
      intros A B c k h.
      destruct c.
      - cbn. apply inversion_valid_opr in h. intuition auto.
        constructor. auto.
      - cbn. apply inversion_valid_getr in h. intuition auto.
        constructor. auto.
      - cbn. apply inversion_valid_putr in h. split.
        + constructor. intuition auto.
        + intros []. intuition auto.
      - cbn. split.
        + constructor.
        + intro. eapply inversion_valid_sampler in h. eauto.
    Qed.

    Lemma bind_assoc :
      ∀ {A B C : choiceType} (v : raw_program A)
        (k1 : A → raw_program B) (k2 : B → raw_program C),
        bind (bind v k1) k2 =
        bind v (λ x, bind (k1 x) k2).
    Proof.
      intros A B C v k1 k2.
      induction v in k1, k2 |- *.
      - cbn. reflexivity.
      - cbn. f_equal. apply functional_extensionality. auto.
      - cbn. f_equal. extensionality z. auto.
      - cbn. f_equal. auto.
      - cbn. f_equal. extensionality z. auto.
    Qed.

    Lemma bind_ret :
      ∀ A (v : raw_program A),
        bind v (λ x, ret x) = v.
    Proof.
      intros A v.
      induction v.
      all: cbn. 1: reflexivity.
      all: try solve [ f_equal ; apply functional_extensionality ; eauto ].
      f_equal. auto.
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


  (* Having an instance here means that it will use ret when the program
    is unknown. Pretty bad.
    We will instead use Hint Extern.
  *)
  (* Instance ValidProgram_ret (A : choiceType) (x : A) L I :
    ValidProgram L I (ret x).
  Proof.
    apply valid_ret.
  Qed. *)

  Hint Extern 1 (ValidProgram ?L ?I (ret ?x)) =>
    apply valid_ret
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (opr ?o ?x ?k)) =>
    eapply valid_opr ; [
      auto_in_fset
    | intro ; apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (getr ?o ?k)) =>
    eapply valid_getr ; [
      auto_in_fset
    | intro ; apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (putr ?o ?x ?k)) =>
    eapply valid_putr ; [
      auto_in_fset
    | apply valid_program_from_class
    ] : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (sampler ?op ?k)) =>
    eapply valid_sampler ;
    intro ; apply valid_program_from_class
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (bind ?p ?k)) =>
    eapply valid_bind ; [
      apply valid_program_from_class
    | intro ; apply valid_program_from_class
    ]
    : typeclass_instances.

  Coercion prog : program >-> raw_program.

  Hint Extern 1 (ValidProgram ?L ?I (?p.(prog))) =>
    eapply p.(prog_valid)
    : typeclass_instances.

  Arguments valid_command _ _ [_] _.

  Hint Extern 1 (ValidCommand ?L ?I (cmd_op ?o ?x)) =>
    eapply valid_cmd_op ;
    auto_in_fset
    : typeclass_instances.

  Hint Extern 1 (ValidCommand ?L ?I (cmd_get ?l)) =>
    eapply valid_cmd_get ;
    auto_in_fset
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (cmd_put ?l ?v)) =>
    eapply valid_cmd_put ;
    auto_in_fset
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (cmd_sample ?op)) =>
    eapply valid_cmd_sample
    : typeclass_instances.

  Hint Extern 1 (ValidProgram ?L ?I (cmd_bind ?c ?k)) =>
    eapply valid_cmd_bind ; [
      apply valid_command_from_class
    | intro ; apply valid_program_from_class
    ]
    : typeclass_instances.

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

    Lemma valid_cmd_injectLocations :
      ∀ A L1 L2 (v : command A),
        fsubset L1 L2 →
        valid_command L1 import v →
        valid_command L2 import v.
    Proof.
      intros A L1 L2 v h p.
      destruct p.
      all: try solve [ constructor ; eauto ].
      - constructor.
        eapply injectSubset. all: eauto.
      - constructor.
        eapply injectSubset. all: eauto.
    Qed.

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

  End FreeMap.

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

  Notation "{ 'package' p }" :=
    (mkpackage p _)
    (format "{ package  p  }") : package_scope.

  Notation "{ 'package' p '#with' h }" :=
    (mkpackage p h)
    (only parsing) : package_scope.

  Coercion pack : package >-> raw_package.

  Hint Extern 1 (ValidPackage ?L ?I ?E (?p.(pack))) =>
    eapply p.(pack_valid)
    : typeclass_instances.

  Lemma valid_package_from_class :
    ∀ L I E (p : raw_package),
      ValidPackage L I E p →
      valid_package L I E p.
  Proof.
    intros A p h. auto.
  Defined.

  Notation "{ 'locpackage' p }" :=
    (mkloc_package _ (mkpackage p _))
    (format "{ locpackage  p  }") : package_scope.

  Notation "{ 'locpackage' p '#with' h }" :=
    (mkloc_package _ (mkpackage p h))
    (only parsing) : package_scope.

  (* Some validity lemmata *)

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

  Lemma package_ext :
    ∀ {L I E} (p1 p2 : package L I E),
      p1.(pack) =1 p2.(pack) →
      p1 = p2.
  Proof.
    intros L I E p1 p2 e.
    destruct p1 as [p1 h1], p2 as [p2 h2].
    apply eq_fmap in e.
    cbn in *. subst.
    f_equal. apply proof_irrelevance.
  Qed.

  (* Rewriting in packages *)

  Lemma mkpackage_rewrite :
    ∀ {L I E T} {x y} (p : T → _) h (e : x = y),
      @mkpackage L I E (p x) h = mkpackage (p y) (sig_rewrite_aux p h e).
  Proof.
    intros L I E T x y p h e. subst. reflexivity.
  Qed.

  Ltac mkpackage_rewrite e :=
    lazymatch type of e with
    | ?x = _ =>
      match goal with
      | |- context [ mkpackage ?p ?h ] =>
        lazymatch p with
        | context [ x ] =>
          lazymatch eval pattern x in p with
          | (fun x => @?q x) ?y =>
            erewrite (mkpackage_rewrite q _ e)
          end
        end
      end
    end.

  (** Tactic package rewrite

  Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
  a term of the form mkpackage u v, specifically inside the term u.
  sig rewrite e will replace x by y in u and update v accordingly.

  *)
  Tactic Notation "package" "rewrite" constr(e) :=
    mkpackage_rewrite e.

  (* Rewriting in programs *)

  Lemma mkprog_rewrite :
    ∀ {L I A T} {x y} (p : T → _) h (e : x = y),
      @mkprog L I A (p x) h = mkprog (p y) (sig_rewrite_aux p h e).
  Proof.
    intros L I A T x y p h e. subst. reflexivity.
  Qed.

  Ltac mkprog_rewrite e :=
    lazymatch type of e with
    | ?x = _ =>
      match goal with
      | |- context [ mkprog ?p ?h ] =>
        lazymatch p with
        | context [ x ] =>
          lazymatch eval pattern x in p with
          | (fun x => @?q x) ?y =>
            erewrite (mkprog_rewrite q _ e)
          end
        end
      end
    end.

  (** Tactic program rewrite

  Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
  a term of the form mkprogram u v, specifically inside the term u.
  sig rewrite e will replace x by y in u and update v accordingly.

  *)
  Tactic Notation "program" "rewrite" constr(e) :=
    mkprog_rewrite e.

End CorePackageTheory.
