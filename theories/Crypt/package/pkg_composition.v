(*
  This file defines linking (sequential composition), parallel composition, and identity packages
  for linking. It further proves that
  - raw/unbundled/bundled linking is associative (raw_link_assoc, link_assoc, blink_assoc)
  - par is commutative (raw_par_commut, par_commut, bpar_commut)
  - interchange
 *)



From Coq Require Import Utf8.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool ssrnat.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd
  StateTransformingLaxMorph pkg_chUniverse pkg_core_definition
  RulesStateProb.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Module PackageComposition (π : RulesParam).

  Include (CorePackageTheory π).

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

  Derive NoConfusion NoConfusionHom for sigT.
  Derive NoConfusion NoConfusionHom for option.

  Lemma cast_fun_K :
    ∀ S T f e1 e2,
      @cast_fun S T S T e1 e2 f = f.
  Proof.
    intros S T f e1 e2.
    rewrite (uip e1 erefl).
    rewrite (uip e2 erefl).
    reflexivity.
  Qed.

  Lemma lookup_op_spec :
    ∀ p o f,
      lookup_op p o = Some f →
      p (ide o) = Some (chsrc o ; chtgt o ; f).
  Proof.
    intros p o f e.
    destruct o as [id [S T]]. cbn in *.
    destruct (p id) as [[S' [T' g]]|] eqn:e1. 2: discriminate.
    destruct chUniverse_eqP. 2: discriminate.
    destruct chUniverse_eqP. 2: discriminate.
    noconf e. subst.
    reflexivity.
  Qed.

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
      lookup_op (@mapm _ typed_raw_function _ (λ '(So ; To ; g), (So ; To ; f So To g)) p) o =
      omap (f (chsrc o) (chtgt o)) (lookup_op p o).
  Proof.
    intros p [n [So To]] f. unfold lookup_op.
    rewrite mapmE. destruct (p n) as [[St [Tt ft]]|] eqn:e.
    2:{ cbn. reflexivity. }
    cbn. destruct chUniverse_eqP. 2: reflexivity.
    destruct chUniverse_eqP. 2: reflexivity.
    cbn. subst. cbn. reflexivity.
  Qed.

  Fixpoint program_link {A} (v : raw_program A) (p : raw_package) :
    raw_program A :=
    match v with
    | ret a => ret a
    | opr o a k =>
      (* The None branch doesn't happen when valid *)
      (* We continue with a default value to preserve associativity. *)
      match lookup_op p o with
      | Some f => bind (f a) (λ x, program_link (k x) p)
      | None => program_link (k (chCanonical (chtgt o))) p
      end
    | getr l k => getr l (λ x, program_link (k x) p)
    | putr l v k => putr l v (program_link k p)
    | sampler op k => sampler op (λ x, program_link (k x) p)
    end.

  Lemma valid_program_link :
    ∀ A L Im Ir (v : raw_program A) p,
      valid_program L Im v →
      valid_package L Ir Im p →
      valid_program L Ir (program_link v p).
  Proof.
    intros A L Im Ir v p hv hp.
    induction hv.
    all: try solve [ constructor ; auto ].
    eapply lookup_op_valid in hp as hf. 2: eauto.
    destruct hf as [f [ef hf]].
    cbn. rewrite ef.
    apply valid_bind. all: auto.
  Qed.

  Hint Extern 1 (ValidProgram ?L ?I (program_link ?v ?p)) =>
    eapply valid_program_link ; [
      apply valid_program_from_class
    | apply valid_package_from_class
    ]
    : typeclass_instances.

  (* Linking *)
  Definition link (p1 p2 : raw_package) : raw_package :=
    @mapm _ typed_raw_function _
      (λ '(So ; To ; f), (So ; To ; λ x, program_link (f x) p2)) p1.

  (* Remove unexported functions from a raw package *)
  Definition trim (E : Interface) (p : raw_package) :=
    filterm (λ n '(So ; To ; f), (n, (So, To)) \in E) p.

  (* TODO MOVE *)
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

  Lemma valid_link :
    ∀ L1 L2 I M E p1 p2,
      valid_package L1 M E p1 →
      valid_package L2 I M p2 →
      valid_package (L1 :|: L2) I E (link p1 p2).
  Proof.
    intros L1 l2 I M E p1 p2 h1 h2.
    intros [n [So To]] ho. unfold link.
    rewrite mapmE.
    specialize (h1 _ ho) as h1'. cbn in h1'.
    destruct h1' as [f [ef hf]].
    rewrite ef. cbn.
    eexists. split. 1: reflexivity.
    intro x.
    eapply valid_program_link.
    - eapply valid_injectLocations.
      + apply fsubsetUl.
      + eapply hf.
    - eapply valid_package_inject_locations.
      + apply fsubsetUr.
      + auto.
  Qed.

  Hint Extern 1 (ValidPackage ?L ?I ?E (link ?p1 ?p2)) =>
    eapply valid_link ; [
      apply valid_package_from_class
    | apply valid_package_from_class
    ]
    : typeclass_instances.

  (* TODO MOVE? *)
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

  Lemma program_link_bind :
    ∀ {A B : choiceType} (v : raw_program A)
      (k : A → raw_program B) (p : raw_package),
      program_link (bind v k) p =
      bind (program_link v p) (λ x, program_link (k x) p).
  Proof.
    intros A B v k p.
    induction v.
    - cbn. reflexivity.
    - cbn. destruct lookup_op.
      + rewrite bind_assoc. f_equal.
        apply functional_extensionality. auto.
      + eauto.
    - cbn. f_equal. apply functional_extensionality. auto.
    - cbn. f_equal. auto.
    - cbn. f_equal. apply functional_extensionality. auto.
  Qed.

  Lemma program_link_assoc :
    ∀ A (v : raw_program A) f g,
      program_link (program_link v f) g =
      program_link v (link f g).
  Proof.
    intros A v f g.
    induction v in f, g |- *.
    - cbn. reflexivity.
    - cbn. unfold link in *.
      rewrite lookup_op_map.
      destruct lookup_op eqn:e.
      + cbn. rewrite program_link_bind. f_equal.
        apply functional_extensionality. auto.
      + cbn. eauto.
    - cbn. f_equal. apply functional_extensionality. auto.
    - cbn. f_equal. auto.
    - cbn. f_equal. apply functional_extensionality. auto.
  Qed.

  (* TODO MOVE? *)
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

  Hint Extern 1 (ValidPackage ?L ?I ?E (trim ?E ?p)) =>
    apply valid_trim ;
    apply valid_package_from_class
    : typeclass_instances.

  (* TODO MOVE? *)
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

  (* Technical lemma before proving assoc *)
  Lemma link_trim_commut :
    ∀ E p1 p2,
      link (trim E p1) p2 =
      trim E (link p1 p2).
  Proof.
    intros E p1 p2.
    apply eq_fmap. intro n.
    unfold link. unfold trim.
    repeat rewrite ?filtermE ?mapmE.
    destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
    cbn.
    destruct ((n, (S1, T1)) \in E) eqn:e1.
    2:{ rewrite e1. cbn. reflexivity. }
    rewrite e1. cbn. reflexivity.
  Qed.

  Lemma trim_idemp :
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

  Lemma program_link_trim_right :
    ∀ A L E (v : raw_program A) p,
      valid_program L E v →
      program_link v (trim E p) = program_link v p.
  Proof.
    intros A L E v p h.
    induction h in p |- *.
    - cbn. reflexivity.
    - cbn. rewrite lookup_op_trim.
      destruct lookup_op eqn:e.
      + cbn. rewrite H. f_equal. apply functional_extensionality.
        intuition auto.
      + cbn. eauto.
    - cbn. f_equal. apply functional_extensionality. intuition auto.
    - cbn. f_equal. intuition auto.
    - cbn. f_equal. apply functional_extensionality. intuition auto.
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

  Lemma link_trim_right :
    ∀ L I E p1 p2,
      valid_package L I E p1 →
      link (trim E p1) (trim I p2) =
      link (trim E p1) p2.
  Proof.
    intros L I E p1 p2 h.
    apply eq_fmap. intro n.
    unfold link.
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
    eapply program_link_trim_right.
    apply h.
  Qed.

  Lemma link_assoc :
    ∀ p1 p2 p3,
      link p1 (link p2 p3) =
      link (link p1 p2) p3.
  Proof.
    intros p1 p2 p3.
    apply eq_fmap.
    unfold link.
    intro n. repeat rewrite ?mapmE.
    destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e. 2: reflexivity.
    cbn. f_equal. f_equal. f_equal. extensionality x.
    rewrite program_link_assoc.
    reflexivity.
  Qed.

  (* Lemma bundle_ext :
    ∀ (b1 b2 : bundle),
      locs b1 = locs b2 →
      import b1 = import b2 →
      export b1 = export b2 →
      (pack b1) =1 (pack b2) →
      b1 = b2.
  Proof.
    intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] el ei ee ep.
    cbn in *. apply eq_fmap in ep. subst. f_equal. f_equal.
    apply proof_irrelevance.
  Qed. *)

  Notation "p1 ∘ p2" :=
    (link p1 p2) (right associativity, at level 20) : package_scope.

  (* TODO Probably move somewhere else? *)
  Section fset_par_facts.

    Fact disjoint_in_both {T : ordType} (s1 s2 : {fset T}) :
      fdisjoint s1 s2 → ∀ x, x \in s1 → x \in s2 → False.
    Proof.
      move => Hdisjoint x x_in_s1 x_in_s2.
      assert (x \notin s2) as H.
      { exact (fdisjointP s1 s2 Hdisjoint x x_in_s1). }
      rewrite x_in_s2 in H. by [].
    Qed.

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

  End fset_par_facts.

  (** Parallel composition *)

  (** Two packages can be composed in parallel or merged if they implement
      disjoint interfaces. As such, it might be worth it to trim the packages
      before using par.
  *)

  Definition par (p1 p2 : raw_package) :=
    unionm p1 p2.

  Class Parable (p1 p2 : raw_package) :=
    parable : fdisjoint (domm p1) (domm p2).

  Lemma valid_par :
    ∀ L1 L2 I1 I2 E1 E2 p1 p2,
      Parable p1 p2 →
      valid_package L1 I1 E1 p1 →
      valid_package L2 I2 E2 p2 →
      valid_package (L1 :|: L2) (I1 :|: I2) (E1 :|: E2) (par p1 p2).
  Proof.
    intros L1 L2 I1 I2 E1 E2 p1 p2 h h1 h2.
    intros [n [So To]] ho.
    unfold par. rewrite unionmE.
    rewrite in_fsetU in ho. move: ho => /orP [ho | ho].
    - specialize (h1 _ ho) as h'. cbn in h'.
      destruct h' as [f [e hf]].
      rewrite e. cbn.
      exists f. intuition auto.
      eapply valid_injectLocations. 1: apply fsubsetUl.
      eapply valid_injectMap. 1: apply fsubsetUl.
      auto.
    - specialize (h2 _ ho) as h'. cbn in h'.
      destruct h' as [f [e hf]].
      destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e1.
      1:{
        exfalso.
        assert (i1 : isSome (p1 n)).
        { rewrite e1. auto. }
        assert (i2 : isSome (p2 n)).
        { rewrite e. auto. }
        rewrite -mem_domm in i1.
        rewrite -mem_domm in i2.
        unfold Parable in h.
        eapply disjoint_in_both. all: eauto.
      }
      cbn. rewrite e.
      exists f. intuition auto.
      eapply valid_injectLocations. 1: apply fsubsetUr.
      eapply valid_injectMap. 1: apply fsubsetUr.
      auto.
  Qed.

  (* TODO Check if the first branch is generated *)
  Hint Extern 1 (ValidPackage ?L ?I ?E (par ?p1 ?p2)) =>
    apply valid_par ; [
      exact _
    | apply valid_package_from_class
    | apply valid_package_from_class
    ]
    : typeclass_instances.

  Class FDisjoint {A : ordType} s1 s2 :=
    are_disjoint : @fdisjoint A s1 s2.

  (** When comparing export interfaces, since we disallow overloading
      we need to have only the identifier parts disjoint.
  *)
  Definition idents (E : Interface) : {fset ident} :=
    (λ '(n, _), n) @: E.

  Lemma domm_trim :
    ∀ E p,
      fsubset (domm (trim E p)) (idents E).
  Proof.
    intros E p. unfold trim. unfold idents.
    apply fsubset_ext. cbn. intros x h.
    rewrite mem_domm in h.
    rewrite filtermE in h.
    destruct (p x) as [[S' [T' f]]|] eqn:e.
    2:{ rewrite e in h. cbn in h. discriminate. }
    rewrite e in h. cbn in h.
    destruct ((x, (S', T')) \in E) eqn:e1.
    2:{ rewrite e1 in h. discriminate. }
    eapply mem_imfset in e1. exact e1.
  Qed.

  Lemma parable_trim :
    ∀ E1 E2 p1 p2,
      fdisjoint (idents E1) (idents E2) →
      Parable (trim E1 p1) (trim E2 p2).
  Proof.
    intros E1 E2 p1 p2 h.
    unfold Parable.
    eapply fdisjoint_trans.
    { eapply domm_trim. }
    rewrite fdisjointC.
    eapply fdisjoint_trans.
    { eapply domm_trim. }
    rewrite fdisjointC. auto.
  Qed.

  Lemma fdisjoint_from_class :
    ∀ A s1 s2,
      @FDisjoint A s1 s2 →
      fdisjoint s1 s2.
  Proof.
    intros. auto.
  Qed.

  Instance FDisjointUr {A : ordType} (s1 s2 s3 : {fset A}) :
    FDisjoint s1 s2 →
    FDisjoint s1 s3 →
    FDisjoint s1 (s2 :|: s3).
  Proof.
    intros h2 h3.
    unfold FDisjoint in *.
    rewrite fdisjointUr.
    rewrite h2 h3. reflexivity.
  Qed.

  Hint Extern 1 (FDisjoint (fset ?l1) (fset ?l2)) =>
    repeat rewrite [fset]unlock ;
    eauto
    : typeclass_instances.

  Hint Extern 1 (Parable _ _) =>
    apply fdisjoint_from_class
    : typeclass_instances.

  Hint Extern 1 (Parable (trim ?E1 ?p1) (trim ?E2 ?p2)) =>
    apply parable_trim ;
    apply fdisjoint_from_class
    : typeclass_instances.

  (* unionmC For symmetry *)

  (* Lemma parable_sym :
    ∀ {E1 E2},
      parable E1 E2 →
      parable E2 E1.
  Proof.
    intros E1 E2 h.
    unfold parable.
    rewrite fdisjointC.
    auto.
  Qed. *)

  (* TODO MOVE *)
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

  Lemma par_commut :
    ∀ p1 p2,
      Parable p1 p2 →
      par p1 p2 = par p2 p1.
  Proof.
    intros p1 p2 h.
    apply unionmC. auto.
  Qed.

  Lemma par_assoc :
    ∀ p1 p2 p3,
      par p1 (par p2 p3) = par (par p1 p2) p3.
  Proof.
    intros p1 p2 p3.
    unfold par.
    rewrite unionmA. reflexivity.
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

  Lemma program_link_par_left :
    ∀ A I L L' E (v : raw_program A) p1 p2,
      ValidProgram L E v →
      ValidPackage L' I E p1 →
      program_link v (par p1 p2) = program_link v p1.
  Proof.
    intros A I L L' E v p1 p2 hv hp1.
    unfold ValidProgram in hv.
    induction hv.
    - cbn. reflexivity.
    - simpl. rewrite lookup_op_unionm.
      eapply lookup_op_valid in hp1 as hf. 2: eauto.
      destruct hf as [f [e hf]].
      rewrite e. eapply lookup_op_spec in e as e'.
      rewrite e'. cbn. f_equal. extensionality z.
      eauto.
    - simpl. f_equal. extensionality x. eauto.
    - simpl. f_equal. eauto.
    - simpl. f_equal. extensionality x. eauto.
  Qed.

  Lemma program_link_par_right :
    ∀ A I L L' E (v : raw_program A) p1 p2,
      Parable p1 p2 →
      ValidProgram L E v →
      ValidPackage L' I E p2 →
      program_link v (par p1 p2) = program_link v p2.
  Proof.
    intros A I L L' E v p1 p2 h hv hp1.
    rewrite par_commut. eapply program_link_par_left.
    all: eauto.
  Qed.

  (* Predicate stating that a package exports all it implements *)
  Definition trimmed E p :=
    trim E p = p.

  Lemma trimmed_valid_Some_in :
    ∀ L I E p n S T f,
      valid_package L I E p →
      trimmed E p →
      p n = Some (S ; T ; f) →
      (n, (S, T)) \in E.
  Proof.
    intros L I E p n S T f hv ht e.
    unfold trimmed in ht. pose e as e'. rewrite <- ht in e'.
    unfold trim in e'. rewrite filtermE in e'.
    rewrite e in e'. simpl in e'.
    destruct ((n, (S, T)) \in E) eqn:e2.
    2:{ rewrite e2 in e'. discriminate. }
    reflexivity.
  Qed.

  Lemma interchange :
    ∀ A B C D E F L1 L2 L3 L4 p1 p2 p3 p4,
      ValidPackage L1 B A p1 →
      ValidPackage L2 E D p2 →
      ValidPackage L3 C B p3 →
      ValidPackage L4 F E p4 →
      trimmed A p1 →
      trimmed D p2 →
      Parable p3 p4 →
      par (link p1 p3) (link p2 p4) = link (par p1 p2) (par p3 p4).
  Proof.
    intros A B C D E F L1 L2 L3 L4 p1 p2 p3 p4 h1 h2 h3 h4 t1 t2 p34.
    apply eq_fmap. intro n.
    unfold par.
    rewrite unionmE. unfold link.
    rewrite !mapmE. rewrite unionmE.
    destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e1.
    - simpl. f_equal. f_equal. f_equal.
      extensionality x.
      eapply trimmed_valid_Some_in in e1 as hi. 2,3: eauto.
      specialize (h1 _ hi). cbn in h1.
      destruct h1 as [g [eg hg]].
      rewrite e1 in eg. noconf eg. cbn in hg.
      erewrite program_link_par_left. 2: eapply hg.
      all: eauto.
    - simpl. destruct (p2 n) as [[S2 [T2 f2]]|] eqn:e2.
      + simpl. f_equal. f_equal. f_equal. extensionality x.
        eapply trimmed_valid_Some_in in e2 as hi. 2,3: eauto.
        specialize (h2 _ hi). cbn in h2.
        destruct h2 as [g [eg hg]].
        rewrite e2 in eg. noconf eg. cbn in hg.
        erewrite program_link_par_right. all: eauto.
        eapply hg.
      + simpl. reflexivity.
  Qed.

  Local Open Scope type_scope.

  (** Package builder from a function *)
  (* TODO: Still works, but outdated. *)

  Definition typed_function L I :=
    ∑ (S T : chUniverse), S → program L I T.

  Equations? map_interface (I : seq opsig) {A} (f : ∀ x, x \in I → A) :
    seq A :=
      map_interface (a :: I') f := f a _ :: map_interface I' (λ x h, f x _) ;
      map_interface [::] f := [::].
    Proof.
      - rewrite in_cons. apply/orP. left. apply/eqP. reflexivity.
      - rewrite in_cons. apply/orP. right. auto.
    Qed.

  Notation "[ 'interface' e | h # x ∈ I ]" :=
    (map_interface I (λ x h, e))
    (format "[ interface  e  |  h  #  x  ∈  I ]") : package_scope.

  Local Open Scope package_scope.

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
      + noconf e. cbn.
        rewrite e1. move: e1 => /eqP e1. subst.
        exists a.2. unshelve eexists.
        { destruct a. cbn. rewrite in_cons.
          apply/orP. left. apply/eqP. reflexivity.
        }
        split. 1: reflexivity.
        destruct a. cbn. f_equal.
        apply bool_irrelevance.
      + cbn. rewrite e1.
        specialize IHI with (1 := e).
        destruct IHI as [z [h [h1 h2]]].
        exists z. unshelve eexists.
        { rewrite in_cons. apply/orP. right. auto. }
        intuition auto. subst. f_equal.
        apply bool_irrelevance.
  Qed.

  Lemma getm_def_map_interface_None :
    ∀ A (I : seq opsig) (f : ∀ x, x \in I → A) n,
      getm_def [interface (ide x, f x h) | h # x ∈ I] n = None →
      getm_def I n = None.
  Proof.
    cbn. intros A I f n e.
    induction I in f, n, e |- *.
    - simp map_interface in e. auto.
    - simp map_interface in e. cbn in e.
      destruct eqn eqn:e1. 1: discriminate.
      cbn. rewrite e1.
      specialize IHI with (1 := e).
      auto.
  Qed.

  (** Since the type of interfaces allows for overloading,
      we define the predicate [flat] on them, stating that they only export
      each symbol once.
  *)
  Definition flat (I : Interface) :=
    ∀ n u1 u2,
      (n, u1) \in I →
      (n, u2) \in I →
      u1 = u2.

  Lemma in_getm_def_None :
    ∀ {A : eqType} n (x : A) (s : seq (nat * A)),
      (n,x) \in s →
      getm_def s n = None →
      False.
  Proof.
    intros A n x s h1 h2.
    induction s as [| [m a] s ih] in n, x, h1, h2 |- *.
    - inversion h1.
    - cbn in h2. rewrite in_cons in h1.
      destruct eqn eqn:e.
      + discriminate.
      + cbn in h1. rewrite e in h1. cbn in h1.
        eapply ih. all: eauto.
  Qed.

  Definition funmkpack {L I} {E : Interface} (hE : flat E)
    (f : ∀ (o : opsig), o \in E → src o → program L I (tgt o)) :
    package L I E.
  Proof.
    pose foo : seq (nat * typed_function L I) :=
      [interface (ide o, (chsrc o ; chtgt o ; f o h)) | h # o ∈ E].
    pose bar := mkfmap foo.
    exists (@mapm _ (typed_function L I) typed_raw_function
      (λ '(So ; To ; f), (So ; To ; λ x, (f x).(prog))) bar).
    intros [n [So To]] ho.
    rewrite mapmE. subst bar foo.
    rewrite mkfmapE.
    destruct getm_def eqn:e.
    - apply getm_def_map_interface_Some in e as h.
      destruct h as [[S T] [h [h1 h2]]]. subst. cbn.
      specialize (hE _ _ _ h ho). noconf hE.
      eexists. split. 1: reflexivity.
      intro x. cbn.
      exact ((f (n, (So, To)) h x).(prog_valid)).
    - exfalso. apply getm_def_map_interface_None in e.
      eapply in_getm_def_None. 2: eauto.
      exact ho.
  Defined.

  (* Identity package *)

  (* Maybe lock this definition? *)
  Definition mkdef (A B : chUniverse) (f : A → raw_program B)
    : typed_raw_function :=
    (A ; B ; f).

  Definition ID (I : Interface) : raw_package :=
    mkfmap [seq
      let '(n, p) := i in
      (n, let '(s, t) := p in mkdef s t (λ x, opr (n, (s, t)) x (λ y, ret y)))
    | i <- I ].

  Lemma getm_def_map :
    ∀ (T : ordType) S1 S2 (l : seq (T * S1)) (f : S1 → S2) x,
      getm_def [seq let '(i,s) := u in (i, f s) | u <- l ] x =
      omap f (getm_def l x).
  Proof.
    intros T S1 S2 l f x.
    induction l as [| u l ih].
    - simpl. reflexivity.
    - simpl. destruct u as [i s]. simpl.
      destruct (x == i).
      + reflexivity.
      + apply ih.
  Qed.

  Lemma getm_def_map_dep :
    ∀ (T : ordType) S1 S2 (l : seq (T * S1)) (f : T → S1 → S2) x,
      getm_def [seq let '(i,s) := u in (i, f i s) | u <- l ] x =
      omap (f x) (getm_def l x).
  Proof.
    intros T S1 S2 l f x.
    induction l as [| u l ih].
    - simpl. reflexivity.
    - simpl. destruct u as [i s]. simpl.
      destruct (x == i) eqn:e.
      + cbn. move: e => /eqP e. subst. reflexivity.
      + apply ih.
  Qed.

  Lemma IDE :
    ∀ I n,
      ID I n =
      omap
        (λ '(So,To), (So ; To ; λ x, opr (n,(So,To)) x (λ y, ret y)))
        (getm_def I n).
  Proof.
    intros I n.
    unfold ID. rewrite mkfmapE.
    rewrite getm_def_map_dep. reflexivity.
  Qed.

  Lemma getm_def_in :
    ∀ {A : eqType} n (x : A) (s : seq (nat_eqType * A)),
      getm_def s n = Some x →
      (n,x) \in s.
  Proof.
    simpl. intros A n x s h.
    induction s as [| [m a] s ih] in n, x, h |- *.
    - inversion h.
    - cbn in h. rewrite in_cons. apply/orP.
      destruct eqn eqn:e.
      + noconf h. move: e => /eqP e. subst.
        left. apply/eqP. reflexivity.
      + right. eapply ih. auto.
  Qed.

  Lemma lookup_op_ID :
    ∀ I o,
      flat I →
      lookup_op (ID I) o =
      if o \in I
      then Some (λ x, opr o x (λ y, ret y))
      else None.
  Proof.
    intros I [n [S T]] h.
    unfold lookup_op. rewrite IDE.
    destruct getm_def as [[So To]|] eqn:e.
    - cbn. apply getm_def_in in e as h1.
      destruct chUniverse_eqP.
      2:{
        destruct ((n, (S, T)) \in I) eqn:e1.
        2:{ rewrite e1. reflexivity. }
        specialize (h _ _ _ h1 e1). noconf h. congruence.
      }
      destruct chUniverse_eqP.
      2:{
        destruct ((n, (S, T)) \in I) eqn:e1.
        2:{ rewrite e1. reflexivity. }
        specialize (h _ _ _ h1 e1). noconf h. congruence.
      }
      subst. rewrite h1. reflexivity.
    - cbn. destruct ((n, (S, T)) \in I) eqn:e1.
      1:{
        exfalso. eapply in_getm_def_None. 2: eauto.
        exact e1.
      }
      rewrite e1. reflexivity.
  Qed.

  Lemma program_link_id :
    ∀ A (v : raw_program A) L I,
      flat I →
      valid_program L I v →
      program_link v (ID I) = v.
  Proof.
    intros A v L I h hv.
    induction hv.
    - cbn. reflexivity.
    - simpl.
      rewrite lookup_op_ID. 2: auto.
      rewrite H. simpl. f_equal.
      extensionality z. auto.
    - simpl. f_equal. apply functional_extensionality. auto.
    - simpl. f_equal. auto.
    - simpl. f_equal. apply functional_extensionality. auto.
  Qed.

  Lemma link_id :
    ∀ L I E p,
      valid_package L I E p →
      flat I →
      trimmed E p →
      link p (ID I) = p.
  Proof.
    intros L I E p hp hI tp.
    apply eq_fmap. intro n. unfold link.
    rewrite mapmE. destruct (p n) as [[S [T f]]|] eqn:e.
    - cbn. f_equal. f_equal. f_equal. extensionality x.
      eapply trimmed_valid_Some_in in e as hi. 2,3: eauto.
      specialize (hp _ hi) as h'. cbn in h'.
      destruct h' as [g [eg hg]].
      rewrite e in eg. noconf eg. cbn in hg.
      eapply program_link_id. all: eauto.
    - reflexivity.
  Qed.

  (* TODO MOVE *)
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

  Lemma id_link :
    ∀ L I E p,
      valid_package L I E p →
      trimmed E p →
      link (ID E) p = p.
  Proof.
    intros L I E p hp tp.
    apply eq_fmap. intro n. unfold link.
    rewrite mapmE. rewrite IDE.
    destruct getm_def as [[So To]|] eqn:e.
    - eapply getm_def_in in e as hi.
      specialize (hp _ hi) as h'. cbn in h'.
      destruct h' as [f [ef hf]].
      cbn. destruct (p n) as [[St [Tt g]]|] eqn:e1. 2: discriminate.
      destruct chUniverse_eqP. 2:{ noconf ef. contradiction. }
      destruct chUniverse_eqP. 2:{ noconf ef. contradiction. }
      subst. cbn.
      f_equal. f_equal. f_equal.
      extensionality x.
      apply bind_ret.
    - simpl. unfold trimmed in tp.
      destruct (p n) as [[St [Tt g]]|] eqn:e1.
      1:{
        eapply trimmed_valid_Some_in in e1 as hi. 2,3: eauto.
        exfalso. eapply in_getm_def_None.
        - exact hi.
        - cbn. auto.
      }
      reflexivity.
  Qed.

End PackageComposition.
