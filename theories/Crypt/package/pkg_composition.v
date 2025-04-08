(*
  This file defines linking (sequential composition), parallel composition, and identity packages
  for linking. It further proves that
  - raw/unbundled/bundled linking is associative (raw_link_assoc, link_assoc, blink_assoc)
  - par is commutative (raw_par_commut, par_commut, bpar_commut)
  - interchange
 *)



From Coq Require Import Utf8.
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype choice seq ssrfun ssrbool ssrnat.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd
  StateTransformingLaxMorph choice_type pkg_core_definition
  RulesStateProb fmap_extra.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Definition cast_fun {So To St Tt : choice_type}
  (hS : St = So) (hT : Tt = To) (f : St → raw_code Tt) :
  So → raw_code To.
Proof.
  subst. auto.
Defined.

Definition lookup_op (p: raw_package) (o : opsig) :
  option (src o → raw_code (tgt o)) :=
  let '(n, (So, To)) := o in
  match p n with
  | Some (St ; Tt ; f) =>
    match choice_type_eqP St So, choice_type_eqP Tt To with
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
  destruct choice_type_eqP. 2: discriminate.
  destruct choice_type_eqP. 2: discriminate.
  noconf e. subst.
  reflexivity.
Qed.

Lemma lookup_op_valid :
  ∀ L I E p o,
    ValidPackage L I E p →
    fhas E o →
    ∃ f,
      lookup_op p o = Some f ∧
      ∀ x, ValidCode L I (f x).
Proof.
  intros L I E p o hp ho.
  eapply from_valid_package in hp.
  specialize (hp o ho).
  destruct o as [n [So To]].
  destruct hp as [f [ef hf]].
  exists f. intuition auto. cbn.
  destruct (p n) as [[St [Tt ft]]|] eqn:e. 2: discriminate.
  destruct choice_type_eqP.
  2:{ inversion ef. congruence. }
  destruct choice_type_eqP.
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
  cbn. destruct choice_type_eqP. 2: reflexivity.
  destruct choice_type_eqP. 2: reflexivity.
  cbn. subst. cbn. reflexivity.
Qed.

Fixpoint code_link {A} (v : raw_code A) (p : raw_package) :
  raw_code A :=
  match v with
  | ret a => ret a
  | opr o a k =>
    (* The None branch doesn't happen when valid *)
    (* We continue with a default value to preserve associativity. *)
    match lookup_op p o with
    | Some f => bind (f a) (λ x, code_link (k x) p)
    | None => code_link (k (chCanonical (chtgt o))) p
    end
  | getr l k => getr l (λ x, code_link (k x) p)
  | putr l v k => putr l v (code_link k p)
  | sampler op k => sampler op (λ x, code_link (k x) p)
  end.

Lemma valid_code_link :
  ∀ A L Im Ir (v : raw_code A) p,
    ValidCode L Im v →
    ValidPackage L Ir Im p →
    ValidCode L Ir (code_link v p).
Proof.
  intros A L Im Ir v p hv hp.
  induction hv.
  all: try solve [ constructor ; auto ].
  eapply lookup_op_valid in hp as hf. 2: eauto.
  destruct hf as [f [ef hf]].
  cbn. rewrite ef.
  apply valid_bind. all: auto.
Qed.

#[export] Hint Extern 1 (ValidCode ?L ?I (code_link ?v ?p)) =>
  eapply valid_code_link
  : typeclass_instances ssprove_valid_db.


(* Linking *)
Definition link (p1 p2 : raw_package) : raw_package :=
  @mapm _ typed_raw_function _
    (λ '(So ; To ; f), (So ; To ; λ x, code_link (f x) p2)) p1.

(* Remove unexported functions from a raw package *)
Definition trim (E : Interface) (p : raw_package) :=
  filterm (λ n _, E n) p.

Lemma valid_link :
  ∀ L1 L2 I M E p1 p2,
    ValidPackage L1 M E p1 →
    ValidPackage L2 I M p2 →
    fcompat L1 L2 →
    ValidPackage (unionm L1 L2) I E (link p1 p2).
Proof.
  intros L1 l2 I M E p1 p2 h1 h2 hc.
  apply prove_valid_package.
  eapply from_valid_package in h1.
  intros [n [So To]] ho. unfold link.
  rewrite mapmE.
  specialize (h1 _ ho) as h1'. cbn in h1'.
  destruct h1' as [f [ef hf]].
  rewrite ef. cbn.
  eexists. split. 1: reflexivity.
  intro x.
  eapply valid_code_link.
  - eapply valid_injectLocations.
    + apply fsubmapUl.
    + eapply hf.
  - eapply valid_package_inject_locations.
    + by apply fsubmapUr.
    + auto.
Qed.

Ltac package_evar :=
  lazymatch goal with
  | |- (ValidPackage ?L ?I ?E ?P) =>
    tryif assert_fails (is_evar L)
      then (eapply valid_package_inject_locations; swap 1 2; package_evar) else
    tryif assert_fails (is_evar I)
      then (eapply valid_package_inject_import; swap 1 2; package_evar) else
    tryif assert_fails (is_evar E)
      then (eapply valid_package_inject_export; swap 1 2; package_evar) else
    idtac
  | _ => idtac
  end.

#[export] Hint Extern 5 (ValidPackage ?L ?I ?E ?p) =>
  package_evar ; [ eapply pack_valid | .. ]
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (link ?p1 ?p2)) =>
  package_evar ; [ eapply valid_link | .. ]
  : typeclass_instances ssprove_valid_db.


Lemma code_link_bind :
  ∀ {A B : choiceType} (v : raw_code A)
    (k : A → raw_code B) (p : raw_package),
    code_link (bind v k) p =
    bind (code_link v p) (λ x, code_link (k x) p).
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

Lemma code_link_assoc :
  ∀ A (v : raw_code A) f g,
    code_link (code_link v f) g =
    code_link v (link f g).
Proof.
  intros A v f g.
  induction v in f, g |- *.
  - cbn. reflexivity.
  - cbn. unfold link in *.
    rewrite lookup_op_map.
    destruct lookup_op eqn:e.
    + cbn. rewrite code_link_bind. f_equal.
      apply functional_extensionality. auto.
    + cbn. eauto.
  - cbn. f_equal. apply functional_extensionality. auto.
  - cbn. f_equal. auto.
  - cbn. f_equal. apply functional_extensionality. auto.
Qed.

Lemma trim_get :
  ∀ (E : Interface) (p : raw_package) n So To f,
    fhas p (n, (So; To; f)) →
    fhas E (n, (So, To)) →
    trim E p n = Some (So ; To ; f).
Proof.
  intros E p n So To f e h.
  unfold trim. rewrite filtermE. rewrite e. cbn.
  rewrite h. reflexivity.
Qed.

Lemma valid_trim :
  ∀ L I E p,
    ValidPackage L I E p →
    ValidPackage L I E (trim E p).
Proof.
  intros L I E p h.
  apply prove_valid_package.
  eapply from_valid_package in h.
  intros [n [So To]] ho.
  specialize (h _ ho). cbn in h. destruct h as [f [ef hf]].
  exists f. intuition auto.
  apply trim_get. all: auto.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (trim ?E ?p)) =>
  eapply valid_trim
  : typeclass_instances ssprove_valid_db.

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
  destruct (p1 n), (E n) => //.
Qed.

Lemma trim_idemp :
  ∀ E p,
    trim E (trim E p) = trim E p.
Proof.
  intros E p.
  apply eq_fmap. intro n.
  unfold trim. rewrite !filtermE.
  destruct (p n), (E n) => //.
Qed.

Lemma lookup_op_trim :
  ∀ E o p,
    lookup_op (trim E p) o =
    obind (λ f, if E o.1 then Some f else None) (lookup_op p o).
Proof.
  intros E [n [So To]] p.
  unfold lookup_op, trim.
  rewrite filtermE.
  destruct (p n) as [[S1 [T1 f1]]|] => //=;
    destruct (E n) as [[S2 T2]|] => //=.
  1,2: do 2 destruct choice_type_eqP => //=.
Qed.

Lemma code_link_trim_right :
  ∀ A L E (v : raw_code A) p,
    ValidCode L E v →
    code_link v (trim E p) = code_link v p.
Proof.
  intros A L E v p h.
  induction h in p |- *.
  - cbn. reflexivity.
  - cbn. rewrite lookup_op_trim.
    destruct o as [n [S T]].
    destruct lookup_op eqn:e.
    + cbn. rewrite H //=. f_equal. apply functional_extensionality.
      intuition auto.
    + cbn. eauto.
  - cbn. f_equal. apply functional_extensionality. intuition auto.
  - cbn. f_equal. intuition auto.
  - cbn. f_equal. apply functional_extensionality. intuition auto.
Qed.

Lemma trim_get_inv :
  ∀ E p n So To f,
    trim E p n = Some (So ; To ; f) →
    p n = Some (So ; To ; f) ∧ n \in domm E.
Proof.
  intros E p n So To f e.
  unfold trim in e. rewrite filtermE in e. cbn in e.
  destruct (p n) as [[S1 [T1 f1]]|] eqn:e1.
  2:{ cbn in e. discriminate. }
  cbn in e.
  destruct (E n) eqn:e2.
  2:{ discriminate. }
  noconf e.
  intuition auto.
  apply /dommP.
  eexists; apply e2.
Qed.

Lemma link_trim_right :
  ∀ L I E p1 p2,
    ValidPackage L I E p1 →
    link (trim E p1) (trim I p2) =
    link (trim E p1) p2.
Proof.
  intros L I E p1 p2 h.
  apply eq_fmap. intro n.
  rewrite /link !mapmE.
  destruct (trim E p1 n) as [[S1 [T1 f1]]|] eqn:e.
  2:{ reflexivity. }
  simpl.
  do 3 f_equal.
  extensionality x.
  apply trim_get_inv in e as [e he].
  eapply from_valid_package in h.
  move: he => /dommP [[So To] he].
  specialize (h (n, (So, To)) he). cbn in h.
  destruct h as [f [ef h]].
  rewrite ef in e. noconf e.
  eapply code_link_trim_right.
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
  rewrite code_link_assoc.
  reflexivity.
Qed.

Notation "p1 ∘ p2" :=
  (link p1 p2) (right associativity, at level 20) : package_scope.


(** Parallel composition *)

(** Two packages can be composed in parallel or merged if they implement
    disjoint interfaces. As such, it might be worth it to trim the packages
    before using par.
*)

Definition par (p1 p2 : raw_package) :=
  unionm p1 p2.

Lemma valid_par :
  ∀ L1 L2 I1 I2 E1 E2 p1 p2,
    ValidPackage L1 I1 E1 p1 →
    ValidPackage L2 I2 E2 p2 →
    fseparate p1 p2 →
    fcompat L1 L2 →
    fcompat I1 I2 →
    ValidPackage (unionm L1 L2) (unionm I1 I2) (unionm E1 E2) (par p1 p2).
Proof.
  intros L1 L2 I1 I2 E1 E2 p1 p2 h1 h2 h cL cI.
  apply prove_valid_package.
  eapply from_valid_package in h1.
  eapply from_valid_package in h2.
  intros [n [So To]] ho.
  unfold par. rewrite /fhas 2!unionmE //= in ho |- *.
  destruct (E1 n) as [[S T]|] eqn:E.
  - specialize (h1 (n, (S, T)) E) as h'. cbn in h'.
    destruct h' as [f [e hf]].
    rewrite e. cbn.
    simpl in ho.
    injection ho => ? ?; subst.
    exists f. intuition auto.
    eapply valid_injectLocations. 1: apply fsubmapUl.
    eapply valid_injectMap. 1: apply fsubmapUl.
    auto.
  - destruct (E2 n) as [[S T]|] eqn:E' => //.
    specialize (h2 (n, (S, T)) E') as h'. cbn in h'.
    destruct h' as [f [e hf]].
    destruct (p1 n) as [[S1 [T1 f1]]|] eqn:e1.
    1:{
      exfalso.
      move: h => [] /fdisjointP h.
      specialize (h n).
      rewrite 2!mem_domm e e1 // in h.
      specialize (h erefl).
      move: h => /negP //.
    }
    cbn. rewrite e.
    simpl in ho.
    injection ho => ? ?; subst.
    exists f. intuition auto.
    eapply valid_injectLocations. 1: by apply fsubmapUr.
    eapply valid_injectMap. 1: by apply fsubmapUr.
    auto.
Qed.

#[export] Hint Extern 1 (ValidPackage ?L ?I ?E (par ?p1 ?p2)) =>
  package_evar ; [ eapply valid_par | .. ]
  : typeclass_instances ssprove_valid_db.

Class FDisjoint {A : ordType} s1 s2 :=
  are_disjoint : @fdisjoint A s1 s2.

(** When comparing export interfaces, since we disallow overloading
    we need to have only the identifier parts disjoint.
*)
Definition idents (E : Interface) : {fset ident} := domm E.

Lemma domm_trim :
  ∀ E p,
    domm (trim E p) :<=: idents E.
Proof.
  intros E p. unfold trim. unfold idents.
  apply /fsubsetP => n.
  rewrite 2!mem_domm filtermE.
  destruct (E n), (p n) => //=.
Qed.

Lemma parable_trim :
  ∀ E1 E2 p1 p2,
    fdisjoint (idents E1) (idents E2) →
    fseparate (trim E1 p1) (trim E2 p2).
Proof.
  intros E1 E2 p1 p2 h.
  apply fsep.
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

#[export] Instance FDisjointUr {A : ordType} (s1 s2 s3 : {fset A}) :
  FDisjoint s1 s2 →
  FDisjoint s1 s3 →
  FDisjoint s1 (s2 :|: s3).
Proof.
  intros h2 h3.
  unfold FDisjoint in *.
  rewrite fdisjointUr.
  rewrite h2 h3. reflexivity.
Qed.

#[export] Hint Extern 1 (FDisjoint _ _) =>
  reflexivity
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (FDisjoint (fset ?l1) (fset ?l2)) =>
  repeat rewrite [fset]unlock
  : typeclass_instances ssprove_valid_db.

(*
#[export] Hint Extern 1 (Parable _ _) =>
  eapply fdisjoint_from_class
  : typeclass_instances ssprove_valid_db.

#[export] Hint Extern 1 (Parable (trim ?E1 ?p1) (trim ?E2 ?p2)) =>
  eapply parable_trim ;
  eapply fdisjoint_from_class
  : typeclass_instances ssprove_valid_db.
 *)

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
    fseparate p1 p2 →
    par p1 p2 = par p2 p1.
Proof.
  intros p1 p2 h.
  apply unionmC. apply h.
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

Lemma code_link_par_left :
  ∀ A I L L' E (v : raw_code A) p1 p2,
    ValidCode L E v →
    ValidPackage L' I E p1 →
    code_link v (par p1 p2) = code_link v p1.
Proof.
  intros A I L L' E v p1 p2 hv hp1.
  unfold ValidCode in hv.
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

Lemma code_link_par_right :
  ∀ A I L L' E (v : raw_code A) p1 p2,
    fseparate p1 p2 →
    ValidCode L E v →
    ValidPackage L' I E p2 →
    code_link v (par p1 p2) = code_link v p2.
Proof.
  intros A I L L' E v p1 p2 h hv hp1.
  rewrite par_commut. 1: eapply code_link_par_left.
  all: eauto.
Qed.

(* Predicate stating that a package exports all it implements *)
Definition trimmed E p :=
  trim E p = p.

Lemma domm_trimmed :
  ∀ E p,
    trimmed E p →
    fsubset (domm p) (idents E).
Proof.
  intros E p h.
  unfold trimmed in h. rewrite <- h.
  apply domm_trim.
Qed.

Lemma trimmed_valid_Some_in :
  ∀ L I E p n S T f,
    ValidPackage L I E p →
    trimmed E p →
    p n = Some (S ; T ; f) →
    E n = Some (S, T).
Proof.
  intros L I E p n S T f hv ht e.
  unfold trimmed in ht. pose e as e'. rewrite <- ht in e'.
  unfold trim in e'. rewrite filtermE in e'.
  rewrite e in e'. simpl in e'.
  eapply from_valid_package in hv.
  destruct (E n) as [[S' T']|] eqn:e2 => //.
  specialize (hv (n, (S', T')) e2).
  simpl in hv.
  destruct hv as [f' [hv hv']].
  rewrite hv in e.
  injection e => ? ? ?; by subst.
Qed.

Lemma interchange :
  ∀ A B C D E F L1 L2 L3 L4 p1 p2 p3 p4,
    ValidPackage L1 B A p1 →
    ValidPackage L2 E D p2 →
    ValidPackage L3 C B p3 →
    ValidPackage L4 F E p4 →
    trimmed A p1 →
    trimmed D p2 →
    fseparate p3 p4 →
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
    eapply from_valid_package in h1.
    specialize (h1 (n, (S1, T1)) hi). cbn in h1.
    destruct h1 as [g [eg hg]].
    rewrite e1 in eg. noconf eg. cbn in hg.
    erewrite code_link_par_left. 2: eapply hg.
    all: eauto.
  - simpl. destruct (p2 n) as [[S2 [T2 f2]]|] eqn:e2.
    + simpl. f_equal. f_equal. f_equal. extensionality x.
      eapply trimmed_valid_Some_in in e2 as hi. 2,3: eauto.
      eapply from_valid_package in h2.
      specialize (h2 (n, (S2, T2)) hi). cbn in h2.
      destruct h2 as [g [eg hg]].
      rewrite e2 in eg. noconf eg. cbn in hg.
      erewrite code_link_par_right. all: eauto.
    + simpl. reflexivity.
Qed.

Local Open Scope type_scope.

(** Package builder from a function *)
(* TODO: Still works, but outdated. *)

Definition typed_function L I :=
  ∑ (S T : choice_type), S → code L I T.

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

(* MK: Should this be fixed?
Definition funmkpack {L I} {E : Interface}
  (f : ∀ (o : opsig), E o.1 = Some o.2 → src o → code L I (tgt o)) :
  package L I E.
Proof.
  pose foo : seq (nat * typed_function L I) :=
    [interface (ide o, (chsrc o ; chtgt o ; f o h)) | h # o ∈ E].
  pose bar := mkfmap foo.
  exists (@mapm _ (typed_function L I) typed_raw_function
    (λ '(So ; To ; f), (So ; To ; λ x, (f x).(prog))) bar).
  apply prove_valid_package.
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
 *)

(* Identity package *)

(* Maybe lock this definition? *)
Definition mkdef (A B : choice_type) (f : A → raw_code B)
  : typed_raw_function :=
  (A ; B ; f).

Definition ID (I : Interface) : raw_package :=
  mapim (λ n '(s, t), mkdef s t (λ x, opr (n, (s, t)) x (λ y, ret y))) I.

(*
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
  ∀ {A : eqType} n (x : A) (s : seq ((nat:eqType)%type * A)),
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
 *)

Lemma lookup_op_ID :
  ∀ (I : Interface) o,
    fhas I o →
    lookup_op (ID I) o =
    Some (λ x, opr o x (λ y, ret y)).
Proof.
  intros I [n [S T]] E.
  unfold lookup_op.
  rewrite mapimE E //=.
  do 2 destruct choice_type_eqP => //=.
  rewrite cast_fun_K //.
Qed.

Lemma valid_ID :
  ∀ I,
    ValidPackage emptym I I (ID I).
Proof.
  intros I.
  apply prove_valid_package.
  intros [id [S T]] ho.
  rewrite mapimE ho //=.
  eexists; split; [ reflexivity |].
  intros x.
  apply valid_opr => // y.
  apply valid_ret.
Qed.

(* Only for pacakages because we don't expect to infer a flat proof *)
#[export] Hint Extern 2 (ValidPackage ?L ?I ?E (ID ?I')) =>
  eapply valid_ID
  : typeclass_instances ssprove_valid_db.

Lemma trimmed_ID :
  ∀ I, trimmed I (ID I).
Proof.
  intros I.
  unfold trimmed. apply eq_fmap. intro n.
  unfold trim. rewrite filtermE mapimE.
  destruct (I n) => //.
Qed.

Lemma code_link_id :
  ∀ A (v : raw_code A) L I,
    ValidCode L I v →
    code_link v (ID I) = v.
Proof.
  intros A v L I hv.
  induction hv.
  - cbn. reflexivity.
  - simpl.
    rewrite (lookup_op_ID _ _ H) //=.
    f_equal.
    extensionality y.
    apply H1.
  - simpl. f_equal. apply functional_extensionality. auto.
  - simpl. f_equal. auto.
  - simpl. f_equal. apply functional_extensionality. auto.
Qed.

Lemma link_id :
  ∀ L I E p,
    ValidPackage L I E p →
    trimmed E p →
    link p (ID I) = p.
Proof.
  intros L I E p hp tp.
  apply eq_fmap. intro n. unfold link.
  rewrite mapmE. destruct (p n) as [[S [T f]]|] eqn:e.
  - cbn. f_equal. f_equal. f_equal. extensionality x.
    eapply trimmed_valid_Some_in in e as hi. 2,3: eauto.
    eapply from_valid_package in hp.
    specialize (hp (n, (S, T)) hi) as h'. cbn in h'.
    destruct h' as [g [eg hg]].
    rewrite e in eg. noconf eg. cbn in hg.
    eapply code_link_id. all: eauto.
  - reflexivity.
Qed.

Lemma id_link :
  ∀ L I E p,
    ValidPackage L I E p →
    trimmed E p →
    link (ID E) p = p.
Proof.
  intros L I E p hp tp.
  apply eq_fmap. intro n. unfold link.
  rewrite mapmE mapimE.
  rewrite -{2}tp.
  rewrite /trim filtermE.
  destruct (E n) as [[S T]|] eqn:E' => //=.
  2: destruct (p n) => //.
  apply from_valid_package in hp.
  specialize (hp (n, (S, T)) E').
  destruct hp as [f [H H']].
  rewrite H.
  do 2 destruct choice_type_eqP => //=.
  rewrite cast_fun_K //=.
  do 3 f_equal.
  extensionality x.
  apply bind_ret.
Qed.

Lemma code_link_if :
  ∀ A (c₀ c₁ : raw_code A) (p : raw_package) b,
    code_link (if b then c₀ else c₁) p =
    if b then code_link c₀ p else code_link c₁ p.
Proof.
  intros A c₀ c₁ p b.
  destruct b. all: reflexivity.
Qed.

Lemma domm_ID :
  ∀ I, domm (ID I) = domm I.
Proof.
  intros I. rewrite domm_mapi //.
Qed.
