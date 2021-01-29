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

    Derive NoConfusion NoConfusionHom for chUniverse.
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

    Fixpoint raw_program_link {A} (v : raw_program A) (p : raw_package) :
      raw_program A :=
      match v with
      | ret a => ret a
      | opr o a k =>
        (* The None branch doesn't happen when valid *)
        match lookup_op p o with
        | Some f => bind (f a) (λ x, raw_program_link (k x) p)
        | None => opr o a (λ x, raw_program_link (k x) p)
        end
      | getr l k => getr l (λ x, raw_program_link (k x) p)
      | putr l v k => putr l v (raw_program_link k p)
      | sampler op k => sampler op (λ x, raw_program_link (k x) p)
      end.

    Lemma raw_program_link_valid :
      ∀ A L Im Ir (v : raw_program A) p,
        valid_program L Im v →
        valid_package L Ir Im p →
        valid_program L Ir (raw_program_link v p).
    Proof.
      intros A L Im Ir v p hv hp.
      induction hv.
      all: try solve [ constructor ; auto ].
      eapply lookup_op_valid in hp as hf. 2: eauto.
      destruct hf as [f [ef hf]].
      cbn. rewrite ef.
      apply bind_valid. all: auto.
    Qed.

    (* TODO NEEDED? *)
    (* Definition program_link {A L Im Ir}
      (v : program L Im A) (p : opackage L Ir Im) :
      program L Ir A.
    Proof.
      exists (raw_program_link (v ∙1) (p ∙1)).
      destruct v as [v hv], p as [p hp]. cbn.
      eapply raw_program_link_valid. all: eauto.
    Defined. *)

    Definition raw_link (p1 p2 : raw_package) : raw_package :=
      @mapm _ typed_raw_function _
        (λ '(So ; To ; f), (So ; To ; λ x, raw_program_link (f x) p2)) p1.

    (* TODO Maybe trim on the left? *)
    (* Definition olink {L I E I'}
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
    Defined. *)

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

    Lemma raw_program_link_bind :
      ∀ {A B : choiceType} (v : raw_program A)
        (k : A → raw_program B) (p : raw_package),
        raw_program_link (bind v k) p =
        bind (raw_program_link v p) (λ x, raw_program_link (k x) p).
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
      | ret a => True
      | opr o a k =>
        match lookup_op p o with
        | Some f => ∀ x, provides p (k x)
        | None => False
        end
      | getr l k => ∀ x, provides p (k x)
      | putr l v k => provides p k
      | sampler op k => ∀ x, provides p (k x)
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
      induction hv.
      all: try solve [ cbn ; auto ].
      cbn.
      destruct lookup_op eqn:e.
      2:{
        specialize (hp _ H) as hp'.
        destruct o as [n [So To]]. cbn in *.
        destruct hp' as [f [ef hf]].
        destruct (p n) as [[St [Tt ft]]|] eqn:et. 2: discriminate.
        destruct chUniverse_eqP.
        2:{ inversion ef. congruence. }
        destruct chUniverse_eqP.
        2:{ inversion ef. congruence. }
        discriminate.
      }
      eauto.
    Qed.

    (* Lemma program_link_assoc :
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
    Qed. *)

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
    (* Definition opackage_inject_locations {I E L1 L2}
      (hL : fsubset L1 L2) (p : opackage L1 I E) :
      opackage L2 I E.
    Proof.
      exists (p ∙1).
      destruct p as [p h]. cbn.
      eapply valid_package_inject_locations. all: eauto.
    Defined. *)

    (* Definition program_link' {A L1 L2 I M}
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
    Defined. *)

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
    Definition link {L1 L2 I M E}
      (p1 : package L1 M E) (p2 : package L2 I M) :
      package (L1 :|: L2) I E.
    Proof.
      exists (raw_link (trim E (p1.(pack))) (p2.(pack))).
      destruct p1 as [p1 h1], p2 as [p2 h2]. cbn.
      eapply link_valid. all: eauto.
    Defined.

    (* Definition link' {I M1 M2 E} (p1 : package M1 E) (p2 : package I M2)
      (h : fsubset M1 M2) : package I E.
    Proof.
      exists (p1.π1 :|: p2.π1).
      exists (raw_link (trim E (p1.π2 ∙1)) (p2.π2 ∙1)).
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]]. cbn.
      eapply link_valid.
      - eauto.
      - eapply valid_package_inject_export. all: eauto.
    Defined. *)

    (* Definition olink' {L1 L2 I E I'}
      (p1 : opackage L1 I E) (p2 : opackage L2 I' I) :
      opackage (L1 :|: L2) I' E.
    Proof.
      exists (raw_link (trim E (p1 ∙1)) p2 ∙1).
      destruct p1 as [p1 h1], p2 as [p2 h2]. cbn.
      eapply link_valid. all: eauto.
    Defined. *)

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

    (* Lemma package_ext :
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
    Qed. *)

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

    Lemma raw_program_link_trim_right :
      ∀ A L E (v : raw_program A) p,
        valid_program L E v →
        raw_program_link v (trim E p) = raw_program_link v p.
    Proof.
      intros A L E v p h.
      induction h in p |- *.
      - cbn. reflexivity.
      - cbn. rewrite lookup_op_trim.
        destruct lookup_op eqn:e.
        + cbn. rewrite H. f_equal. apply functional_extensionality.
          intuition auto.
        + cbn. f_equal. apply functional_extensionality. intuition auto.
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
      rewrite trim_idemp.
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

    (* Lemma link_assoc :
      ∀ {L1 L2 L3 E M1 M2 I}
        (p1 : package L1 M1 E)
        (p2 : package L2 M2 M1)
        (p3 : package L3 I M2),
        link p1 (link p2 p3) = link (link p1 p2) p3.
    Proof.
      intros E M1 M2 I [l1 [p1 h1]] [l2 [p2 h2]] [l3 [p3 h3]].
      apply package_ext.
      - cbn. apply fsetUA.
      - cbn. eapply raw_link_assoc. all: eauto.
    Qed. *)

    (* bundled versions *)
    (* Definition blink p1 p2 (h : import p1 = export p2) : bundle.
    Proof.
      unshelve econstructor.
      - exact (locs p1 :|: locs p2).
      - exact (import p2).
      - exact (export p1).
      - exists (raw_link (trim (export p1) ((pack p1) ∙1)) ((pack p2) ∙1)).
        destruct p1 as [L1 I1 E1 [p1 h1]], p2 as [L2 I2 E2 [p2 h2]].
        cbn in h. subst. cbn.
        eapply link_valid. all: eauto.
    Defined. *)

    (* Lemma blink_export :
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
    Qed. *)

    (* Lemma blink_assoc :
      ∀ p1 p2 p3 (h12 : import p1 = export p2) (h23 : import p2 = export p3),
        blink p1 (blink p2 p3 h23) h12 =
        blink (blink p1 p2 h12) p3 h23.
    Proof.
      intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] [L3 I3 E3 [p3 h3]] h12 h23.
      cbn in *. subst.
      apply bundle_ext. all: cbn. 2,3: auto.
      - apply fsetUA.
      - eapply raw_link_assoc. all: eauto.
    Qed. *)

  End Link.

  (* Notation "p1 ∘ p2" :=
      (link p1 p2) (right associativity, at level 80) : package_scope. *)

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

    Lemma parable_union :
      ∀ {E1 E2 E3},
        parable E1 E2 →
        parable E1 E3 →
        parable E1 (E2 :|: E3).
    Proof.
      rewrite /parable.
      move=> E1 E2 E3 h1 h2.
      rewrite /idents imfsetU.
      rewrite fdisjointUr.
      by apply andb_true_intro.
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

    (* Definition bpar (p1 p2 : bundle) (h : parable (export p1) (export p2)) :
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
    Defined. *)

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

    Lemma trim_union_trim : forall A1 A2 p1 p2,
        parable A1 A2 →
        (trim (A1 :|: A2) (unionm (trim A1 p1) (trim A2 p2)))
        = (unionm (trim A1 p1) (trim A2 p2)).
    Proof.
      (* TL: this has to be my worst proof ever.. I should clean it up! *)
      move=> A1 A2 p1 p2 H.
      unfold trim at 1.
      rewrite filterm_union.
      - f_equal.
        + unfold trim.
          apply eq_fmap. move=> n.
          rewrite filtermE /obind /oapp.
          rewrite filtermE /obind /oapp.
          move: (p1 n) => [[a [b c]]|]. 2: { reflexivity. }
          set X:= _ \in _. remember X as Y eqn: eqY.
          move: Y eqY. rewrite /X. clear X. move=> [|] eqY. 2: { reflexivity. }
          suff: (n, (a, b)) \in A1 :|: A2.
          * by move=> ->.
          * rewrite in_fsetU. apply Bool.orb_true_intro. auto.
        + unfold trim.
          apply eq_fmap. move=> n.
          rewrite filtermE /obind /oapp.
          rewrite filtermE /obind /oapp.
          move: (p2 n) => [[a [b c]]|]. 2: { reflexivity. }
          set X:= _ \in _. remember X as Y eqn: eqY.
          move: Y eqY. rewrite /X. clear X. move=> [|] eqY. 2: { reflexivity. }
          suff: (n, (a, b)) \in A1 :|: A2.
          * by move=> ->.
          * rewrite in_fsetU. apply Bool.orb_true_intro. auto.
      - unfold parable in H.
        eapply fdisjoint_trans. 1:{ apply trim_domm_subset. }
        rewrite fdisjointC.
        eapply fdisjoint_trans. 1: { apply trim_domm_subset. }
        rewrite fdisjointC.
        assumption.
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

    Lemma raw_par_assoc :
      ∀ E1 E2 E3 p1 p2 p3,
        parable E1 E2 →
        parable E2 E3 →
        parable E1 E3 →
        raw_par E1 (E2 :|: E3) p1 (raw_par E2 E3 p2 p3) =
        raw_par (E1 :|: E2) E3 (raw_par E1 E2 p1 p2) p3.
    Proof.
      move=> E1 E2 E3 p1 p2 p3 h12 h23 h13.
      unfold raw_par.
      rewrite trim_union_trim. 2: try auto.
      rewrite trim_union_trim. 2: try auto.
      apply unionmA.
    Qed.

    (* TODO See what we should keep / what we need *)

    (* Lemma bpar_commut :
      ∀ p1 p2 (h : parable (export p1) (export p2)),
        bpar p1 p2 h = bpar p2 p1 (parable_sym h).
    Proof.
      intros [L1 I1 E1 [p1 h1]] [L2 I2 E2 [p2 h2]] h.
      simpl in *.
      apply bundle_ext. all: simpl.
      1-3: apply fsetUC.
      intro. f_equal.
      apply raw_par_commut. assumption.
    Qed. *)

    (* Definition par {I1 I2 E1 E2} (p1 : package I1 E1) (p2 : package I2 E2)
      (h : parable E1 E2) : package (I1 :|: I2) (E1 :|: E2).
    Proof.
      exists (p1.π1 :|: p2.π1).
      exists (raw_par E1 E2 p1.π2 ∙1 p2.π2 ∙1).
      destruct p1 as [l1 [p1 h1]], p2 as [l2 [p2 h2]]. simpl.
      apply valid_par. all: auto.
    Defined.

    Definition opackage_transport {L I1 I2 E1 E2}
      (eI : I1 = I2) (eE : E1 = E2)
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

    Lemma par_assoc :
      ∀ {I1 I2 I3 E1 E2 E3}
        (p1 : package I1 E1)
        (p2 : package I2 E2)
        (p3 : package I3 E3)
        (h12 : parable E1 E2)
        (h23 : parable E2 E3)
        (h13 : parable E1 E3),
        (* TL: hm, this use of parable_union + parable_sym is quite cumbersome.. *)
        package_transport (fsetUA I1 I2 I3) (fsetUA E1 E2 E3)
                          (par p1 (par p2 p3 h23) (parable_union h12 h13)) =
        par (par p1 p2 h12) p3 (parable_sym (parable_union (parable_sym h13) (parable_sym h23))).
    Proof.
      move=> I1 I2 I3 E1 E2 E3 [l1 [p1 h1]] [l2 [p2 h2]] [l3 [p3 h3]] ? ? ?.
      apply package_ext.
      - simpl. apply fsetUA.
      - simpl. move=> ?. f_equal.
        apply raw_par_assoc.
        all: auto.
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
        rewrite <- raw_link_trim_commut. rewrite trim_idemp.
        rewrite <- raw_link_trim_commut. rewrite trim_idemp.
        rewrite trim_raw_par. unfold raw_par.
        rewrite raw_link_unionm.
        erewrite <- import_raw_par_left. 2-3: eauto.
        erewrite <- (import_raw_par_right p2 _ p4). 2-4: eauto.
        intro. reflexivity.
    Qed. *)

  End Par.

  Local Open Scope type_scope.

  (* TODO OUTDATED *)

  (** Package builder

    The same way we have constructors for program, we provide constructors
    for packages that are correct by construction.
  *)

  Definition typed_function L I :=
    ∑ (S T : chUniverse), S → program L I T.

  (* Definition export_interface {L I} (p : {fmap ident -> typed_function L I})
    : Interface :=
    fset (mapm (λ '(So ; To ; f), (So, To)) p).

  Definition mkpack {L I} (p : {fmap ident -> typed_function L I}) :
    opackage L I (export_interface p).
  Proof.
    exists (@mapm _ (typed_function L I) typed_raw_function
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
  Defined. *)

  (* Alternative from a function *)

  Equations? map_interface (I : seq opsig) {A} (f : ∀ x, x \in I → A) :
    seq A :=
      map_interface (a :: I') f := f a _ :: map_interface I' (λ x h, f x _) ;
      map_interface [::] f := [::].
    Proof.
      - rewrite in_cons. apply/orP. left. apply/eqP. reflexivity.
      - rewrite in_cons. apply/orP. right. auto.
    Qed.

  Notation "[ 'interface' e | h # x ∈ I ]" :=
    (map_interface I (λ x h, e)) : package_scope.

  Open Scope package_scope.

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

  Section ID.

    Definition ID (I : Interface) (h : flat I) : package fset0 I I :=
      (funmkpack h (λ o ho x, {program opr o x (λ x, ret x) })).

    (* Definition idb (I : Interface) (h : flat I) : bundle := {|
      locs := fset0 ;
      import := I ;
      export := I ;
      pack := funmkpack h (λ o ho x, opr o ho x (λ x, ret x))
    |}. *)

    Definition raw_id I h :=
      (ID I h).(pack).

    Definition ptrim {L I E} (p : package L I E) : package L I E.
    Proof.
      exists (trim E p.(pack)).
      destruct p as [p h]. cbn.
      apply valid_trim. auto.
    Defined.

    (* Definition ptrim {I E} (p : package I E) : package I E :=
      (p.π1 ; optrim (p.π2)).

    Definition btrim (b : bundle) : bundle := {|
      locs := locs b ;
      import := import b ;
      export := export b ;
      pack := optrim (pack b)
    |}. *)

    Lemma raw_idE :
      ∀ I h n,
        raw_id I h n =
        omap (λ '(So,To), (So ; To ; λ x, _opr (n,(So,To)) x (λ y, _ret y))) (getm_def I n).
    Proof.
      intros I h n.
      unfold raw_id. simpl.
      rewrite mapmE. rewrite mkfmapE.
      destruct getm_def eqn:e.
      - apply getm_def_map_interface_Some in e as h1.
        destruct h1 as [[S T] [hn [h1 h2]]]. subst. cbn.
        rewrite h1. cbn. reflexivity.
      - apply getm_def_map_interface_None in e.
        rewrite e. reflexivity.
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

    Lemma lookup_op_raw_id :
      ∀ I h o,
        lookup_op (raw_id I h) o =
        if o \in I
        then Some (λ x, _opr o x (λ y, _ret y))
        else None.
    Proof.
      intros I h [n [S T]].
      unfold lookup_op. rewrite raw_idE.
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

    Lemma raw_program_link_id :
      ∀ A (v : raw_program A) L I h,
        valid_program L I v →
        raw_program_link v (raw_id I h) = v.
    Proof.
      intros A v L I h hv.
      induction v in hv |- *.
      - cbn. reflexivity.
      - simpl. cbn in hv. destruct hv as [ho hv].
        rewrite lookup_op_raw_id. rewrite ho. simpl. f_equal.
        extensionality z. intuition auto.
      - simpl. cbn in hv. f_equal. apply functional_extensionality.
        intuition auto.
      - simpl. cbn in hv. f_equal. intuition auto.
      - simpl. cbn in hv. f_equal. apply functional_extensionality.
        intuition auto.
    Qed.

    Lemma link_id :
      ∀ I E (p : package I E) h,
        link p (ID I h) = ptrim p.
    Proof.
      intros I E [L [p hp]] h.
      apply package_ext.
      - cbn. rewrite fsetU0. reflexivity.
      - simpl. intro n. unfold raw_link.
        rewrite mapmE. destruct (trim E p n) as [[S [T f]]|] eqn:e.
        + rewrite e. simpl. f_equal. f_equal. f_equal.
          apply functional_extensionality. intro x.
          apply trim_get_inv in e. destruct e as [e ho].
          specialize (hp _ ho). cbn in hp.
          destruct hp as [g [eg hg]].
          rewrite e in eg. noconf eg. cbn in hg.
          eapply raw_program_link_id. eauto.
        + rewrite e. simpl. reflexivity.
      Unshelve. auto.
    Qed.

    Lemma trim_ID :
      ∀ I h,
        ptrim (ID I h) = ID I h.
    Proof.
      intros I h.
      apply package_ext.
      - cbn. reflexivity.
      - simpl. intro n. unfold trim.
        rewrite filtermE. unfold obind, oapp.
        rewrite mapmE. unfold omap, obind, oapp.
        destruct (mkfmap (T:=nat_ordType) _ _) eqn:m.
        + destruct t as [S [T p]].
          destruct ((n, (S, T)) \in I) eqn:hin.
          * rewrite hin. reflexivity.
          * rewrite hin.
            rewrite mkfmapE in m.
            apply getm_def_map_interface_Some in m.
            destruct m as [[S' T'] [hin' [L R]]].
            inversion R; subst.
            rewrite hin'  in hin.
            discriminate.
        + reflexivity.
    Qed.

  End ID.

  (* Some folding lemmata *)

  Lemma fold_ret :
    ∀ (A : choiceType) L I (x : A) (h : valid_program L I _),
      exist _ (_ret x) h = ret x.
  Proof.
    intros A L I x h.
    apply program_ext. reflexivity.
  Qed.

  Lemma valid_opr_in :
    ∀ {A L I} {o x} {k : tgt o → raw_program A},
      valid_program L I (_opr o x k) →
      o \in I.
  Proof.
    intros A L I o x k h.
    cbn in h. intuition auto.
  Qed.

  Lemma valid_opr_k :
    ∀ {A L I} {o x} {k : tgt o → raw_program A},
      valid_program L I (_opr o x k) →
      ∀ v, valid_program L I (k v).
  Proof.
    intros A L I o x k h.
    cbn in h. intuition auto.
  Qed.

  Lemma fold_opr :
    ∀ (A : choiceType) L I
      (o : opsig) (x : src o) (k : tgt o → raw_program A)
      (h : valid_program L I _),
      exist _ (_opr o x k) h =
      opr o (valid_opr_in h) x (λ x, exist _ (k x) (valid_opr_k h x)).
  Proof.
    intros A L I o x k h.
    apply program_ext. reflexivity.
  Qed.

  Lemma valid_getr_in :
    ∀ {A L I} {l} {k : Value l.π1 → raw_program A},
      valid_program L I (_getr l k) →
      l \in L.
  Proof.
    intros A L I l k h.
    cbn in h. intuition auto.
  Qed.

  Lemma valid_getr_k :
    ∀ {A L I} {l} {k : Value l.π1 → raw_program A},
      valid_program L I (_getr l k) →
      ∀ v, valid_program L I (k v).
  Proof.
    intros A L I l k h.
    cbn in h. intuition auto.
  Qed.

  Lemma fold_getr :
    ∀ (A : choiceType) L I
      (l : Location) (k : Value l.π1 → raw_program A)
      (h : valid_program L I _),
      exist _ (_getr l k) h =
      getr l (valid_getr_in h) (λ x, exist _ (k x) (valid_getr_k h x)).
  Proof.
    intros A L I l k h.
    apply program_ext. reflexivity.
  Qed.

  Lemma valid_putr_in :
    ∀ {A L I} {l} {v : Value l.π1} {k : raw_program A},
      valid_program L I (_putr l v k) →
      l \in L.
  Proof.
    intros A L I l v k h.
    cbn in h. intuition auto.
  Qed.

  Lemma valid_putr_k :
    ∀ {A L I} {l} {v : Value l.π1} {k : raw_program A},
      valid_program L I (_putr l v k) →
      valid_program L I k.
  Proof.
    intros A L I l v k h.
    cbn in h. intuition auto.
  Qed.

  Lemma fold_putr :
    ∀ (A : choiceType) L I
      (l : Location) (v : Value l.π1) (k : raw_program A)
      (h : valid_program L I _),
      exist _ (_putr l v k) h =
      putr l (valid_putr_in h) v (exist _ k (valid_putr_k h)).
  Proof.
    intros A L I l v k h.
    apply program_ext. reflexivity.
  Qed.

  Lemma fold_sampler :
    ∀ (A : choiceType) L I
      (op : Op) (k : Arit op → raw_program A)
      (h : valid_program L I _),
      exist _ (_sampler op k) h =
      sampler op (λ x, exist _ (k x) (h x)).
  Proof.
    intros A L I op k h.
    apply program_ext. reflexivity.
  Qed.

  Lemma valid_bind_1 :
    ∀ {A B L I} {v : raw_program A} {k : A → raw_program B},
      valid_program L I (bind_ v k) →
      valid_program L I v.
  Proof.
    intros A B L I v k h.
    induction v in k, h |- *.
    - cbn. auto.
    - cbn. cbn in h. intuition eauto.
    - cbn. cbn in h. intuition eauto.
    - cbn. cbn in h. intuition eauto.
    - cbn. cbn in h. intuition eauto.
  Qed.

  Lemma fold_bind :
    ∀ A B L I
      (v : raw_program A) (k : A → raw_program B)
      (h : valid_program L I (bind_ v k))
      (h' : ∀ x, valid_program L I (k x)),
      exist _ (bind_ v k) h =
      bind (exist _ v (valid_bind_1 h)) (λ x, exist _ (k x) (h' x)).
  Proof.
    intros A B L I v k h h'.
    apply program_ext. cbn. reflexivity.
  Qed.

  Lemma fold_program_link :
    ∀ A L Im Ir (v : raw_program A) (p : raw_package)
      (hv : valid_program L Im v)
      (hp : valid_package L Ir Im p)
      (h : valid_program L Ir (raw_program_link v p)),
        exist _ (raw_program_link v p) h =
        program_link (exist _ v hv) (exist _ p hp).
  Proof.
    intros A L Im Ir v p hv hp h.
    apply program_ext. cbn.
    reflexivity.
  Qed.

  Lemma opackage_transport_K :
    ∀ L I E eI eE p,
      @opackage_transport L I I E E eI eE p = p.
  Proof.
    intros L I E eI eE p.
    rewrite (uip eI erefl).
    rewrite (uip eE erefl).
    unfold opackage_transport. apply opackage_ext. cbn.
    intro.
    reflexivity.
  Qed.

  (** Turn put/get/sample into binds *)

  Lemma putr_bind :
    ∀ L I A l h v k,
      @putr L I A l h v k =
      bind (putr l h v (ret Datatypes.tt)) (λ _, k).
  Proof.
    intros. apply program_ext. reflexivity.
  Qed.

  Lemma getr_bind :
    ∀ L I A l h k,
      @getr L I A l h k =
      bind (getr l h (λ y, ret y)) k.
  Proof.
    intros. apply program_ext. reflexivity.
  Qed.

  Lemma sampler_bind :
    ∀ L I A op k,
      @sampler L I A op k =
      bind (sampler op (λ x, ret x)) k.
  Proof.
    intros L I A op k.
    apply program_ext. reflexivity.
  Qed.

  Lemma link_olink :
    ∀ {I M E} (p₁ : package M E) (p₂ : package I M),
      link p₁ p₂ = (p₁.π1 :|: p₂.π1 ; olink' p₁.π2 p₂.π2).
  Proof.
    intros I M E p₁ p₂.
    apply package_ext.
    - reflexivity.
    - cbn. intro x. reflexivity.
  Qed.

End PackageComposition.
