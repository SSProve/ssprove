(** Tactics to help prove things abouve packages

  TODO

**)

From mathcomp Require Import all_ssreflect ssrbool eqtype seq eqtype choice.
From extructures Require Import ord fset fmap.
From Crypt Require Import Prelude pkg_core_definition pkg_composition
  pkg_notation RulesStateProb pkg_rhl pkg_tactics pkg_chUniverse.
From Coq Require Import Utf8 FunctionalExtensionality
  Setoids.Setoid Classes.Morphisms.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Module PackageUserUtil (π : RulesParam).

  Include (PackageRHL π).
  Import PackageNotation.

  Lemma in_pdom_fset :
    ∀ id l,
      id \in pdom (fset l) →
      id \in [seq let '(i,_) := x in i | x <- l].
  Proof.
    intros id l h.
    unfold pdom in h.
    move: h => /imfsetP h. cbn in h.
    destruct h as [[i [S' T']] h e]. subst.
    rewrite in_fset in h.
    eapply map_f in h. exact h.
  Qed.

  Definition vprogram_link {L₁ L₂ I E}
    (f : pointed_vprogram L₁ E) (p : opackage L₂ I E) :
    pointed_vprogram (L₁ :|: L₂) I :=
    let '(S' ; T' ; g) := f in
    (S' ; T' ; λ x, program_link' (g x)p).

  Definition seq_link {L₁ L₂ I E}
    (l : seq (nat * pointed_vprogram L₁ E))
    (p : opackage L₂ I E) :
    seq (nat * pointed_vprogram (L₁ :|: L₂) I) :=
    [seq let '(i, f) := d in (i, vprogram_link f p) | d <- l].

  (* TODO MOVE *)
  Lemma getm_def_map :
    ∀ (T : ordType) (S S' : Type) (s : seq (T * S)) (k : T) (f : S → S'),
      getm_def [seq let '(a,b) := x in (a, f b) | x <- s] k =
      omap f (getm_def s k).
  Proof.
    intros T S S' s k f.
    induction s as [| [a b] s ih].
    - cbn. reflexivity.
    - cbn. destruct (k == a).
      + reflexivity.
      + apply ih.
  Qed.

  Lemma export_interface_link :
    ∀ {L₁ L₂ I E} l p,
      export_interface (mkfmap (@seq_link L₁ L₂ I E l p)) =
      export_interface (mkfmap l).
  Proof.
    intros L₁ L₂ I E l p.
    unfold export_interface. apply (f_equal (λ x, fset (FMap.fmval x))).
    apply eq_fmap. cbn. intro x.
    rewrite !mapmE. rewrite !mkfmapE.
    rewrite getm_def_map.
    destruct getm_def as [[S' [T' f]]|].
    - cbn. reflexivity.
    - cbn. reflexivity.
  Qed.

  Lemma olink_package_def :
    ∀ L₁ L₂ I E
      (l : seq (nat_ordType * pointed_vprogram L₁ E)) (p : opackage L₂ I E),
      olink' (L1 := L₁) (mkpack (mkfmap l)) p =
      opackage_transport erefl (export_interface_link _ _)
        (mkpack (mkfmap (seq_link l p))).
  Proof.
    intros L₁ L₂ I E l p.
    apply opackage_ext. cbn. intro x.
    rewrite mapmE. rewrite mkfmapE.
    rewrite getm_def_map.
    unfold raw_link. rewrite mapmE.
    lazymatch goal with
    | |- context [ trim ?E ?p ] =>
      destruct (trim E p x) as [[So [To f]]|] eqn:e
    end.
    - eapply trim_get_inv in e as h. destruct h as [h hin].
      rewrite mapmE in h. rewrite mkfmapE in h.
      destruct getm_def as [[S' [T' g]]|] eqn:e1. 2: discriminate.
      cbn in h. simpl.
      rewrite e. simpl.
      noconf h. reflexivity.
    - rewrite e. simpl.
      unfold trim in e. rewrite filtermE in e.
      rewrite mapmE in e. rewrite mkfmapE in e.
      destruct getm_def as [[S' [T' g]]|] eqn:e1.
      + cbn in e. destruct (_ \in _) eqn:e2. 1: discriminate.
        unfold export_interface in e2. rewrite in_fset in e2.
        move: e2 => /getmP e2. rewrite mapmE in e2.
        rewrite mkfmapE in e2. rewrite e1 in e2. cbn in e2. contradiction.
      + clear e. cbn. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma program_link'_ret :
    ∀ (A : choiceType) L₁ L₂ I E x p,
      @program_link' A L₁ L₂ I E (ret x) p = ret x.
  Proof.
    intros A L₁ L₂ I E x p.
    apply program_ext. cbn. reflexivity.
  Qed.
  Hint Rewrite program_link'_ret : program_link.

  Lemma opsig_in_unfold :
    ∀ {o : opsig} {E : Interface},
      o \in E →
      (ide o, (chsrc o, chtgt o)) \in E.
  Proof.
    intros [i [S T]] E h. cbn. auto.
  Defined.

  Open Scope pack.

  Lemma program_link'_opr :
    ∀ (A : choiceType) L₁ L₂ I E o h x k p,
      @program_link' A L₁ L₂ I E (opr o h x k) p =
      (y ← injectLocations (fsubsetUr _ _) (olookup p (opsig_in_unfold h) x) ;;
      program_link' (k y) p).
  Proof.
    intros A L₁ L₂ I E o h x k p.
    apply program_ext. cbn.
    eapply lookup_op_valid in h as h'.
    2:{ eapply p.π2. }
    destruct h' as [f [e h']].
    rewrite e.
    erewrite olookup_fst.
    2:{ eapply lookup_op_spec. eauto. }
    reflexivity.
  Qed.
  Hint Rewrite program_link'_opr : program_link.

  Lemma program_link'_getr :
    ∀ (A : choiceType) L₁ L₂ I E l h k p,
      @program_link' A L₁ L₂ I E (getr l h k) p =
      getr l (injectSubset (fsubsetUl _ _) h) (λ x, program_link' (k x) p).
  Proof.
    intros A L₁ L₂ I E l h k p.
    apply program_ext. cbn. reflexivity.
  Qed.
  Hint Rewrite program_link'_getr : program_link.

  Lemma program_link'_putr :
    ∀ (A : choiceType) L₁ L₂ I E l h v k p,
      @program_link' A L₁ L₂ I E (putr l h v k) p =
      putr l (injectSubset (fsubsetUl _ _) h) v (program_link' k p).
  Proof.
    intros A L₁ L₂ I E l h v k p.
    apply program_ext. cbn. reflexivity.
  Qed.
  Hint Rewrite program_link'_putr : program_link.

  Lemma program_link'_sampler :
    ∀ (A : choiceType) L₁ L₂ I E op k p,
      @program_link' A L₁ L₂ I E (sampler op k) p =
      sampler op (λ x, program_link' (k x) p).
  Proof.
    intros A L₁ L₂ I E op k p.
    apply program_ext. cbn. reflexivity.
  Qed.
  Hint Rewrite program_link'_sampler : program_link.

  (* As programs might match on options we account for it. *)
  (* Only in the non-dependent case for now *)
  (* Lemma apply_match_option :
    ∀ A (o : option A) (P : option A → Type) B (f : P o → B) vS vN,
      f match o as o' return P o' with Some x => vS x | None => vN end =
      match o with Some x => f (vS x) | None => f vN end. *)
  Lemma apply_match_option :
    ∀ A (o : option A) (P : Type) B (f : P → B) vS vN,
      f match o as o' return P with Some x => vS x | None => vN end =
      match o with Some x => f (vS x) | None => f vN end.
  Proof.
    intros A o P B f vS vN.
    destruct o. all: reflexivity.
  Qed.

  Lemma program_link_match_option :
    ∀ (A : choiceType) L₁ L₂ I E p B (o : option B) vS vN,
      @program_link' A L₁ L₂ I E
        match o with Some x => vS x | None => vN end p =
      match o with
      | Some x => program_link' (vS x) p
      | None => program_link' vN p
      end.
  Proof.
    intros A L₁ L₂ I E p B o vS vN.
    eapply apply_match_option with (f := λ x, program_link' x p).
  Qed.
  Hint Rewrite program_link_match_option : program_link.

  (* Similar but with equality involved *)
  Lemma apply_eqmatch_option :
    ∀ A (o : option A) (P : Type) B (f : P → B) vS vN,
      f (match o as o' return o' = o → P with Some x => vS x | None => vN end erefl) =
      match o as o' return o' = o → B with
      | Some x => λ e, f (vS x e)
      | None => λ e, f (vN e)
      end erefl.
  Proof.
    intros A o P B f vS vN.
    destruct o. all: reflexivity.
  Qed.

  Lemma program_link_eqmatch_option :
    ∀ (A : choiceType) L₁ L₂ I E p B (o : option B) vS vN,
      @program_link' A L₁ L₂ I E
        (match o as o' return o' = o → _ with
        | Some x => vS x
        | None => vN end erefl) p =
      match o as o' return o' = o → _ with
      | Some x => λ e, program_link' (vS x e) p
      | None => λ e, program_link' (vN e) p
      end erefl.
  Proof.
    intros A L₁ L₂ I E p B o vS vN.
    eapply apply_eqmatch_option with (f := λ x, program_link' x p).
  Qed.
  Hint Rewrite program_link_eqmatch_option : program_link.

  Ltac simpl_seq_link :=
    unfold seq_link ;
    repeat change (map ?f (?x :: ?l)) with (f x :: map f l) ;
    repeat change (@map _ ?B ?f [::]) with (@nil B).

  Ltac package_link_simplify :=
    rewrite !link_olink ;
    repeat change ((_ ; ?v).π2) with v ;
    (* Matching of the lhs is not robust here so we do it ourselves. *)
    (* rewrite olink_package_def *)
    repeat match goal with
    | |- context [ olink' (mkpack (mkfmap ?l)) ?p ] =>
      rewrite (olink_package_def _ _ _ _ l p)
    end ;
    simpl_seq_link.

  (* Actually more general than interfaces here. *)
  Ltac _invert_interface_in h :=
    tryif (rewrite mem_seq1 in h)
    then (move: h => /eqP h ; subst)
    else (
      rewrite in_cons in h ;
      let e := fresh "e" in
      let h' := fresh "h'" in
      move: h => /orP [/eqP e | h'] ; [
        subst
      | _invert_interface_in h'
      ]
    ).

  Ltac invert_interface_in h :=
    let h' := fresh h in
    apply in_pdom_fset in h as h' ;
    cbn in h' ;
    _invert_interface_in h'.

  Ltac opackage_transport_simplify :=
    match goal with
    | |- context [ opackage_transport _ ?e _ ] =>
      rewrite (uip e erefl) ;
      change (opackage_transport erefl erefl ?x) with x
    end.

  Ltac package_pdef_simpl :=
    repeat match goal with
    | |- context [ pdef (mkpack (mkfmap ?l)) ?h ] =>
      rewrite (pdef_unfold _ _ _ l h)
    end ;
    unfold ldef, ldefS, ldefT ;
    unfold safe_getm_def ; simpl ;
    rewrite !cast_vfun_K.

  Ltac program_link_simpl :=
    autorewrite with program_link ;
    repeat rewrite_strat (repeat (outermost (hints program_link))).

  Ltac eq_up_to_inv_simplify :=
    apply eq_up_to_inv_from_alt2 ;
    package_link_simplify ;
    let id := fresh "id" in
    let h := fresh "h" in
    let x := fresh "x"  in
    intros id h x ;
    invert_interface_in h ;
    repeat opackage_transport_simplify ;
    package_pdef_simpl ;
    program_link_simpl.

End PackageUserUtil.