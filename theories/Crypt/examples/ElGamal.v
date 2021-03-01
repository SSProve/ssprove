(** ElGamal encryption scheme.

  We show that DH security implies the security of ElGamal.

*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition pkg_chUniverse pkg_composition pkg_rhl Package Prelude
  pkg_notation AsymScheme.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.
Import mc_1_10.Num.Theory.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Parameter η : nat.
Parameter gT : finGroupType.
Definition ζ : {set gT} := [set : gT].
Parameter g :  gT.
Parameter g_gen : ζ = <[g]>.
Parameter prime_order : prime #[g].

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

Lemma group_prodC :
  ∀ x y : gT, x * y = y * x.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.


Inductive probEmpty : Type → Type := .

Module MyParam <: AsymmetricSchemeParams.

  Definition SecurityParameter : choiceType := nat_choiceType.
  Definition Plain  : finType := FinGroup.arg_finType gT.
  Definition Cipher : finType :=
    prod_finType (FinGroup.arg_finType gT) (FinGroup.arg_finType gT).
  Definition PubKey : finType := FinGroup.arg_finType gT.
  Definition SecKey : finType := [finType of 'Z_q].

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

  Definition probE : Type → Type := probEmpty.
  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes → choiceType.
  Proof.
    intro. contradiction.
  Defined.

  Definition prob_handler : ∀ T : choiceType, probE T → SDistr T.
  Proof.
    intro. contradiction.
  Defined.

  Definition Hch : ∀ r : rel_choiceTypes, chEmb r.
  Proof.
    intro. contradiction.
  Defined.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.
  Module asym_rules := (ARules MyParam).
  Import asym_rules.
  Include (Package_Make myparamU).

  Module MyPackage := Package_Make myparamU.

  Import MyPackage.
  Import PackageNotation.

  Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  Instance positive_SecKey : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sec0. auto.
  Qed.

  Definition choicePlain  : chUniverse := 'fin #|gT|.
  Definition choicePubKey : chUniverse := 'fin #|gT|.
  Definition choiceCipher : chUniverse := chProd ('fin #|gT|) ('fin #|gT|).
  Definition choiceSecKey : chUniverse := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (choicePubKey ; 1%N).
  Definition sk_loc : Location := (choiceSecKey ; 2%N).
  Definition m_loc  : Location := (choicePlain ; 3%N).
  Definition c_loc  : Location := (choiceCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)

  Definition U (i : Index) :
    {rchT : myparamU.rel_choiceTypes &
            myparamU.probE (myparamU.chEmb rchT)} :=
    (existT (λ rchT : myparamU.rel_choiceTypes, myparamU.probE (chEmb rchT))
            (inl (inl i)) (inl (Uni_W i))).

  Definition gT2ch : gT → 'fin #|gT|.
  Proof.
    move => /= A.
    destruct (@cyclePmin gT g A) as [i Hi].
    - rewrite -g_gen. apply: in_setT.
    - exists i.
      rewrite orderE in Hi.
      rewrite /= -cardsT.
      setoid_rewrite g_gen.
      assumption.
  Defined.

  Definition ch2gT : 'fin #|gT| → gT.
  Proof.
    move => /= [i Hi]. exact: (g^+i).
  Defined.

  Lemma ch2gT_gT2ch (A : gT) : ch2gT (gT2ch A) = A.
  Proof.
    unfold gT2ch.
    destruct (@cyclePmin gT g A) as [i Hi]. subst.
    simpl. reflexivity.
  Qed.

  Lemma gT2ch_ch2gT (chA : 'fin #|gT|) : gT2ch (ch2gT chA) = chA.
  Proof.
    unfold ch2gT, gT2ch.
    destruct chA as [i hi]. simpl in *.
    destruct cyclePmin as [j hj e].
    assert (e' : i = j).
    { move: e => /eqP e. rewrite eq_expg_mod_order in e.
      move: e => /eqP e.
      rewrite !modn_small in e.
      - auto.
      - auto.
      - rewrite orderE. rewrite -g_gen. rewrite cardsT. auto.
    }
    subst j.
    f_equal.
    apply bool_irrelevance.
  Qed.

  Definition pk2ch : PubKey → choicePubKey := gT2ch.
  Definition ch2pk : choicePubKey → PubKey := ch2gT.
  Definition m2ch : Plain → choicePlain := gT2ch.
  Definition ch2m : choicePlain → Plain := ch2gT.

  (* *)
  Definition sk2ch : SecKey → choiceSecKey.
  Proof.
    move => /= [a Ha].
    exists a.
    rewrite card_ord. assumption.
  Defined.

  Definition ch2sk : 'fin #|SecKey| → SecKey.
    move => /= [a Ha].
    exists a.
    rewrite card_ord in Ha. assumption.
  Defined.

  (* *)
  Definition c2ch  : Cipher → choiceCipher.
  Proof.
    move => [g1 g2] /=.
    exact: (gT2ch g1, gT2ch g2).
  Defined.

  Definition ch2c : choiceCipher → Cipher.
  Proof.
    move => [A B].
    exact: (ch2gT A, ch2gT B).
  Defined.

  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    program L [interface] (choicePubKey × choiceSecKey) :=
    {program
      x ← sample U i_sk ;;
      ret (pk2ch (g^+x), sk2ch x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : choicePubKey) (m : choicePlain) :
    program L [interface] choiceCipher :=
    {program
      y ← sample U i_sk ;;
      ret (c2ch (g^+y, (ch2pk pk)^+y * (ch2m m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : choiceSecKey) (c : choiceCipher) :
    program L [interface] choicePlain :=
    {program
      ret (m2ch ((fst (ch2c c)) * ((snd (ch2c c))^-(ch2sk sk))))
    }.

  Notation " 'chSecurityParameter' " :=
    ('nat) (in custom pack_type at level 2).
  Notation " 'chPlain' " :=
    choicePlain
    (in custom pack_type at level 2).
  Notation " 'chCipher' " :=
    choiceCipher
    (in custom pack_type at level 2).
  Notation " 'chPubKey' " :=
    choicePubKey
    (in custom pack_type at level 2).
  Notation " 'chSecKey' " :=
    choiceSecKey
    (in custom pack_type at level 2).

End MyAlg.

Local Open Scope package_scope.

Module ElGamal_Scheme := AsymmetricScheme MyParam MyAlg.

Import MyParam MyAlg asym_rules MyPackage ElGamal_Scheme PackageNotation.

Lemma counter_loc_in :
  counter_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma pk_loc_in :
  pk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Lemma sk_loc_in :
  sk_loc \in (fset [:: counter_loc; pk_loc; sk_loc ]).
Proof.
  auto_in_fset.
Qed.

Definition DH_loc := fset [:: pk_loc ; sk_loc].

Definition DH_real :
  package DH_loc [interface]
    [interface val #[10] : 'unit → chPubKey × chCipher ] :=
    [package
      def #[10] (_ : 'unit) : chPubKey × chCipher
      {
        a ← sample U i_sk ;;
        b ← sample U i_sk ;;
        put pk_loc := pk2ch (g^+a) ;;
        put sk_loc := sk2ch a ;;
        ret (pk2ch (g^+a), c2ch (g^+b, g^+(a * b)))
      }
    ].

Definition DH_rnd :
  package DH_loc [interface]
    [interface val #[10] : 'unit → chPubKey × chCipher ] :=
    [package
      def #[10] (_ : 'unit) : chPubKey × chCipher
      {
        a ← sample U i_sk ;;
        b ← sample U i_sk ;;
        c ← sample U i_sk ;;
        put pk_loc := pk2ch (g^+a) ;;
        put sk_loc := sk2ch a ;;
        ret (pk2ch (g^+a), c2ch (g^+b, g^+c))
      }
    ].

Definition Aux :
  package (fset [:: counter_loc])
    [interface val #[10] : 'unit → chPubKey × chCipher]
    [interface val #[challenge_id'] : chPlain → 'option chCipher] :=
    [package
      def #[challenge_id'] (m : chPlain) : 'option chCipher
      {
        #import {sig #[10] : 'unit → chPubKey × chCipher } as query ;;
        count ← get counter_loc ;;
        put counter_loc := (count + 1)%N ;;
        if (count == 0)%N then
          '(pk, c) ← query Datatypes.tt ;;
          ret (Some (c2ch ((ch2c c).1 , (ch2m m) * ((ch2c c).2))))
        else ret None
      }
    ].

Definition DH_security : Prop :=
  ∀ LA A,
    ValidPackage LA [interface val #[10] : 'unit → chPubKey × chCipher ] A_export A →
    fdisjoint LA DH_loc →
    AdvantageE DH_real DH_rnd A = 0.

Lemma ots_real_vs_rnd_equiv_false :
  ots_real_vs_rnd false ≈₀ Aux ∘ DH_real.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁). 2: reflexivity.
  1:{
    simpl. intros s₀ s₁. split.
    - intro e. rewrite e. auto.
    - intro e. rewrite e. auto.
  }
  (* We now conduct the proof in relational logic. *)
  intros id S T m hin.
  invert_interface_in hin.
  rewrite get_op_default_link.
  (* First we need to squeeze the programs out of the packages *)
  (* Hopefully I will find a way to automate it. *)
  unfold get_op_default.
  destruct lookup_op as [f|] eqn:e.
  2:{
    exfalso.
    simpl in e.
    destruct chUniverse_eqP. 2: eauto.
    destruct chUniverse_eqP. 2: eauto.
    discriminate.
  }
  eapply lookup_op_spec in e. simpl in e.
  rewrite setmE in e. rewrite eq_refl in e.
  noconf e.
  (* Now to the RHS *)
  destruct lookup_op as [f|] eqn:e.
  2:{
    exfalso.
    simpl in e.
    destruct chUniverse_eqP. 2: eauto.
    destruct chUniverse_eqP. 2: eauto.
    discriminate.
  }
  eapply lookup_op_spec in e.
  match type of e with
  | ?x = _ =>
    let x' := eval hnf in x in
    change x with x' in e
  end.
  match type of e with
  | context [ mkdef _ _ ?p ] =>
    set (foo := p) in e
  end.
  cbn in e. unfold mkdef in e. noconf e. subst foo.
  cbn beta.
  (* Now the linking *)
  simpl.
  (* Too bad but linking doesn't automatically commute with match *)
  setoid_rewrite program_link_if.
  simpl.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  simpl.
  (* We are now in the realm of program logic *)
  eapply (rsame_head_cmd (cmd_get _)). intro count.
  eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
  match goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn:e
  end.
  - eapply (rsame_head_cmd (cmd_sample _)). intro a.
    eapply r_transR.
    1:{
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
    eapply r_transR.
    1:{
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
    (* Not clear how to relate the two sampling to me. *)
    (* We might want a ret rule that asks us to show equality
      of the arguments or even just pre -> post?
    *)
    (* The following is to see clearer, might be best not to do it. *)
    setoid_rewrite gT2ch_ch2gT.
    setoid_rewrite ch2gT_gT2ch.
    admit.
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    intros [? ?] [? ?] ee. inversion ee. intuition reflexivity.
Admitted.

Lemma ots_real_vs_rnd_equiv_true :
  Aux ∘ DH_rnd ≈₀ ots_real_vs_rnd true.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind with (λ '(h₀, h₁), h₀ = h₁). 2: reflexivity.
  1:{
    simpl. intros s₀ s₁. split.
    - intro e. rewrite e. auto.
    - intro e. rewrite e. auto.
  }
  (* We now conduct the proof in relational logic. *)
  intros id S T m hin.
  invert_interface_in hin.
  rewrite get_op_default_link.
  (* First we need to squeeze the programs out of the packages *)
  (* Hopefully I will find a way to automate it. *)
  unfold get_op_default.
  destruct lookup_op as [f|] eqn:e.
  2:{
    exfalso.
    simpl in e.
    destruct chUniverse_eqP. 2: eauto.
    destruct chUniverse_eqP. 2: eauto.
    discriminate.
  }
  eapply lookup_op_spec in e. simpl in e.
  rewrite setmE in e. rewrite eq_refl in e.
  noconf e.
  (* Now to the RHS *)
  destruct lookup_op as [f|] eqn:e.
  2:{
    exfalso.
    simpl in e.
    destruct chUniverse_eqP. 2: eauto.
    destruct chUniverse_eqP. 2: eauto.
    discriminate.
  }
  eapply lookup_op_spec in e. simpl in e.
  rewrite setmE in e. rewrite eq_refl in e.
  noconf e.
  (* Now the linking *)
  simpl.
  (* Too bad but linking doesn't automatically commute with match *)
  setoid_rewrite program_link_if.
  simpl.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  simpl.
  (* We are now in the realm of program logic *)
  eapply (rsame_head_cmd (cmd_get _)). intro count.
  eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
  match goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn:e
  end.
  - eapply (rsame_head_cmd (cmd_sample _)). intro a.
    eapply r_transL.
    1:{
      eapply (rsame_head_cmd (cmd_sample _)). intro x.
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply r_transL.
    1:{
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
    eapply r_transL.
    1:{
      eapply (rsame_head_cmd (cmd_sample _)). intro x.
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply r_transL.
    1:{
      eapply (rswap_cmd _ _ _ _ (cmd_put _ _) (cmd_sample (U i_sk)) (λ a₁ z, _)).
      - auto.
      - intros ? ?.
        eapply rpre_weaken_rule. 1: eapply rreflexivity_rule.
        cbn. auto.
      - eapply rsamplerC_cmd.
    }
    simpl.
    eapply (@rsame_head_cmd _ _ (λ z, _) (λ z, _) (cmd_put _ _)). intros _.
    (* Now I guess is where gT × gT vs gT sampling appears? *)
    (* The following is to see clearer, might be best not to do it. *)
    setoid_rewrite gT2ch_ch2gT.
    setoid_rewrite ch2gT_gT2ch.
    admit.
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    intros [? ?] [? ?] ee. inversion ee. intuition reflexivity.
Admitted.

Theorem ElGamal_OT (dh_secure : DH_security) : OT_rnd_cipher.
Proof.
  unfold OT_rnd_cipher. intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  apply Advantage_le_0.
  rewrite Advantage_E.
  pose proof (
    Advantage_triangle_chain (ots_real_vs_rnd false) [::
      Aux ∘ DH_real ;
      Aux ∘ DH_rnd
    ] (ots_real_vs_rnd true) A
  ) as ineq.
  advantage_sum simpl in ineq.
  rewrite !GRing.addrA in ineq.
  eapply ler_trans. 1: exact ineq.
  clear ineq.
  rewrite -Advantage_link. erewrite dh_secure. 2: exact _.
  2:{
    rewrite fdisjointUl. apply/andP. split.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
    - unfold DH_loc. rewrite fset_cons. rewrite -fset0E. rewrite fsetU0.
      rewrite fdisjoint1s.
      apply/negP. intro e.
      rewrite in_fset in e. rewrite in_cons in e. rewrite mem_seq1 in e.
      move: e => /orP [/eqP e | /eqP e].
      all: discriminate.
  }
  rewrite ots_real_vs_rnd_equiv_false. 2: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. rewrite -fset0E. rewrite fsetU0.
      apply fsubsetUl.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite ots_real_vs_rnd_equiv_true. 3: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. rewrite -fset0E. rewrite fsetU0.
      apply fsubsetUl.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite !GRing.addr0. auto.
Qed.

(* TODO Updated definitions of old theorems
  They will have to be moved upstream to use in the above theorems.
*)

Lemma repr_Uniform :
  ∀ (i : Index),
    repr (x ← sample U i ;; ret x) = @Uniform_F i _.
Proof.
  intro i. reflexivity.
Qed.

(* Alternative, we'll see which is better. *)
Lemma repr_cmd_Uniform :
  ∀ (i : Index),
    repr_cmd (cmd_sample (U i)) = @Uniform_F i _.
Proof.
  intro i. reflexivity.
Qed.

(*CA: probably already here we need that repr (sample U i) is Uniform i. *)
Lemma UniformIprod_UniformUniform :
  ∀ (i j : Index),
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      xy ← sample U (i_prod i j) ;; ret xy ≈
      x ← sample U i ;; y ← sample U j ;; ret (x, y)
    ⦃ eq ⦄.
Proof.
  intros i j.
  change (
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      xy ← sample U (i_prod i j) ;; ret xy ≈
      x ← cmd (cmd_sample (U i)) ;; y ← cmd (cmd_sample (U j)) ;; ret (x, y)
    ⦃ eq ⦄
  ).
  rewrite rel_jdgE.
  rewrite repr_Uniform. repeat setoid_rewrite repr_cmd_bind.
  change (repr_cmd (cmd_sample (U ?i))) with (@Uniform_F i heap_choiceType).
  cbn - [semantic_judgement Uniform_F].
Admitted.

Lemma group_OTP :
  ∀ m,
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      c ← sample U i_cipher ;; ret (Some (c2ch c))
      ≈
      b ← sample U i_sk ;;
      c ← sample U i_sk ;;
      ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c)))
    ⦃ eq ⦄.
Proof.
  intros m.
  unshelve apply: rrewrite_eqDistrR.
  - exact (
      bc ← sample U (i_prod i_sk i_sk) ;;
      ret (Some (c2ch ( g^+ (bc.1), (ch2m m) * g ^+ (bc.2))))
    ).
  - apply (
      @rpost_conclusion_rule_cmd _ _ _
        (λ '(s₀,s₁), s₀ = s₁)
        (cmd_sample (U i_cipher))
        (cmd_sample (U (i_prod i_sk i_sk)))
        (λ c, Some (c2ch c))
        (λ bc, Some (c2ch (g ^+ bc.1, ch2m m * g ^+ bc.2)))
    ).
    rewrite rel_jdgE. rewrite !repr_cmd_bind.
    rewrite !repr_cmd_Uniform.
    simpl (repr (ret _)).
    (* For some reason the lemma doesn't apply?? *)
    (* rewrite bindrFree_and_ret. *)
    match goal with
    | |- context [ @bindrFree ?S ?P ?A ?B ?m ?k ] =>
      change (@bindrFree S P A B m k) with (@Uniform_F i_cipher heap_choiceType)
    end.
    match goal with
    | |- context [ @bindrFree ?S ?P ?A ?B ?m ?k ] =>
      change (@bindrFree S P A B m k) with (@Uniform_F (i_prod i_sk i_sk) heap_choiceType)
    end.
    (* Conclude with Uniform_bij_rule? *)
    admit.
  - intro s. unshelve eapply rcoupling_eq.
  1:{ exact (λ '(s₀, s₁), s₀ = s₁). }
  2: reflexivity.
  (*TODO: massage a bit more the RHS and then apply rf_preserves_eq and then UniformIprod_UniformUniform *)
  admit.
Admitted.

Lemma pk_encoding_correct :
  ∀ p,
    ch2pk (pk2ch p ) = p.
Proof.
  move => /= A. rewrite /ch2pk /pk2ch. exact: ch2gT_gT2ch.
Qed.

Lemma ch2c_c2ch : ∀ x, ch2c (c2ch x) = x.
Proof.
  move => [C1 C2]. rewrite /ch2c /c2ch.
  by rewrite !ch2gT_gT2ch.
Qed.

Lemma cipher_encoding_correct :
  ∀ b c m,
    c2ch (g ^+ b, ch2m m * g ^+ c) =
    c2ch ((ch2c (c2ch (g ^+ b, g ^+ c))).1, ch2m m * (ch2c (c2ch (g ^+ b, g ^+ c))).2).
Proof.
  move => b c m. by rewrite !ch2c_c2ch.
Qed.

(* TODO OLD BELOW
  Some parts are still salvageable, the rest has been scraped.
*)

(* Lemma game_hop : forall A Hdisj1 Hdisj2 Hdisj1' Hdisj2',
  @AdvantageE _ (ots_real_vs_rnd false) (ots_real_vs_rnd true) A Hdisj1 Hdisj2 =
  @AdvantageE _ (Aux ∘ DH_real) (Aux ∘ DH_rnd) A Hdisj1' Hdisj2'.
Proof.
  rewrite /AdvantageE => A Hdisj1 Hdisj2 Hdisj1' Hdisj2'.
  have HR : Pr (A ∘ ots_real_vs_rnd false) true = Pr (A ∘ Aux ∘ DH_rnd) true.
  { apply: GRing.subr0_eq. apply: normr0_eq0.
    (* strangely this does not fold *)
    have Hfool : `|Pr (A ∘ ots_real_vs_rnd false) true - Pr (A ∘ Aux ∘ DH_rnd) true| =
    (@AdvantageE [interface val #[challenge_id'] : chPlain → 'option chCipher ]
                 (ots_real_vs_rnd false) (Aux ∘ DH_rnd) A Hdisj1 Hdisj1') by [].
    rewrite Hfool.
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold Aux, Enc, DH_rnd. unfold Aux_opkg.
    unfold ots_real_vs_rnd. unfold L_pk_ots_rnd.
    unfold L_pk_ots_rnd_open.
    package_link_simplify.
    intros id hinterface m.
    invert_interface_in hinterface.
     repeat opackage_transport_simplify.
    package_pdef_simpl.
    unfold pdefS in m. simpl in m.
    suffices: ⊨ ⦃ fun '(h1,h2) => h1 = h2⦄ repr (RHS0 m) ≈ repr (Aux_DH_rnd m) ⦃ eq ⦄.
    { eapply eq_prog_semj_impl.
      - by rewrite /L_locs_counter.
      - by rewrite /DH_loc -fset_cat /=.
      - rewrite /RHS0 /=.
        f_equal. extensionality counter.
        f_equal. by destruct counter eqn:Hcounter.
      - cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality counter.
        f_equal. destruct counter eqn:Hcounter. 2: reflexivity.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn - [lookup_op raw_par sk2ch pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal. extensionality b.
        f_equal. extensionality c.
        f_equal. f_equal. f_equal. f_equal.
        exact: (cipher_encoding_correct (b%N) (c%N) m).
    }
    - rewrite /RHS0 /Aux_DH_rnd.
      apply: rsame_head => counter.
      destruct counter eqn:Hcounter.
      -- apply: rsame_head => tt.
         unshelve apply: rrewrite_eqDistrR.
         { eapply (
             (a ← (a ← sample U i_sk ;; ret a) ;;
              c ← (c ← sample U i_cipher ;; ret c) ;;
              (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
              (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
              ret (Some (c2ch c))) ). }
         { apply: rsame_head => a.
           apply: rrewrite_eqDistrR. { apply: rsame_head => tt1. apply: rswap_ruleR.
                                       + move => bs bs' H. assumption.
                                       + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                                                        apply: rreflexivity_rule.
                                       + by apply (rsamplerC (U i_cipher)). }
         move => s. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
         apply: rswap_ruleR. { move => bs bs' H. assumption. }
           - move => tt1 aa. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                             apply: rreflexivity_rule.
           - apply (rsamplerC (U i_cipher)). }
         move => s. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
         apply: rsame_head => a.
         apply: rrewrite_eqDistrL.
         --- exact: rreflexivity_rule.
         --- move => s0. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
             { unshelve apply: rrewrite_eqDistrL.
               { eapply (
                   (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
                   (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
                   (b ← (b ← sample U i_sk ;; ret b) ;;
                    c ← (c ← sample U i_sk ;; ret c) ;;
                    ret (Some (c2ch (g ^+ b, ch2m m * g ^+ c))) )). }
               -- unshelve apply: rrewrite_eqDistrL.
                  { eapply (
                        (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt) ;;
                        (put sk_loc := sk2ch a ;; ret Datatypes.tt) ;;
                        (c ← (c ← sample U i_cipher ;; ret c) ;;
                        ret (Some (c2ch c))) ). }
                  --- apply: rrewrite_eqDistrL.
                      { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                        + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                        + apply: rsamplerC (U i_cipher) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                      move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                      apply: rsame_head => tt'. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                        + move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                        + apply: rsamplerC' (U i_cipher)(put sk_loc := sk2ch a ;; ret Datatypes.tt).
                  --- move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                      apply: rsame_head => tt'. apply: rsame_head => tt''. exact: group_OTP.
               -- move => s1. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rrewrite_eqDistrL.
                  { apply: rsame_head => b. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC (U i_sk) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                  move => s2. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rrewrite_eqDistrR.
                  { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC' (U i_sk) (put pk_loc := pk2ch (g ^+ a) ;; ret Datatypes.tt). }
                  move => s3. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rsame_head => tt1.
                  apply: rrewrite_eqDistrL.
                  { apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC' (U i_sk) (put sk_loc := sk2ch a ;; ret Datatypes.tt). }
                  move => s4. apply rcoupling_eq with (ψ := (fun '(s1,s2) => s1 = s2)). 2: by reflexivity.
                  apply: rsame_head => b. apply: rswap_ruleR. { move => bs bs' H. assumption. }
                    ++ move => tt2 c. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. } apply: rreflexivity_rule.
                    ++ apply: rsamplerC (U i_sk) (put sk_loc := sk2ch a ;; ret Datatypes.tt).  }
      -- apply: rreflexivity_rule. }
  rewrite HR. clear HR.
  have HL : Pr (A ∘ ots_real_vs_rnd true) true = Pr (A ∘ Aux ∘ DH_real) true.
  { apply: GRing.subr0_eq. apply: normr0_eq0.
    have Hfool : `|Pr (A ∘ ots_real_vs_rnd true) true - Pr (A ∘ Aux ∘ DH_real) true| =
    (@AdvantageE [interface val #[challenge_id'] : chPlain → 'option chCipher ]
                 (ots_real_vs_rnd true) (Aux ∘ DH_real) A Hdisj1 Hdisj1') by [].
    rewrite Hfool.
    rewrite (prove_relational' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
    1,3: auto.
    1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
    apply: eq_up_to_inv_from_alt2.
    unfold Aux, DH_real, DH_real_opkg. unfold Aux_opkg.
    unfold ots_real_vs_rnd. unfold L_pk_ots_real.
    unfold L_pk_ots_real_open.
    package_link_simplify.
    intros id hinterface m.
    invert_interface_in hinterface.
    repeat opackage_transport_simplify.
    package_pdef_simpl.
    unfold pdefS in m. simpl in m.
    suffices: ⊨ ⦃ fun '(h1,h2) => h1 = h2⦄ repr (LHS0 m) ≈ repr (Aux_DH_real m) ⦃ eq ⦄.
     { eapply eq_prog_semj_impl.
      - by rewrite /L_locs_counter.
      - by rewrite /DH_loc -fset_cat /=.
      - rewrite /LHS0 /=.
        f_equal. extensionality counter.
        f_equal. destruct counter eqn:Hcounter; rewrite //=.
        f_equal. extensionality a.
        f_equal. f_equal. f_equal. extensionality b.
        f_equal. f_equal.
         rewrite pk_encoding_correct.
        f_equal. by rewrite expgM group_prodC.
      - rewrite /Aux_DH_real.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal.
        destruct a. 2: reflexivity.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        destruct lookup_op as [f|] eqn:e.
        2:{
          exfalso.
          simpl in e.
          destruct chUniverse_eqP. 2: eauto.
          destruct chUniverse_eqP. 2: eauto.
          discriminate.
        }
        eapply lookup_op_spec in e. rewrite mapmE in e.
        simpl in e. noconf e.
        cbn - [lookup_op raw_par pk2ch "^+" "*"].
        f_equal. extensionality a.
        f_equal. extensionality b.
        f_equal. f_equal. f_equal.
        f_equal.
        exact: cipher_encoding_correct (b%N) ((a * b)%Nrec) m.
     }
     rewrite /LHS0 /Aux_DH_real.
     apply: rsame_head => counter.
     apply: rsame_head => tt.
     destruct counter eqn:Hcounter.
    ++ apply: rsame_head => a.
       apply: rrewrite_eqDistrL.
       { apply: rswap_ruleR. { move => bs bs' H. assumption. }
       -- move => x y. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                       apply: rreflexivity_rule.
       -- apply (rsamplerC ( U i_sk)). }
       move => s. apply rcoupling_eq with (ψ := fun '(s1, s2) => s1 = s2). 2: by reflexivity.
       apply: rsame_head => tt1.
       apply: rswap_ruleR. { move => bs bs' H. assumption. }
       --- move => b tt2. apply: rsym_pre. { move => h1 h2 H. symmetry. assumption. }
                                       apply: rreflexivity_rule.
       --- apply (rsamplerC' (U i_sk)).
    ++ apply: rreflexivity_rule. }
  rewrite HL. clear HL.
  by rewrite distrC.
Qed. *)

(* Lemma counter_DH_loc : (fset [:: counter_loc] :|: DH_loc) = fset ([:: counter_loc; pk_loc; sk_loc]).
Proof.
  rewrite /DH_loc.
  apply eq_fset => x.
  by rewrite in_fsetU !in_fset  mem_seq1 mem_seq2 mem_seq3.
Qed. *)

(* Lemma counter_pk_sk_disj : fset [:: counter_loc] :&: fset [:: pk_loc; sk_loc] == fset0 .
Proof.
  apply /eqP.
  apply eq_fset => x.
  rewrite in_fsetI in_fset0.
  apply: negPf. apply /andP.  move => [H1 H2].
  rewrite in_fset mem_seq1 in H1. move/eqP: H1. move => H1. subst.
  rewrite in_fset mem_seq2 in H2. move /orP: H2. move => [K | K]; move /eqP : K ; move => K ; inversion K.
Qed. *)