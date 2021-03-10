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

  Definition U (i : Index) : Op :=
    existT _ (inl (inl i)) (inl (Uni_W i)).

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
    code L [interface] (choicePubKey × choiceSecKey) :=
    {code
      x ← sample U i_sk ;;
      ret (pk2ch (g^+x), sk2ch x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : choicePubKey) (m : choicePlain) :
    code L [interface] choiceCipher :=
    {code
      y ← sample U i_sk ;;
      ret (c2ch (g^+y, (ch2pk pk)^+y * (ch2m m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : choiceSecKey) (c : choiceCipher) :
    code L [interface] choicePlain :=
    {code
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

Set Warnings "-custom-entry-overriden".
Import MyParam MyAlg asym_rules MyPackage ElGamal_Scheme PackageNotation.
Set Warnings "custom-entry-overriden".

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

Lemma ots_real_vs_rnd_equiv_true :
  Aux ∘ DH_real ≈₀ ots_real_vs_rnd true.
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
  (* First we need to squeeze the codes out of the packages *)
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
  setoid_rewrite code_link_if.
  simpl.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  destruct chUniverse_eqP as [e|]. 2: contradiction.
  assert (e = erefl) by apply uip. subst e.
  simpl.
  (* We are now in the realm of program logic *)
  ssprove_same_head_r. intro count.
  ssprove_same_head_r. intros _.
  destruct count.
  2:{
    simpl. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  }
  simpl. ssprove_same_head_r. intro a.
  ssprove_swap_lhs 0%N.
  ssprove_same_head_r. intros _.
  ssprove_swap_lhs 0%N.
  ssprove_same_head_r. intros _.
  ssprove_same_head_r. intro b.
  unfold ch2pk, pk2ch.
  rewrite !ch2gT_gT2ch.
  rewrite expgM group_prodC.
  eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
  cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
Qed.

(** Technical steps

  Ideally, this would go somewhere else to live in the form of rules.
  This burden should not be on the user.

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

Lemma fin_family_inhabited :
  ∀ (i : Index), fin_family i.
Proof.
  intros i. induction i.
  - cbn. exact g.
  - cbn. split. all: exact g.
  - cbn. exact g.
  - cbn. exact 0.
  - cbn. exact false.
  - split. all: auto.
Qed.

Section Mkdistrd_nonsense.

  Context {T : choiceType}.
  Context (mu0 : T -> R) (Hmu : isdistr mu0).

  Let mu := mkdistr Hmu.

  Lemma mkdistrd_nonsense :
    mkdistrd mu0 = mu.
  Proof.
    apply distr_ext. move=> t /=. rewrite /mkdistrd.
    destruct (@idP (boolp.asbool (@isdistr R T mu0))).
    - cbn. reflexivity.
    - rewrite boolp.asboolE in n. contradiction.
  Qed.

End Mkdistrd_nonsense.

Section Uniform_prod.

  Let SD_bind
      {A B : choiceType}
      (m : SDistr_carrier A)
      (k : A -> SDistr_carrier B) :=
    SDistr_bind k m.

  Let SD_ret {A : choiceType} (a : A) :=
    SDistr_unit A a.

  Arguments r _ _ : clear implicits.

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
    eapply rewrite_eqDistrR.
    1:{
      apply (@reflexivity_rule _ _ (@Uniform_F (i_prod i j) heap_choiceType)).
    }
    intro s. cbn.
    unshelve erewrite !mkdistrd_nonsense.
    1-3: unshelve eapply is_uniform.
    1: refine (_,_).
    1-4: apply fin_family_inhabited.
    unshelve eassert (as_uniform :
      (mkdistr (mu:=λ f : UParam.fin_family i * UParam.fin_family j, r (prod_finType (UParam.fin_family i) (UParam.fin_family j)) f) is_uniform)
      =
      @uniform_F (prod_finType (fin_family i) (fin_family j)) _
    ).
    3:{ rewrite /uniform_F. reflexivity. }
    1:{ refine (_,_). all: apply fin_family_inhabited. }
    rewrite as_uniform.
    erewrite prod_uniform.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.
    cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xi.
    epose (bind_bind := ord_relmon_law3 SDistr _ _ _ _ _).
    eapply equal_f in bind_bind.  cbn in bind_bind.
    unfold SubDistr.SDistr_obligation_2 in bind_bind.
    erewrite <- bind_bind. clear bind_bind.
    f_equal.
    apply boolp.funext. intro xj.
    epose (bind_ret := ord_relmon_law2 SDistr _ _ _).
    eapply equal_f in bind_ret.
    cbn in bind_ret.
    unfold SubDistr.SDistr_obligation_2 in bind_ret.
    unfold SubDistr.SDistr_obligation_1 in bind_ret.
    erewrite bind_ret. reflexivity.
  Qed.

End Uniform_prod.

Lemma r_uniform_prod :
  ∀ {A : ord_choiceType} i j
    (r : fin_family i → fin_family j → raw_code A),
    (∀ x y, ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ r x y ≈ r x y ⦃ eq ⦄) →
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      '(x,y) ← sample U (i_prod i j) ;; r x y ≈
      x ← sample U i ;; y ← sample U j ;; r x y
    ⦃ eq ⦄.
Proof.
  intros A i j r h.
  change (
    ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄
      '(x,y) ← (z ← sample (U (i_prod i j)) ;; ret z) ;; r x y ≈
      '(x,y) ← (x ← sample U i ;; y ← sample U j ;; ret (x, y)) ;; r x y
    ⦃ eq ⦄
  ).
  rewrite rel_jdgE.
  eapply rbind_rule.
  - rewrite -rel_jdgE. eapply UniformIprod_UniformUniform.
  - intros [? ?] [? ?]. rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros ? ? e. noconf e.
    eapply rpre_weaken_rule.
    1: eapply h.
    simpl. intros ? ? [? ?]. subst. reflexivity.
Qed.

(* TODO Generalise and move with other rules *)
Lemma r_uniform_bij :
  ∀ {A₀ A₁ : ord_choiceType} i j pre post f
    (c₀ : _ → raw_code A₀) (c₁ : _ → raw_code A₁),
    bijective f →
    (∀ x, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ (f x) ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄
      x ← sample U i ;; c₀ x ≈
      x ← sample U j ;; c₁ x
    ⦃ post ⦄.
Proof.
  intros A₀ A₁ i j pre post f c₀ c₁ bijf h.
  rewrite rel_jdgE.
  change (repr (sampler (U ?i) ?k))
  with (bindrFree (@Uniform_F i heap_choiceType) (λ x, repr (k x))).
  eapply bind_rule_pp.
  - eapply Uniform_bij_rule. eauto.
  - intros a₀ a₁. simpl.
    rewrite -rel_jdgE.
    eapply rpre_hypothesis_rule. intros s₀ s₁ [hs e].
    move: e => /eqP e. subst.
    eapply rpre_weaken_rule. 1: eapply h.
    intros h₀ h₁. simpl. intros [? ?]. subst. auto.
Qed.

Lemma bijective_expgn :
  bijective (λ (a : 'Z_q), g ^+ a).
Proof.
  assert (hq : (1 < q)%N).
  { eapply prime_gt1. unfold q. apply prime_order. }
  unshelve eexists (λ x, (proj1_sig (@cyclePmin gT g x _) %% q)%:R).
  - rewrite -g_gen. unfold ζ. apply in_setT.
  - simpl. intros a.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl.
    move: e => /eqP e. rewrite eq_expg_mod_order in e.
    move: e => /eqP e.
    rewrite !modn_small in e. 2: auto.
    2:{
      eapply leq_trans. 1: eapply ltn_ord. fold q.
      unfold Zp_trunc.
      erewrite <- Lt.S_pred. 2:{ eapply Lt.lt_pred. apply /leP. eauto. }
      apply /leP.
      rewrite PeanoNat.Nat.succ_pred_pos.
      2:{ move: hq => /leP hq. auto with arith. }
      auto.
    }
    subst.
    rewrite modn_small. 2: auto.
    apply natr_Zp.
  - simpl. intro x.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl. subst.
    rewrite modn_small. 2: auto.
    f_equal. rewrite val_Zp_nat. 2: auto.
    apply modn_small. auto.
Qed.

(** End of technical steps *)

Lemma ots_real_vs_rnd_equiv_false :
  ots_real_vs_rnd false ≈₀ Aux ∘ DH_rnd.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_link_commute. simpl.
  simplify_linking.
  (* We are now in the realm of program logic *)
  ssprove_same_head_r. intro count.
  ssprove_same_head_r. intros _.
  destruct count.
  2:{
    cbn. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  }
  simpl.
  ssprove_same_head_r. intro a.
  ssprove_swap_rhs 1%N.
  ssprove_swap_rhs 0%N.
  ssprove_same_head_r. intros _.
  ssprove_swap_rhs 1%N.
  ssprove_swap_rhs 0%N.
  ssprove_same_head_r. intros _.
  eapply r_transR.
  1:{ eapply r_uniform_prod. intros x y. eapply rreflexivity_rule. }
  pose (f := (λ '(a,b), (g^+a, (ch2m m) * g^+b)) : 'Z_q * 'Z_q -> gT * gT).
  assert (fbij : bijective f).
  { pose proof bijective_expgn as bij.
    destruct bij as [d hed hde].
    eexists (λ '(x,y), (d x, d ((ch2m m)^-1 * y))).
    - intros [? ?]. simpl. rewrite hed. f_equal.
      rewrite mulgA. rewrite mulVg. rewrite mul1g.
      apply hed.
    - intros [x y]. simpl. rewrite hde. f_equal.
      rewrite hde. rewrite mulgA. rewrite mulgV. rewrite mul1g.
      reflexivity.
  }
  simpl.
  eapply rsymmetry.
  eapply @r_uniform_bij with (f := f). 1: auto.
  simpl. intros [x y].
  rewrite !gT2ch_ch2gT !ch2gT_gT2ch.
  unfold c2ch. simpl.
  eapply r_ret. intros s ? e. subst.
  intuition auto.
Qed.

Theorem ElGamal_OT :
  ∀ LA A,
    ValidPackage LA [interface val #[challenge_id'] : chPlain → 'option chCipher] A_export A →
    fdisjoint LA (ots_real_vs_rnd true).(locs) →
    fdisjoint LA (ots_real_vs_rnd false).(locs) →
    Advantage ots_real_vs_rnd A <= AdvantageE DH_rnd DH_real (A ∘ Aux).
Proof.
  intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  rewrite Advantage_E.
  pose proof (
    Advantage_triangle_chain (ots_real_vs_rnd false) [::
      Aux ∘ DH_rnd ;
      Aux ∘ DH_real
    ] (ots_real_vs_rnd true) A
  ) as ineq.
  advantage_sum simpl in ineq.
  rewrite !GRing.addrA in ineq.
  eapply ler_trans. 1: exact ineq.
  clear ineq.
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
  rewrite GRing.addr0. rewrite GRing.add0r.
  rewrite -Advantage_link. auto.
Qed.
