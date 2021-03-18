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
  pkg_core_definition chUniverse pkg_composition pkg_rhl Package Prelude
  pkg_notation AsymScheme.
Set Warnings "-custom-entry-overriden".
From Crypt Require Import package_instance.
Set Warnings "custom-entry-overriden".

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

Import PackageNotation.

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

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.

  Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  Instance positive_SecKey : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sec0. auto.
  Qed.

  Definition Plain_pos : Positive #|Plain| := _.
  Definition PubKey_pos : Positive #|PubKey| := _.
  Definition SecKey_pos : Positive #|SecKey| := _.

  Instance Cipher_pos : Positive #|Cipher|.
  Proof.
    unfold Cipher. rewrite card_prod.
    exact _.
  Qed.

  Definition choicePlain  : chUniverse := 'fin #|gT|.
  Definition choicePubKey : chUniverse := 'fin #|gT|.
  (* Sadly it's not a 'fin so I have to change it *)
  (* Definition choiceCipher : chUniverse := chProd ('fin #|gT|) ('fin #|gT|). *)
  Definition choiceCipher : chUniverse := 'fin #|Cipher|.
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
  Definition sk2ch : SecKey → choiceSecKey := fto.

  Definition ch2sk : 'fin #|SecKey| → SecKey := otf.

  (* *)
  Definition c2ch  : Cipher → choiceCipher := fto.

  Definition ch2c : choiceCipher → Cipher := otf.

  Definition i_plain := #|Plain|.
  Definition i_cipher := #|Cipher|.
  Definition i_pk := #|PubKey|.
  Definition i_sk := #|SecKey|.
  Definition i_bool := 2.

  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    code L [interface] (choicePubKey × choiceSecKey) :=
    {code
      x ← sample U i_sk ;;
      let x := ch2sk x in
      ret (pk2ch (g^+x), sk2ch x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : choicePubKey) (m : choicePlain) :
    code L [interface] choiceCipher :=
    {code
      y ← sample U i_sk ;;
      let y := ch2sk y in
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

Import MyParam MyAlg ElGamal_Scheme.

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
        let a := ch2sk a in
        b ← sample U i_sk ;;
        let b := ch2sk b in
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
        let a := ch2sk a in
        b ← sample U i_sk ;;
        let b := ch2sk b in
        c ← sample U i_sk ;;
        let c := ch2sk c  in
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
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_link_commute. simpl.
  simplify_linking.
  (* We are now in the realm of program logic *)
  ssprove_same_head_r. intro count.
  ssprove_same_head_r. intros _.
  destruct count.
  2:{ simpl. eapply r_ret. intuition eauto. }
  simpl. ssprove_same_head_r. intro a.
  ssprove_swap_lhs 0%N.
  ssprove_same_head_r. intros _.
  ssprove_swap_lhs 0%N.
  ssprove_same_head_r. intros _.
  ssprove_same_head_r. intro b.
  unfold ch2pk, pk2ch.
  rewrite ch2gT_gT2ch.
  unfold c2ch, ch2c. rewrite !otf_fto.
  eapply r_ret. intuition eauto.
  f_equal. f_equal. f_equal.
  rewrite group_prodC. f_equal. simpl.
  rewrite -expgnE. rewrite -expgnE.
  rewrite -expgM. reflexivity.
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

#[local] Definition f m : 'Z_q * 'Z_q -> gT * gT :=
  λ '(a,b), (g^+a, (ch2m m) * g^+b).

Lemma bijective_f : ∀ m, bijective (f m).
Proof.
  intro m.
  pose proof bijective_expgn as bij.
  destruct bij as [d hed hde].
  eexists (λ '(x,y), (d x, d ((ch2m m)^-1 * y))).
  - intros [? ?]. simpl. rewrite hed. f_equal.
    rewrite mulgA. rewrite mulVg. rewrite mul1g.
    apply hed.
  - intros [x y]. simpl. rewrite hde. f_equal.
    rewrite hde. rewrite mulgA. rewrite mulgV. rewrite mul1g.
    reflexivity.
Qed.

#[local] Definition f' (m : choicePlain) : Arit (U (i_prod i_sk i_sk)) → Arit (U i_cipher) :=
  λ x,
    let '(a, b) := ch2prod x in
    fto (f m (otf a, otf b)).

Lemma bijective_f' : ∀ m, bijective (f' m).
Proof.
  intro m.
  pose proof (bijective_f m) as bij. destruct bij as [g gf fg].
  unfold f'.
  exists (λ x, let '(a,b) := g (otf x) in prod2ch (fto a, fto b)).
  - cbn - [f]. intros x. rewrite -[RHS]prod2ch_ch2prod.
    set (y := ch2prod x). clearbody y. clear x.
    simpl in y. destruct y as [a b].
    rewrite otf_fto. rewrite gf. f_equal.
    rewrite !fto_otf. reflexivity.
  - cbn - [f]. intro x.
    replace x with (fto (f m (g (otf x)))) at 2.
    2:{ rewrite fg. rewrite fto_otf. reflexivity. }
    set (y := g (otf x)). change (g (otf x)) with y. clearbody y. clear x.
    destruct y as [a b]. rewrite ch2prod_prod2ch. rewrite !otf_fto.
    reflexivity.
Qed.

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
  simpl.
  eapply rsymmetry.
  eapply @r_uniform_bij with (f := f' m). 1: apply bijective_f'.
  simpl. intros x.
  unfold f'. set (z := ch2prod x). clearbody z. clear x.
  destruct z as [x y]. simpl.
  eapply r_ret. intros s ? e. subst.
  intuition auto.
  unfold c2ch, ch2c, ch2m. rewrite !otf_fto. simpl.
  reflexivity.
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
