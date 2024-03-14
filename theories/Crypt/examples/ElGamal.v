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
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  AsymScheme.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Theory.
Import Order.POrderTheory.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

Module Type ElGamalParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter order_gt1 : (1 < #[g])%N.

End ElGamalParam.

Module ElGamal (EGP : ElGamalParam).

Import EGP.

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

  Definition SecurityParameter : choiceType := nat.
  Definition Plain  : finType := gT.
  Definition Cipher : finType := prod (gT:finType) (gT:finType).
  Definition PubKey : finType := gT.
  Definition SecKey : finType := Finite.clone _ 'Z_q.

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Import MyParam.

  #[export] Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  #[export] Instance positive_SecKey : Positive #|SecKey|.
  Proof.
    apply /card_gt0P. exists sec0. auto.
  Qed.

  Definition Plain_pos : Positive #|Plain| := _.
  Definition PubKey_pos : Positive #|PubKey| := _.
  Definition SecKey_pos : Positive #|SecKey| := _.

  #[export] Instance Cipher_pos : Positive #|Cipher|.
  Proof.
    unfold Cipher. rewrite card_prod.
    exact _.
  Qed.

  Definition chPlain  : choice_type := 'fin #|gT|.
  Definition chPubKey : choice_type := 'fin #|gT|.
  Definition chCipher : choice_type := 'fin #|Cipher|.
  Definition chSecKey : choice_type := 'fin #|SecKey|.

  Definition counter_loc : Location := ('nat ; 0%N).
  Definition pk_loc : Location := (chPubKey ; 1%N).
  Definition sk_loc : Location := (chSecKey ; 2%N).
  Definition m_loc  : Location := (chPlain ; 3%N).
  Definition c_loc  : Location := (chCipher ; 4%N).

  Definition kg_id : nat := 5.
  Definition enc_id : nat := 6.
  Definition dec_id : nat := 7.
  Definition challenge_id : nat := 8. (*challenge for LR *)
  Definition challenge_id' : nat := 9. (*challenge for real rnd *)
  Definition getpk_id : nat := 42. (* routine to get the public key *)
  Definition query_id : nat := 10.

  Definition i_plain := #|Plain|.
  Definition i_cipher := #|Cipher|.
  Definition i_pk := #|PubKey|.
  Definition i_sk := #|SecKey|.
  Definition i_bool : nat := 2.

  (** Key Generation algorithm *)
  Definition KeyGen {L : {fset Location}} :
    code L [interface] (chPubKey × chSecKey) :=
    {code
      x ← sample uniform i_sk ;;
      let x := otf x in
      ret (fto (g^+x), fto x)
    }.

  (** Encryption algorithm *)
  Definition Enc {L : {fset Location}} (pk : chPubKey) (m : chPlain) :
    code L [interface] chCipher :=
    {code
      y ← sample uniform i_sk ;;
      let y := otf y in
      ret (fto (g^+y, (otf pk)^+y * (otf m)))
    }.

  (** Decryption algorithm *)
  Definition Dec_open {L : {fset Location}} (sk : chSecKey) (c : chCipher) :
    code L [interface] chPlain :=
    {code
      ret (fto ((fst (otf c)) * ((snd (otf c))^-(otf sk))))
    }.

  Notation " 'plain " :=
    chPlain
    (in custom pack_type at level 2).

  Notation " 'cipher " :=
    chCipher
    (in custom pack_type at level 2).

  Notation " 'pubkey " :=
    chPubKey
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
    [interface #val #[query_id] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[query_id] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+(a * b)))
      }
    ].

Definition DH_rnd :
  package DH_loc [interface]
    [interface #val #[query_id] : 'unit → 'pubkey × 'cipher ] :=
    [package
      #def #[query_id] (_ : 'unit) : 'pubkey × 'cipher
      {
        a ← sample uniform i_sk ;;
        let a := otf a in
        b ← sample uniform i_sk ;;
        let b := otf b in
        c ← sample uniform i_sk ;;
        let c := otf c  in
        #put pk_loc := fto (g^+a) ;;
        #put sk_loc := fto a ;;
        ret (fto (g^+a), fto (g^+b, g^+c))
      }
    ].

Definition Aux :
  package (fset [:: counter_loc ; pk_loc ])
    [interface #val #[query_id] : 'unit → 'pubkey × 'cipher]
    [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ]
  :=
  [package
    #def #[getpk_id] (_ : 'unit) : 'pubkey
    {
      pk ← get pk_loc ;;
      ret pk
    } ;

    #def #[challenge_id'] (m : 'plain) : 'cipher
    {
      #import {sig #[query_id] : 'unit → 'pubkey × 'cipher } as query ;;
      count ← get counter_loc ;;
      #put counter_loc := (count + 1)%N ;;
      #assert (count == 0)%N ;;
      '(pk, c) ← query Datatypes.tt ;;
      @ret chCipher (fto ((otf c).1 , (otf m) * ((otf c).2)))
    }
  ].

Lemma ots_real_vs_rnd_equiv_true :
  Aux ∘ DH_real ≈₀ ots_real_vs_rnd true.
Proof.
  (* We go to the relation logic using equality as invariant. *)
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    move => [a1 h1] [a2 h2] [Heqa Heqh]. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq.
    ssprove_sync_eq. move => /eqP e. subst.
    ssprove_sync_eq. intro a.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq.
    ssprove_sync_eq. intro b.
    rewrite !otf_fto. simpl.
    eapply r_ret. intuition eauto.
    f_equal. f_equal.
    rewrite group_prodC. f_equal.
    apply expgM.
Qed.

Lemma bijective_expgn :
  bijective (λ (a : 'Z_q), g ^+ a).
Proof.
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
    rewrite -e.
    (* case_eq (q == 1)%N.
    1:{
      fold q in *. set (q' := q) in *. clearbody q'.
      move /eqP => ?. subst. rewrite modn1.
      clear h n e hn.
      destruct a as [a h]. unfold Zp_trunc in *. simpl in *.
      (* So in the case where q = 1, we have 'Z_1 = {0, 1} but a mod 1 = 0. *)
    } *)
    rewrite modn_small.
    2:{
      fold q. eapply leq_trans. 1: eapply ltn_ord.
      rewrite Zp_cast.
      2: apply order_gt1.
      auto.
    }
    apply natr_Zp.
  - simpl. intro x.
    match goal with
    | |- context [ @cyclePmin _ _ _ ?hh ] =>
      set (h := hh)
    end.
    clearbody h. simpl in h.
    destruct cyclePmin as [n hn e]. simpl. subst.
    rewrite modn_small. 2: auto.
    f_equal. rewrite val_Zp_nat. 2: apply order_gt1.
    apply modn_small. auto.
Qed.

#[local] Definition f m : 'Z_q * 'Z_q → gT * gT :=
  λ '(a,b), (g^+a, (otf m) * g^+b).

Lemma bijective_f : ∀ m, bijective (f m).
Proof.
  intro m.
  pose proof bijective_expgn as bij.
  destruct bij as [d hed hde].
  eexists (λ '(x,y), (d x, d ((otf m)^-1 * y))).
  - intros [? ?]. simpl. rewrite hed. f_equal.
    rewrite mulgA. rewrite mulVg. rewrite mul1g.
    apply hed.
  - intros [x y]. simpl. rewrite hde. f_equal.
    rewrite hde. rewrite mulgA. rewrite mulgV. rewrite mul1g.
    reflexivity.
Qed.

#[local] Definition f' (m : chPlain) :
  Arit (uniform (i_sk * i_sk)) → Arit (uniform i_cipher) :=
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
    rewrite otf_fto. rewrite gf.
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
  all: ssprove_code_simpl.
  (* We are now in the realm of program logic *)
  - eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
    cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  - ssprove_sync_eq. intro count.
    ssprove_sync_eq.
    destruct count.
    2:{
      cbn. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    }
    simpl.
    ssprove_sync_eq. intro a.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq.
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
    rewrite !otf_fto. simpl.
    reflexivity.
Qed.

Theorem ElGamal_OT :
  ∀ LA A,
    ValidPackage LA [interface
      #val #[getpk_id] : 'unit → 'pubkey ;
      #val #[challenge_id'] : 'plain → 'cipher
    ] A_export A →
    fdisjoint LA (ots_real_vs_rnd true).(locs) →
    fdisjoint LA (ots_real_vs_rnd false).(locs) →
    Advantage ots_real_vs_rnd A <= AdvantageE DH_rnd DH_real (A ∘ Aux).
Proof.
  intros LA A vA hd₀ hd₁.
  simpl in hd₀, hd₁. clear hd₁. rename hd₀ into hd.
  rewrite Advantage_E.
  ssprove triangle (ots_real_vs_rnd false) [::
    Aux ∘ DH_rnd ;
    Aux ∘ DH_real
  ] (ots_real_vs_rnd true) A
  as ineq.
  eapply le_trans. 1: exact ineq.
  clear ineq.
  rewrite ots_real_vs_rnd_equiv_true. 3: auto.
  2:{
    rewrite fdisjointUr. apply/andP. split.
    - unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
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
      rewrite fset_cons. apply fsetUS.
      rewrite !fset_cons -fset0E.
      apply fsetUS.
      apply fsub0set.
    - unfold DH_loc. unfold L_locs_counter in hd.
      rewrite fdisjointC.
      eapply fdisjoint_trans. 2:{ rewrite fdisjointC. exact hd. }
      rewrite [X in fsubset _ X]fset_cons.
      apply fsubsetUr.
  }
  rewrite GRing.addr0. rewrite GRing.add0r.
  rewrite -Advantage_link. auto.
Qed.

End ElGamal.

Module EGP_Z3 <: ElGamalParam.

  Definition gT : finGroupType := 'Z_2.
  Definition ζ : {set gT} := [set : gT].
  Definition g :  gT := Zp1.

  Lemma g_gen : ζ = <[g]>.
  Proof.
    unfold ζ, g. apply Zp_cycle.
  Qed.

  Lemma order_gt1 : (1 < #[g])%N.
  Proof.
    unfold g.
    rewrite order_Zp1.
    reflexivity.
  Qed.

End EGP_Z3.

Module ElGamal_Z3 := ElGamal EGP_Z3.
