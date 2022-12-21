(** PRF Example

  Inspired by "State Separation for Code-Based Game-Playing Proofs"
  by Brzuska et al.

  Appendix A.

  "Given a pseudorandom function (PRF) we construct a symmetric encryption
  scheme that is indistinguishable under chosen plaintext attacks (IND-CPA)."

*)
From JasminSSProve Require Import jasmin_translate.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq word word.ssrZ.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.


From Jasmin Require Import word.

Section PRF_example.

  Context (n : wsize).

  Notation key := 'word n.
  Notation pt := 'word n.
  Notation ct := 'word n.

  Notation " 'word " := ('word n) (in custom pack_type at level 2).
  Notation " 'key " := ('word n) (in custom pack_type at level 2).

  Context (f : key -> pt -> ct).

  Notation N := ((expn 2 n).-1.+1).

  #[export] Instance : Positive N.
  Proof. red; by rewrite prednK_modulus expn_gt0. Qed.

  #[export] Instance word_pos (i : wsize.wsize) : Positive i.
  Proof. by case i. Qed.

  Notation "m ⊕ k" := (wxor m k) (at level 70).

  #[local] Open Scope package_scope.

  Definition key_location : Location := ('option key ; 0).
  Definition plain_location : Location := ( pt ; 1).
  Definition cipher_location : Location := ( ct ; 2).
  Definition i0 : nat := 3.
  Definition i1 : nat := 4.
  Definition i2 : nat := 5.
  Definition salt_location : Location := ('nat ; 6).
  Definition table_location : Location :=
    (chMap 'nat ('word n) ; 7).

  Definition rel_loc : {fset Location} :=
    fset [:: key_location ; table_location ].

  Definition enc (m : pt) (k : key) :
    code fset0 [interface] ('word n) :=
      {code
        r ← sample uniform N ;;
        let pad := f (word_of_ord r) k in
        let c := m ⊕ pad in
        ret c
      }.

  Definition kgen : code (fset [:: key_location]) [interface] 'word n :=
      {code
       k ← get key_location ;;
       match k with
       | None =>
           k_val ← sample uniform N ;;
           #put key_location := Some (word_of_ord k_val) ;;
           ret (word_of_ord k_val) 
       | Some k_val =>
         ret k_val
       end
      }.

  Definition dec (c : 'word n) (k : 'word n) :
    code fset0 [interface] ('word n) :=
    enc k c.

  Definition EVAL_location_tt := (fset [:: key_location]).
  Definition EVAL_location_ff := (fset [:: table_location]).

  Definition EVAL_pkg_tt :
    package EVAL_location_tt [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package
      #def #[i0] (r : 'word) : 'key
      {
        k_val ← kgen ;;
        ret (f r k_val)
      }
    ].

  Definition EVAL_pkg_ff :
    package EVAL_location_ff [interface]
      [interface #val #[i0] : 'word → 'key ] :=
    [package
      #def #[i0] (r : 'word) : 'key
      {
        T ← get table_location ;;
        match getm T (ord_of_word r) with
        | None =>
            T_key ← sample uniform N ;;
            #put table_location := (setm T (ord_of_word r) (word_of_ord T_key)) ;;
            ret (word_of_ord T_key)
        | Some T_key => ret T_key
        end
      }
    ].

  Definition EVAL : loc_GamePair [interface #val #[i0] : 'word → 'key ] :=
    λ b, if b then {locpackage EVAL_pkg_tt } else {locpackage EVAL_pkg_ff }.

  Definition MOD_CPA_location : {fset Location} := fset0.

  Definition MOD_CPA_tt_pkg :
    package MOD_CPA_location 
      [interface #val #[i0] : 'word → 'key ]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
      #def #[i1] (m : 'word) : 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform N ;;
        pad ← eval (word_of_ord r) ;;
        let c := m ⊕ pad in
        ret c
      }
    ].

  Definition MOD_CPA_ff_pkg :
    package MOD_CPA_location 
      [interface #val #[i0] : 'word → 'key]
      [interface #val #[i1] : 'word → 'word]:=
    [package
      #def #[i1] (m : 'word) : 'word
      {
        #import {sig #[i0] : 'word → 'key } as eval ;;
        r ← sample uniform N ;;
        m' ← sample uniform N ;;
        pad ← eval (word_of_ord r) ;;
        let c := (word_of_ord m' ⊕ pad) in
        ret c
      }
    ].

  Definition IND_CPA_location : {fset Location} := fset [:: key_location].

  Program Definition IND_CPA_pkg_tt :
    package IND_CPA_location
      [interface]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
      #def #[i1] (m : 'word) : 'word
      {
        k_val ← kgen ;;
        enc m k_val
      }
   ].
  (* why is this not inferred? *)
  Next Obligation.
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity. 
    intros. repeat constructor.
    1: auto_in_fset. destruct v.
    1: intros; repeat constructor.
    1: intros; repeat constructor.
    auto_in_fset.
  Defined.

  Program Definition IND_CPA_pkg_ff :
    package IND_CPA_location
      [interface]
      [interface #val #[i1] : 'word → 'word ] :=
    [package
      #def #[i1] (m : 'word) : 'word
      {
        k_val ← kgen ;;
        m' ← sample uniform N ;;
        enc (word_of_ord m') k_val
      }
    ].
  (* TODO: infer this *)
  Next Obligation.
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity. 
    intros. repeat constructor.
    1: auto_in_fset. destruct v.
    1: intros; repeat constructor.
    1: intros; repeat constructor.
    auto_in_fset.
  Defined.

  Program Definition IND_CPA :
    loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_tt } else {locpackage IND_CPA_pkg_ff }.

  Local Open Scope ring_scope.

  Definition prf_epsilon A := Advantage EVAL A.

  Definition statistical_gap :=
    AdvantageE (MOD_CPA_ff_pkg ∘ EVAL false) (MOD_CPA_tt_pkg ∘ EVAL false).

  Lemma IND_CPA_equiv_false :
    IND_CPA false ≈₀ MOD_CPA_ff_pkg ∘ (EVAL true).
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq. cbn -[expn]. intros [k|].
    - cbn -[expn]. ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule.
      1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn -[expn].
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  Lemma IND_CPA_equiv_true :
    MOD_CPA_tt_pkg ∘ (EVAL true) ≈₀ IND_CPA true.
  Proof.
    (* We go to the relation logic using equality as invariant. *)
    eapply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    simplify_linking.
    (* We now conduct the proof in relational logic. *)
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq. cbn -[expn]. intros [k|].
    - cbn -[expn]. eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
    - cbn -[expn].
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      eapply rpost_weaken_rule. 1: eapply rreflexivity_rule.
      cbn. intros [? ?] [? ?] e. inversion e. intuition auto.
  Qed.

  (** Security of PRF

    The bound is given by using the triangle inequality several times,
    using the following chain:
    IND_CPA false ≈ MOD_CPA_ff_pkg ∘ EVAL true
                  ≈ MOD_CPA_ff_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL false
                  ≈ MOD_CPA_tt_pkg ∘ EVAL true
                  ≈ IND_CPA true

  *)
  Theorem security_based_on_prf :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word ] A_export A →
      fdisjoint LA (IND_CPA false).(locs) →
      fdisjoint LA (IND_CPA true).(locs) →
      Advantage IND_CPA A <=
      prf_epsilon (A ∘ MOD_CPA_ff_pkg) +
      statistical_gap A +
      prf_epsilon (A ∘ MOD_CPA_tt_pkg).
  Proof.
    intros LA A vA hd₀ hd₁. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    ssprove triangle (IND_CPA false) [::
      MOD_CPA_ff_pkg ∘ EVAL true ;
      MOD_CPA_ff_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL false ;
      MOD_CPA_tt_pkg ∘ EVAL true
    ] (IND_CPA true) A
    as ineq.
    eapply le_trans. 1: exact ineq.
    clear ineq.
    erewrite IND_CPA_equiv_false. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    erewrite IND_CPA_equiv_true. all: eauto.
    2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. }
    rewrite GRing.add0r GRing.addr0.
    rewrite !Advantage_link. rewrite Advantage_sym. auto.
  Qed.

End PRF_example.

From JasminSSProve Require Import aes.aes aes_jazz jasmin_utils aes_valid.
From Jasmin Require Import expr sem.

Import JasminNotation JasminCodeNotation.

(* From Jasmin Require Import expr. *)
Require Import String.
Local Open Scope string.

Section JasminPRF.

  Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

  Notation n := U128.
  
  Definition key := 'word n.
  Definition pt := 'word n.
  Definition ct := 'word n.

  Notation " 'word " := ('word n) (in custom pack_type at level 2).
  Notation " 'key " := ('word n) (in custom pack_type at level 2).
  Notation N := ((expn 2 n).-1.+1).

  (* #[export] Instance : Positive N. *)
  (* Proof. generalize 128; intros; red; by rewrite prednK_modulus expn_gt0. Qed. *)
  (* (* #[export] Instance : Positive ((2 ^ n).-1.+1). *) *)
  (* Proof. exact _. Qed. *)

  (* #[export] Instance word_pos (i : wsize.wsize) : Positive i. *)
  (* Proof. by case i. Qed. *)
  (* Notation N :=  *)
  Notation enc := (enc U128 aes).
  Notation kgen := (kgen U128).
  Notation key_location := (key_location U128).

  Definition ltup2 (l : tchlist) :=
    match l with
    | [::] => (word0, word0)
    | a1 :: l1 => 
        match l with
        | [::] => (word0, word0)
        | a2 :: l2 => (coerce_to_choice_type ('word n) a1.π2, coerce_to_choice_type ('word n) a2.π2)
        end
    end.

  (* Program Definition IND_CPA_pkg_Caes : *)
  (*   package (fset [:: rkeys; state]) *)
  (*     [interface #val #[i2] : 'unit → 'word] *)
  (*     [interface #val #[i1] : 'word → 'word] := *)
  (*   [package *)
  (*     #def #[i1] (m : 'word) : 'word *)
  (*     { *)
  (*       k ← get key_location ;; *)
  (*       k_val ← match k with *)
  (*               | None => *)
  (*                   k_val ← sample uniform N ;; *)
  (*                   #put key_location := Some (word_of_ord k_val) ;; *)
  (*                   ret (word_of_ord k_val)  *)
  (*               | Some k_val => *)
  (*                   ret k_val *)
  (*       end ;; *)
  (*       #import {sig #[i2] : 'unit → 'key } as kg ;; *)
  (*       k_val ← kg (chCanonical 'unit) ;; *)
  (*       Caes m k_val *)
  (*     } *)
  (*  ]. *)
  (* Next Obligation. *)
  (*   (* infer this *) *)
  (*   repeat constructor. red. *)
  (*   intros []. *)
  (*   rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl. *)
  (*   eexists. *)
  (*   split. *)
  (*   1: reflexivity.  *)
  (*   intros. repeat constructor. *)
  (*   all: auto_in_fset. *)
  (* Defined. *)
  (* Opaque Caes. *)
    
  Definition Cenc (m : pt) (k : key) :
    code (fset [:: state ; rkeys]) [interface] ('word n). 
  Proof.
    refine
      {code
        r ← sample uniform N ;;
        pad ← Caes (word_of_ord r) k ;; 
        ret (m ⊕ pad)
      }.
    repeat constructor.
    all: auto_in_fset.
    Unshelve. exact _.
  Defined.

  Definition Cenc_locs := [:: state ; rkeys].
  Opaque wrange.
  Opaque expn.

  Definition IND_CPA_pkg_Cenc :
    package (fset (key_location :: Cenc_locs))
      [interface]
      [interface #val #[i1] : 'word → 'word].
  Proof.
    refine
      [package
        #def #[i1] (m : 'word) : 'word
        {
          k_val ← kgen ;;
          Cenc m k_val
        }
      ].
    (* infer this *)
    repeat constructor. red.
    intros [].
    rewrite in_fset in_cons. move=>/orP []. 2: easy. move=>/eqP H. noconf H. simpl.
    eexists.
    split.
    1: reflexivity.
    intros. repeat constructor.
    all: auto_in_fset.
    intros. destruct v.
    1: repeat constructor; auto_in_fset.
    1: repeat constructor; auto_in_fset.
  Defined.
  
  Definition IND_CPA_pkg_JENC (id0 : p_id) :
    package (fset (key_location :: (JENC_valid id0).π1))
      [interface]
      [interface #val #[i1] : 'word → 'word ].
  Proof.
    refine
      [package
        #def #[i1] (m : 'word) : 'word
          {
            k_val ← kgen ;;
            r ← sample uniform N ;;
            res ← JENC id0 (word_of_ord r) k_val m ;;
            ret (hdtc128 res)
          }
        ].
    repeat constructor.
    intros [].
    rewrite in_fset in_cons => /orP []; [|easy]; move=> /eqP H; noconf H.
    cbv zeta match.
    eexists.
    split. 
    1: reflexivity.
    intros x.
    constructor.
    1: auto_in_fset.
    intros. destruct v.
    - constructor. intros.
      eapply valid_bind.
      + red. eapply valid_code_cons.
        1: eapply (JENC_valid id0).π2.
      + constructor.
    - constructor.
       intros.
       constructor.
       1: auto_in_fset.
       constructor. intros.
       eapply valid_bind.
       + red. eapply valid_code_cons.
         1: eapply (JENC_valid id0).π2.
       + constructor.
    Unshelve. all: exact _.
  Defined.

  (* Notation KG_pkg := (KG_pkg U128). *)
  Notation IND_CPA_pkg_ff := (IND_CPA_pkg_ff U128 aes).
  Notation MOD_CPA_ff_pkg := (MOD_CPA_ff_pkg U128).
  Notation IND_CPA := (IND_CPA U128 aes).
  Notation EVAL := (EVAL U128 aes).

  (* Lemma fsubsetUl' : forall [T : ordType] (s1 s2 s3 : {fset T}), fsubset s1 s2 -> fsubset s1 (s2 :|: s3). *)
  (* Proof. *)
    
  (*   intros. *)
  (*   eapply fsubsetU. *)
  (*   rewrite -[s1]fsetUid. *)
  (*   eapply fsetSU. *)
  Lemma fsubset_ext2 : ∀ [T : ordType] (s1 s2 : {fset T}), fsubset s1 s2 -> (forall x, x \in s1 -> x \in s2). 
  Proof.
    intros.
    rewrite -fsub1set.
    eapply fsubset_trans. 2: eassumption.
    rewrite fsub1set. assumption.
  Qed.

  Lemma fsubset_cons : ∀ [T : ordType] a (s1 s2 : {fset T}), fsubset s1 s2 -> fsubset s1 (a |: s2). 
  Proof.
    intros.
    apply fsubset_ext.
    intros. rewrite in_fset in_cons.
    apply/orP. right.
    eapply fsubset_ext2.
    1: eassumption.
    assumption.
  Qed.
  
(* fsubsetUl: ∀ [T : ordType] (s1 s2 : {fset T}), fsubset s1 (s1 :|: s2) *)
  Definition IND_CPA_Cenc :
    loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_Cenc } else (IND_CPA true).

  Definition IND_CPA_JENC id0 :
    loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_JENC id0} else {locpackage IND_CPA_pkg_Cenc}.
(* Lemma aes_h k m : *)
(*   (* (forall i, (0 <= i < 11)%nat -> rkeys i = Some (key_i k i)) -> *) *)
(*   ⊢ ⦃ fun '(h0, h1) => heap_ignore (fset Cenc_locs) (h0, h1) ⦄ *)
(*     Caes k m *)
(*     ≈ *)
(*     ret (chCanonical chUnit)  *)
(*     ⦃ fun '(v0, h0) '(_, h1) => heap_ignore (fset Cenc_locs) (h0, h1) /\ v0 = aes k m ⦄. *)
(* Proof. *)
(*   unfold Caes. *)
(*   eapply r_bind with (m₁ := ret _). *)
(*   - eapply aes_keyExpansion_h. *)
(*   - intros a0 []. *)
(*     eapply r_bind with (m₁ := ret _). *)
(*     eapply aes_rounds_h. *)
(*     intros a1 []. *)
(*     eapply r_ret. *)
(*     intros. *)
(*     assumption. *)
(* Qed. *)
(* Print Instances Invariant. *)
  (* Lemma heap_ignore_set_l h1 h2 l v L : l \notin L -> heap_ignore L ((set_heap h1 l v), h2). *)
  (* Proof. *)
  (*   intros H a anin. *)
  (*   unfold heap_igno *)
  (*   eexists. *)
  (*   o *)


  (* Lemma heap_ignore_fset0 h1 h2 : heap_ignore fset0 (h1, h2). *)
  (* Proof. *)
  (*   intros l lnin. *)
(* pdisj *)
  (* Definition heap_ignore_later (id : p_id) (L : {fset Location}) : precond := *)
  (*   λ '(h₀, h₁), *)
  (*     ∀ (ℓ : Location) (s_id : p_id) (v : var), ℓ \notin L \/ (id ≺ s_id /\ ℓ = translate_var s_id v) → get_heap h₀ ℓ = get_heap h₁ ℓ. *)
  (* (* Instance : forall L1 L2, Invariant L1 L2 pdisj. := pdisj. *) *)
            
(* Lemma INV'_heap_ignore_later id : *)
(*   ∀ L L₀ L₁, *)
(*     fsubset L (L₀ :|: L₁) → *)
(*     INV' L₀ L₁ (heap_ignore_later id L). *)
(* Proof. *)
(*   intros L L₀ L₁ hs h₀ h₁. split. *)
(*   - intros hh ℓ n₀ n₁. *)
(*     eapply hh. *)
(*     left. *)
(*     apply /negP. intro h. *)
(*     eapply injectSubset in h. 2: eauto. *)
(*     rewrite in_fsetU in h. move: h => /orP [h | h]. *)
(*     + rewrite h in n₀. discriminate. *)
(*     + rewrite h in n₁. discriminate. *)
(*   - intros h ℓ v n₀ n₁ ℓ' n. *)
(*     destruct (ℓ' != ℓ) eqn:e. *)
(*     + rewrite get_set_heap_neq. 2: auto. *)
(*       rewrite get_set_heap_neq. 2: auto. *)
(*       apply h. *)
(*     + move: e => /eqP e. subst. *)
(*       rewrite !get_set_heap_eq. reflexivity. *)
(*       Unshelve. 1: exact xH. exact (Var sbool "").  *)
(* Qed. *)

(* Lemma Invariant_heap_ignore_later id : *)
(*   ∀ L L₀ L₁, *)
(*     fsubset L (L₀ :|: L₁) → *)
(*     Invariant L₀ L₁ (heap_ignore_later id L). *)
(* Proof. *)
(*   intros L L₀ L₁ h. split. *)
(*   - apply INV'_heap_ignore_later. auto. *)
(*   - intros L' id' v H. apply get_empty_heap.   *)
(* Qed. *)

(* Hint Extern 10 (Invariant _ _ (heap_ignore_later _ _)) => *)
  (* eapply Invariant_heap_ignore_later *)
  (* : (* typeclass_instances *) ssprove_invariant. *)

(* Definition heap_ignore_pred' (P : Location -> Prop) : precond := *)
  (* λ '(h₀, h₁), *)
    (* forall (ℓ : Location), ~ P ℓ -> get_heap h₀ ℓ = get_heap h₁ ℓ. *)

(* Arguments heap_ignore_pred' : simpl never. *)

(* Lemma heap_ignore_pred'_empty : *)
(*   ∀ P, *)
(*     heap_ignore_pred' P (empty_heap, empty_heap). *)
(* Proof. *)
(*   intros P ℓ hℓ. reflexivity. *)
(* Qed. *)

Definition heap_ignore_pred' (P : Location -> Prop) : precond :=
  λ '(h₀, h₁),
    forall (ℓ : Location), P ℓ -> get_heap h₀ ℓ = get_heap h₁ ℓ.

Lemma heap_ignore_pred'_empty :
  ∀ P,
    heap_ignore_pred' P (empty_heap, empty_heap).
Proof.
  intros P ℓ hℓ. reflexivity.
Qed.

Lemma INV''_heap_ignore_pred' (P : Location -> Prop) :
  ∀ P0 P1 : Location -> Prop,
    (forall ℓ : Location, ~ P0 ℓ /\ ~ P1 ℓ -> P ℓ) ->
    INV'' P0 P1 (heap_ignore_pred' P).
Proof.
  intros P0 P1 hP h0 h1. split.
  - intros hh l nin1 nin2.
    eapply hh.
    apply hP.
    eauto.
  - intros h ℓ v nin0 nin1 ℓ' n.
    destruct (ℓ' != ℓ) eqn:e.
    + rewrite get_set_heap_neq. 2: auto.
      rewrite get_set_heap_neq. 2: auto.
      apply h. auto.
    + move: e => /eqP e. subst.
      rewrite !get_set_heap_eq. reflexivity.
Qed.

Lemma Invariant'_heap_ignore_pred' :
  ∀ P0 P1 (P : Location -> Prop),
    (forall ℓ : Location, ~ P0 ℓ /\ ~ P1 ℓ -> P ℓ) ->
    Invariant' P0 P1 (heap_ignore_pred' P).
Proof.
  intros L P h. split.
  - apply INV''_heap_ignore_pred'. auto.
  - apply heap_ignore_pred'_empty.
Qed.

Definition adv_equiv' P0 P1 {L₀ L₁ E} (G₀ G₁ : raw_package)
  `{ValidPackage L₀ Game_import E G₀} `{ValidPackage L₁ Game_import E G₁} ε :=
  ∀ LA A,
    ValidPackage LA E A_export A →
    pdisjoint LA P0 →
    pdisjoint LA P1 →
    AdvantageE G₀ G₁ A = ε A.

Lemma eq_rel_perf_ind'' :
  ∀ P0 P1 {L₀ L₁ E} (p₀ p₁ : raw_package) (inv : precond)
    `{ValidPackage L₀ Game_import E p₀}
    `{ValidPackage L₁ Game_import E p₁},
    Invariant' P0 P1 inv →
    eq_up_to_inv E inv p₀ p₁ →
    adv_equiv' P0 P1 p₀ p₁ (λ _ : raw_package, 0%R).
Proof.
  intros P0 P1 L₀ L₁ E p₀ p₁ inv v₀ v₁ [? ?] he.
  (* adv_equiv. *)
  (* Locate "≈₀". *)
  intros LA A vA hd₀ hd₁.
  eapply eq_upto_inv_perf_ind'. all: eauto.
Qed.

(* TODO: move *)
Lemma JXOR_E pre id0 x y :
  (pdisj pre id0 fset0) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    JXOR id0 x y
    ≈
    ret (chCanonical chUnit) 
    ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) /\ (exists o, (v0 = cons ('word U128 ; o ) nil ) /\ (o = x ⊕ y)) ⦄.
Proof.
  unfold JXOR.
  unfold get_translated_static_fun.
  unfold translate_prog_static.
  unfold translate_funs_static.
  unfold translate_call_body.
  intros disj.

  simpl. simpl_fun.
  repeat setjvars.
  ssprove_code_simpl.
  repeat clear_get.
  repeat eapply r_put_lhs.
  eapply r_ret.
  rewrite !zero_extend_u.
  (* rewrite coerce_to_choice_type_K. *)
  intros.  destruct_pre; split_post.
  1: pdisj_apply disj.
  eexists; split; [reflexivity|]. reflexivity.
Qed.

Lemma IND_CPA_JENC_equiv_false id0 :
    adv_equiv' (fun l => exists s_id v, id0 ⪯ s_id /\ l = translate_var s_id v) (fun l => l = state \/ l = rkeys) (IND_CPA_JENC id0 true) (IND_CPA_JENC id0 false) (λ _ : raw_package, 0%R).
  Proof.
    eapply eq_rel_perf_ind''.
    1: eapply Invariant'_heap_ignore_pred' with
    (* with (L := JENC_locs id0). *)
      (P := fun l => forall s_id v, id0 ⪯ s_id -> l != translate_var s_id v).

     (* (id:=id0) *) (* (L:=fset0) *) (* (L:=(fset (JENC_valid id0 (fset [::])).π1)). *)
(* _ignore with (L := fset Cenc_locs). *)
    - intros. apply/eqP. intros contra.
      destruct H.
      apply H.
      exists s_id, v. split; auto.
      

      (* admit. *)
    (*     eapply fsubsetU. apply/orP; left. simpl. *)
    (*   rewrite [fset (key_location :: _)]fset_cons. *)
    (*   eapply fsubset_cons. *)
    (*   eapply fsubsetxx. *)
    -

      unfold eq_up_to_inv.
      unfold get_op_default.
      unfold lookup_op.
      unfold IND_CPA_JENC.
      unfold IND_CPA_pkg_JENC.

      (* unfold JENC. *)
      (* unfold get_translated_static_fun. *)
      (* unfold translate_prog_static. *)
      (* unfold translate_funs_static. *)
      (* unfold translate_call_body. *)
  Opaque Caes.
  Opaque translate_call.
  (* Opaque wrange. *)
  Opaque wrange.
  Opaque expn.
  Arguments heap_ignore_pred' : simpl never.
  simpl.
  (* simplify_linking. *)
    simplify_eq_rel m.
    simplify_linking.
    rewrite !cast_fun_K.
    ssprove_sync.
    { intros h0 h1 hpre. apply hpre. admit. }
      (* Transparent heap_ignore_later. *)
    (* {  unfold get_pre_cond. intros. eapply H. left. admit. } intros. *)
    (* ssprove_sync.  *)
    destruct a.
    + ssprove_code_simpl.
      simpl.
      ssprove_sync. intros.
      rewrite !zero_extend_u.
      repeat clear_get.
      do 3 eapply r_put_lhs.
      eapply r_bind.
      * 
(* eapply rpre_weak_hypothesis_rule'. *)
        (* intros. *)
        (* destruct_pre. *)
        
        eapply aes_E; split.
        ** intros.
           destruct_pre.
           eexists.
           eexists.
           *** eexists.
               eexists.
               **** eexists.
                    split.
                    ***** instantiate (1 := set_heap H6 (translate_var s_id' v) a0).
                    intros l lnin.
                    rewrite get_set_heap_neq.
                    1: eapply H7. 1: assumption.
                    eapply lnin.
                    admit.
                    ***** reflexivity.
               **** reflexivity.
           *** rewrite set_heap_commut.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: reflexivity.
               (* 1: unfold heap_ignore_pred' in H7. *)
               (* Unset Printing Notations. *)
               1-3: admit.
        ** intros.
           destruct_pre.
          
           eexists.
           eexists.
           *** eexists.
               eexists.
               **** eexists.
                    split.
                    ***** instantiate (1 := H5).
                    intros l2 lnin.
                    rewrite get_set_heap_neq.
                    1: eapply H6. 1: assumption.
                    admit.
                    ***** reflexivity.
               **** reflexivity.
           *** reflexivity.
      * 
        simpl.
        intros.
        
        eapply rpre_weak_hypothesis_rule'; intros.
           destruct_pre. 
           simpl.
           clear_get.
           eapply r_put_lhs with (pre := fun _ => _).
           eapply r_get_remember_lhs. intros.
    eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _).
    1: eapply JXOR_E; split.

        ** intros.
           unfold set_lhs.
           simpl.
           destruct_pre.
           simpl.
           eexists.
           1: do 2 eexists.
           1: do 7 eexists.
           1: instantiate (1:= (set_heap H13 (translate_var s_id' v) a0)).
           1: { intros l hl. rewrite get_set_heap_neq. 1: eapply H14. 1: assumption. apply hl.  admit. }
           1: reflexivity.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: rewrite [set_heap _ _ a0]set_heap_commut.
               1: reflexivity.
               1-4: admit.
               sheap. simpl. rewrite get_set_heap_neq. 1: sheap. 1:  reflexivity.
               admit.
        ** 
          intros.
          easy.
        **
          
          intros.
          eapply rpre_weak_hypothesis_rule'; intros.
          destruct_pre; simpl.
          clear_get.
           eapply r_put_lhs with (pre := fun _ => _).
           (* eapply rpost_weaken_rule. *)
          eapply r_ret.
          rewrite !coerce_to_choice_type_K.
          rewrite !zero_extend_u.
          intros.
          destruct_pre; simpl; split_post.
          1: sheap.
          1: by rewrite wxorC.
          intros l s_id.
          rewrite !get_set_heap_neq.
          (* Unset Printing Notations. *)
          1: eapply H18.
          1: eassumption.
          1-5: apply s_id; reflexivity.
    + admit.
  Admitted.
  
  Lemma IND_CPA_jazz_equiv_false :
    (IND_CPA_Cenc) true ≈₀ (IND_CPA_Cenc) false.
  Proof.
    eapply eq_rel_perf_ind_ignore  with (L := fset Cenc_locs).
    - eapply fsubsetU. apply/orP; left. simpl.
      rewrite [fset (key_location :: _)]fset_cons.
      eapply fsubset_cons.
      eapply fsubsetxx.
    -
    (* We go to the relation logic using equality as invariant. *)
    (* eapply eq_rel_perf_ind_eq. *)
    unfold eq_up_to_inv.
  Opaque Caes.
  (* Opaque wrange. *)
  Opaque wrange.
  Opaque expn.
    simplify_eq_rel m.
    ssprove_sync. intros.
    destruct a.
    + simpl.  
      ssprove_sync. intros x.
       eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _).
      * 1: eapply aes_h.
        intros h1 h2 l a lin h.
        intros l2 lnin.
        unfold Cenc_locs in *.
        admit.
      * intros. eapply r_ret.
        intros. destruct_pre; split_post; auto.
    + simpl.  
      ssprove_sync. intros x.
      ssprove_sync. 
      ssprove_sync.  intros.
       eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _).
      * 1: eapply aes_h.
        intros h1 h2 l a2 lin h.
        intros l2 lnin.
        unfold Cenc_locs in *.
        rewrite get_set_heap_neq.
        1: eapply h. 1: assumption.
        admit.
      * intros. eapply r_ret.
        intros. destruct_pre; split_post; auto.
  Admitted.

  Definition JIND_CPA id0 :
    loc_GamePair [interface #val #[i1] : 'word → 'word ] :=
    λ b,
      if b then {locpackage IND_CPA_pkg_JENC id0 } else (IND_CPA true).
  
  Theorem jasmin_security_based_on_prf id0 :
    ∀ LA A,
      ValidPackage LA
        [interface #val #[i1] : 'word → 'word ] A_export A →
      pdisjoint LA (λ l : Location, ∃ (s_id : p_id) (v : var), id0 ⪯ s_id ∧ l = translate_var s_id v) ->
      pdisjoint LA (λ l : Location, l = state ∨ l = rkeys) ->
      (* fdisjoint LA (JIND_CPA id0 false).(locs) → *)
      (* fdisjoint LA (JIND_CPA id0 true).(locs) → *)
      Advantage (JIND_CPA id0) A = 0%R.
  Proof.
    intros LA A vA hd₀ hd₁. unfold prf_epsilon, statistical_gap.
    rewrite !Advantage_E.
    eapply AdvantageE_le_0.
    ssprove triangle (JIND_CPA id0 false) [::
      IND_CPA_pkg_Cenc : raw_package
    ] (JIND_CPA id0 true) A
      as ineq.
    eapply Order.POrderTheory.le_trans.
    1: exact ineq.
    clear ineq.
    rewrite Advantage_sym.
    erewrite IND_CPA_jazz_equiv_false. all: eauto.
    2-3: admit.
    rewrite Advantage_sym.
    pose proof IND_CPA_JENC_equiv_false id0.
    unfold adv_equiv' in H.
    specialize (H LA A vA hd₀ hd₁).
    rewrite H.
    rewrite GRing.addr0.
    apply Order.POrderTheory.le_refl.
  Admitted.
  (*   reflexivity. *)
  (*   auto. *)

  (*   erewrite IND_CPA_equiv_true. all: eauto. *)
  (*   2:{ simpl. unfold MOD_CPA_location. rewrite fset0U. auto. } *)
  (*   rewrite GRing.add0r GRing.addr0. *)
  (*   rewrite !Advantage_link. rewrite Advantage_sym. auto. *)
  (* Qed. *)
  (*   + eapply rpre_weaken_rule. 1: eapply r_ret.  eapply rreflexivity_rule. *)
  (*   -  intros. *)
  (*      (* cbv zeta match. *) *)
  (*      (* eapply cmd_sample_preserve_pre. *) *)
  (*      (* eapply rsame_head. *) *)
  (*      ssprove_code_simpl. *)
  (*      eapply rpre_weaken_rule. *)
  (*      1: ssprove_sync_eq. *)
  (*      2: { intros. noconf H. easy. } *)
  (*      intros. *)
  (*      eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _). *)
  (*      + eapply rpre_weaken_rule. 1: eapply aes_h. *)
  (*        easy. *)
  (*      + intros. *)
  (*        eapply r_ret. *)
  (*        intros. subst. split. *)
  (*        auto. *)
  (*        rreflexivity_rule. *)
         
  (*      eapply r_bind. *)
  (*      rewrite !zero_extend_u. *)
  (*      eapply r_put_lhs with (pre := fun '(_, _) => _). *)
  (*      eapply r_put_lhs. *)
  (*      eapply r_put_lhs. *)
  (*      eapply r_bind with (m₁ := ret (chCanonical chUnit)) (f₁ := fun _ => _). *)
  (*      +  *)
       
  (*      eapply r_bind with (pre := fun _ => _). *)
       
  (*      (* eapply sampler_case. *) *)
  (*      2: easy. *)
  (*      eapply cmd_sample_preserve_pre. *)
  (*      eapply r_bind. *)
  (*      ssprove_code_simpl. *)
  (*      eapply r_uniform_bij. *)
  (*      eapply r_sample. *)
  (*      ssprove_sync. *)
  (*   ssprove_sync_eq. intros. *)
  (*      eapply rsame_head. *)
  (*      eapply r_bind. *)
  (*   ssprove_sync. intros. *)

  (*     1: ssprove_sync_eq. *)
  (*     ssprove_code_simpl. *)
  (*     simplify_linking. *)
  (*     simpl. *)
  (*     simplify_linking. *)
  (*     unfold get_op_default. *)
  (*     unfold lookup_op. *)
  (*     cbv match zeta. *)
  (*               unfold IND_CPA_jazz. *)
  (*               (* cbn. *) *)
  (*               (* cbn. *) *)
  (*               (* unfold IND_CPA_pkg_ff. *) *)
  (*               (* move: H; rewrite in_fset in_cons=>/orP []. 2: easy. *) *)
  (*               (* move=> /eqP H. noconf H. *) *)


  (*               unfold JKEYS_EXPAND. *)
  (*               unfold get_translated_static_fun. *)
  (*               unfold translate_prog_static. *)
  (*               unfold translate_funs_static. *)
  (*               unfold translate_call_body. *)
                
  (*               simplify_eq_rel m. *)
  (*               simplify_linking. *)
  (*               (* We now conduct the proof in relational logic. *) *)
  (*               ssprove_swap_rhs 1%N. *)
  (*               ssprove_swap_rhs 0%N. *)
  (*               ssprove_sync_eq. cbn -[expn]. intros [k|]. *)
  (*               - cbn -[expn]. ssprove_swap_rhs 0%N. *)
  (*                 eapply rpost_weaken_rule. *)
  (*                 1: eapply rreflexivity_rule. *)
  (*                 cbn. intros [? ?] [? ?] e. inversion e. intuition auto. *)
  (*               - cbn -[expn]. *)
  (*                 ssprove_swap_rhs 0%N. *)
  (*                 ssprove_swap_rhs 1%N. *)
  (*                 ssprove_swap_rhs 0%N. *)
  (*                 ssprove_swap_rhs 2%N. *)
  (*                 ssprove_swap_rhs 1%N. *)
  (*                 eapply rpost_weaken_rule. 1: eapply rreflexivity_rule. *)
  (*                 cbn. intros [? ?] [? ?] e. inversion e. intuition auto. *)
  (* Qed. *)
  
  (* Opaque translate_for. *)
  (* Opaque translate_call. *)
  (* simpl. *)
  (* (* Opaque wrange. *) *)
  (* (* Opaque for_loop'. *) *)
  (* constructor. *)
  (* 1: rewrite in_fset; apply/xseq.InP; apply List.in_eq.  *)
  (* constructor. *)
  (* 1: rewrite in_fset. 1: apply/xseq.InP; apply List.in_cons; eapply List.in_eq.  *)
  (* constructor. *)
  (* 1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end.  *)
  (* constructor. *)
  (* 1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end.  *)
  (* constructor. *)
  (* 1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end. *)
  (* intros. rewrite 3!bind_assoc. *)
  (* eapply valid_bind. *)
  (* { Transparent translate_call. unfold translate_call. Opaque translate_call. simpl. constructor. *)
  (*   Set Printing All. *)
  (*   valid_code *)

  (*     simpl. *)
  (*   constructor. *)
  (*   1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end.  *)
  (*   constructor. *)
  (*   1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end.  *)
  (*   constructor. *)
  (*   1: rewrite in_fset; apply/xseq.InP; repeat lazymatch goal with | |- List.In _ (_ :: _) => eapply List.in_cons | |- _ => eapply List.in_eq end.  *)
  (*   1: erewrite -> in_cons. *)
    
  (*   cbn. simpl. *)
  (*   2: easy. *)
  (*   simpl. *)

  (*   Program Definition jazz_enc id0 {L : { fset Location }} (m : pt U128) (k : key U128) : *)
  (*     code L [interface] ('word U128 × 'word U128) := *)
  (*     {code *)
  (*        r ← sample uniform N ;; *)
  (*      pad ← JAES id0 (word_of_ord r) k ;; *)
  (*      let c := m ⊕ (hdtc128 pad) in *)
  (*      ret (word_of_ord r, c) *)
  (*     }. *)
