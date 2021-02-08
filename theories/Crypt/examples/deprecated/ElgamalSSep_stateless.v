From Coq Require Import
     RelationClasses 
     Morphisms.
From Mon Require Import
     FiniteProbabilities
     SPropMonadicStructures
     SpecificationMonads
     MonadExamples
     SPropBase
     FiniteProbabilities.
From Relational Require Import
     OrderEnrichedCategory
     GenericRulesSimple.
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum
     fingroup.fingroup
     solvable.cyclic
     prime.
From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     Rules
     UniformDistrLemmas
     FreeProbProg
     Theta_dens
     Rules
     UniformDistr
     SSep.

Import Num.Theory.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Parameter η : nat.
Parameter gT : finGroupType.
Parameter ζ : {set gT}.
Parameter g :  gT.
Parameter g_gen : ζ == <[g]>.
Parameter prime_order : prime #[g].

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g.
  by move/eqP: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

Inductive probEmpty : Type -> Type := .

Module MyParam <: AsymmetricSchemeParams. 

  Definition SecurityParameter : choiceType := nat_choiceType.
  Definition Plain  : finType := FinGroup.arg_finType gT.
  Definition Cipher : finType := prod_finType (FinGroup.arg_finType gT) (FinGroup.arg_finType gT).
  Definition PubKey : finType := FinGroup.arg_finType gT.
  Definition SecKey : finType := [finType of 'Z_q].

  Definition plain0 := g.
  Definition cipher0 := (g, g).
  Definition pub0 := g.
  Definition sec0 : SecKey := 0.

  Definition probE : Type -> Type := probEmpty.
  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes -> choiceType.
  Proof.  move => contra. contradiction. Defined.

  Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
  Proof. move => contra. contradiction. Defined.

  Definition Hch : forall r : rel_choiceTypes, chEmb r.
  Proof. move => contra. contradiction. Defined.

End MyParam.

Module MyAlg <: AsymmetricSchemeAlgorithms MyParam.

  Export MyParam.

  Module MyARules := ARules MyParam.
  Export MyARules.

  (* KG(η) := x <$ Z_q; return (g^x, x) *)
  Definition KG (sparam : SecurityParameter) : FrDist (prod_choiceType PubKey SecKey) :=
    x ∈ (choice_incl (fin_family i_sk)) <<- (@Uniform_F i_sk) ;;
    retF (g^+x, x).

    (* bindrFree _ _ Uniform_F *)
    (*               (fun x : choice_incl  (fin_family i_sk) => *)
    (*                  retrFree _ _ _ (g^+x, x)).  *)

  (* Enc pk m := y <$ Z_q; return (g^y, pk^y × m) *)
    Definition Enc (pk : PubKey) (m : Plain) : FrDist Cipher :=
      y ∈ (choice_incl (fin_family i_sk)) <<- (@Uniform_F i_sk);;
      retF (g^+y, (pk^+y) * m).

    (* bindrFree _ _ Uniform_F *)
    (*           (fun y : choice_incl (fin_family i_sk) => *)
    (*              retrFree _ _ _ (g^+y, (pk^+y) * m)).  *)


  (* Dec (x, (β, γ)) := return (γ × β^(-x)) *)
  Definition Dec (sk : SecKey) (c : Cipher) : Plain := c.2 * (c.1)^-sk.

  Definition chEmb_non_trivial : forall r : rel_choiceTypes, chEmb r.
  Proof.
    move => [r | r].
    - unfold Urel_choiceTypes in r.
      destruct r; simpl; [exact: g | exact: (g, g) | exact: g | exact: 0 | exact: true].
    - inversion r.
  Qed.

  Definition SecKey2PubKey : SecKey -> PubKey := fun x => g^+x.

  Definition SecKey_op : SecKey -> SecKey -> SecKey := fun x y => x * y.

End MyAlg.

Module Elgamal_Scheme :=  AsymmetricScheme MyParam MyAlg.
Export Elgamal_Scheme.

Definition L1 (m : Plain) : L_pk_ots.
Proof.
  move => oo.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => a.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => b.
  apply: inj_left.
  exact: retF ((g^+b), (g^+(a * b)) * m).
Defined.

Definition L2 (m : Plain) : package_type (fun u : unit_choiceType => prod_choiceType gT (prod_choiceType gT gT))
                                         (fun u : unit_choiceType => Cipher).
Proof.
  move => oo.
  apply: bindrFree.
  apply: callrFree. now right.
  move => [ga [gb gab]].
  apply: inj_left.
  exact: retF (gb, gab * m).
Defined.

Definition DH_real : package_type  L_interface
                                   (fun u : unit_choiceType => prod_choiceType gT (prod_choiceType gT gT)).
Proof.
  move => oo.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => a.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => b.
  apply: inj_left.
  exact: retF (g^+a, (g^+b, g^+(a*b))).
Defined.

Definition DH_rnd : package_type  L_interface
                                  (fun u : unit_choiceType => prod_choiceType gT (prod_choiceType gT gT)).
Proof.
  move => oo.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => a.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => b.
  apply: bindrFree.
  apply: inj_left. exact: @Uniform_F i_sk.
  rewrite /= => c.
  apply: inj_left.
  exact: retF (g^+a, (g^+b, g^+c)).
Defined.


Lemma ropr_bindrFree_inl { C } { i } { cont } :
    bindrFree Ops Arit (@Uniform_F i) cont = ropr Ops Arit C (existT (fun rchT => probE (chEmb rchT)) (inl i) (inl (Uni_W i))) cont.
Proof.  by []. Qed.

Lemma ropr_bindrFree_inr { C } { ops : Ops } { cont } :
  bindrFree Ops Arit (callrFree Ops Arit ops) cont = ropr Ops Arit C ops cont.
Proof. by []. Qed.

Ltac unfold_tac := repeat lazymatch goal with [ |- context [ ?arg1 ?arg2] ]=>
                                              (try rewrite -ropr_bindrFree_inl); (try rewrite -ropr_bindrFree_inr)  end.

(* "the group operation acts as a one-time-pad" *)
Lemma group_otp ( m : Plain) :
  θ0 (@Uniform_F i_cipher) = θ0 ( y ∈ 'Z_q <<- @Uniform_F i_sk;; z ∈ 'Z_q <<- @Uniform_F i_sk ;; retF (g^+y, g^+z * m)).
Proof.
Admitted.

Definition DDH_assumption : Prop :=
 θ0 ( x ∈ 'Z_q <<- @Uniform_F i_sk ;; y ∈ 'Z_q <<- @Uniform_F i_sk;; z ∈ 'Z_q <<- @Uniform_F i_sk ;; retF (g^+y, g^+z)) =
 θ0 ( x ∈ 'Z_q <<- @Uniform_F i_sk ;; y ∈ 'Z_q <<- @Uniform_F i_sk;; retF (g^+y, g^+(x * y))).

Lemma DDH_lemma (m : Plain) (ddh : DDH_assumption) :
  θ0 ( x ∈ 'Z_q <<- @Uniform_F i_sk ;; y ∈ 'Z_q <<- @Uniform_F i_sk;; z ∈ 'Z_q <<- @Uniform_F i_sk ;; retF (g^+y, g^+z * m)) =
  θ0 ( x ∈ 'Z_q <<- @Uniform_F i_sk ;; y ∈ 'Z_q <<- @Uniform_F i_sk;; retF (g^+y, g^+(x * y) * m)).
Proof.
  (* this follows from group_otp.

     write m = g^+k for some k. then in LHS the last ret is (g^+y, g^+z * g^k)
                                        RHS                 (g^+y, g^+(x * y) * g^k) = (g^+y, g^+(y * x) * g^k) = (g^+y, g^+ y * g^(x *k))

     apply group_otp on the LHS with m = g^k and on the RHS with m = g^(x * k).
*)
Admitted.

Theorem one_time_security_Elgamal (ddh : DDH_assumption) : @ot_CPA η.
Proof.
  apply: (@ot_CPA_rnd_implies_ot_CPA η).
  rewrite /ot_CPA_rnd. move => m.
  apply (rewrite_eqDistrL (L1 m ⋈ @PK_scheme η)).
  apply (rewrite_eqDistrL ((L2 m ∘ DH_real) ⋈ (@PK_scheme η))).
  apply (rewrite_eqDistrL ((L2 m ∘ DH_rnd) ⋈ (@PK_scheme η))).
  apply (rewrite_eqDistrL ((L_rnd m) ⋈ (@PK_scheme η))).
  by apply: reflexivity_rule.
  { apply: (@coupling_eq _ _ _ True); auto.
    rewrite /link /L_rnd /L2 /PK_scheme /remove_void /=.
    unfold_tac.
    apply seq_rule_ch with eq.
    - by apply: reflexivity_rule.
    - rewrite /= => x' x. apply: pre_hypothesis_rule_ch => a_eq. subst.
      unfold_tac.
      apply: rewrite_eqDistrL.
        by apply: reflexivity_rule.
          by rewrite [RHS] (group_otp m). }
  { rewrite /link /L1 /L2 /DH_rnd /PK_scheme /remove_void /=.
    unfold_tac. by rewrite [LHS] (DDH_lemma m ddh). }
  {  by f_equal. }
  { apply: (@coupling_eq _ _ _ True); auto.
    rewrite /link /L_rnd /L2 /PK_scheme /remove_void /=.
    unfold_tac.
    apply seq_rule_ch with eq.
    - by apply: reflexivity_rule.
    - rewrite /= => x' x. apply: pre_hypothesis_rule_ch => a_eq. subst.
      unfold_tac.
      apply seq_rule_ch with eq.
      -- by apply: reflexivity_rule.
      -- rewrite /= => y' y. apply: pre_hypothesis_rule_ch => a_eq. subst.
         rewrite expgM.
         exact: reflexivity_rule. }
Qed.
