From Coq Require Import Utf8.
From Crypt Require pkg_composition pkg_advantage PRF ElGamal pkg_rhl
  UniformStateProb RulesStateProb KEMDEM SigmaProtocol Schnorr.

(* Notation to chain lets and end with 0 *)
Notation "[ 'let' ]" :=
  (0)
  (at level 0, only parsing).

Notation "[ 'let' x1 ]" :=
  (let foo := x1 in [let])
  (at level 0, only parsing).

Notation "[ 'let' x ; .. ; z ]" :=
  (let foo := x in .. (let foo := z in [let]) ..)
  (at level 0, only parsing).

Definition results_from_the_paper := [let
  pkg_composition.valid_link ;
  pkg_composition.link_assoc ;
  pkg_composition.valid_par ;
  pkg_composition.par_commut ;
  pkg_composition.par_assoc ;
  pkg_composition.valid_ID ;
  pkg_composition.link_id ;
  pkg_composition.id_link ;
  pkg_composition.interchange ;
  PRF.security_based_on_prf ;
  ElGamal.ElGamal_Z3.ElGamal_OT ;
  @pkg_rhl.rreflexivity_rule ;
  @pkg_rhl.rbind_rule ;
  @pkg_rhl.rswap_rule ;
  @pkg_rhl.rrewrite_eqDistrL ;
  @UniformStateProb.Uniform_bij_rule ;
  @UniformStateProb.assert_rule ;
  @UniformStateProb.assert_rule_left ;
  @RulesStateProb.bounded_do_while_rule ;
  @pkg_rhl.for_loop_rule ;
  pkg_advantage.Advantage_triangle ;
  pkg_advantage.Advantage_link ;
  @pkg_rhl.eq_upto_inv_perf_ind ;
  @pkg_rhl.Pr_eq_empty ;
  KEMDEM.PKE_security ;
  Schnorr.Schnorr.fiat_shamir_correct ;
  Schnorr.schnorr_com_binding
].

Print Assumptions results_from_the_paper.
