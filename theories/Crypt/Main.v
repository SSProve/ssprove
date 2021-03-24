From Crypt Require Import pkg_composition PRF ElGamal pkg_rhl UniformStateProb RulesStateProb.

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
  valid_link ;
  link_assoc ;
  valid_par ;
  par_commut ;
  par_assoc ;
  valid_ID ;
  link_id ;
  id_link ;
  interchange ;
  security_based_on_prf ;
  ElGamal_Z3.ElGamal_OT ;
  @rreflexivity_rule ;
  @rbind_rule ;
  @rswap_rule ;
  @rrewrite_eqDistrL ;
  @Uniform_bij_rule ;
  @assert_rule ;
  @assert_rule_left ;
  @bounded_do_while_rule;
  @for_loop_rule;
  Advantage_triangle ;
  Advantage_link ;
  @prove_relational ;
  @Pr_eq_empty
].

Print Assumptions results_from_the_paper.
