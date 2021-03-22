From Crypt Require Import pkg_composition PRF ElGamal pkg_rhl UniformStateProb.

Definition results_from_the_paper :=
  (valid_link,
  (link_assoc,
  (valid_par,
  (par_commut,
  (par_assoc,
  (valid_ID,
  (link_id,
  (id_link,
  (interchange,
  (* (PRF_example.security_based_on_prf, *)
  (* (ElGamal_OT, *)
  (@rreflexivity_rule,
  (@rbind_rule,
  (@rswap_rule,
  (@rrewrite_eqDistrL,
  (@Uniform_bij_rule,
  (@assert_rule,
  (@assert_rule_left,
  (Advantage_triangle,
  (Advantage_link,
  (@prove_relational,
  (@Pr_eq_empty,
  0)))))))))))))))))))).

Print Assumptions results_from_the_paper.
