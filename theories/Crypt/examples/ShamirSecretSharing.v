(******************************************************************************)
(*                          Shamir Secret Sharing                             *)
(*                                                                            *)
(* This formalises Theorem 3.13 from "The Joy of Cryptography" (p. 60).       *)
(* It formalises Shamir's Secret Sharing scheme and proves that it has        *) 
(* perfect security. It is a t-out-of-n secret sharing scheme over the        *) 
(* field 'F_p.                                                                *)
(*                                                                            *) 
(* To prove security in SSProve, we need to define a bijection for the        *)
(* random polynomials f_r and f_l. The bijection is:                          *)
(*                                                                            *)
(*   f_r(x) = f_l(x) + g_r(x) - g_l(x) = m_r + x * q_r(x)                     *)                             
(*                                                                            *)
(* The proof conducted here differs a bit from the one in the book, since     *)
(* our proof is based on the construction of a bijection, whereas the one     *)
(* in the book is based on statistical analysis.                              *)
(*                                                                            *)
(* We skip Lemma 3.12, since the bijection technique used in this proof       *)
(* doesn't benefit from the extra steps. (Note, earlier commits did include   *)
(* it, so if you are interested, feel free to check out the commit history.   *)
(*                                                                            *)
(* Since SSProve does not support using polynomials directly, we represent    *)
(* polynomials with an inhabited finite type of size p^t (PolyEnc t) because  *) 
(* there are [p^t] polynomials of size [<= t] over the field ['F_p].          *)
(*                                                                            *)
(* We then define a bijection functions between polynomials and [PolyEnc t].  *)
(* We combine all three bijections to create a bijection from [PolyEnc t]     *)
(* to [PolyEnc t] that we can use to prove security of the protocol.          *)
(*                                                                            *)
(* The final statement (unconditional_secrecy) is equivalent to that of       *)
(* the book: The scheme achieves perfect secrecy, for any t, n and any        *)
(* prime p.                                                                   *)
(*                                                                            *)
(* Section ShamirSecretSharing_example                                        *)
(*   Word == type of the words in the protocol       			                    *)
(*  'word == notation for Word						                                    *)
(*  Share == type of the shares in the protocol                               *)
(* 'share == notation for Share                                               *)
(*  Party == type of the parties in the protocol                              *)
(* 'party == notation for Party                                               *)
(*      t == the number of shares needed for reconstruction.                  *)
(*     t' == the maximum number of shares the scheme is secure against.       *)
(*      n == number of shares.                                                *)
(*      p == number of possible messages. It is is a prime.                   *)
(* 'seq t == local choice_type for sequences				                          *)
(* 'set t == local choice_type for sets 				                              *)
(******************************************************************************)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From SSProve.Crypt.examples Require Import PolynomialUtils.

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

Local Open Scope ring_scope.

Local Open Scope nat_scope.

Section ShamirSecretSharing_example.

Variable (p: nat).

Context (p_prime: prime p).

(* We have to use [(Zp_trunc (pdiv p)).+2] for [Word] to be considered a      *)
(* field. This is important for uniqueness of Lagrange polynomials.           *)

Definition Word_N := (Zp_trunc (pdiv p)).+2.
Definition Word := 'fin Word_N.

Lemma words_p_eq:
  Word_N = p.
Proof.
  by apply: Fp_cast.
Qed.

(* Shares are simply a point in ['F_p], i.e. a pair.                          *)
Definition Share: choice_type := Word × Word.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Notation " 'share " := (Share) (in custom pack_type at level 2).
Notation " 'share " := (Share) (at level 2): package_scope.

(* We can't use sequences directly in [choice_type] so instead we use a map   *)
(* from natural numbers to the type.                                          *)

Definition chSeq t := chMap 'nat t.

Notation " 'seq t " := (chSeq t) (in custom pack_type at level 2).
Notation " 'seq t " := (chSeq t) (at level 2): package_scope.

(* We can't use sets directly in [choice_type] so instead we use a map to     *)
(* units. We can then use [domm] to get the domain, which is a set.           *)

Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

(* [n] is the number of shares.                                               *)
Variable (n: nat).
Context (n_positive: Positive n).

(* We cannot possibly have more than [p-1] shares.                            *)
Context (n_ltn_p: n < p).

(* Each party gets a share. We use a finity type to represent parties as it   *)
(* makes later proofs easier.                                                 *)
Definition Party := 'fin n.

Notation " 'party " := (Party) (in custom pack_type at level 2).
Notation " 'party " := (Party) (at level 2): package_scope.

(* The share of each party is the point with [x = 1 + the party index].       *)
#[program]
Definition party_to_word (x: Party): Word := @Ordinal _ x.+1 _.
Next Obligation.
  case: x => [x Hx] /=.
  rewrite words_p_eq.
  apply: leq_trans.
  2: by apply: n_ltn_p.
  by rewrite ltnS.
Qed.

(* Shares are points on a polynomial [q].                                     *)
Definition make_share (q: {poly Word}) (x: Party): Share :=
  (party_to_word x, q.[party_to_word x]).

(* This is a convenience function for computing the shares for a message [m]. *)
(* [q] is a randomly sampled polynomial.                                      *)
Definition make_shares (m: Word) (q: {poly Word}) (U: seq Party): seq Share :=
  map (make_share (cons_poly m q)) U.

(* Bijection *)
Definition poly_bij (U: seq Party) (m m': Word) (q: {poly Word}): {poly Word} :=
  let sh := make_shares m q U in
  let g  := lagrange_poly ((0%R, m ) :: sh) in
  let g' := lagrange_poly ((0%R, m') :: sh) in
  let q' := (q + tail_poly (g' - g))%R in
  q'.

Lemma leq_pred_S (a b: nat):
  (a.-1 <= b) = (a <= b.+1).
Proof.
  by case: a.
Qed.

Lemma size_poly_bij {t: nat} (U: seq Party) (m m': Word) (q: {poly Word}):
  size U <= t ->
  size q <= t ->
  size (poly_bij U m m' q) <= t.
Proof.
  move=> Hu Hq.
  apply: leq_trans.
  1: by apply: size_add.
  rewrite geq_max.
  apply /andP. split => //.
  rewrite size_tail_poly leq_pred_S.
  apply: leq_trans.
  1: by apply: size_add.
  rewrite geq_max.
  apply /andP.
  split.
  2: rewrite size_opp.
  all: apply: (leq_trans (size_lagrange_poly _)).
  all: by rewrite /= size_map.
Qed.

Lemma no_zero_share (U: seq Party) (m: Word) (q: {poly Word}):
  0%R \notin unzip1 (make_shares m q U).
Proof.
  by elim: U.
Qed.

Lemma in_make_shares (x: Party) (U: seq Party) (m: Word) (q: {poly Word}):
  (party_to_word x \in unzip1 (make_shares m q U)) = (x \in U).
Proof.
  elim: U => [// | b U IHu] /=.
  rewrite in_cons.
  destruct (x == b) eqn:Heq.
  - move /eqP in Heq.
    by rewrite Heq in_cons !eq_refl.
  - by rewrite in_cons -val_eqE eqSS val_eqE Heq.
Qed.

Lemma uniq_make_shares (U: seq Party) (m: Word) (q: {poly Word}):
  uniq U ->
  uniq (unzip1 (make_shares m q U)).
Proof.
  elim: U => [// | a U IHu] /=.
  move=> /andP [H1 H2].
  by rewrite IHu // in_make_shares H1.
Qed.

Lemma make_shares_same_x (m m': Word) (U: seq Party) (q: {poly Word}):
  unzip1 (make_shares m' q U) = unzip1 (make_shares m q U).
Proof.
  elim: U => [// | a U IHu] /=.
  by rewrite IHu.
Qed.

(*Ask why this is not imported*)
Ltac simpl_dif_point :=
  rewrite /dif_points /unzip1 ?map_cons ?map_cat ?cons_uniq -?/unzip1.


Lemma sec_poly_bij_part (x: Party) (U: seq Party) (m m': Word) (q: {poly Word}):
  uniq U ->
  x \in U ->
  (cons_poly m' (poly_bij U m m' q)).[party_to_word x] =
  (cons_poly m                   q ).[party_to_word x].
Proof.
  move=> Huniq Hin.
  rewrite (cons_poly_add m) lagrange_sub_zero_cons.
  2: by rewrite /= no_zero_share uniq_make_shares.
  rewrite hornerD cons_eq_head_tail_poly.
  2: {
    rewrite /head_poly -horner_coef0.
    rewrite (lagrange_poly_correct 0 (m' - m)) //.
    - simpl_dif_point. 
      by rewrite unzip1_zero_points no_zero_share uniq_make_shares.
    - by rewrite in_cons eq_refl.
  }
  rewrite (lagrange_poly_correct (party_to_word x) 0%R) ?GRing.addr0 //.
  - simpl_dif_point. 
    by rewrite unzip1_zero_points no_zero_share uniq_make_shares.
  - by rewrite in_cons pt_in_zero_points ?Bool.orb_true_r // in_make_shares.
Qed.

Lemma sec_poly_bij_rec (l r: seq Party) (m m': Word) (q: {poly Word}):
  uniq (l ++ r) ->
  make_shares m' (poly_bij (l ++ r) m m' q) r =
  make_shares m                          q  r.
Proof.
  elim: r => [// | a r IHr] in l*.
  rewrite -cat_rcons -cats1 /= => H.
  rewrite IHr // /make_share sec_poly_bij_part //.
  by rewrite mem_cat cats1 mem_rcons in_cons eq_refl.
Qed.

Lemma sec_poly_bij (U: seq Party) (m m': Word) (q: {poly Word}):
  uniq U ->
  make_shares m' (poly_bij U m m' q) U =
  make_shares m                   q  U.
Proof.
  move=> H.
  by rewrite (sec_poly_bij_rec [::]).
Qed.

Lemma bij_poly_bij (U: seq Party) (m m': Word) (q: {poly Word}):
  uniq U ->
  poly_bij U m' m (poly_bij U m m' q) = q.
Proof.
  move=> Huniq.
  rewrite /poly_bij sec_poly_bij //.
  rewrite !lagrange_sub_zero_cons.
  2,3: by rewrite /= no_zero_share uniq_make_shares.
  rewrite -GRing.addrA -tail_poly_add.
  rewrite (make_shares_same_x m' m).
  rewrite lagrange_add_zero_cons.
  2: by rewrite /= no_zero_share uniq_make_shares.
  rewrite -GRing.opprB GRing.addNr.
  rewrite /zero_points -map_cons -/(zero_points _).
  rewrite lagrange_zero.
  2: by rewrite /= no_zero_share uniq_make_shares.
  by rewrite /tail_poly polyseq0 GRing.addr0.
Qed.


Instance p_pow_positive t:
  Positive (p ^ t).
Proof.
  by rewrite /Positive expn_gt0 prime_gt0.
Qed.

(* Representation of polynomials for SSProve*)
Definition PolyEnc t := 'fin (p ^ t).

#[program] Definition mod_p (a: nat): Word :=
  @Ordinal _ (a %% p) _.
Next Obligation.
  by rewrite words_p_eq ltn_mod prime_gt0.
Qed.

Lemma mod_p_muln_p (a: nat) (m: Word):
  mod_p (a * p + m) = m.
Proof.
  apply: ord_inj => /=.
  by rewrite modnMDl -words_p_eq modn_small.
Qed.

Fixpoint nat_to_poly (t a: nat): {poly Word} :=
  match t with
  | 0 => 0
  | t'.+1 => cons_poly (mod_p a) (nat_to_poly t' (a %/ p))
  end.

Fixpoint poly_to_nat (t: nat) (q: {poly Word}): nat :=
  match t with
  | 0 => 0
  | t'.+1 => poly_to_nat t' (tail_poly q) * p + head_poly q
  end.

Lemma size_nat_to_poly (t a: nat):
  size (nat_to_poly t a) <= t.
Proof.
  elim: t => [|t IHt] /= in a*.
  1: by rewrite size_poly0.
  rewrite size_cons_poly.
  destruct (_ && _) => //.
  by rewrite ltnS.
Qed.

Lemma size_poly_to_nat (t: nat) (q: {poly Word}):
  poly_to_nat t q < p ^ t.
Proof.
  elim: t => [// | t IHt] /= in q*.
  apply: (@leq_trans (poly_to_nat t (tail_poly q) * p + p)).
  2: by rewrite expnSr -mulSnr leq_pmul2r // prime_gt0.
  case: (head_poly q) => a Ha /=.
  by rewrite ltn_add2l -words_p_eq.
Qed.

Lemma nat_poly_nat (t a: nat):
  a < p ^ t ->
  poly_to_nat t (nat_to_poly t a) = a.
Proof.
  elim: t a => [|t IHt] a H.
  1: by destruct a.
  rewrite expnS mulnC in H.
  rewrite /= head_cons_poly tail_cons_poly IHt -?divn_eq //.
  by rewrite ltn_divLR // prime_gt0.
Qed.

Lemma poly_nat_poly (t: nat) (q: {poly Word}):
  size q <= t ->
  nat_to_poly t (poly_to_nat t q) = q.
Proof.
  elim: t q => [|t IHt] q H.
  1: {
    rewrite size_poly_leq0 in H.
    move /eqP in H. by subst.
  }
  rewrite /= mod_p_muln_p.
  rewrite divnMDl ?prime_gt0 // divn_small.
  2: {
    destruct (head_poly q) as [c Hc] => /=.
    by rewrite -words_p_eq.
  }
  rewrite addn0 IHt ?cons_head_tail_poly //.
  rewrite size_tail_poly.
  destruct (size q) eqn:P; by rewrite P.
Qed.

Variable (t': nat).
Definition t := t'.+1.

(* This is the final bijection explained in the header. We prove the          *)
(* analogus lemmas as the ones stated above.                                  *)
#[program]
Definition share_bij (U: seq Party) (m m': Word) (c: PolyEnc t'): PolyEnc t' :=
  @Ordinal _ (poly_to_nat t' (poly_bij U m m' (nat_to_poly t' c))) _.
Next Obligation.
  by apply: size_poly_to_nat.
Qed.

Lemma sec_share_bij (U: seq Party) (m m': Word) (c: PolyEnc t'):
  uniq U ->
  (size U <= t')%N ->
  make_shares m' (nat_to_poly t' (share_bij U m m' c)) U =
  make_shares m  (nat_to_poly t'  c                  ) U.
Proof.
  move=> Huniq Hltn.
  rewrite /share_bij /= poly_nat_poly ?size_poly_bij ?size_nat_to_poly //.
  by apply: sec_poly_bij.
Qed.

Lemma bij_share_bij (U: seq Party) (m m': Word):
  uniq U ->
  (size U <= t')%N ->
  bijective (share_bij U m m').
Proof.
  move=> Huniq Hleq.
  exists (share_bij U m' m) => q;
  apply: ord_inj;
  rewrite /= poly_nat_poly ?size_poly_bij ?size_nat_to_poly //;
  by rewrite bij_poly_bij ?nat_poly_nat.
Qed.

Local Open Scope package_scope.

(*  Identifier of the signature *)
Definition shares : nat := 0.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

(**
  Finally, we can define the packages and prove security of the protocol.
  This part is fairly easy now that we have a bijection.
*)
Definition SHARE_pkg_tt:
  package fset0 [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'party → 'seq 'share ] :=
  [package
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'party): 'seq 'share {
      if size (domm U) >= t then ret emptym
      else
      q <$ uniform (p ^ t') ;;
      let q := nat_to_poly t' q in
      let sh := make_shares ml q (domm U) in
      ret (fmap_of_seq sh)
    }
  ].

Definition SHARE_pkg_ff:
  package fset0 [interface]
    [interface #val #[shares]: ('word × 'word) × 'set 'party → 'seq 'share ] :=
  [package
    #def #[shares] ('(ml, mr, U): ('word × 'word) × 'set 'party): 'seq 'share {
      if size (domm U) >= t then ret emptym
      else
      q <$ uniform (p ^ t') ;;
      let q := nat_to_poly t' q in
      let sh := make_shares mr q (domm U) in
      ret (fmap_of_seq sh)
    }
  ].

Definition SHARE := mkpair SHARE_pkg_tt SHARE_pkg_ff.

Lemma SHARE_equiv:
  SHARE true ≈₀ SHARE false.
Proof.
  (**
    Since the games have no state, we don’t need to maintain an invariant, and only
    need to ensure the games have the same output distribution.
  *)
  apply: eq_rel_perf_ind_eq.
    
  (* Create a goal for each procedure, one in this case *)
  simplify_eq_rel m.

  (* We can weaken the postcondition*)
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  
  (* Unpack m as ml, mr and U *)
  case: m => [[ml mr] U].

  (* Perform case analysis over the following inequality *)
  destruct (t <= size (domm U)) eqn:Heq; rewrite Heq.
  (* First case is very easy since we return emptym in both cases *)
  1: apply: rreflexivity_rule. 
  
  (* t > size(domm U) *)
  apply negbT in Heq.
  rewrite -ltnNge ltnS in Heq.
  (**
     We need to prove it is bijective and that the operations performed after the sampling
     result in the program returning the same distribution of values. 
  *)
  apply: r_uniform_bij => [|q].
  (* Bijection *)
  1: {
    apply: (bij_share_bij (domm U) ml mr) => //.
    by apply: uniq_fset.
  }
  (* Since there exists a bijection, we finish by proving that the last operations are
     equivalent
  *)
  rewrite sec_share_bij ?uniq_fset //.
  by apply: rreflexivity_rule.
Qed.

(**
  This corresponds to Theorem 3.13 from "The Joy of Cryptography".
*)
Theorem unconditional_secrecy LA A:
  ValidPackage LA
    [interface #val #[shares]: ('word × 'word) × 'set 'party → 'seq 'share ]
    A_export A ->
  Advantage SHARE A = 0%R.
Proof.
  move=> vA.
  rewrite Advantage_E Advantage_sym.
  by rewrite SHARE_equiv ?fdisjoints0.
Qed.

End ShamirSecretSharing_example.
