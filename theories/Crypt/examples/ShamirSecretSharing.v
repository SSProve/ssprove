(**
  This formalises Theorem 3.13 from "The Joy of Cryptography" (p. 60).
  It formalises Shamir's Secret Sharing scheme and proves that it has perfect
  security. It is a t-out-of-n secret sharing scheme over the field ['F_p].

  We also formalise Theorem 3.8 and 3.9 from the book
  We skip Lemma 3.12, since the bijection technique used in this proof doesn't
  benefit from the extra steps. (Note, earlier commits did include it, so if you
  are interested, feel free to check out the commit history.)

  By far most of the proof is spent on proving various properties of polynomials
  that are used to define and prove security of a bijection. After this the
  remaining part of the proof is just using that bijection to prove the scheme
  is secure.

  This differs a bit from the proof in "The Joy of Cryptography" since this is
  based on a bijection whereas it is based on statistical analysis. This
  arguably harder to prove, but it is the method that is directly supported by
  SSProve, and it is also easier verify that you got it right.

  The final statement ([unconditional_secrecy]) is equivalent to that of the
  books: The scheme achieves perfect secrecy, for any [t], [n] and any prime
  [p].
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

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

(**
  First step is to define Lagrange interpolation.
  This is implemented in the [lagrange_poly] function, which is split up into
  several helper functions.
*)
Definition lagrange_basis {R: unitRingType} (s: seq R) (x: R): {poly R} :=
  \prod_(c <- s) ((x-c)^-1 *: Poly [:: -c ; 1]).

Fixpoint subseqs_rec {T} l m r: seq (T * seq T) :=
  match r with
  | [::] => [:: (m, l)]
  | a :: r' => (m, l ++ r) :: subseqs_rec (l ++ [:: m]) a r'
  end.

Definition subseqs {T} (s: seq T): seq (T * seq T) :=
  match s with
  | [::] => [::]
  | m :: r => subseqs_rec [::] m r
  end.

Definition lagrange_poly_part {R: unitRingType} (j: R * R * seq (R * R)): {poly R} :=
  j.1.2 *: lagrange_basis (unzip1 j.2) j.1.1.

Definition lagrange_poly {R: unitRingType} (pts: seq (R * R)): {poly R} :=
  \sum_(j <- subseqs pts) lagrange_poly_part j.

(**
  Then we prove some fundamental properties of Lagrange Interpolation.
  Specifically:
  - [size_lagrange_poly]: The size of a Lagrange polynomial is [<= size pts].
  - [lagrange_poly_correct]: Evaluating a Lagrange polynomial at a point gives the corresponding y value.
  - [lagrange_poly_unique]: There is exactly one polynomial with size [<= size pts], that satisfies [lagrange_poly_correct].

  These together formalise Theorem 3.8 and 3.9 from the book
*)

Lemma lagrange_basis_0 {R: comUnitRingType} (x1 x: R) (s: seq R):
  x \in s ->
  (lagrange_basis s x1).[x] = 0.
Proof.
  rewrite /lagrange_basis.
  elim: s => [// | a s IHs].
  rewrite in_cons big_cons hornerM hornerZ !horner_cons hornerC GRing.mul0r GRing.add0r GRing.mul1r.
  destruct (x == a) eqn:Heq.
  - move /eqP in Heq.
    by rewrite Heq GRing.subrr GRing.mulr0 GRing.mul0r.
  - move=> H.
    by rewrite IHs // GRing.mulr0.
Qed.

Lemma lagrange_basis_1 {R: fieldType} (x: R) (s: seq R):
  (x \notin s) = ((lagrange_basis s x).[x] == 1).
Proof.
  rewrite /lagrange_basis.
  elim: s => [|a s IHs].
  1: by rewrite big_nil hornerC eq_refl.
  rewrite in_cons big_cons hornerM hornerZ !horner_cons hornerC GRing.mul0r GRing.add0r GRing.mul1r.
  destruct (x == a) eqn:Heq.
  - move /eqP in Heq.
    by rewrite Heq GRing.subrr GRing.mulr0 GRing.mul0r eq_sym GRing.oner_eq0.
  - apply negbT in Heq.
    rewrite -GRing.subr_eq0 in Heq.
    by rewrite GRing.mulVf // GRing.mul1r IHs.
Qed.

Lemma size_lagrange_basis {R: fieldType} (x: R) (s: seq R):
  (size (lagrange_basis s x) <= S (size s))%N.
Proof.
  rewrite /lagrange_basis.
  elim: s => [|a s IHs].
  1: by rewrite big_nil size_poly1.
  rewrite big_cons.
  destruct (x == a) eqn:Heq.
  1: {
    move /eqP in Heq.
    by rewrite Heq GRing.subrr GRing.invr0 -mul_polyC polyC0 !GRing.mul0r size_poly0.
  }
  apply negbT in Heq.
  apply: leq_trans.
  1: by apply: size_mul_leq.
  rewrite size_scale.
  - by rewrite (@PolyK R 0) // GRing.oner_neq0.
  - by rewrite GRing.invr_neq0 // GRing.subr_eq0.
Qed.

Lemma lagrange_poly_part_0 {R: fieldType} (x: R) l m r:
  uniq (unzip1 (l ++ (m :: r))) ->
  x \in unzip1 l ->
  (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j).[x] = 0.
Proof.
  elim: r l m => [|m' r IHr] l [x0 y0] Huniq Hin.
  1: by rewrite big_seq1 hornerZ lagrange_basis_0 ?GRing.mulr0.
  rewrite /= big_cons hornerD hornerZ.
  rewrite lagrange_basis_0 ?IHr ?GRing.mulr0 ?GRing.add0r //.
  1: by rewrite -catA cat_cons.
  all: by rewrite /unzip1 map_cat -/unzip1 mem_cat Hin.
Qed.

Lemma uniq_unzip1_in {S T: eqType} (a: S * T) (s: seq (S * T)):
  uniq (unzip1 (a :: s)) ->
  a.1 \notin unzip1 s.
Proof.
  by rewrite /unzip1 map_cons cons_uniq -/unzip1 => /andP [].
Qed.

Lemma lagrange_poly_part_correct {R: fieldType} (x y: R) l m r:
  uniq (unzip1 (l ++ (m :: r))) ->
  (x, y) \in m :: r ->
  (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j).[x] = y.
Proof.
  elim: r l m => [|m' r IHr] l [x0 y0] Huniq Hin.
  1: {
    rewrite big_seq1 hornerZ.
    rewrite mem_seq1 in Hin.
    move /eqP in Hin.
    case: Hin => -> ->.
    rewrite /unzip1 map_cat uniq_catC -/unzip1 /= in Huniq.
    move: Huniq => /andP [Hnotin Huniq].
    rewrite lagrange_basis_1 in Hnotin.
    move /eqP in Hnotin.
    by rewrite Hnotin GRing.mulr1.
  }
  rewrite /= big_cons hornerD hornerZ.
  rewrite in_cons in Hin.
  move: Hin => /orP [/eqP Heq|Hin].
  1: {
    case: Heq => -> ->.
    rewrite lagrange_poly_part_0 ?GRing.addr0 //.
    2: by rewrite -catA cat_cons.
    2: by rewrite /unzip1 map_cat mem_cat Bool.orb_comm mem_seq1 eq_refl.
    rewrite /unzip1 map_cat uniq_catC -map_cat cat_cons -/unzip1 in Huniq.
    apply (uniq_unzip1_in (x0, y0)) in Huniq.
    rewrite /unzip1 map_cat mem_cat Bool.orb_comm -mem_cat -map_cat -/unzip1 in Huniq.
    rewrite lagrange_basis_1 /= in Huniq.
    move /eqP in Huniq.
    by rewrite Huniq GRing.mulr1.
  }
  rewrite IHr //.
  2: by rewrite -catA cat_cons.
  rewrite lagrange_basis_0 ?GRing.mulr0 ?GRing.add0r //.
  apply (map_f fst) in Hin.
  by rewrite /unzip1 map_cat mem_cat Bool.orb_comm Hin.
Qed.

Lemma size_lagrange_poly_part {R: fieldType} l (m: R * R) r:
  (size (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j)%R <= size (l ++ m :: r))%N.
Proof.
  generalize dependent m.
  generalize dependent l.
  elim: r => /= [|m' r IHr] l m.
  1: {
    rewrite big_seq1 size_cat addn1.
    apply: leq_trans.
    1: by apply: size_scale_leq.
    apply: leq_trans.
    - by apply: size_lagrange_basis.
    - by rewrite /unzip1 size_map ltnSn.
  }
  rewrite big_cons.
  apply: leq_trans.
  1: by apply: size_add.
  rewrite geq_max.
  apply /andP.
  split.
  - rewrite /lagrange_poly_part /=.
    apply: leq_trans.
    1: by apply: size_scale_leq.
    replace (size (l ++ [:: m, m' & r])) with (size (unzip1 (l ++ [:: m' & r]))).+1.
    1: by apply: size_lagrange_basis.
    by rewrite /unzip1 size_map !size_cat -addnS.
  - replace (size (l ++ [:: m, m' & r])) with (size ((l ++ [:: m]) ++ m' :: r)).
    1: by apply: IHr.
    by rewrite !size_cat addn1 !addnS.
Qed.

Lemma size_lagrange_poly {R: fieldType} (pts: seq (R * R)):
  (size (lagrange_poly pts) <= size pts)%N.
Proof.
  case: pts => [|m r].
  - by rewrite /lagrange_poly big_nil size_poly0.
  - by apply: (size_lagrange_poly_part [::]).
Qed.

Lemma lagrange_poly_correct {R: fieldType} (x y: R) pts:
  uniq (unzip1 (pts)) ->
  (x, y) \in pts ->
  (lagrange_poly pts).[x] = y.
Proof.
  case: pts => [// | m r] Huniq Hin.
  by apply: lagrange_poly_part_correct.
Qed.

Lemma lagrange_poly_unique {R: fieldType} (pts: seq (R * R)) (q: {poly R}):
  uniq (unzip1 pts) ->
  (size q <= size pts)%N ->
  (forall x y, (x, y) \in pts -> q.[x] = y) ->
  q = lagrange_poly pts.
Proof.
  move=> Huniq Hsize1 Hpred.
  assert (size (q - lagrange_poly pts)%R <= size pts)%N as Hsize.
  1: {
    move: (size_lagrange_poly pts) => Hsize2.
    apply: leq_trans.
    1: apply: size_add.
    by rewrite geq_max size_opp Hsize1 Hsize2.
  }
  apply /eqP.
  rewrite -GRing.subr_eq0 -size_poly_eq0.
  rewrite size_poly_eq0.
  apply /negPn /negP => Hcontra.
  rewrite leqNgt in Hsize.
  move /negP in Hsize.
  apply: Hsize.
  replace (size pts) with (size (unzip1 (pts))).
  2: by rewrite size_map.
  apply: max_poly_roots => //.
  apply /allP => x' /mapP [[x y] Hin Heq].
  subst.
  rewrite /root hornerD hornerN.
  rewrite (Hpred x y) //.
  rewrite (lagrange_poly_correct x y) //.
  by rewrite GRing.subr_eq0 eq_refl.
Qed.

(**
  We also prove some useful properties for how Lagrange polynomials behave when
  added or subtracted, specifically with regards to points with [y = 0], which
  are defined by [zero_points].
  Specifically:
  - [lagrange_sub_zero_cons]: Subtracting Langrange polynomials with similar points.
  - [lagrange_add_zero_cons]: Adding Langrange polynomials where all but one points have [y = 0].
  - [lagrange_zero]: Evaluating Lagrange polynomials where all points have [y = 0].
*)
Definition zero_points {R: ringType} (s: seq R): seq (R * R) :=
  [seq (x, 0) | x <- s ].

Lemma unzip1_zero_points {R: ringType} (s: seq R):
  unzip1 (zero_points s) = s.
Proof.
  rewrite /unzip1 /zero_points.
  elim: s => [// | a s IHs].
  by rewrite !map_cons IHs.
Qed.

Lemma x_in_zero_points {R: ringType} (x y: R) (s: seq R):
  (x, y) \in zero_points s ->
  x \in s.
Proof.
  rewrite /zero_points.
  elim: s => [// | a s IHs] H.
  rewrite in_cons.
  rewrite map_cons in_cons xpair_eqE in H.
  destruct (x == a) eqn:Heq => //=.
  by apply: IHs.
Qed.

Lemma y_in_zero_points {R: ringType} {x y: R} {s: seq R}:
  (x, y) \in zero_points s ->
  y = 0.
Proof.
  rewrite /zero_points.
  elim: s => [// | a s IHs] H.
  rewrite map_cons in_cons in H.
  destruct ((x, y) == (a, 0)) eqn:Heq.
  - move /eqP in Heq.
    by case: Heq.
  - by apply: IHs.
Qed.

Lemma pt_in_zero_points {R: ringType} {x: R} {s: seq R}:
  x \in s ->
  (x, 0) \in zero_points s.
Proof.
  rewrite /zero_points.
  elim: s => [// | a s IHs] H /=.
  rewrite in_cons in H.
  rewrite in_cons.
  destruct (x == a) eqn:Heq.
  - move /eqP in Heq.
    by rewrite Heq eq_refl.
  - by rewrite xpair_eqE Heq IHs.
Qed.

Lemma lagrange_sub_zero {R: fieldType} (x: R) (l1 l2 r: seq (R * R)):
  uniq (unzip1 (l1 ++ r)) ->
  uniq (unzip1 (l2 ++ r)) ->
  x \in unzip1 r ->
  (lagrange_poly (l1 ++ r) - lagrange_poly (l2 ++ r)).[x] = 0.
Proof.
  rewrite hornerD hornerN.
  generalize dependent l2.
  generalize dependent l1.
  elim: r => [// | a r IHr] l1 l2 Huniq1 Huniq2 Hin.
  rewrite /= in_cons in Hin.
  destruct (x == a.1) eqn:Heq.
  - move /eqP in Heq.
    rewrite Heq (lagrange_poly_correct a.1 a.2) //.
    1: rewrite (lagrange_poly_correct a.1 a.2) ?GRing.subrr //.
    all: by rewrite -surjective_pairing mem_cat in_cons eq_refl Bool.orb_true_r.
  - rewrite -!cat_rcons -!cats1 in Huniq1 Huniq2*.
    by apply: IHr.
Qed.

Lemma lagrange_sub_zero_cons {R: fieldType} (x y1 y2: R) (pts: seq (R * R)):
  uniq (x :: unzip1 pts) ->
  lagrange_poly ((x, y1) :: pts) - lagrange_poly ((x, y2) :: pts) =
  lagrange_poly ((x, y1 - y2) :: zero_points (unzip1 pts)).
Proof.
  move=> Huniq.
  apply: lagrange_poly_unique.
  - by rewrite /unzip1 map_cons -/unzip1 unzip1_zero_points.
  - apply: leq_trans.
    1: by apply: size_add.
    rewrite size_opp /= !size_map geq_max.
    apply /andP.
    split.
    all: apply: leq_trans.
    1,3: by apply: size_lagrange_poly.
    all: by [].
  - move=> x0 y0 Hin.
    rewrite in_cons in Hin.
    destruct (_ == _) eqn:Heq.
    + move /eqP in Heq.
      case: Heq => ? ?.
      subst.
      rewrite hornerD hornerN (lagrange_poly_correct x y1) //.
      1: rewrite (lagrange_poly_correct x y2) //.
      all: by rewrite in_cons eq_refl.
    + rewrite (y_in_zero_points Hin).
      rewrite -!(cat1s _ pts).
      apply: lagrange_sub_zero => //.
      by apply: (x_in_zero_points x0 y0).
Qed.

Lemma lagrange_add_zero {R: fieldType} (x: R) (l1 l2: seq (R * R)) (r: seq R):
  uniq (unzip1 (l1 ++ zero_points r)) ->
  uniq (unzip1 (l2 ++ zero_points r)) ->
  x \in r ->
  (lagrange_poly (l1 ++ zero_points r) + lagrange_poly (l2 ++ zero_points r)).[x] = 0.
Proof.
  rewrite hornerD.
  generalize dependent l2.
  generalize dependent l1.
  elim: r => [// | a r IHr] l1 l2 Huniq1 Huniq2 Hin.
  rewrite /= in_cons in Hin.
  destruct (x == a) eqn:Heq.
  - move /eqP in Heq.
    rewrite Heq (lagrange_poly_correct a 0) //.
    1: rewrite (lagrange_poly_correct a 0) ?GRing.addr0 //.
    all: by rewrite mem_cat in_cons eq_refl Bool.orb_true_r.
  - rewrite -!cat_rcons -!cats1 in Huniq1 Huniq2*.
    by apply: IHr.
Qed.

Lemma lagrange_add_zero_cons {R: fieldType} (x y1 y2: R) (s: seq R):
  uniq (x :: s) ->
  lagrange_poly ((x, y1) :: zero_points s) +
  lagrange_poly ((x, y2) :: zero_points s) =
  lagrange_poly ((x, y1 + y2) :: zero_points s).
Proof.
  move=> Huniq.
  apply: lagrange_poly_unique.
  - by rewrite /unzip1 map_cons -/unzip1 unzip1_zero_points.
  - apply: leq_trans.
    1: by apply: size_add.
    rewrite /= !size_map geq_max.
    apply /andP.
    split.
    all: apply: leq_trans.
    1,3: by apply: size_lagrange_poly.
    all: by rewrite /= size_map.
  - move=> x0 y0 Hin.
    rewrite in_cons in Hin.
    destruct (_ == _) eqn:Heq.
    + move /eqP in Heq.
      case: Heq => ? ?.
      subst.
      rewrite hornerD (lagrange_poly_correct x y1) //.
      1: rewrite (lagrange_poly_correct x y2) //.
      2,4: by rewrite in_cons eq_refl.
      all: by rewrite /unzip1 map_cons -/unzip1 unzip1_zero_points.
    + rewrite (y_in_zero_points Hin).
      rewrite -!(cat1s _ (zero_points s)).
      apply: lagrange_add_zero.
      3: by apply: (x_in_zero_points x0 y0).
      all: by rewrite /unzip1 map_cons -/unzip1 unzip1_zero_points.
Qed.

Lemma lagrange_zero {R: fieldType} (s: seq R):
  uniq s ->
  lagrange_poly (zero_points s) = 0.
Proof.
  move=> Huniq.
  symmetry.
  apply: lagrange_poly_unique.
  - by rewrite unzip1_zero_points.
  - by rewrite polyseq0.
  - move=> x y Hin.
    rewrite hornerC.
    by rewrite (y_in_zero_points Hin).
Qed.

(**
  We also define some functions that lets us treat polynomials like lists ending
  in infinite zeroes, and prove some useful lemmas that they do indeed behave
  like lists.
*)
Definition head_poly {R: ringType} (q: {poly R}): R := q`_0.
Definition tail_poly {R: ringType} (q: {poly R}): {poly R} := Poly (behead q).

Lemma head_cons_poly {R: ringType} (a: R) (q: {poly R}):
  head_poly (cons_poly a q) = a.
Proof.
  by rewrite /head_poly coef_cons.
Qed.

Lemma tail_cons_poly {R: ringType} (a: R) (q: {poly R}):
  tail_poly (cons_poly a q) = q.
Proof.
  rewrite /tail_poly polyseq_cons.
  destruct (nilp q) eqn:Heq => /=.
  2: by rewrite polyseqK.
  rewrite /nilp size_poly_eq0 in Heq.
  move /eqP in Heq.
  rewrite Heq polyseqC.
  by destruct (a != 0).
Qed.

Lemma size_tail_poly {R: ringType} (q: {poly R}):
  size (tail_poly q) = (size q).-1.
Proof.
  rewrite /tail_poly.
  case: q => [[|a s] /= Hs].
  - by rewrite polyseq0.
  - by rewrite (PolyK Hs).
Qed.

Lemma last_neq_0 {R: ringType} (a: R) (s: seq R):
  (last a s != 0 -> last 1 s != 0).
Proof.
  case: s => H //=.
  by apply: GRing.oner_neq0.
Qed.

Lemma cons_head_tail_poly {R: ringType} (q: {poly R}):
  cons_poly (head_poly q) (tail_poly q) = q.
Proof.
  apply: poly_inj.
  rewrite /head_poly /tail_poly polyseq_cons.
  case: q => [[|a s] /= Hs].
  1: by rewrite polyseq0.
  rewrite (PolyK Hs).
  destruct s => //=.
  by rewrite polyseqC Hs.
Qed.

Lemma cons_eq_head_tail_poly {R: ringType} (a: R) (q: {poly R}):
  a = head_poly q ->
  cons_poly a (tail_poly q) = q.
Proof.
  move=> H.
  by rewrite H cons_head_tail_poly.
Qed.

(**
  We also prove two polynomials are equal if, and only if, all their
  coefficients are equal.
  This is then used to prove how [tail_poly] and [cons_poly] behaves when added
  and negated.
*)
Lemma coef_poly_eq {R: ringType} (q1 q2: {poly R}):
  (forall i, q1`_i = q2`_i) <-> q1 = q2.
Proof.
  split=> H.
  2: by rewrite H.
  apply: poly_inj.
  move: H.
  case: q2.
  case: q1.
  elim=> [|a1 s1 IHs1] Hs1 [|a2 s2 ] //= Hs2 H.
  - move /eqP in Hs2.
    destruct Hs2.
    specialize (H (size s2)).
    rewrite nth_nil nth_last in H.
    by rewrite H.
  - move /eqP in Hs1.
    destruct Hs1.
    specialize (H (size s1)).
    rewrite nth_nil nth_last in H.
    by rewrite -H.
  - move: (fun i => H i.+1) => HS.
    specialize (H 0%N).
    simpl in *.
    rewrite H.
    f_equal.
    apply: IHs1 => //.
    all: apply: last_neq_0.
    + by apply: Hs1.
    + by apply: Hs2.
Qed.

Lemma tail_poly_add {R: ringType} (q1 q2: {poly R}):
  tail_poly (q1 + q2) = tail_poly q1 + tail_poly q2.
Proof.
  apply coef_poly_eq => i.
  by rewrite coefD !coef_Poly !nth_behead coefD.
Qed.

Lemma tail_poly_opp {R: ringType} (q: {poly R}):
  tail_poly (-q) = -tail_poly q.
Proof.
  apply coef_poly_eq => i.
  by rewrite coefN !coef_Poly !nth_behead coefN.
Qed.

Lemma cons_poly_add {R: ringType} (m m': R) (q1 q2: {poly R}):
  (cons_poly m' (q1 + q2) = (cons_poly m q1) + cons_poly (m'-m) q2)%R.
Proof.
  apply coef_poly_eq => i.
  rewrite coefD !coef_cons coefD.
  case: i => //=.
  by rewrite GRing.addrC -GRing.addrA GRing.addNr GRing.addr0.
Qed.

Local Open Scope nat_scope.

(**
  With the work on polynomials out of the way we can start to actually define
  the scheme.
*)
Section ShamirSecretSharing_example.

(**
  [p] is the number of possible messages. It is is a [prime]. *)
Variable (p: nat).

Context (p_prime: prime p).

(**
  We have to use [(Zp_trunc (pdiv p)).+2] for [Word] to be considered a field.
  This is important for uniqueness of Lagrange polynomials.
*)
Definition Word_N := (Zp_trunc (pdiv p)).+2.
Definition Word := 'fin Word_N.

Lemma words_p_eq:
  Word_N = p.
Proof.
  by apply: Fp_cast.
Qed.

(**
  Shares are simply a point in ['F_p], i.e. a pair.
*)
Definition Share: choice_type := Word × Word.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Notation " 'share " := (Share) (in custom pack_type at level 2).
Notation " 'share " := (Share) (at level 2): package_scope.

(**
  We can't use sequences directly in [choice_type] so instead we use a map from
  natural numbers to the type.
*)
Definition chSeq t := chMap 'nat t.

Notation " 'seq t " := (chSeq t) (in custom pack_type at level 2).
Notation " 'seq t " := (chSeq t) (at level 2): package_scope.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

(**
  [n] is the number of shares.
  It is always positive.
*)
Variable (n: nat).
Context (n_positive: Positive n).

(**
  We cannot possibly have more than [p-1] shares.
*)
Context (n_ltn_p: n < p).

(**
  Each party gets a share.
  We use a finity type to represent parties as it makes later proofs easier.
*)
Definition Party := 'fin n.

Notation " 'party " := (Party) (in custom pack_type at level 2).
Notation " 'party " := (Party) (at level 2): package_scope.

(**
  The share of each party is the point with [x = 1 + the party index].
*)
#[program]
Definition party_to_word (x: Party): Word := @Ordinal _ x.+1 _.
Next Obligation.
  case: x => [x Hx] /=.
  rewrite words_p_eq.
  apply: leq_trans.
  2: by apply: n_ltn_p.
  by rewrite ltnS.
Qed.

(**
  Finally we can define how actual shares are computed.
  They are simply points on a polynomial [q].
*)
Definition make_share (q: {poly Word}) (x: Party): Share :=
  (party_to_word x, q.[party_to_word x]).

(**
  This is a convenience function for computing the shares for a message [m].
  [q] is a randomly sampled polynomial.
*)
Definition make_shares (m: Word) (q: {poly Word}) (U: seq Party): seq Share :=
  map (make_share (cons_poly m q)) U.

(**
  In order to prove security in SSProve we need to define a bijection
  The bijection between polynomials works like this:
  1. We compute the shares for the parties [U], message [m] and random
     polynomial [q].
  2. Then we compute two Lagrange polynomials, [g] and [g'], through those
     shares and, respectively, (0, m) and (0, m').
  3. We then compute the tail of [g' - g] and add it to [q] giving us [q'].

  It is secure, because [make_shares m' q' U] will yield the same [sh].

  It is a bijection, because we can compute [sh] from [q'], from which we can
  compute [g] and [g'], from which [q = q' - tail_poly (g' - g)].

  [sec_poly_bij] and [bij_poly_bij] simply formalise the above intuitions.
*)
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
  apply /andP.
  split => //.
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

Lemma sec_poly_bij_part (x: Party) (U: seq Party) (m m': Word) (q: {poly Word}):
  uniq U ->
  x \in U ->
  (cons_poly m' (poly_bij U m m' q)).[party_to_word x] =
  (cons_poly m                   q ).[party_to_word x].
Proof.
  move=> Huniq Hin.
  rewrite (cons_poly_add m).
  rewrite lagrange_sub_zero_cons.
  2: by rewrite /= no_zero_share uniq_make_shares.
  rewrite hornerD cons_eq_head_tail_poly.
  2: {
    rewrite /head_poly -horner_coef0.
    rewrite (lagrange_poly_correct 0 (m' - m)) //.
    - by rewrite /unzip1 /= -/unzip1 unzip1_zero_points no_zero_share uniq_make_shares.
    - by rewrite in_cons eq_refl.
  }
  rewrite (lagrange_poly_correct (party_to_word x) 0%R) ?GRing.addr0 //.
  - by rewrite /unzip1 /= -/unzip1 unzip1_zero_points no_zero_share uniq_make_shares.
  - by rewrite in_cons pt_in_zero_points ?Bool.orb_true_r // in_make_shares.
Qed.

Lemma sec_poly_bij_rec (l r: seq Party) (m m': Word) (q: {poly Word}):
  uniq (l ++ r) ->
  make_shares m' (poly_bij (l ++ r) m m' q) r =
  make_shares m                          q  r.
Proof.
  elim: r => [// | a r IHr] in l*.
  rewrite -cat_rcons -cats1 /= => H.
  rewrite IHr //.
  rewrite /make_share sec_poly_bij_part //.
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
  rewrite {1}/poly_bij.
  rewrite sec_poly_bij //.
  rewrite /poly_bij.
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
  Positive (p^t).
Proof.
  by rewrite /Positive expn_gt0 prime_gt0.
Qed.

(**
  [PolyEnc] is an isomorphism we use to be able to represent polynomials in SSProve.
  SSProve does not support using polynomials directly.
  There are [p^t] polynomials of size [<= t] over the field ['F_p].

  We want to sample [q] uniformly, but this is not directly possible in SSProve.
  Instead we sample from [PolyEnc t] which is isomorphic to polynomials of
  size [<= t] over ['F_p].

  We then define a bijection between polynomials and [PolyEnc t] and vice versa.
  Finally we combine all three bijections to create a bijection from [PolyEnc t]
  to [PolyEnc t] that we can use to prove security of the protocol.
*)
Definition PolyEnc t := 'fin (p^t).

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
  poly_to_nat t q < p^t.
Proof.
  elim: t => [// | t IHt] /= in q*.
  apply: (@leq_trans (poly_to_nat t (tail_poly q) * p + p)).
  2: by rewrite expnSr -mulSnr leq_pmul2r // prime_gt0.
  case: (head_poly q) => a Ha /=.
  by rewrite ltn_add2l -words_p_eq.
Qed.

Lemma nat_poly_nat (t a: nat):
  a < p^t ->
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
    move /eqP in H.
    by subst.
  }
  rewrite /= mod_p_muln_p.
  rewrite divnMDl ?prime_gt0 // divn_small.
  2: {
    destruct (head_poly q) as [c Hc] => /=.
    by rewrite -words_p_eq.
  }
  rewrite addn0 IHt ?cons_head_tail_poly //.
  rewrite size_tail_poly.
  by destruct (size q).
Qed.

(**
  [t] is the number of shares needed for reconstruction.
  [t'] is the maximum number of shares the scheme is secure against. This
  happens to often be the number we actually care about so we will frequently
  use it directly.
*)
Variable (t': nat).
Definition t := t'.+1.

(**
  This is the final bijection used to
*)
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
  exists (share_bij U m' m) => q.
  all: apply: ord_inj.
  all: rewrite /= poly_nat_poly ?size_poly_bij ?size_nat_to_poly //.
  all: by rewrite bij_poly_bij ?nat_poly_nat.
Qed.

Local Open Scope package_scope.

Definition shares: nat := 0.

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
      q <$ uniform (p^t') ;;
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
      q <$ uniform (p^t') ;;
      let q := nat_to_poly t' q in
      let sh := make_shares mr q (domm U) in
      ret (fmap_of_seq sh)
    }
  ].

Definition SHARE := mkpair SHARE_pkg_tt SHARE_pkg_ff.

Lemma SHARE_equiv:
  SHARE true ≈₀ SHARE false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  case: m => [[ml mr] U].
  destruct (t <= size _) eqn:Heq.
  1: by apply: rreflexivity_rule.
  apply negbT in Heq.
  rewrite -ltnNge ltnS in Heq.
  apply: r_uniform_bij => [|q].
  1: {
    apply: (bij_share_bij (domm U) ml mr) => //.
    by apply: uniq_fset.
  }
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
