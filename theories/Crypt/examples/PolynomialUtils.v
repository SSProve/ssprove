(******************************************************************************)
(* Proof of different properties of polynomials, more concretely around       *)
(* the existence and uniqueness of the Lagrange polynomial.                   *)
(* We also formalise Theorem 3.8 from the book "The joy of cryptography"      *)
(*                                                                            *)
(*                                                                            *)
(* The Lagrange interpolation polynomial for a set of d+1 points:             *)
(*                                                                            *)
(*   {(x_1, y_1), ..., (x_d+1, y_d+1)} where x_i != x_j                       *)  
(*                                                                            *)
(* Is the polinomial defined as:                                              *)
(*                                                                            *)
(*   f(x) = y_1 * l_1(x) + ... + y_d+1 * l_d+1(x)                                *)
(*                                                                            *)
(* where each of the l_i(x) is defined as:                                    *)
(*                                                                            *)
(* l_i(x) = (x-x_1) * (x-x_2) *...* (x-x_i-1) * (x-x_i+1)* ... * (x-x_d+1)    *)
(*           --------------------------------------------------------------   *)
(*                         (x_i-x_1) * ... * (x_i-x_d+1)                      *)
(*                                                                            *)
(*                                                                            *)
(* Section Lagrange_Poly                                                      *)
(*     lagrange_poly pts == given a set of points(pts) it returns the         *)
(*                          lagrange polynomial(f(x)).                        *)
(*    lagrange_basis s x == returns each of the l_i(x) given x = x_i and      *)
(*                          s = [x_1; x_2; ... ; x_d+1].                      *)
(*  lagrange_poly_part j == returns y_i * l_i(x) for a certain j =            *)
(*                          ((x_i, y_i), [(x_1, y_1), ..., (x_d+1, y_d+1)]).  *)
(*             subseqs s == returns a list of pairs where each pair           *)
(*                          represents a point(first) and the list of the     *)
(*                          rest of the points needed for calculating l_i(x). *)
(*                          E.g:                                              *)   
(*                          subseqs [(1,2); (2,3); (3, 4)] =                  *)
(*                          [((1,2), [(2,3);(3,4)]);                          *)
(*                           ((2,3), [(1,2) ;(3,4)]);                         *)
(*                           ((3,4), [(1,2); (2,3))])                         *)
(*                          ]                                                 *)
(*         zero_points s == given a sequence returns a sequence of pairs      *)
(*                          where the first element of each pair is the       *)
(*                          elements of s in the same order as in s and the   *)
(*                          second element is always zero                     *)
(*           head_poly p == returns the head of the list resulting from       *)
(*                          interpreting the polynomial p as a list ending    *)
(*                          with infinite zeroes                              *)
(*           tail_poly p == returns the tail of the list resulting from       *)
(*                          interpreting the polynomial p as a list ending    *)
(*                          with infinite zeroes                              *)
(*                                                                            *)
(******************************************************************************)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.

Definition dif_points {A : eqType} { B : Type} (l : seq (A * B)) := 
  (uniq (unzip1 l)).

Ltac simpl_dif_point :=
  rewrite /dif_points /unzip1 ?map_cons ?map_cat ?cons_uniq -?/unzip1.

Section Lagrange_Poly. 

Definition lagrange_basis {R: unitRingType} (s: seq R) (x: R): {poly R} :=
  \prod_(c <- s) ((x-c)^-1 *: Poly [:: -c ; 1]).

Definition lagrange_poly_part {R: unitRingType} 
  (j: R * R * seq (R * R)): {poly R} :=
    j.1.2 *: lagrange_basis (unzip1 j.2) j.1.1.

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

Definition lagrange_poly {R: unitRingType} (pts: seq (R * R)): {poly R} :=
  \sum_(j <- subseqs pts) lagrange_poly_part j.

(**
  We prove some fundamental properties of Lagrange Interpolation.
  Specifically:
  - [size_lagrange_poly]: The size of a Lagrange polynomial is [<= size pts].
  - [lagrange_poly_correct]: Evaluating a Lagrange polynomial at a point gives 
    the corresponding y value.
  - [lagrange_poly_unique]: There is exactly one polynomial with size 
    [<= size pts], that satisfies [lagrange_poly_correct].

  These together formalise Theorem 3.8 and 3.9 from the book
*)

(* If we evaluate l_i(x) for any of the points used to build it, we obtain 0 *)
Lemma lagrange_basis_0 {R: comUnitRingType} (x1 x: R) (s: seq R):
  x \in s ->
  (lagrange_basis s x1).[x] = 0.
Proof.
  rewrite /lagrange_basis.
  elim: s => [// | a s IHs].
  rewrite in_cons big_cons hornerM hornerZ.
  rewrite !horner_cons hornerC GRing.mul0r GRing.add0r GRing.mul1r.
  case Heq: (x == a).
  - move: Heq => /eqP-Heq.
    by rewrite Heq GRing.subrr GRing.mulr0 GRing.mul0r.
  - move=> H.
    by rewrite IHs // GRing.mulr0.
Qed.

(* If we evaluate l_i(x) for the point x_i we obtain 1 *)
Lemma lagrange_basis_1 {R: fieldType} (x: R) (s: seq R):
  (x \notin s) = ((lagrange_basis s x).[x] == 1).
Proof.
  rewrite /lagrange_basis.
  elim: s => [|a s IHs].
  - rewrite big_nil hornerC.
    by rewrite eq_refl.
  - rewrite in_cons big_cons hornerM hornerZ.
    rewrite !horner_cons hornerC GRing.mul0r GRing.add0r GRing.mul1r.
    case Heq: (x == a).
    + move: Heq => /eqP-Heq.
      rewrite Heq GRing.subrr GRing.mulr0 GRing.mul0r eq_sym.
      by rewrite GRing.oner_eq0.
    + move: Heq => /negbT-Heq.
      move: Heq; rewrite -GRing.subr_eq0 => Heq.
      by rewrite GRing.mulVf // GRing.mul1r IHs.
Qed.

(* The size of l_i(x) polynomial is <= size of the sequence is built uppon. *)
Lemma size_lagrange_basis {R: fieldType} (x: R) (s: seq R):
  (size (lagrange_basis s x) <= (size s).+1)%N.
Proof.
  rewrite /lagrange_basis.
  elim: s => [|a s IHs].
  1: by rewrite big_nil size_poly1.
  rewrite big_cons.
  case Heq: (x == a).
  - move: Heq => /eqP-Heq. rewrite Heq.
    rewrite GRing.subrr GRing.invr0.
    rewrite -mul_polyC polyC0 !GRing.mul0r.
    by rewrite size_poly0.
  - move: Heq => /negbT-Heq.
    apply: leq_trans.
    1: by apply: size_mul_leq.
    rewrite size_scale.
    + by rewrite (@PolyK R 0) // GRing.oner_neq0.
    + by rewrite GRing.invr_neq0 // GRing.subr_eq0.
Qed.

(*
   Proof that when we construct (partially) our polynomial, the evaluation for 
   an x_i in the list is zero.
*)
Lemma lagrange_poly_part_0 {R : fieldType} (x: R) (l : seq (R * R)) m r:
  x \in unzip1 l ->
  (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j).[x] = 0.
Proof.
  elim: r l m => [|m' r IHr] l [x0 y0] Hin.
  1: by rewrite big_seq1 hornerZ lagrange_basis_0 ?GRing.mulr0.
  rewrite /= big_cons hornerD hornerZ.
  rewrite lagrange_basis_0 ?IHr ?GRing.mulr0 ?GRing.add0r //;
  simpl_dif_point; by rewrite mem_cat Hin.
Qed.

Lemma uniq_unzip1_in {S T: eqType} (a: S * T) (s: seq (S * T)):
  dif_points (a :: s) ->
  a.1 \notin unzip1 s.
Proof.
  rewrite /dif_points. simpl_dif_point.
  by move => /andP [].
Qed.

(**
   If we have a list of different points (l ++ m :: r) and (x, y) \in m::r
   we have that the sum over the j <- (subseqs_rec l m r) of the l_j(x) when 
   evaluated in x is equal to y. 
*)
Lemma lagrange_poly_part_correct {R: fieldType} (x y: R) l m r:
  dif_points (l ++ (m :: r)) ->
  (x, y) \in m :: r ->
  (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j).[x] = y.
Proof.
  elim: r l m => [|m' r IHr] l [x0 y0] Huniq Hin.
  - rewrite big_seq1 hornerZ.
    move: Hin. rewrite mem_seq1 => /eqP-Hin.
    case: Hin => -> ->.
    move: Huniq. simpl_dif_point.
    rewrite uniq_catC -/unzip1 /= => Huniq.
    move: Huniq => /andP [Hnotin Huniq].
    move: Hnotin. rewrite lagrange_basis_1 => /eqP-Hnotin.
    by rewrite Hnotin GRing.mulr1.

  - rewrite /= big_cons hornerD hornerZ.
    move: Hin. rewrite in_cons => /orP [/eqP Heq|Hin].
    + case: Heq => -> ->.
      rewrite lagrange_poly_part_0 ?GRing.addr0 //.
      2: by rewrite /unzip1 map_cat mem_cat Bool.orb_comm mem_seq1 eq_refl.
      move: Huniq. 
      rewrite /dif_points /unzip1 map_cat uniq_catC -map_cat cat_cons -/unzip1.
      move => /(uniq_unzip1_in (x0, y0))-Huniq.
      move: Huniq;
      rewrite /unzip1 map_cat mem_cat Bool.orb_comm -mem_cat -map_cat -/unzip1;
      move => Huniq.
      move: Huniq; rewrite lagrange_basis_1 /= => /eqP-Huniq.
      by rewrite Huniq GRing.mulr1.
    + rewrite IHr //.
      2: by rewrite -catA cat_cons.
      rewrite lagrange_basis_0 ?GRing.mulr0 ?GRing.add0r //.
      move: Hin => /(map_f fst)-Hin.
      rewrite /unzip1 map_cat mem_cat Bool.orb_comm.
      by rewrite Hin.
Qed.

(**
   Proof that the size of a Lagrange polynomial is [<= size pts] for
   the second recursive case. 
*)
Lemma size_lagrange_poly_part {R: fieldType} l (m: R * R) r:
  (size (\sum_(j <- subseqs_rec l m r) lagrange_poly_part j)%R 
    <= size (l ++ m :: r))%N.
Proof.
  generalize dependent m.
  generalize dependent l.
  elim: r => /= [|m' r IHr] l m.
  - rewrite big_seq1 size_cat addn1.
    apply: leq_trans.
    1: by apply: size_scale_leq.
    apply: leq_trans.
    + by apply: size_lagrange_basis.
    + by rewrite /unzip1 size_map ltnSn.
  - rewrite big_cons.
    apply: leq_trans.
    1: by apply: size_add.
    rewrite geq_max.
      apply /andP; split.
      + rewrite /lagrange_poly_part /=.
        apply: leq_trans.
        1: by apply: size_scale_leq.
        have: 
          size (l ++ [:: m, m' & r]) = (size (unzip1 (l ++ [:: m' & r]))).+1.
        1: by rewrite /unzip1 size_map !size_cat -addnS.
        by move => Heq; rewrite Heq; apply: size_lagrange_basis.
      + have : size (l ++ [:: m, m' & r]) = size ((l ++ [:: m]) ++ m' :: r).
        1: by rewrite !size_cat addn1 !addnS.
        by move => H; rewrite H; apply: IHr.
Qed.

(* The size of a Lagrange polynomial is [<= size pts]. *)
Lemma size_lagrange_poly {R: fieldType} (pts: seq (R * R)):
  (size (lagrange_poly pts) <= size pts)%N.
Proof.
  case: pts => [|m r].
  - by rewrite /lagrange_poly big_nil size_poly0.
  - by apply: (size_lagrange_poly_part [::]).
Qed.

(* Evaluating a Lagrange polynomial at a point gives the corresponding y value. *)
Lemma lagrange_poly_correct {R: fieldType} (x y: R) pts:
  dif_points pts ->
  (x, y) \in pts ->
  (lagrange_poly pts).[x] = y.
Proof.
  case: pts => [// | m r] Huniq Hin.
  by apply: lagrange_poly_part_correct.
Qed.

(**
   There is exactly one polynomial with size [<= size pts], that satisfies [lagrange_poly_correct].
   This is a stronger version of Theorem 3.9 of the book.
*)
Lemma lagrange_poly_unique {R: fieldType} (pts: seq (R * R)) (q: {poly R}):
  dif_points pts ->
  (size q <= size pts)%N ->
  (forall x y, (x, y) \in pts -> q.[x] = y) ->
  q = lagrange_poly pts.
Proof.
  move=> Huniq Hsize1 Hpred.
  have Hsize : (size (q - lagrange_poly pts)%R <= size pts)%N.
  - move: (size_lagrange_poly pts) => Hsize2.
    apply: leq_trans.
    1: apply: size_add.
    by rewrite geq_max size_opp Hsize1 Hsize2.
  - apply /eqP.
    rewrite -GRing.subr_eq0 -size_poly_eq0.
    rewrite size_poly_eq0.
    apply /negPn /negP => Hcontra.
    move : Hsize; rewrite leqNgt => /negP-Hsize.
    apply: Hsize.
    have : size pts = size (unzip1 (pts)).
    1: by rewrite size_map.
    move => Hsize2; rewrite Hsize2.
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
  elim: s => [// | a s IHs] Hin.
  rewrite in_cons.
  move: Hin; rewrite map_cons in_cons xpair_eqE => Hin.
  case Heq : (x == a) => //=.
  move: Hin; by rewrite Heq /=.
Qed.

Lemma y_in_zero_points {R: ringType} {x y: R} {s: seq R}:
  (x, y) \in zero_points s ->
  y = 0.
Proof.
  rewrite /zero_points.
  elim: s => [// | a s IHs] H.
  rewrite map_cons in_cons in H.
  case Heq : ((x, y) == (a, 0)) H.
  - move : Heq => /eqP-/pair_equal_spec-Heq.
    case Heq => Heqx Heqy. 
    by rewrite Heqy /=.
  - move => /=-Hneq.
    apply: IHs.
    by rewrite Hneq. 
Qed.

Lemma pt_in_zero_points {R: ringType} {x: R} {s: seq R}:
  x \in s ->
  (x, 0) \in zero_points s.
Proof.
  rewrite /zero_points.
  elim: s => [// | a s IHs] H /=.
  rewrite in_cons in H.
  rewrite in_cons.
  case Heq : (x == a).
  - move : Heq => /eqP-Heq.
    by rewrite Heq eq_refl.
  - rewrite xpair_eqE Heq /=. 
    apply: IHs.
    move : H.
    by rewrite Heq /=.
Qed.

Lemma lagrange_sub_zero {R: fieldType} (x: R) (l1 l2 r: seq (R * R)):
  dif_points (l1 ++ r) ->
  dif_points (l2 ++ r) ->
  x \in unzip1 r ->
  (lagrange_poly (l1 ++ r) - lagrange_poly (l2 ++ r)).[x] = 0.
Proof.
  rewrite hornerD hornerN.
  generalize dependent l2.
  generalize dependent l1.
  elim: r => [// | a r IHr] l1 l2 Huniq1 Huniq2.
  rewrite in_cons.
  case Heq : (x == a.1).
  - move : Heq => /eqP-Heq. 
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
  - simpl_dif_point. by rewrite unzip1_zero_points.
  - apply: leq_trans.
    1: by apply: size_add.
    rewrite size_opp /= !size_map geq_max.
    apply /andP.
    split.
    all: apply: leq_trans.
    1,3: by apply: size_lagrange_poly.
    all: by [].
  - move=> x0 y0 Hin.
    move: Hin; rewrite in_cons => Hin.
    case Heq: ((x0, y0) == (x, y1 - y2)).
    + move: Heq => /eqP-Heq.
      case: Heq => ? ?.
      subst.
      rewrite hornerD hornerN (lagrange_poly_correct x y1) //.
      1: rewrite (lagrange_poly_correct x y2) //.
      all: by rewrite in_cons eq_refl.
    + move: Hin; rewrite Heq => Hin.
      rewrite (y_in_zero_points Hin).
      rewrite -!(cat1s _ pts).
      apply: lagrange_sub_zero => //.
      by apply: (x_in_zero_points x0 y0).
Qed.

Lemma lagrange_add_zero {R: fieldType} (x: R) (l1 l2: seq (R * R)) (r: seq R):
  dif_points (l1 ++ zero_points r) ->
  dif_points (l2 ++ zero_points r) ->
  x \in r ->
  (lagrange_poly (l1 ++ zero_points r) + lagrange_poly (l2 ++ zero_points r)).[x] = 0.
Proof.
  rewrite hornerD.
  generalize dependent l2.
  generalize dependent l1.
  elim: r => [// | a r IHr] l1 l2 Huniq1 Huniq2.
  rewrite /= in_cons => Hin.
  case Heq: (x == a).
  - move: Heq => /eqP-Heq.
    rewrite Heq (lagrange_poly_correct a 0) //.
    1: rewrite (lagrange_poly_correct a 0) ?GRing.addr0 //.
    all: by rewrite mem_cat in_cons eq_refl Bool.orb_true_r.
  - rewrite -!cat_rcons -!cats1 in Huniq1 Huniq2 *.
    move: Hin; rewrite Heq => Hin. 
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
  - simpl_dif_point. by rewrite unzip1_zero_points.
  - apply: leq_trans.
    1: by apply: size_add.
    rewrite /= !size_map geq_max.
    apply/andP.
    split.
    all: apply: leq_trans.
    1,3: by apply: size_lagrange_poly.
    all: by rewrite /= size_map.
  - move=> x0 y0 Hin.
    move: Hin; rewrite in_cons => Hin.
    case Heq: ((x0, y0) == (x, y1 + y2)).
    + move: Heq => /eqP Heq.
      case: Heq => ? ?.
      subst.
      rewrite hornerD (lagrange_poly_correct x y1) //.
      1: rewrite (lagrange_poly_correct x y2) //.
      2,4: by rewrite in_cons eq_refl.
      all: simpl_dif_point; by rewrite unzip1_zero_points.
    + move: Hin; rewrite Heq => Hin.
      rewrite (y_in_zero_points Hin).
      rewrite -!(cat1s _ (zero_points s)).
      apply: lagrange_add_zero.
      3: by apply: (x_in_zero_points x0 y0).
      all: simpl_dif_point; by rewrite unzip1_zero_points.
Qed.

Lemma lagrange_zero {R: fieldType} (s: seq R):
  uniq s ->
  lagrange_poly (zero_points s) = 0.
Proof.
  move=> Huniq.
  symmetry.
  apply: lagrange_poly_unique.
  - simpl_dif_point. by rewrite unzip1_zero_points.
  - by rewrite polyseq0.
  - move=> x y Hin.
    rewrite hornerC.
    by rewrite (y_in_zero_points Hin).
Qed.

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
  case Heq: (nilp q). 
  2: by rewrite polyseqK.
  move: Heq; rewrite /nilp size_poly_eq0 => /eqP-Heq.
  rewrite Heq polyseqC.
  by case: (a != 0).
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
  move: Hs; case s => //= Hs.
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
  Proof that two polynomials are equal if, and only if, all their
  coefficients are equal.

  Used to prove how [tail_poly] and [cons_poly] behaves when added
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
  - move: Hs2 => /eqP-Hs2.
    case Hs2. specialize (H (size s2)).
    move: H; rewrite nth_nil nth_last => H.
    by rewrite H.
  - move: Hs1 => /eqP Hs1.
    case Hs1. specialize (H (size s1)).
    move: H; rewrite nth_nil nth_last => H.
    by rewrite -H.
  - move: (fun i => H i.+1) => HS.
    specialize (H 0%N). move: IHs1 H => /= IHs1 H.
    rewrite H. f_equal.
    apply: IHs1 => //.
    all: apply: last_neq_0.
    + by apply: Hs1.
    + by apply: Hs2.
Qed.

Lemma tail_poly_add {R: ringType} (q1 q2: {poly R}):
  tail_poly (q1 + q2) = tail_poly q1 + tail_poly q2.
Proof.
  apply/coef_poly_eq; move => i.
  by rewrite coefD !coef_Poly !nth_behead coefD.
Qed.

Lemma cons_poly_add {R: ringType} (m m': R) (q1 q2: {poly R}):
  (cons_poly m' (q1 + q2) = (cons_poly m q1) + cons_poly (m'-m) q2)%R.
Proof.
  apply/coef_poly_eq; move => i.
  rewrite coefD !coef_cons coefD.
  case: i => //=.
  by rewrite GRing.addrC -GRing.addrA GRing.addNr GRing.addr0.
Qed.

End Lagrange_Poly.