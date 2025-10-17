From Coq Require Import Utf8 Lia.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal NominalPrelude TotalProbability.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.
#[local] Open Scope package_scope.


Definition unif (n : nat) : code emptym emptym nat := locked {code
  match n with
  | 0 => ret 0
  | S n' => x ← sample uniform (S n') ;; ret (nat_of_ord x)
  end }.

#[export] Instance Lossless_unif {n} : LosslessCode (unif n).
Proof.
  case n.
  - rewrite /unif -lock. exact _.
  - intros n'. rewrite /unif -lock.
    apply Lossless_sample; [| exact _ ].
    apply LosslessOp_uniform.
Qed.

Lemma eq_sum_sum {n} {F : nat → R} :
  (\sum_i F (@nat_of_ord n i)
  = \sum_(0 <= i < n) F i)%R.
Proof.
  induction n.
  - rewrite big_nil big_ord0 //.
  - by rewrite big_ord_recr big_nat_recr //= IHn.
Qed.

Lemma dlet_uniform {Y : choiceType} {n} `{H : Positive n}
  {f : _ → distr R Y} {y : Y} :
  (\dlet_(x <- (@uniform n H).π2) f x) y = ((\sum_x f x y) / n%:~R)%R.
Proof.
  rewrite dletE psum_fin.
  rewrite GRing.mulr_suml.
  apply eq_bigr => /= i _.
  rewrite /UniformDistrLemmas.r card_ord /=.
  rewrite GRing.mul1r GRing.mulrC.
  rewrite Num.Theory.ger0_norm //.
  apply Num.Theory.mulr_ge0 => //.
  rewrite Num.Theory.invr_ge0.
  rewrite ler0z //.
Qed.

Lemma Pr_RAND_unif {n} {A} `{IsAdversary (IPICK nat) A} :
  (Pr' (A ∘ RAND (unif n)) true *+ n
      = \sum_(0 <= i < n) Pr' (A ∘ @PICK nat i) true)%R.
Proof.
  destruct n.
  1: rewrite GRing.mulr0n big_nil //.
  rewrite -> TotalProbability; try exact _.
  rewrite /unif -lock Pr_rand_sample.
  rewrite dlet_dlet.
  under dlet_f_equal.
  1: intros x; rewrite Pr_rand_ret; rewrite dlet_unit_ext; over.
  rewrite dlet_uniform.
  rewrite -eq_sum_sum.
  rewrite -(GRing.Theory.mulr_natr (_ / _)%R n.+1).
  rewrite -GRing.mulrA.
  rewrite GRing.mulVf ?GRing.mulr1 //.
  apply /eqP => H0.
  erewrite <- GRing.mul0rn in H0.
  apply Num.Theory.pmulrnI in H0 => //.
  move: (GRing.oner_eq0 R) => /eqP //.
Qed.

Lemma Adv_PICK_hybrid {I} {n : nat} {A R R'} `{IsAdversary I A}
  `{IsPackage (IPICK nat) I R} `{IsPackage (IPICK nat) I R'}
  : (∀ i, i < n → perfect I (R' ∘ PICK i) (R ∘ PICK i.+1))
  → (Adv (R ∘ PICK 0%N) (R ∘ PICK n) A
  = Adv (R ∘ RAND (unif n)) (R' ∘ RAND (unif n)) A *+ n)%R.
Proof.
  intros IH.
  do 2 (rewrite -> Adv_sym; symmetry).
  rewrite /Adv -Num.Theory.normrMn.
  rewrite <- (@GRing.mulr_natr Axioms.R).
  rewrite GRing.mulrBl.
  do 2 rewrite -> (@GRing.mulr_natr Axioms.R).
  symmetry.
  do 2 (rewrite -> sep_link_assoc, Pr_RAND_unif).
  rewrite <- (GRing.telescope_sumr (fun i => Pr' (A ∘ R ∘ PICK i) true)) => //.
  rewrite GRing.sumrB.
  do 2 f_equal.
  - rewrite 2!big_nat.
    apply eq_bigr => i /andP [_ H].
    rewrite <- sep_link_assoc.
    by apply Adv_Pr, IH.
  - f_equal. apply eq_bigr => i _.
    by rewrite <- sep_link_assoc.
Qed.

Lemma Adv_hybrid {IMulti IGame} {n : nat} {Multi Game : bool → nom_package}
  {H A : nom_package} `{IsAdversary IMulti A} `{∀ b, IsGame IGame (Game b)}
  `{IsPackage (unionm IGame (IPICK 'nat)) IMulti H}
  : perfect IMulti (Multi true) (H ∘ (Game true || PICK 0))
  → perfect IMulti (Multi false) (H ∘ (Game true || PICK n))
  → (∀ i : 'nat, i < n →
    perfect IMulti (H ∘ (Game false || PICK i )) (H ∘ (Game true || PICK i.+1)))
  → AdvOf Multi A = (AdvOf Game (A ∘ H ∘ (ID IGame || RAND (unif n))) *+ n)%R.
Proof.
  intros p p' p''.
  rewrite (Adv_perfect_l p) (Adv_perfect_r p').
  rewrite (sep_par_factor_game_l (P' := PICK 0)).
  rewrite (sep_par_factor_game_l (P' := PICK n)).
  rewrite 2!sep_link_assoc.
  erewrite @Adv_PICK_hybrid.
  5: {
    intros i; specialize (p'' i).
    rewrite (sep_par_factor_game_l (P' := PICK i)) in p''.
    rewrite (sep_par_factor_game_l (P' := PICK i.+1)) in p''.
    do 2 rewrite -> sep_link_assoc in p''.
    exact p''.
  }
  2-4: ssprove_valid.
  do 2 rewrite <- sep_link_assoc.
  erewrite <- sep_par_factor_game_l.
  2,3: ssprove_valid.
  erewrite <- sep_par_factor_game_l.
  2,3: ssprove_valid.
  rewrite (sep_par_factor_game_r (P := Game true)).
  rewrite (sep_par_factor_game_r (P := Game false)).
  rewrite 2!Adv_reduction sep_link_assoc //.
Qed.

Lemma Adv_hybrid_dep {IGame} {n : nat} {Multi : bool → nom_package}
  {Game : nat → bool → nom_package} {A} `{IsAdversary IGame A}
  `{∀ n, IsGame IGame (Game n true)} `{∀ n, IsGame IGame (Game n false)}
  : perfect IGame (Multi true) (Game 0 true)
  → perfect IGame (Multi false) (Game n true)
  → (∀ i : 'nat, i < n → perfect IGame (Game i false) (Game i.+1 true))
  → (AdvOf Multi A <= \sum_(0 <= i < n) AdvOf (Game i) A)%R.
Proof.
  intros p p' p''.
  rewrite (Adv_perfect_l p) (Adv_perfect_r p').
  elim: {-2}n (leqnn n).
  - intros ?. rewrite Adv_same big_nil //.
  - intros j IH H'.
    rewrite big_nat_recr //=.
    ssprove_hop (Game j true)%sep.
    rewrite -(Adv_perfect_r (p'' j H')) //.
    apply ltnW in H'.
    apply Num.Theory.lerD; auto.
Qed.
