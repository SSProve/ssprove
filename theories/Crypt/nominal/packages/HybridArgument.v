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


Definition unif (n : nat) : dist nat :=
  {code x ← sample uniform n ;; ret (nat_of_ord x) }.

Lemma eq_sum_sum {n} {F : nat → R} :
  (\sum_i F (@nat_of_ord n i)
  = \sum_(0 <= i < n) F i)%R.
Proof.
  induction n.
  - rewrite big_nil big_ord0 //.
  - by rewrite big_ord_recr big_nat_recr //= IHn.
Qed.

Lemma dlet_uniform {Y : choiceType} {n} `{Hlt : Lt 0 n}
  {f : _ → distr R Y} {y : Y} :
  (\dlet_(x <- (uniform n).π2) f x) y = ((\sum_x f x y) / n%:~R)%R.
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

Lemma Pr_RAND_unif {n} {A} `{ValidPackage (loc A) (IPICK nat) A_export A} :
  (Pr' (A ∘ RAND (unif n)) true *+ n
      = \sum_(0 <= i < n) Pr' (A ∘ @PICK nat i) true)%R.
Proof.
  destruct n.
  1: rewrite GRing.mulr0n big_nil //.
  rewrite -> TotalProbability; try exact _.
  rewrite Pr_fst_sample dlet_dlet.
  under dlet_f_equal.
  1: intros x; rewrite Pr_fst_ret; rewrite dlet_unit_ext; over.
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

Lemma Adv_PICK_hybrid {I} {n} {A R R'}
  `{VA  : ValidPackage (loc A) I A_export A}
  `{VR  : ValidPackage (loc R) (IPICK nat) I R}
  `{VR' : ValidPackage (loc R') (IPICK nat) I R'}
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
    by apply perfect_Pr, IH.
  - f_equal. apply eq_bigr => i _.
    by rewrite <- sep_link_assoc.
Qed.

Lemma Adv_hybrid {IMulti IGame} {n : nat} {Multi Game : bool → nom_package}
  {H A : nom_package} `{VA : ValidPackage (loc A) IMulti A_export A}
  `{VG : ∀ b, ValidPackage (loc (Game b)) [interface] IGame (Game b)}
  `{VH : ValidPackage (loc H) (unionm IGame (IPICK 'nat)) IMulti H}
  : perfect IMulti (Multi true) (H ∘ (Game true || PICK 0))
  → perfect IMulti (Multi false) (H ∘ (Game true || PICK n))
  → (∀ i : 'nat, i < n →
    perfect IMulti (H ∘ (Game false || PICK i )) (H ∘ (Game true || PICK i.+1)))
  → AdvOf Multi A = (AdvOf Game (A ∘ H ∘ (ID IGame || RAND (unif n))) *+ n)%R.
Proof.
  intros p p' p''.
  rewrite (Adv_perfect_l p) (Adv_perfect_r p').
  rewrite (sep_par_factor_game_l _ (PICK 0)).
  rewrite (sep_par_factor_game_l _ (PICK n)).
  rewrite 2!sep_link_assoc.
  erewrite @Adv_PICK_hybrid.
  5: {
    intros i; specialize (p'' i).
    rewrite (sep_par_factor_game_l _ (PICK i)) in p''.
    rewrite (sep_par_factor_game_l _ (PICK i.+1)) in p''.
    do 2 rewrite -> sep_link_assoc in p''.
    exact p''.
  }
  2-4: ssprove_valid.
  do 2 rewrite <- sep_link_assoc.
  erewrite <- sep_par_factor_game_l.
  2,3: ssprove_valid.
  erewrite <- sep_par_factor_game_l.
  2,3: ssprove_valid.
  rewrite (sep_par_factor_game_r (Game true)).
  rewrite (sep_par_factor_game_r (Game false)).
  rewrite 2!Adv_reduction sep_link_assoc //.
Qed.

Lemma Adv_hybrid_dep {IGame} {n : nat} {Multi : bool → nom_package}
  {Game : nat → bool → nom_package} {A}
  `{VA : ValidPackage (loc A) IGame A_export A}
  `{VG : ∀ n b, ValidPackage (loc (Game n b)) [interface] IGame (Game n b)}
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


Ltac replace_true e :=
  progress ( replace e with true in * by (symmetry; (apply /ltP || apply /eqP); lia) ).

Ltac replace_false e :=
  progress ( replace e with false in * by (symmetry; (apply /ltP || apply /eqP); lia) ).

Lemma hybrid_cases (c i : nat) (T : Type) :
  ((c < i)%coq_nat → T) →
  ((c = i) → T) →
  ((c = i.+1) → T) →
  ((c > i.+1)%coq_nat → T) →
  T.
Proof.
  intros H1 H2 H3 H4.
  destruct (c < i)%N eqn:E1; move: E1 => /ltP // E1.
  destruct (c == i)%B eqn:E2; move: E2 => /eqP // E2.
  destruct (c == i.+1)%B eqn:E3; move: E3 => /eqP // E3.
  destruct (c > i.+1)%N eqn:E4; move: E4 => /ltP // E4. lia.
Qed.

Ltac replace_next :=
  match goal with
  | |- context[ (?n <= ?m)%N ] =>
      try replace_true (n <= m)%N ;
      try replace_false (n <= m)%N
  | |- context[ (?n == ?m :> nat)%B ] =>
      try replace_true (n == m :> nat)%B ;
      try replace_false (n == m :> nat)%B
  end.

Ltac replace_many := repeat replace_next.

Ltac hybrid_cases c i :=
  apply (hybrid_cases c i) => ? ;
  [ replace_many
  | subst ; replace_many
  | subst ; replace_many
  | replace_many
  ].
