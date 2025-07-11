From Coq Require Import Utf8.

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra 
  fingroup.fingroup solvable.cyclic prime.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Record CyclicGroup := {
  gT : finGroupType ;
  g : gT ;
  g_gen : generator [set : gT] g ;
  prime_order : prime #[g]
}.

(* Additive group of order 3 *)
Program Definition Z3 : CyclicGroup :=
 {| gT := 'Z_3 ;
    g := Zp1
 |}. 
Obligation 1. unfold g. unfold generator. apply /eqP. apply Zp_cycle. Qed.
Obligation 2. unfold g. rewrite order_Zp1. reflexivity. Qed.

(*
Program Definition MF3 : CyclicGroup :=
 {| gT := {unit 'F_3} ;
    g := _
 |}. 
Obligation 1.
  apply (@FinRing.Unit _ 2%:R).
  apply (@unitfE 'F_3 2).
Defined.
Obligation 2.
  unfold MF3_obligation_1.
  unfold generator.
  (*
  rewrite eqEsubset.
  apply /andP; split.
  apply /subsetP => x H.
   *)
Admitted.
Obligation 3.
  unfold MF3_obligation_1.
  rewrite (@nt_prime_order _ 2); try done.
  rewrite expgnE //=.
Admitted.
 *)

Definition q G : nat := #[g G].

Definition el G : finType := gT G.
Definition exp G : finType := Finite.clone _ 'Z_(q G).

Section Theorems.

Context {G : CyclicGroup}. 

Lemma el_in_g {x : el G} : x \in <[G.(g)]>.
Proof. move: (g_gen G) => /eqP <-. apply in_setT. Qed.

Lemma expgE (x : el G) : ∃ a, x = G.(g) ^+ a.
Proof. apply /cycleP. apply el_in_g. Qed.

Lemma expgq (x : el G) : x ^+ q G = 1.
Proof.
  destruct (expgE x).
  rewrite H.
  rewrite expgAC.
  rewrite expg_order.
  by rewrite expg1n.
Qed.

Lemma trunc_q : (Zp_trunc (q G)).+2 = q G.
Proof.
  apply Zp_cast, prime_gt1, prime_order.
Qed.

Lemma expg_modq (x : el G) (k : nat) : x ^+ (k %% ((Zp_trunc (q G)).+2)) = x ^+ k.
Proof.
  rewrite expg_mod //.
  rewrite trunc_q.
  apply expgq.
Qed.

Lemma expg_frac (x : el G) (a b : exp G) : x ^+ (a / b) = x ^+ a ^+ (b^-1)%R.
Proof.
  rewrite expg_modq expgM //.
Qed.

Lemma expg_fracgg (x : el G) (a : exp G) : (a != 0) → x ^+ (a / a) = x.
Proof.
  intros H.
  replace (nat_of_ord (a / a))
    with (nat_of_ord (Zp_mul a (Zp_inv a)))
    by easy.
  rewrite Zp_mulzV.
  2: {
    rewrite prime_coprime.
    2: rewrite trunc_q; apply prime_order.
    rewrite gtnNdvd.
    - done.
    - by rewrite lt0n.
    - simpl.
      rewrite -modZp.
      apply ltn_mod.
  }
  rewrite expg_modq expg1 //.
Qed.

Lemma expg_sub (x : el G) (a b : exp G) : x ^+ (a - b)%R = x ^+ a * x ^- b.
Proof.
  rewrite expg_modq expgD expg_zneg //=.
  destruct (expgE x); subst.
  apply mem_cycle.
Qed.

Lemma mulgC (x y : el G) : x * y = y * x.
Proof.
  destruct (expgE x), (expgE y).
  subst.
  by rewrite -expgD -expgD addnC.
Qed.

Lemma mulgA (x y z : el G) : x * (y * z) = (x * y) * z.
Proof.
  destruct (expgE x), (expgE y), (expgE z).
  subst.
  by rewrite -!expgD addnA.
Qed.

Definition log (x : el G) : exp G :=
  inord (sval (@cyclePmin (el G) (g G) x el_in_g)).

Lemma log_expg (x : el G) (a : exp G) : log x = a → (g G) ^+ a = x.
Proof.
  unfold log.
  destruct cyclePmin => H.
  subst; simpl.
  f_equal.
  apply inordK.
  rewrite trunc_q //.
Qed.

Lemma expg_log (x : el G) (a : exp G) : (g G) ^+ a = x → log x = a.
Proof.
  intros H.
  unfold log.
  destruct cyclePmin.
  subst; simpl.
  move: e => /eqP.
  rewrite eq_expg_mod_order => /eqP.
  rewrite (modn_small i) => e.
  rewrite -e.
  rewrite modn_small.
  1: apply inord_val.
  rewrite -modZp.
  rewrite {2}trunc_q.
  rewrite ltn_mod.
  apply order_gt0.
Qed.

Lemma expgn_bij : bijective (λ n : exp G, (g G) ^+ n : el G).
Proof.
  eexists log => [a|x].
  - by apply expg_log.
  - by apply log_expg.
Qed.

End Theorems.

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

#[export] Instance Positive_el {G} : Positive #|el G|.
Proof. apply /card_gt0P. by exists 1. Qed.

#[export] Instance Positive_exp {G} : Positive #|exp G|.
Proof. apply /card_gt0P. by exists 0. Qed.

Notation " 'el G " := 'fin #|el G|
  (at level 3) : package_scope.

Notation " 'exp G " := 'fin #|exp G|
  (at level 3) : package_scope.

Notation " 'g " := (fto (g _))
  (at level 3) : package_scope.

Notation " x * y " :=
   (fto (mulg (otf x) (otf y))) : package_scope.

Notation " x ^ a " :=
  (fto (otf x ^+ otf a)) : package_scope.

Notation " x ^- a " :=
  (fto (otf x ^- otf a)) : package_scope.