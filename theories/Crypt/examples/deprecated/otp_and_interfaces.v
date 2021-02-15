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
     OrderEnrichedCategory.

From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     Rules
     UniformDistrLemmas
     FreeProbProg
     Theta_dens
     UniformDistr.

Import Num.Theory.

Local Open Scope ring_scope.

Variable Words : finType.
Variable w0 : Words.
Variable xorW : Words -> Words -> Words.
Hypothesis xorWC : commutative xorW.
Hypothesis xorWA : associative xorW.
Hypothesis xorW0 : forall w, xorW w w0 = w.
Hypothesis xorWK : forall w, xorW w w = w0.

(*Rem. : when adding adversaries we might want also
       uniform distributions over booleans. In this
       case just change the Index to (≈ bool)

       Inductive Index :=
       | word_index : Index
       | bool_index : Index.

 *)

Inductive Index :=
| words_index : Index
| bool_index : Index.

Module WordsParam <:  UniformParameters.

  Definition Index : Type := Index.
  Definition i0 : Index := words_index.
  Definition fin_family : Index -> finType := fun i => match i with
                                                   | words_index => Words
                                                   | bool_index => bool_finType
                                                   end.
  Definition F_w0 : forall i : Index, (fin_family i).
  Proof.
    move => i.
    case: i.
    rewrite /fin_family.
    exact w0.
    rewrite /fin_family.
    exact false.
  Defined.

End WordsParam.

Inductive probEmpty : Type -> Type := .

(*Rem.: probably change this when adding adversaries
      (non necessarily uniform distributions over booleans!)
 *)
Module OtherParam <: ProbRulesParam.

  Definition probE : Type -> Type := probEmpty.

  Definition rel_choiceTypes : Type := void.

  Definition chEmb : rel_choiceTypes -> choiceType.
  Proof.  move => contra. contradiction. Defined.

  Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
  Proof. move => contra. contradiction. Defined.

  Definition Hch : forall r : rel_choiceTypes, chEmb r.
  Proof. move => contra. contradiction. Defined.

End OtherParam.

Module MyRulesUniform := DerivedRulesUniform OtherParam WordsParam.
Export WordsParam.
Export MyRulesUniform.

Let FrDist X := MyRulesUniform.MyRulesU.MFreePr X.
Let θ0 {A} (c : FrDist A) := unary_theta_dens MyRulesUniform.myparamU.prob_handler _ c.

Definition Plain : ord_choiceType := Words.
Definition Cipher : ord_choiceType := Words.
Definition Key : ord_choiceType := Words.

Definition KG  : FrDist Key  := (@Uniform_F words_index).

Definition Enc (m : Plain) (k : Key) : FrDist Cipher :=
  pure (xorW m k).

Definition Dec (c : Cipher) (k : Key) : FrDist Plain :=
  pure (xorW c k).

(* KG; Enc *)
Definition Game (m : Plain) : FrDist Cipher :=
  k <- KG ;;
  c <- Enc m k ;;
  pure c.

Definition RND : FrDist Cipher := (@Uniform_F words_index).

Lemma xork_xork_eq (k : Words) :
 forall w1 w2, ((fun w => xorW (xorW w k) k) w1 = w2) -> (w1 = w2).
Proof.
  rewrite /= => w1 w2.
  by rewrite -xorWA xorWK xorW0.
Qed.

Lemma bijective_xor_xor (k : Words) : bijective (fun w => xorW (xorW w k) k).
Proof.
  exists (fun w => w); by move => w; rewrite -xorWA xorWK xorW0.
Qed.


Lemma bijective_xor (m : Words) : bijective (fun w => xorW m w).
Proof.
  exists (fun w => xorW m w);
  by move => w'; rewrite xorWA xorWK xorWC xorW0.
Qed.

Lemma id_bijective : bijective (fun w : Words => w).
Proof. by exists (fun w => w). Qed.


Lemma dunit_gt0_eq  {A : ord_choiceType} (x y : A) : (SDistr_unit _ x) y > 0 -> y = x.
  rewrite /SDistr_unit dunit1E.
  case (x == y) eqn:Heq.
  - case: Heq. by move/eqP.
  - by rewrite (ltrr 0).
Qed.

Theorem secrecy (m : Plain) : ⊨ ⦃ True ⦄ (Game m) ≈ RND ⦃ eq ⦄.
Proof.
  rewrite /(Game m) /RND.
  eapply (seq_rule_ch KG RND True (fun a1 a2 => xorW m a1 == a2) eq).
  - by apply (@Uniform_bij_rule words_index _ (bijective_xor m)).
  - move => k c.
    apply: pre_hypothesis_rule_ch => Heq.
    move/eqP: Heq => Heq.
    rewrite -Heq.
    apply: MyRulesU.sample_rule_ch.
    by apply: SDistr_unit_F_choice_prod_coupling.
    move => c1 c2 Hpr.
    move: (dunit_gt0_eq _ _ Hpr).
    move => [H1 H2].
    by subst.
Qed.

(* Addition of interfaces *)
Definition sum_ar {op1 op2 : Type} (s1 : op1 -> choiceType) (s2 : op2 -> choiceType) : op1 + op2 -> choiceType
  := fun v => match v with
           | inl v => s1 v
           | inr v => s2 v
           end.

(* A computation can be embedded as a computation with more oracles *)
Definition inj_left {a : choiceType} {op1 op2 : Type} {s1 : op1 -> choiceType} {s2 : op2 -> choiceType} (v : rFreeF op1 s1 a) : rFreeF (op1 + op2) (sum_ar s1 s2) a.
Proof.
  induction v.
  - constructor; assumption.
  - constructor 2 with (s := inl s).
    auto.
Defined.

(* The empty interface *)
Definition zero_ar (v : void) : choiceType := match v with end.

(* Wrapping of a package *)
(* Each package comes with access to sampling operations (this is the left side of the addition) *)
Definition package_type {op_import : Type}
           (import : op_import -> choiceType) {op_export : Type}
           (export : op_export -> choiceType) : Type :=
  forall (oo : op_export), rFreeF (MyRulesUniform.MyRulesU.Ops + op_import)
                             (sum_ar MyRulesUniform.MyRulesU.Arit import) (export oo).

Definition package_closed_type {op_export : Type}
           (export : op_export -> choiceType) : Type :=
  forall (oo : op_export), rFreeF (MyRulesUniform.MyRulesU.Ops)
                             MyRulesUniform.MyRulesU.Arit (export oo).

(* This is the classical function for handling free computations, but works on choiceTypes *)
Fixpoint handlerFree {op : Type} {s : op -> choiceType} {a : choiceType} {b : Type} (alg : forall (l : op), (s l -> b) -> b) (f : a -> b) (m : rFreeF op s a) : b :=
  match m with
  | retrFree x => f x
  | ropr s k => alg s (fun r => handlerFree alg f (k r))
  end.

(* This function removes the void interface *)
Definition remove_void {a : choiceType} {op1} {s1 : op1 -> choiceType} (v : rFreeF (op1 + void) (sum_ar s1 zero_ar) a) : rFree op1 s1 a.
Proof.
  refine (handlerFree (fun l k => _) (retrFree _ _ _) v).
  eapply (bindrFree _ _).
  destruct l.
  simpl in *.
  apply (ropr _ _ _ o k).
  destruct e.
  simpl.
  apply (retrFree _ _).
Defined.

Lemma il_rv {a : choiceType} {op1} {s1 : op1 -> choiceType} (v : rFreeF (op1 + void) (sum_ar s1 zero_ar) a) : inj_left (remove_void v) = v.
  induction v; try reflexivity.
  destruct s.
  - rewrite /remove_void. simpl. f_equal.
    extensionality s. rewrite -(H s).
    f_equal. rewrite (H s).
    pose (ord_relmon_law1 (rFree _ s1) a).
    simpl in e.
    unfold FreeProbProg.rFree_obligation_2 in e.
    unfold FreeProbProg.rFree_obligation_1 in e.
    simpl in e.
    rewrite (equal_f_dep e _).
    reflexivity.
  - destruct e.
Qed.

Lemma rv_il {a : choiceType} {op1} {s1 : op1 -> choiceType} (v : rFreeF op1 s1 a) : remove_void (inj_left v) = v.
  induction v; try reflexivity.
  rewrite /inj_left /remove_void. simpl.
  f_equal. extensionality p.
  pose (ord_relmon_law1 (rFree _ s1) a).
  simpl in e.
  unfold FreeProbProg.rFree_obligation_2 in e.
  unfold FreeProbProg.rFree_obligation_1 in e.
  simpl in e.
  rewrite (equal_f_dep e _).
  apply H.
Qed.

Definition sampleCall {op_import : Type} {import : op_import -> choiceType} (s : MyRulesUniform.MyRulesU.Ops) :
  rFreeF (MyRulesUniform.MyRulesU.Ops + op_import)
         (sum_ar MyRulesUniform.MyRulesU.Arit import)
         (MyRulesUniform.MyRulesU.Arit s) := callrFree _ _ (inl s).

Definition link {op_import op_middle op_export : Type}
           {import : op_import -> choiceType}
           {middle : op_middle -> choiceType}
           {export : op_export -> choiceType}
           (p1 : package_type middle export)
           (p2 : package_type import middle)
  : package_type import export.
Proof.
  intro oo.
  refine (handlerFree _ (retrFree _ _ _) (p1 oo)).
  move => l H.
  destruct l.
  - simpl in *.
    eapply (bindrFree _ _).
    apply sampleCall.
    exact H.
  - refine (bindrFree _ _ (p2 o) _).
    rewrite //=.
Defined.

Definition link_with_closed {op_middle op_export : Type}
           {middle : op_middle -> choiceType}
           {export : op_export -> choiceType}
           (p1 : package_type middle export)
           (p2 : package_closed_type middle)
  :   package_closed_type export.
Proof.
  intro oo.
  refine (handlerFree _ (retrFree _ _ _) (p1 oo)).
  move => l H.
  destruct l.
  - simpl in *.
    eapply (bindrFree _ _).
    apply MyRulesUniform.MyRulesU.Call.
    exact H.
  - refine (bindrFree _ _ (p2 o) _).
    rewrite //=.
Defined.

Definition package_closed_type2package_type {op_export : Type} {export : op_export -> choiceType}
           (p : package_closed_type export) : package_type zero_ar export := fun oo => inj_left (p oo).

Definition package_type2package_closed_type {op_export : Type} {export : op_export -> choiceType}
           (p : package_type zero_ar export) : package_closed_type export := fun oo => remove_void (p oo).

(* Definition package_closed_inv {op_export : Type} {export : op_export -> choiceType} *)
(*            (p : package_type zero_ar export) : remove_void  *)

Lemma comm {op_middle op_export : Type}
           {middle : op_middle -> choiceType}
           {export : op_export -> choiceType} (p1 : package_type middle export)
      (p2 : package_type zero_ar middle) :
  link_with_closed p1 (package_type2package_closed_type p2) = fun oo => remove_void (link p1 p2 oo).
Proof.
  extensionality oo.
  rewrite /link_with_closed /link.
  induction (p1 oo).
  - by reflexivity.
  - rewrite /remove_void. rewrite /remove_void in H.
    destruct s.
    + simpl in *.
      f_equal. extensionality p. simpl. rewrite -H. rewrite /bindrFree /=.
      simpl.
Admitted.

(* An adversary is a package which:
    consumes oracle Plain ~> Cipher
    provides oracle unit ~> bool *)
Let Adversary := package_type (fun m : Plain => Cipher) (fun u : unit => bool_choiceType).

(* A game is a package which:
    consumes no oracle
    provides oracle Plain ~> Cipher *)
Let Games := package_closed_type (fun m : Plain => Cipher).

(* A distribution is a closed package which:
    consumes no oracle
    provides oracle unit ~> bool *)
Let Distribution := package_closed_type (fun u : unit => bool_choiceType).

(* A function Plain -> Dist Cipher can be packed as a game *)
Let pack_game (c : Plain -> FrDist Cipher) : Games := (fun m => c m).

(* A distribution (i.e. closed package) can be translated to a distribution on bool *)
Let Distribution2Distr (C : Distribution) : SDistr bool_choiceType := (θ0 (C tt)).

(* The advantage as in the paper *)
Let advantage (G0 G1 : Games) (A : Adversary) :=
  `|Distribution2Distr (link_with_closed A G0) true - Distribution2Distr (link_with_closed A G1) true|.

(* Example using OTP definitions *)
Definition G0 : Games := pack_game Game.
Definition G1 : Games := pack_game (fun=> RND).

Let GiveMFreePr (C : Distribution) : MyRulesUniform.MyRulesU.MFreePr bool_choiceType :=
  (C tt).


Lemma link_preserves_eq' (A : rFreeF (MyRulesUniform.MyRulesU.Ops + Plain) (sum_ar MyRulesUniform.MyRulesU.Arit (fun m : Plain => Cipher)) bool_choiceType) (K1 K2 : Words -> FrDist Words)
      (H : forall m, θ0 (K1 m) = θ0 (K2 m)) :
    (Distribution2Distr (link_with_closed (fun=> A) (pack_game K1))) =
    (Distribution2Distr (link_with_closed (fun=> A) (pack_game K2))).
Proof.
  rewrite /Distribution2Distr /Theta_dens.unary_theta_dens_obligation_1.
  rewrite /unary_theta_dens /= /Theta_dens.unary_theta_dens_obligation_1.
  induction A.
  - by reflexivity.
  - rewrite /link_with_closed /handlerFree.
    destruct s.
    + apply θ0_preserves_bind. reflexivity.
      intros v. apply H0.
    +  apply θ0_preserves_bind. rewrite /pack_game. apply H.
       intros v. apply H0.
Qed.

Lemma link_preserves_eq (A : Adversary) (K1 K2 : Words -> FrDist Words)
      (H : forall m, θ0 (K1 m) = θ0 (K2 m)) :
    (Distribution2Distr (link_with_closed A (pack_game K1))) =
    (Distribution2Distr (link_with_closed A (pack_game K2))).
Proof.
  apply link_preserves_eq'. apply H.
Qed.

Lemma link_preserves_eq_orig (A : Adversary) (K1 K2 : Words -> FrDist Words)
      (H : forall m, θ0 (K1 m) = θ0 (K2 m)) :
    θ0 (remove_void (link A (fun m : Plain => inj_left (K1 m)) tt)) =
    θ0 (remove_void (link A (fun m : Plain => inj_left (K2 m)) tt)).
Proof.
  pose (comm A (fun m : Plain => inj_left (K2 m))).
  change (link_with_closed A (package_type2package_closed_type (fun m : Plain => inj_left (K2 m)))) with (fun oo => link_with_closed A (package_type2package_closed_type (fun m : Plain => inj_left (K2 m))) oo) in e.
  rewrite -(equal_f_dep e tt).
  pose (comm A (fun m : Plain => inj_left (K1 m))).
  change (link_with_closed A (package_type2package_closed_type (fun m : Plain => inj_left (K1 m)))) with (fun oo => link_with_closed A (package_type2package_closed_type (fun m : Plain => inj_left (K1 m))) oo) in e0.
  rewrite -(equal_f_dep e0 tt).
  pose (link_preserves_eq A K1 K2 H).
  unfold Distribution2Distr in e1.
  rewrite /package_type2package_closed_type.
  assert ((fun oo : Plain => remove_void (inj_left (K1 oo))) = (fun oo : Plain => (K1 oo))).
  { extensionality oo. apply (rv_il (K1 oo)). }
  rewrite H0.
  assert ((fun oo : Plain => remove_void (inj_left (K2 oo))) = (fun oo : Plain => (K2 oo))).
  { extensionality oo. apply (rv_il (K2 oo)). }
  rewrite H1.
  rewrite e1.
  reflexivity.
Qed.

Lemma link_provably_eq_to_eq
      (A : Adversary) (K1 K2 : Words -> FrDist Words)
      (H : forall m, ⊨ ⦃ True ⦄ (K1 m) ≈ (K2 m) ⦃ eq ⦄):
    (Distribution2Distr (link_with_closed A (fun m => (K1 m) ))) =
    (Distribution2Distr (link_with_closed A (fun m => (K2 m) ))).
Proof.
  apply link_preserves_eq.
  move => m. eapply coupling_eq. apply H. auto.
Qed.

Lemma eq_no_advantage (A : Adversary) ( K1 K2 : Words -> FrDist Words)
                      (H : forall m, ⊨ ⦃ True ⦄ (K1 m) ≈ (K2 m) ⦃ eq ⦄) :
  advantage (pack_game K1) (pack_game K2) A = 0.
Proof.
  rewrite /advantage.
  apply /normr0P /eqP.
  suffices :  Distribution2Distr (link_with_closed A (fun m : Plain => K1 m)) =
              Distribution2Distr (link_with_closed A (fun m : Plain => K2 m)).
  move => Heq. rewrite Heq.
  apply: GRing.Theory.subrr.
  apply (link_preserves_eq A K1 K2).
  move => m.
  specialize (H m).
  by apply: coupling_eq.
Qed.

Theorem advantage_negligible (A : Adversary) (ϵ : R) { Heps : 0 <= ϵ }:
  (advantage G0 G1 A) <= ϵ.
Proof.
  rewrite eq_no_advantage.
  assumption.
  exact: secrecy.
Qed.



(* Can we generalize to relations different from equality?  *)

(* Lemma R_advantage (A : Adversary) (K1 K2 : Words -> Dist Words) *)
(*                   (R : Words -> Words -> Prop) *)
(*                   (H : forall m, ⊨ ⦃ True ⦄ (K1 m) ≈ (K2 m) ⦃ R ⦄) : *)
(*   advantage (fun m => inj_left (K1 m)) (fun m => inj_left (K2 m)) A <= (f R).  *)


(* Lemma link_preserves_R (A : Adversary) (K1 K2 : Words -> Dist Words) *)
(*                        (R : Words -> Words -> Prop) *)
(*                        (H : forall m, ⊨ ⦃ True ⦄ (K1 m) ≈ (K2 m) ⦃ R ⦄) : *)
(*   R_bool *)
(*    (Distribution2Distr (link A (fun m => inj_left (K1 m)))) = *)
(*    (Distribution2Distr (link A (fun m => inj_left (K2 m)))). *)
(* Admitted. *)

(* This is another style of proofs, in which the adversary is called by the game *)
Let AdvInt (b : sum_choiceType unit_choiceType Cipher) : choiceType :=
  match b with
  | inl tt => prod_choiceType Plain Plain
  | inr c => bool_choiceType
  end.

Let Adversary' := package_type (fun m : Plain => Cipher) AdvInt.
Let Game' := package_type AdvInt (fun u : unit => bool_choiceType).

(* This definition is the usual: *)
(* def ind_cpa_otp(adversary): *)
(*     m0, m1 = adversary[0](encryption_oracle) *)
(*     b = flip_coin() *)
(*     mb = m1 if b else m0 *)
(*     b_ = adversary[1](encryption_oracle(mb)) *)
(*     return b == b_ *)
Let Game_Ind_CPA : Game' :=
  fun 'tt => bindrFree _ _ (callrFree _ _ (inr (inl tt))) (fun '(m0, m1) => bindrFree _ _ (callrFree _ _ (inl (existT _ (inl bool_index) (inl (Uni_W _))))) (fun b : bool_choiceType => bindrFree _ _ (callrFree _ _ (inr (inr (if b then m0 else m1)))) (fun b' => retrFree _ _ _ (b == b')))).

(* and this should be |Pr[Ind_CPA(A) = 1] - Pr[Ind_CPA(A) = 0]| *)
(* Let adv_Ind_CPA (A : Adversary') := *)
(*    `| Distribution2Distr (link Game_Ind_CPA (link A (pack_game Game))) true - Distribution2Distr (link Game_Ind_CPA (link A (pack_game Game))) false |. *)
