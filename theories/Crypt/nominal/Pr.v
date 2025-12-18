From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

(******************************************************************************)
(* This file shows that renaming is equivariant in the semantics of SSProve.  *)
(* This means that code may be freely replaced with alpha-equivalent code.    *)
(******************************************************************************)

Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import PackageNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.


Section DistrLemmas.
  Context [T U V : choiceType].

  Lemma dlet_commut {A : distr R T} {B : distr R U}
    {f : T → U → distr R V} :
    (\dlet_(x <- A) \dlet_(y <- B) f x y) =
    (\dlet_(y <- B) \dlet_(x <- A) f x y).
  Proof.
    apply distr_ext.
    pose proof @RulesStateProb.SD_commutativity'.
    cbn in H.
    unfold SDistr_bind, SDistr_carrier in H.
    specialize (H T U V A).
    rewrite H //.
  Qed.

  Lemma dlet_unit_ext {v : T} {f : T → distr R U} :
    \dlet_(y <- dunit v) f y = f v.
  Proof. apply distr_ext, dlet_unit. Qed.

  Lemma dfst_dlet_commut (t : distr R T) (f : T → distr R (U * V)%type) :
    dfst (\dlet_(x <- t) f x) = \dlet_(x <- t) dfst (f x).
  Proof. apply distr_ext => ?. by rewrite dmarginE dlet_dlet. Qed.

  Lemma dlet_dlet_ext {t : distr R T}
    {f1 : T → distr R U} {f2 : U → distr R V} :
    \dlet_(x <- \dlet_(y <- t) f1 y) f2 x
    = \dlet_(y <- t) \dlet_(x <- f1 y) f2 x.
  Proof. apply distr_ext, dlet_dlet. Qed.

  Lemma dlet_null_ext {f : T → distr R U} :
    \dlet_(i <- dnull) f i = dnull.
  Proof. apply distr_ext, dlet_null. Qed.

  Lemma eq_dlet {m} {f g : T → distr R U} : f =1 g
    → \dlet_(x <- m) f x = \dlet_(x <- m) g x.
  Proof. intros H. by apply distr_ext, dlet_f_equal. Qed.
End DistrLemmas.


Section PrCodeLemmas.
  Lemma Pr_Pr_code {G} :
    Pr G = dfst (Pr_code (resolve G RUN tt) empty_heap).
  Proof.
    unfold Pr, SDistr_bind, SDistr_unit, Pr_op, dfst.
    apply eq_dlet => [[x h]] //.
  Qed.

  Lemma Pr_code_ret {A : choiceType} {x : A} {h} :
    Pr_code (ret x) h = dunit (x, h).
  Proof. cbn. rewrite /SubDistr.SDistr_obligation_2 2!SDistr_rightneutral //. Qed.

  Lemma Pr_code_get {B : choiceType} {l : Location} {k : l → raw_code B} {h} :
    Pr_code (x ← get l ;; k x) h = Pr_code (k (get_heap h l)) h.
  Proof. cbn; done. Qed.

  Lemma Pr_code_put {B : choiceType} {l : Location} {a} {k : raw_code B} {h} :
    Pr_code (#put l := a ;; k) h = Pr_code k (set_heap h l a).
  Proof. cbn; done. Qed.

  Lemma Pr_code_sample {A : choiceType} {op' : Op}
      {k : Arit op' → raw_code A} {h} :
    Pr_code (x ← sample op' ;; k x) h = \dlet_(x <- op'.π2) Pr_code (k x) h.
  Proof. cbn. rewrite /SubDistr.SDistr_obligation_2 2!SDistr_rightneutral //. Qed.

  Lemma Pr_code_call {B : choiceType} {o : opsig} {a : src o}
      {k : tgt o → raw_code B} {h} :
    Pr_code (x ← op o ⋅ a ;; k x) h = dnull.
  Proof.
    transitivity (\dlet_(x <- dnull) Pr_code (k x) h).
    - cbn; rewrite /SubDistr.SDistr_obligation_2 2!SDistr_rightneutral //.
    - rewrite dlet_null_ext //.
  Qed.

  Lemma Pr_code_bind {T T' : choiceType} {c} {f : T → raw_code T'} {h}
    : Pr_code (x ← c ;; f x) h
    = \dlet_(y <- Pr_code c h) Pr_code (f y.1) y.2.
  Proof.
    move: h.
    induction c; cbn [bind]; intros h.
    - rewrite Pr_code_ret dlet_unit_ext //.
    - rewrite 2!Pr_code_call dlet_null_ext //.
    - rewrite 2!Pr_code_get //.
    - rewrite 2!Pr_code_put //.
    - rewrite 2!Pr_code_sample dlet_dlet_ext.
      by apply eq_dlet.
  Qed.

  Lemma Pr_code_fail {T} {h} : Pr_code (@fail T) h = dnull.
  Proof. rewrite Pr_code_sample dlet_null_ext //. Qed.
End PrCodeLemmas.

Notation dist c := (code emptym [interface] c).

Section PrFstLemmas.
  Definition Pr_fst {T} (c : raw_code T) : distr R T
    := dfst (Pr_code c emptym).

  Lemma Pr_fst_ret {A : choiceType} {x : A} :
    Pr_fst (ret x) = dunit x.
  Proof. rewrite /Pr_fst Pr_code_ret /(dfst _) dlet_unit_ext //. Qed.

  Lemma Pr_fst_sample {A : choiceType} {op' : Op} {k : Arit op' → raw_code A} :
    Pr_fst (x ← sample op' ;; k x) = \dlet_(x <- op'.π2) Pr_fst (k x).
  Proof.  rewrite /Pr_fst Pr_code_sample /(dfst _) dlet_dlet_ext //. Qed.

  Lemma Pr_Pr_fst {G} :
    Pr G true = Pr_fst (resolve G RUN tt) true.
  Proof.
    unfold Pr, SDistr_bind, SDistr_unit, Pr_op, Pr_fst, dfst.
    by apply dlet_f_equal => [[b h]].
  Qed.

  Lemma Pr_code_fst {T T' : choiceType} {c} {f : T → raw_code T'} {h}
    : ValidCode emptym [interface] c
    → Pr_code (x ← c ;; f x) h
    = \dlet_(x <- Pr_fst c) Pr_code (f x) h.
  Proof.
    elim.
    2-4: intros; exfalso; eapply fhas_empty; eassumption.
    - intros x => /=.
      rewrite /Pr_fst Pr_code_ret /(dfst _) 2!dlet_unit_ext //.
    - intros op k VA IH => /=.
      rewrite /Pr_fst 2!Pr_code_sample 2!dlet_dlet_ext.
      f_equal; extensionality x.
      rewrite IH dlet_dlet_ext //.
  Qed.

  Lemma Pr_fst_bind {T T' : choiceType} {c} {f : T → raw_code T'}
    : ValidCode emptym [interface] c
    → Pr_fst (x ← c ;; f x)
    = \dlet_(x <- Pr_fst c) Pr_fst (f x).
  Proof.
    intros VA.
    rewrite /Pr_fst Pr_code_fst 2!dmarginE 2!dlet_dlet_ext.
    by rewrite /Pr_fst dmarginE dlet_dlet_ext.
  Qed.
End PrFstLemmas.

Section LosslessCodeLemmas.
  Context {A : choiceType}.

  Class LosslessCode (c : raw_code A) :=
    lossless : psum (Pr_fst c) = 1%R.

  #[export] Instance Lossless_ret (a : A)
    : LosslessCode (ret a).
  Proof.
    rewrite /LosslessCode Pr_fst_ret.
    apply Couplings.psum_SDistr_unit.
  Qed.

  #[export] Instance Lossless_sample D (k : _ → raw_code A)
    : LosslessOp D
    → (∀ x, LosslessCode (k x))
    → LosslessCode (x ← sample D ;; k x).
  Proof.
    intros H IH. unfold LosslessCode.
    rewrite Pr_fst_sample.
    under eq_psum.
    { intros x. rewrite dletE. over. }
    rewrite interchange_psum.
    2: intros x; apply summable_mu_wgtd; intros y.
    2: apply /andP; split; [ done | apply le1_mu1 ].
    2: eapply eq_summable.
    2: intros x; rewrite -dletE; reflexivity.
    2: apply summable_mu.
    rewrite -H.
    apply eq_psum => x.
    rewrite psumZ // IH GRing.mulr1 //.
  Qed.

  #[export] Instance Lossless_if b (c1 c2 : raw_code A) :
    LosslessCode c1 → LosslessCode c2 → LosslessCode (if b then c1 else c2).
  Proof. by destruct b. Qed.

  Lemma Pr_fstC {T : choiceType} {c : raw_code A} {mu : distr R T}
    : LosslessCode c → \dlet_(_ <- Pr_fst c) mu = mu.
  Proof.
    intros Hpsum. apply distr_ext => ?.
    by rewrite dletC pr_predT Hpsum GRing.mul1r.
  Qed.
End LosslessCodeLemmas.


(* Code as nominal *)

#[non_forgetful_inheritance]
HB.instance Definition _ : DeclareDiscrete R := DeclareDiscrete.Build R.
HB.instance Definition _ : DeclareDiscrete Interface := DeclareDiscrete.Build Interface.

Program Definition Location_HasAction
  := HasAction.Build Location (λ π l, (natize (π (atomize l.1)), l.2)) _ _.
Obligation 1. by elim: x => [T n]. Qed.
Obligation 2. rewrite fpermM natizeK //. Qed.

HB.instance Definition _ : HasAction Location := Location_HasAction.


Fixpoint rename_code_def {A} π (c : raw_code A) := 
  match c with
  | ret x => ret x
  | opr o x k => opr o x (fun y => rename_code_def π (k y))
  | getr l k => getr (rename π l) (fun y => rename_code_def π (k y))
  | putr l v k => putr (rename π l) v (rename_code_def π k)
  | sampler op k => sampler op (fun y => rename_code_def π (k y))
  end.

Program Definition code_HasAction {A}
  := HasAction.Build (raw_code A) rename_code_def _ _.
Obligation 1.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; reflexivity.
Qed.
Obligation 2.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; try reflexivity.
  1,2: unfold rename; simpl; rewrite fpermM natizeK //.
Qed.

HB.instance Definition _ {A} : HasAction (raw_code A) := code_HasAction.

Lemma mcode_bind {A B} : ∀ f (c : raw_code A) (k : A → raw_code B),
  rename f (a ← c ;; k a) = (a ← rename f c ;; rename f (k a)).
Proof.
  intros f c k.
  unfold rename.
  induction c;
    simpl; try setoid_rewrite H;
    try setoid_rewrite IHc; done.
Qed.


Program Definition Locations_HasAction : HasAction Locations
  := HasAction.Build Locations
    (λ π L, mapm2 (λ x, natize (π (atomize x))) id L) _ _.
Obligation 1. apply eq_fmap => y. rewrite mapm2E // omap_id //. Qed.
Obligation 2.
  apply eq_fmap => y.
  pose (na π x := natize (π (atomize x))).
  replace y with (na f (na g (na g^-1%fperm (na f^-1%fperm y)))).
  2: rewrite /na 2!natizeK fpermKV natizeK fpermKV atomizeK //.
  rewrite mapm2E ?mapm2E ?omap_id ?omap_id.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  replace (na f (na g (na g^-1%fperm (na f^-1%fperm y))))
    with (na (f * g)%fperm (na (f * g)^-1%fperm y)).
  2: rewrite /na 2!natizeK fpermKV natizeK fpermKV atomizeK //.
  2: rewrite natizeK fpermKV atomizeK //.
  rewrite mapm2E ?omap_id.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  rewrite Nominal.fperm_mul_inv /na natizeK fpermM //.
Qed.

HB.instance Definition _ : HasAction Locations
  := Locations_HasAction.

Lemma fhas_Location_equi :
  equivariant (λ (L : Locations) (l : Location), fhas L l).
Proof.
  apply equi2_prove => π L l.
  rewrite //= mapm2E.
  2: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  rewrite omap_id.
  by destruct l.
Qed.

Lemma fhas_rename {π} {L : Locations} {l : Location} :
  fhas L l → fhas (π ∙ L : Locations) (π ∙ l : Location).
Proof. by rewrite -(equi2_use _ fhas_Location_equi). Qed.

#[export]
Instance mcode_valid {L : Locations} {I A f} {c : raw_code A}
  : ValidCode L I c → ValidCode (f ∙ L) I (f ∙ c).
Proof.
  intros H.
  induction H.
  + apply valid_ret.
  + apply valid_opr; easy.
  + apply valid_getr.
    - by apply fhas_rename.
    - apply H1.
  + apply valid_putr.
    - by apply fhas_rename.
    - apply IHvalid_code.
  + apply valid_sampler.
    apply H0.
Qed.

(* Package as nominal *)

Definition mtyped f : typed_raw_function → typed_raw_function
  := fun t => match t with
              | (T; P; k) => (T; P; fun s => rename f (k s))
              end.

Program Definition typed_HasAction : HasAction typed_raw_function
  := HasAction.Build _ mtyped _ _.
Obligation 1.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_id.
Qed.
Obligation 2.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_comp.
Qed.

HB.instance Definition _ : HasAction typed_raw_function
  := typed_HasAction.

Program Definition raw_package_HasAction : HasAction raw_package
  := HasAction.Build _ (λ π, mapm (rename π)) _ _.
Obligation 1.
  apply eq_fmap => i.
  rewrite mapmE.
  destruct (x i); [| reflexivity ].
  rewrite //= rename_id //.
Qed.
Obligation 2.
  rewrite -mapm_comp.
  apply eq_mapm => t.
  rewrite //= rename_comp //.
Qed.

HB.instance Definition _ : HasAction raw_package
  := raw_package_HasAction.

Lemma fhas_rename_raw_package (n : nat) (A B : choice_type) π p g :
  fhas p (n, (A; B; g)) → fhas (π ∙ p : raw_package) (n, (A; B; λ x, π ∙ g x)).
Proof.
  intros H.
  rewrite //= mapmE H //=.
Qed.

#[export]
Instance rename_valid {L I E p} f :
  ValidPackage L I E p → ValidPackage (f ∙ L) I E (f ∙ p).
Proof.
  intros [Ve Vi].
  split; [ intros o; split |].
  - intros H.
    specialize (Ve o).
    rewrite Ve in H.
    destruct H as [g H].
    exists (λ x, f ∙ g x).
    apply fhas_rename_raw_package, H.
  - intros H.
    rewrite Ve.
    destruct H as [g H].
    exists (λ x, f^-1%fperm ∙ g x).
    rewrite -(renameK f p).
    apply fhas_rename_raw_package, H.
  - intros n [A [B g]] x H.
    simpl.
    rewrite -(renameKV f (g x)).
    apply mcode_valid.
    specialize (Vi n (A; B; λ x, f^-1%fperm ∙ g x)).
    apply Vi.
    rewrite -(renameK f p).
    apply fhas_rename_raw_package, H.
Qed.

Program Definition heap_HasAction : HasAction heap
  := HasAction.Build heap
    (λ π L, mapm2 (λ x, natize (π (atomize x))) id L) _ _.
Obligation 1. apply eq_fmap => y. rewrite mapm2E // omap_id //. Qed.
Obligation 2.
  etransitivity.
  2: apply (mapm2_comp unit).
  2,3: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  simpl. f_equal. extensionality n => /=.
  by rewrite natizeK fpermM.
Qed.

HB.instance Definition _ : HasAction heap
  := heap_HasAction.

Lemma get_heap_rename π h l : get_heap (π ∙ h) (π ∙ l) = get_heap h l.
Proof.
  rewrite /get_heap mapm2E /= ?omap_id //.
  eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
Qed.

Lemma set_heap_rename π h l v : set_heap (π ∙ h) (π ∙ l) v = π ∙ set_heap h l v.
Proof.
  rewrite /set_heap.
  apply eq_fmap => n.
  replace n with (@rename Location π (π^-1 ∙ mkloc n tt)).1.
  2: rewrite renameKV //.
  rewrite setmE mapm2E ?mapm2E ?setmE.
  2,3: eapply can_inj, (can_comp natizeK), (can_comp (fpermK _)), atomizeK.
  rewrite renameKV 2!omap_id.
  destruct (_ == _)%B eqn:E;
    move: E => /eqP E;
    destruct (_ == _)%B eqn:E';
    move: E' => // /eqP E'.
  - simpl in E.
    by rewrite /rename /= E natizeK fpermK atomizeK in E'.
  - simpl in E'.
    by rewrite /rename /= -E' natizeK fpermKV atomizeK in E.
Qed.


(* Pr proof *)

Lemma Pr_code_rename {A} π (c : raw_code A) x (h' : heap) :
  ∀ h, Pr_code c h (x, h') = Pr_code (π ∙ c) (π ∙ h) (x, π ∙ h').
Proof.
  induction c => h; rewrite {1}/rename /=.
  - rewrite 2!Pr_code_ret 2!dunit1E 2!xpair_eqE.
    destruct (x0 == x)%B => //=.
    destruct (_ == _)%B eqn:E;
      move: E => /eqP E;
      destruct (_ == _)%B eqn:E';
      move: E' => /eqP E' //.
    + by subst.
    + by rewrite -(renameK π (h : heap)) E' renameK in E.
  - rewrite 2!Pr_code_call 2!dnullE //.
  - by rewrite 2!Pr_code_get get_heap_rename.
  - by rewrite 2!Pr_code_put set_heap_rename.
  - rewrite 2!Pr_code_sample 2!dletE.
    apply eq_psum => y.
    by rewrite H.
Qed.

Lemma coerce_kleisli_rename {A A' B B'} π g x
  : π ∙ @coerce_kleisli A A' B B' g x = coerce_kleisli (λ x, π ∙ g x) x.
Proof.
  rewrite /coerce_kleisli -2!lock /coerce_code mcode_bind.
  destruct (coerce x) => /=.
  2: f_equal; extensionality a.
  1,2: rewrite mcode_bind.
  1,2: f_equal; extensionality b; move: (coerce b) => [] //.
Qed.

Lemma resolve_rename π P F x
  : π ∙ (resolve P F x) = resolve (π ∙ P) F x.
Proof.
  rewrite /resolve mapmE.
  elim: (P F.1) => [[S [T f]]|] //.
  by rewrite coerce_kleisli_rename.
Qed.

Lemma Pr_rename {π} {P : raw_package} {t} :
  Pr P t = Pr (π ∙ P) t.
Proof.
  rewrite 2!Pr_Pr_code 2!dfstE.
  rewrite (reindex_psum (P := predT) (h := @rename heap π^-1)) //=.
  - apply eq_psum => x.
    by rewrite (Pr_code_rename π) renameKV -resolve_rename.
  - exists (@rename heap π).
    + intros h _. by rewrite renameKV.
    + intros h _. by rewrite renameK.
Qed.

Add Parametric Morphism : Pr with
  signature alpha ==> eq as Pr_mor.
Proof.
  intros x y [π' H0].
  apply distr_ext.
  intros b.
  rewrite -H0.
  apply Pr_rename.
Qed.
