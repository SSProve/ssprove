From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum order.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From SSProve.Crypt Require Import Axioms SubDistr pkg_composition
  Prelude Package Nominal NominalPrelude.

From HB Require Import structures.

(* Supress warnings due to use of HB *)
Set Warnings "-redundant-canonical-projection,-projection-no-head-constant".

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import PackageNotation.
#[local] Open Scope package_scope.

(* Preparation lemmas *)
Lemma Pr_code_ret {A : choiceType} {x : A} {h} :
  Pr_code (ret x) h = dunit (x, h).
Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

Lemma Pr_code_get {B : choiceType} {l : Location} {k : l → raw_code B} {h} :
  Pr_code (x ← get l ;; k x) h
    = Pr_code (k (get_heap h l)) h.
Proof. done. Qed.

Lemma Pr_code_put {B : choiceType} {l : Location} {a : l} {k : raw_code B} {h} :
  Pr_code (#put l := a ;; k) h
    = Pr_code k (set_heap h l a).
Proof. done. Qed.

Lemma Pr_code_call {B : choiceType} {o : opsig} {a : src o} {k : tgt o → raw_code B} {h} :
  Pr_code (x ← op o ⋅ a ;; k x) h
    = Pr_code (k (chCanonical _)) h.
Proof. done. Qed.

Lemma Pr_code_sample {A : choiceType} {op' : Op} {k : Arit op' → raw_code A} {h} :
  Pr_code (x ← sample op' ;; k x) h = \dlet_(x <- op'.π2) Pr_code (k x) h. 
Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

Lemma dlet_commut {T S U : choiceType} {A B} {f : T → S → distr Axioms.R U} {z} :
  (\dlet_(x <- A) \dlet_(y <- B) f x y) z = 
  (\dlet_(y <- B) \dlet_(x <- A) f x y) z.
Proof.
  pose proof @RulesStateProb.SD_commutativity'.
  cbn in H.
  unfold SDistr_bind, SDistr_carrier in H.
  specialize (H T S U A).
  rewrite H //.
Qed.

Lemma AdvantageE_Pr {LA L L' I} {G G' A}
  `{ValidPackage LA I A_export A}
  `{ValidPackage L Game_import I G}
  `{ValidPackage L' Game_import I G'} :
  fseparate LA L →
  fseparate LA L' →
  G ≈₀ G' → Pr (A ∘ G) true = Pr (A ∘ G') true.
Proof.
  intros S1 S2 H'.
  apply GRing.Theory.subr0_eq.
  apply Num.Theory.normr0_eq0.
  eapply (H' LA); done.
Qed.

Lemma Adv_Pr {L I} {G G' A : nom_package} `{ValidPackage L I A_export A} :
  perfect I G G' → Pr (A ∘ G)%sep true = Pr (A ∘ G')%sep true.
Proof.
  intros H'.
  apply GRing.Theory.subr0_eq.
  apply Num.Theory.normr0_eq0.
  eapply H'.
  exact H.
Qed.

(* PICK game *)

Definition IPICK T := [interface [ 0%N ] : { 'unit ~> T }].

Definition PICK {T : choice_type} (x : T) : game (IPICK T) :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> T } 'tt {
      ret x
    } ].

Definition cell T : Location := (0%N, 'option T).

Definition CELL T : package (IPICK T) (IPICK T) :=
  [package [fmap cell T ] ;
    [ 0%N ] : { 'unit ~> T } 'tt {
      mc ← get cell T ;;
      match mc with
      | Some c => ret c
      | None => 
        r ← call [ 0%N ] : { 'unit ~> T } tt ;;
        #put cell T := Some r ;;
        ret r
      end
    } ].

Lemma CELL_PICK_perf {T : choice_type} (x : T) :
  CELL T ∘ PICK x ≈₀ PICK x.
Proof.
  pose (inv := (heap_ignore [fmap cell T] ⋊ couple_lhs (cell T) (cell T) (λ v _, v = None ∨ v = Some x))).
  apply (eq_rel_perf_ind _ _ inv);
    [ unfold inv; ssprove_invariant; [ fmap_solve | by left ] |].
  unfold inv.
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl; simpl.
  apply r_get_remember_lhs => y.
  eapply (r_rem_couple_lhs (cell T) (cell T)); try exact _.
  intros H.
  destruct H; subst.
  - apply r_put_lhs.
    ssprove_restore_mem.
    { ssprove_invariant. by right. }
    by apply r_ret.
  - apply r_forget_lhs.
    by apply r_ret.
Qed.

Definition unif (n : nat) : code emptym emptym nat := {code
  match n with
  | 0 => ret 0%N
  | S n' =>
      x ← sample uniform (S n') ;; ret (nat_of_ord x)
  end }.

Definition RAND {T : choice_type} (c : code emptym emptym T)
  : game (IPICK T) :=
  [package [fmap cell T] ;
    [ 0%N ] : { 'unit ~> T } 'tt {
      mr ← get cell T ;;
      match mr with
      | Some r => ret r
      | None =>
        r ← c ;;
        #put cell T := Some r ;;
        ret r
      end
    } ].

Inductive NoFail {A} : raw_code A → Prop :=
  | NoFail_ret : ∀ x,
      NoFail (ret x)
  | NoFail_sampler : ∀ op k,
      LosslessOp op →
      (∀ v, NoFail (k v)) →
      NoFail (pkg_core_definition.sampler op k).

Lemma NoFail_unif {n} : NoFail (unif n).
Proof.
  case n.
  - apply NoFail_ret.
  - intros n'. simpl. apply NoFail_sampler.
    { apply LosslessOp_uniform. }
    intros x. apply NoFail_ret.
Qed.

Definition Pr_rand {T} (c : raw_code T ) : distr R T
  := dfst (Pr_code c emptym).

Lemma NoFail_psum {T} (c : raw_code T) : NoFail c → psum (Pr_rand c) = 1%R.
Proof.
  elim.
  - intros x.
    rewrite /Pr_rand Pr_code_ret.
    rewrite /(dfst _) (distr_ext _ _ _ (dlet_unit _ _)).
    apply Couplings.psum_SDistr_unit.
  - intros op k LL NF IH.
    rewrite /Pr_rand Pr_code_sample.
    under eq_psum.
    { intros x.
      rewrite dlet_dlet.
      rewrite dletE.
Admitted.

Lemma Pr_code_rand {T T' : choiceType} {c} {f : T → raw_code T'} {h}
  : NoFail c
  → Pr_code (x ← c ;; f x) h
  = \dlet_(x <- Pr_rand c) Pr_code (f x) h.
Proof.
  elim.
  - intros x => /=.
    rewrite /Pr_rand Pr_code_ret.
    by rewrite /(dfst _) 2!(distr_ext _ _ _ (dlet_unit _ _)).
  - intros op k LL NF IH => /=.
    rewrite /Pr_rand 2!Pr_code_sample.
    rewrite (distr_ext _ _ _ (dlet_dlet _ _ _)).
    rewrite (distr_ext _ _ _ (dlet_dlet _ _ _)).
    apply distr_ext.
    apply dlet_f_equal => x.
    rewrite IH.
    rewrite -(distr_ext _ _ _ (dlet_dlet _ _ _)).
    done.
Qed.

(*
Lemma Pr_code_indep {T'} {c' : raw_code T'} {h h'}
  : ValidCode emptym emptym c' 
  → dfst (Pr_code c emptym) = Pr_rand.
Proof.
  elim.
  - intros. rewrite Pr_ret.
 *)
  

Section Proof.

Context {T : choice_type}.
Context (c : code emptym emptym T).


Lemma testing0 {LA} {T'} {A : raw_code T'} {f f' : T} {h} :
  fseparate LA [fmap cell T] →
  ValidCode LA (IPICK T) A →
  get_heap h (cell T) = Some f' →
  Pr_code (code_link A (RAND c)) h
  = Pr_code (code_link A (RAND {code ret f})) h.
Proof.
  intros SEP VA.
  move: h; induction (VA) => h H'.
  - done.
  - fmap_invert H.
    destruct x.
    cbn [code_link].
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind code_link].
    rewrite 2!Pr_code_get H'.
    cbn [code_link bind].
    by apply H1.
  - cbn[code_link].
    rewrite 2!Pr_code_get.
    by apply H1.
  - cbn [code_link].
    rewrite 2!Pr_code_put.
    erewrite IHv => //.
    rewrite get_set_heap_neq //.
    apply fhas_in in H.
    destruct SEP as [SEP].
    move: SEP => /fdisjointP.
    intros H''.
    specialize (H'' _ H).
    rewrite domm_set domm0 in H''.
    apply /negP.
    move=> /eqP H'''.
    rewrite H''' in H''.
    rewrite in_fsetU in_fset1 eq_refl // in H''.
  - cbn [code_link].
    rewrite 2!Pr_code_sample.
    apply distr_ext.
    apply dlet_f_equal => x.
    by apply H0.
Qed.

Lemma testing1 {LA} {T'} {A : raw_code T'} {h} :
  fseparate LA [fmap cell T] →
  NoFail c →
  ValidCode LA (IPICK T) A →
  Pr_code (code_link A (RAND c)) h
    = \dlet_(f <- Pr_rand c)
      Pr_code (code_link A (RAND {code ret f})) h.
Proof.
  intros SEP LL VA.
  apply distr_ext.
  move: h; induction VA.
  - intros h y.
    rewrite Pr_code_ret.
    rewrite dletC.
    rewrite pr_predT.
    rewrite (NoFail_psum _ LL).
    rewrite GRing.mul1r //.
  - intros h y.
    fmap_invert H.
    cbn [code_link].
    under dlet_f_equal.
    1: intros ?; repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]); over.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    destruct x.
    cbn [bind code_link].
    rewrite Pr_code_get.
    destruct (get_heap h (cell _)) eqn:E.
    { cbn [code_link bind].
      under dlet_f_equal. {
        intros x.
        rewrite Pr_code_get E.
        rewrite -(testing0 SEP (H0 _) E).
        over.
      }
      cbn [bind].
      rewrite dletC.
      rewrite pr_predT.
      rewrite (NoFail_psum _ LL).
      rewrite GRing.mul1r //.
    }
    rewrite bind_assoc.
    rewrite (Pr_code_rand LL).
    apply dlet_f_equal => x.
    rewrite Pr_code_put.
    erewrite testing0.
    + rewrite Pr_code_get E.
      cbn [bind code_link].
      rewrite bind_assoc.
      cbn [ prog bind ].
      rewrite Pr_code_put.
      reflexivity.
    + apply SEP.
    + apply H0.
    + rewrite get_set_heap_eq //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_get.
    rewrite H1 //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_put.
    rewrite IHVA //.
  - intros h y.
    cbn [code_link].
    rewrite Pr_code_sample.
    under eq_in_dlet.
    1: intros ? ? ?; rewrite H0 //; reflexivity.
    1: reflexivity.
    symmetry.
    under eq_in_dlet.
    1: intros ? ? ?; rewrite Pr_code_sample //.
    1: reflexivity.
    rewrite dlet_commut //.
Qed.

Lemma testing {LA} {A : raw_package} :
  fseparate LA [fmap cell T] →
  NoFail c →
  ValidPackage LA (IPICK T) A_export A →
  Pr (A ∘ RAND c) = \dlet_(x <- Pr_rand c) Pr (A ∘ RAND {code ret x}).
Proof.
  intros SEP LL VA.
  apply distr_ext => b.
  unfold Pr, SDistr_bind, SDistr_unit, Pr_op.
  rewrite resolve_link.

  assert (H : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H).
  rewrite (testing1 SEP LL H0).
  rewrite dlet_dlet.
  apply dlet_f_equal => y.
  rewrite resolve_link => //.
Qed.

Lemma PICK_dirac_perf (x : T) :
  RAND {code ret x} ≈₀ PICK x.
Proof.
  pose (inv := (heap_ignore [fmap cell T] ⋊ couple_lhs (cell T) (cell T) (λ v _, v = None ∨ v = Some x))).
  apply (eq_rel_perf_ind _ _ inv);
    [ unfold inv; ssprove_invariant; [ fmap_solve | by left ] |].
  unfold inv.
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl; simpl.
  apply r_get_remember_lhs => y.
  eapply (r_rem_couple_lhs (cell T) (cell T)); try exact _.
  intros H.
  destruct H; subst.
  - apply r_put_lhs.
    ssprove_restore_mem.
    { ssprove_invariant. by right. }
    by apply r_ret.
  - apply r_forget_lhs.
    by apply r_ret.
Qed.

Lemma testing' {LA} {A : raw_package} :
  fseparate LA [fmap cell T] →
  NoFail c →
  ValidPackage LA (IPICK T) A_export A →
  Pr (A ∘ RAND c) true = (\dlet_(x <- Pr_rand c) Pr (A ∘ PICK x)) true.
Proof.
  intros SEP LL VA.
  rewrite testing //.
  rewrite 2!dletE.
  apply eq_psum => x.
  f_equal.
  eapply AdvantageE_Pr.
  - fmap_solve.
  - fmap_solve.
  - apply PICK_dirac_perf.
Qed.

End Proof.

Lemma testing_uni n {LA} {A : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA (IPICK ('fin n)) A_export A →
  Pr (A ∘ RAND {code x ← sample uniform n ;; ret x}) true
      = (\sum_i Pr (A ∘ @PICK ('fin n) i) true / n%:R)%R.
Proof.
  intros SEP VA.
  rewrite testing' //.
  2: apply NoFail_sampler; [ apply LosslessOp_uniform | intros ?; apply NoFail_ret].
  rewrite /Pr_rand Pr_code_sample. 
  rewrite /(dfst _) (distr_ext _ _ _ (dlet_dlet _ _ _)).
  rewrite /(dfst _) (distr_ext _ _ _ (dlet_dlet _ _ _)).
  under dlet_f_equal.
  { intros x.
    rewrite Pr_code_ret.
    rewrite (distr_ext _ _ _ (dlet_unit _ _)).
    rewrite (distr_ext _ _ _ (dlet_unit _ _)).
    cbn [ fst ].
    over. }
  rewrite dletE.
  rewrite psum_fin.
  apply eq_bigr => x _.
  rewrite GRing.mulrC.
  simpl in x.
  replace ((uniform n).π2 x) with (n%:R^-1 : Axioms.R)%R.
  - apply Num.Theory.ger0_norm.
    apply Num.Theory.mulr_ge0.
    + unfold Pr, SDistr_bind; rewrite dletE; apply ge0_psum.
    + rewrite Num.Theory.invr_ge0.
      apply Num.Theory.ler0n.
  - simpl.
    unfold UniformDistrLemmas.r.
    rewrite GRing.Theory.div1r card_ord //.
Qed.

Lemma testing_uni2 n {LA} {A : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA (IPICK ('fin n)) A_export A →
  (Pr (A ∘ RAND {code x ← sample uniform n ;; ret x}) true *+ n
      = \sum_i Pr (A ∘ @PICK ('fin n) i) true)%R.
Proof.
  intros H' H''.
  rewrite testing_uni //.
  rewrite -(GRing.Theory.mulr_natr (\sum__ _) n).
  rewrite GRing.mulr_suml.
  apply eq_big => // i _.
  rewrite -GRing.mulrA GRing.mulVf ?GRing.mulr1 //.
  apply /eqP => H0.
  erewrite <- GRing.mul0rn in H0.
  apply Num.Theory.pmulrnI in H0 => //.
  move: (GRing.oner_eq0 R) => /eqP //.
Qed.

Lemma testing_unif n {LA} {A : raw_package} :
  fseparate LA [fmap cell nat] →
  ValidPackage LA (IPICK nat) A_export A →
  (Pr (A ∘ RAND (unif n)) true *+ n
      = \sum_(0 <= i < n) Pr (A ∘ @PICK nat i) true)%R.
Proof.
  intros SEP VA.
  destruct n.
  1: admit.
  unfold unif.
  cbn [ prog ].
  rewrite testing'.
  2: apply SEP. 
  2: apply NoFail_sampler; [ apply LosslessOp_uniform | intros ?; apply NoFail_ret].
Admitted.
  (*
  erewrite (@testing_uni2 n.+1 LA A _ _ VA).
  etransitivity.
  1: eapply @testing_uni2.
  erewrite testing' => //.
  2: apply SEP.
  2: apply NoFail_unif.
  2: apply VA.
  destruct n.
  1: admit.
  unfold unif.
  rewrite testing_uni2.
  rewrite dletE.
Admitted.
   *)

(*
Lemma testing_unif2 {n} {LA} {A : raw_package} :
  fseparate LA [fmap cell nat ] →
  ValidPackage LA (IPICK nat) A_export A →
  (Pr (A ∘ RAND (unif n)) true *+ n
      = \sum_(0 <= i < n) Pr (A ∘ @PICK 'nat i) true)%R.
Proof.
  intros H' H''.
  rewrite testing_unif //.
  destruct n.
  { rewrite GRing.mulr0n big_nil //. }
  rewrite -(GRing.Theory.mulr_natr (\sum_(_ <= _ < _) _) n.+1).
  rewrite GRing.mulr_suml.
  apply eq_big => // i _.
  rewrite -GRing.mulrA GRing.mulVf ?GRing.mulr1 //.
  apply /eqP => H0.
  erewrite <- GRing.mul0rn in H0.
  apply Num.Theory.pmulrnI in H0 => //.
  move: (GRing.oner_eq0 R) => /eqP //.
Qed.
 *)

Lemma testing_pick {LA LR LR' I} {n : nat} {A R R' : raw_package}
    `{ValidPackage LA I A_export A}
    `{ValidPackage LR (IPICK nat) I R}
    `{ValidPackage LR' (IPICK nat) I R'} :
    fseparate LA LR →
    fseparate LA LR' →
    fseparate LA [fmap cell nat] →
    fseparate LR [fmap cell nat] →
    fseparate LR' [fmap cell nat] →
    (∀ i, R' ∘ PICK i ≈₀ R ∘ PICK i.+1)
  → (AdvantageE (R ∘ PICK 0%N) (R ∘ PICK n) A
  = AdvantageE (R ∘ RAND (unif n)) (R' ∘ RAND (unif n)) A *+ n)%R.
Proof.
  intros C1 C2 S1 S2 S3 IH.
  rewrite Advantage_sym (Advantage_sym (R ∘ RAND (unif n))).
  unfold AdvantageE.
  rewrite -(GRing.telescope_sumr (fun i => Pr (A ∘ R ∘ PICK i) true)) //.
  rewrite GRing.sumrB.
  under eq_big.
  1: intros; over.
  1: intros i _; erewrite (AdvantageE_Pr _ _ (IH i)); over.
  Unshelve. 2,3: fmap_solve.
  rewrite -Num.Theory.normrMn.
  rewrite -GRing.mulr_natr.
  rewrite GRing.mulrBl.
  rewrite 2!GRing.mulr_natr.
  rewrite 2!link_assoc.
  erewrite testing_unif.
  3: ssprove_valid.
  2: fmap_solve.
  erewrite testing_unif.
  3: ssprove_valid.
  2: fmap_solve.
  do 2 f_equal.
  - apply eq_big => // x y; rewrite link_assoc //.
  - f_equal; apply eq_big => // x y; rewrite link_assoc //.
Qed.

(*
Lemma testing_uni2_adv {n} {LA} {I} {A R R' : raw_package} `{Positive n} :
  fseparate LA [fmap cell ('fin n) ] →
  ValidPackage LA I A_export A →
  ValidPackage LA (IPICK 'fin n) I R →
  ValidPackage LA (IPICK 'fin n) I R' →
  (AdvantageE (R ∘ RAND (uniform n)) (R' ∘ RAND (uniform n)) A *+ n
    <= \sum_i AdvantageE
      (R ∘ @PICK 'fin n i)
      (R' ∘ PICK i) A)%R.
Proof.
  intros H' VA VG VG'.
  unfold AdvantageE.
  rewrite -Num.Theory.normrMn.
  rewrite -GRing.mulr_natr.
  rewrite GRing.mulrBl.
  rewrite 2!GRing.mulr_natr.
  rewrite 2!link_assoc.
  do 2 (rewrite testing_uni2; [| fmap_solve ]).
  rewrite -GRing.sumrB.
  eapply Order.POrderTheory.le_trans.
  { apply Num.Theory.ler_norm_sum. }
  apply Num.Theory.ler_sum => i _.
  rewrite 2!link_assoc //.
Qed.
*)
