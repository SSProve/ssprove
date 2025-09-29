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

Lemma Adv_Pr {I} {G G' A : nom_package} `{ValidPackage (loc A) I A_export A} :
  perfect I G G' → Pr' (A ∘ G)%sep true = Pr' (A ∘ G')%sep true.
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

Definition unif (n : nat) : code emptym emptym nat := locked {code
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
  - rewrite /unif -lock. apply NoFail_ret.
  - intros n'. rewrite /unif -lock. apply NoFail_sampler.
    { apply LosslessOp_uniform. }
    intros x. apply NoFail_ret.
Qed.

Definition Pr_rand {T} (c : raw_code T ) : distr R T
  := dfst (Pr_code c emptym).

Lemma Pr_rand_ret {A : choiceType} {x : A} :
  Pr_rand (ret x) = dunit x.
Proof.
  rewrite /Pr_rand Pr_code_ret.
  by rewrite /(dfst _) (distr_ext _ _ _ (dlet_unit _ _)).
Qed.

Lemma Pr_rand_sample {A : choiceType} {op' : Op} {k : Arit op' → raw_code A} :
  Pr_rand (x ← sample op' ;; k x) = \dlet_(x <- op'.π2) Pr_rand (k x).
Proof.
    rewrite /Pr_rand Pr_code_sample.
    by rewrite /(dfst _) (distr_ext _ _ _ (dlet_dlet _ _ _)).
Qed.

Lemma Pr_Pr_rand {G} :
  Pr G true = Pr_rand (resolve G RUN tt) true.
Proof.
  unfold Pr, SDistr_bind, SDistr_unit, Pr_op, Pr_rand, dfst.
  by apply dlet_f_equal => [[b h]].
Qed.

Lemma NoFail_psum {T} (c : raw_code T) : NoFail c → psum (Pr_rand c) = 1%R.
Proof.
  elim.
  - intros x.
    rewrite Pr_rand_ret.
    apply Couplings.psum_SDistr_unit.
  - intros op k LL NF IH.
    rewrite Pr_rand_sample.
    under eq_psum.
    { intros x.
      rewrite dletE.
      over.
    }
    rewrite interchange_psum.
    2: intros x; apply summable_mu_wgtd; intros y.
    2: apply /andP; split; [ done | apply le1_mu1 ].
    2: eapply eq_summable.
    2: intros x; rewrite -dletE; reflexivity.
    2: apply summable_mu.
    under eq_psum.
    1: intros x; rewrite psumZ // IH GRing.mulr1; over.
    apply LL.
Qed.

Lemma Pr_code_bind {T T' : choiceType} {c} {f : T → raw_code T'} {h}
  : Pr_code (x ← c ;; f x) h
  = \dlet_(y <- Pr_code c h) Pr_code (f y.1) y.2.
Proof.
  move: h.
  induction c; cbn [bind]; intros h.
  - rewrite Pr_code_ret.
    rewrite (distr_ext _ _ _ (dlet_unit _ _)) //.
  - rewrite 2!Pr_code_call //.
  - rewrite 2!Pr_code_get //.
  - rewrite 2!Pr_code_put //.
  - rewrite 2!Pr_code_sample.
    rewrite (distr_ext _ _ _ (dlet_dlet _ _ _)).
    apply distr_ext.
    by apply dlet_f_equal.
Qed.

Lemma Pr_code_fail {T} {h}
  : Pr_code (@fail T) h = dnull.
Proof.
  rewrite Pr_code_sample /=.
  apply distr_ext. apply dlet_null.
Qed.

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

Lemma testing'_sep {A : nom_package} :
  NoFail c →
  ValidPackage (loc A) (IPICK T) A_export A →
  Pr' (A ∘ RAND c)%sep true = (\dlet_(x <- Pr_rand c) Pr' (A ∘ PICK x)%sep) true.
Proof.
  intros LL VA.
  pose (π := fresh (as_nom (RAND c), [fmap cell T] : Locations) (A, loc A)).
  rewrite -{1}(@rename_alpha _ A π).
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite testing' //.
  2: rewrite fseparate_disj.
  2: eauto with nominal_db.
  apply dlet_f_equal => x.
  rewrite -{2}(@rename_alpha _ A π).
  rewrite /Pr' -link_sep_link //.
  rewrite -fseparate_disj; fmap_solve.
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
  rewrite Pr_rand_sample.
  rewrite /(dfst _) (distr_ext _ _ _ (dlet_dlet _ _ _)).
  under dlet_f_equal.
  { intros x.
    rewrite Pr_rand_ret.
    rewrite (distr_ext _ _ _ (dlet_unit _ _)).
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

Lemma testing_unif {n} {A : nom_package} :
  ValidPackage (loc A) (IPICK nat) A_export A →
  (Pr' (A ∘ RAND (unif n)) true *+ n
      = \sum_(0 <= i < n) Pr' (A ∘ @PICK nat i) true)%R.
Proof.
  intros VA.
  destruct n.
  1: rewrite GRing.mulr0n big_nil //.
  rewrite -> testing'_sep.
  2: apply NoFail_unif.
  2: assumption.
  unfold unif.
  cbn [ prog ].
  rewrite -lock Pr_rand_sample.
  rewrite dlet_dlet.
  under dlet_f_equal.
  1: intros x; rewrite Pr_rand_ret; rewrite (distr_ext _ _ _ (dlet_unit _ _)); over.
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

Lemma testing_pick {I} {n : nat} {A R R' : nom_package}
  : ValidPackage (loc A) I A_export A
  → ValidPackage (loc R) (IPICK nat) I R
  → ValidPackage (loc R') (IPICK nat) I R'
  → (∀ i, perfect I (R' ∘ PICK i) (R ∘ PICK i.+1))
  → (Adv (R ∘ PICK 0%N) (R ∘ PICK n) A
  = Adv (R ∘ RAND (unif n)) (R' ∘ RAND (unif n)) A *+ n)%R.
Proof.
  intros VA VR VR' IH. 
  rewrite -> Adv_sym.
  symmetry.
  rewrite -> Adv_sym.
  symmetry.
  unfold Adv.
  rewrite <- (GRing.telescope_sumr (fun i => Pr' (A ∘ R ∘ PICK i) true)) => //.
  rewrite GRing.sumrB.
  under eq_bigr.
  { intros i _; erewrite <- (@Adv_Pr _ _ _ _ VA (IH i)), sep_link_assoc; over. }
  rewrite -Num.Theory.normrMn.
  rewrite <- testing_unif; [| ssprove_valid ].
  under eq_bigr.
  { intros i _; erewrite sep_link_assoc; over. }
  simpl.
  rewrite <- testing_unif; [| ssprove_valid ].
  do 2 rewrite -> sep_link_assoc.
  simpl.
  symmetry.
  rewrite <- (@GRing.mulr_natr Axioms.R).
  rewrite GRing.mulrBl.
  do 2 rewrite -> (@GRing.mulr_natr Axioms.R).
  done.
Qed.

Lemma testing_hybrid {IMulti IGame} {n : nat} {Multi Game : bool → nom_package}
  {H A : nom_package}
  : ValidPackage (loc A) IMulti A_export A
  → ValidPackage (loc (Game true)) Game_import IGame (Game true)
  → ValidPackage (loc (Game false)) Game_import IGame (Game false)
  → ValidPackage (loc H) (unionm IGame (IPICK 'nat)) IMulti H
  → perfect IMulti (Multi true) (H ∘ (Game true || PICK 0%N))
  → perfect IMulti (Multi false) (H ∘ (Game true || PICK n))
  → (∀ i : 'nat, perfect IMulti (H ∘ (Game false || PICK i )) (H ∘ (Game true || PICK i.+1)))
  → AdvOf Multi A = (AdvOf Game (A ∘ H ∘ (ID IGame || RAND (unif n))) *+ n)%R.
Proof.
  intros VA VG VG' VH p p' p''.
  rewrite (Adv_perfect_l p) (Adv_perfect_r p').
  rewrite (sep_par_factor_game_l (P' := PICK 0%N)).
  rewrite (sep_par_factor_game_l (P' := PICK n)).
  rewrite 2!sep_link_assoc.
  erewrite testing_pick.
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

Lemma testing_hybrid2 {IMulti IGame} {n : nat} {Multi Game : bool → nom_package}
  {H A : nom_package}
  : ValidPackage (loc A) IMulti A_export A
  → ValidPackage (loc (Game true)) Game_import IGame (Game true)
  → ValidPackage (loc (Game false)) Game_import IGame (Game false)
  → ValidPackage (loc H) (unionm IGame (IPICK ('nat × 'nat))) IMulti H
  → perfect IMulti (Multi true) (H ∘ (Game true || PICK (0%N, 0%N)))
  → perfect IMulti (Multi false) (H ∘ (Game true || PICK (n, n)))
  → (∀ i : 'nat, perfect IMulti (H ∘ (Game false || PICK i )) (H ∘ (Game true || PICK i.+1)))
  → (∀ i : 'nat, perfect IMulti (H ∘ (Game false || PICK i )) (H ∘ (Game true || PICK i.+1)))
  → AdvOf Multi A = (AdvOf Game (A ∘ H ∘ (ID IGame || RAND (unif n))) *+ 'C(n, 2))%R.
Proof.

Admitted.



Definition done : Location := (4%N, 'bool).

Definition IGUESS n `{Positive n} :=
  [interface [ 2%N ] : { 'fin n ~> 'fin n × 'bool }].

Definition GUESS n `{Positive n}
  : bool → game (IGUESS n) := λ b,
  [package [fmap done] ;
    [ 2%N ] : { 'fin n ~> 'fin n × 'bool } (g) {
      d ← get done ;;
      if d then
        fail
      else
        #put done := true ;;
        r ← sample uniform n ;;
        ret (r, b && (r == g))%B
    }
  ].

Lemma guess0 {LA} {T'} {A : raw_code T'} {b} {h} {n} `{Positive n} :
  fseparate LA [fmap done] →
  ValidCode LA (IGUESS n) A →
  get_heap h done = true →
  Pr_code (code_link A (GUESS n b)) h
  = Pr_code (code_link A (GUESS n (~~ b))) h.
Proof.
  intros SEP VA.
  move: h.
  induction VA => h HEAP; cbn [code_link].
  - rewrite Pr_code_ret //.
  - fmap_invert H0.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind].
    rewrite 2!Pr_code_get HEAP.
    rewrite 2!Pr_code_bind.
    rewrite Pr_code_fail.
    by rewrite 2!(distr_ext _ _ _ (dlet_null _)).
  - rewrite 2!Pr_code_get.
    by apply H2.
  - rewrite 2!Pr_code_put.
    apply IHVA.
    rewrite get_set_heap_neq //.
    apply fhas_in in H0.
    destruct SEP as [SEP].
    move: SEP => /fdisjointP.
    intros H''.
    specialize (H'' _ H0).
    rewrite domm_set domm0 in H''.
    apply /negP.
    move=> /eqP H'''.
    rewrite H''' in H''.
    rewrite in_fsetU in_fset1 eq_refl // in H''.
  - rewrite 2!Pr_code_sample.
    apply distr_ext.
    apply dlet_f_equal => x.
    by apply H1.
Qed.

Lemma guess1 {LA} {T'} {A : raw_code T'} {b} {t} {h} {n} `{Positive n} :
  fseparate LA [fmap done] →
  ValidCode LA (IGUESS n) A →
  (dfst (Pr_code (code_link A (GUESS n b)) h) t
    <= dfst (Pr_code (code_link A (GUESS n (~~ b))) h) t + n%:R^-1)%R.
Proof.
  intros SEP VA.
  move: h.
  induction VA => h; cbn [code_link].
  - rewrite Num.Theory.lerDl.
    rewrite Num.Theory.invr_ge0 //.
  - fmap_invert H0.
    repeat (rewrite (resolve_set, resolve_link, resolve_ID_set, coerce_kleisliE, eq_refl); cbn [fst snd mkdef projT2 mkopsig projT1]).
    cbn [bind].
    rewrite 2!Pr_code_get.
    destruct (get_heap h done) eqn:E.
    { rewrite 2!Pr_code_bind Pr_code_fail.
      rewrite 2!(distr_ext _ _ _ (dlet_null _)).
      rewrite /(dfst _) (distr_ext _ _ _ (dlet_null _)).
      rewrite dnullE Num.Theory.lerDl.
      rewrite Num.Theory.invr_ge0 //.
    }
    cbn [bind]. 
    rewrite 2!Pr_code_put.
    rewrite 2!Pr_code_sample.
    do 2 rewrite dlet_dlet dlet_uniform.
    under eq_bigr => i _.
    { erewrite guess0; do 2 try done. 2: rewrite get_set_heap_eq //. over. }
    cbn beta.
    rewrite -{3}(GRing.mul1r n%:R^-1)%R.
    rewrite -GRing.mulrDl.
    apply Num.Theory.ler_pM => //.
    1: apply Num.Theory.sumr_ge0 => i _ //.
    1: rewrite Num.Theory.invr_ge0 //.
    rewrite GRing.addrC (bigD1 x) //.
    apply Num.Theory.lerD.
    1: apply le1_mu1.
    rewrite (bigD1 x erefl) //.
    rewrite -(GRing.add0r (bigop.body _ _ _)).
    apply Num.Theory.lerD => //.
    apply Num.Theory.ler_sum => j /negP H'.
    destruct (j == x)%B eqn:E' => //.
    rewrite E' //.
    rewrite andbC /= andbC //.
  - rewrite 2!Pr_code_get.
    by apply H2.
  - rewrite 2!Pr_code_put.
    apply IHVA.
  - rewrite 2!Pr_code_sample.
    do 2 rewrite dlet_dlet dletE.
    eapply Order.le_trans.
    1: apply le_psum.
    1: move=> y; apply /andP; split.
    1: apply Num.Theory.mulr_ge0 => //.
    1: apply Num.Theory.ler_pM; [ | | | apply H1 ]; done.
    1: eapply eq_summable.
    1: intros y; rewrite GRing.mulrDr; reflexivity.
    1: apply summableD.
    1: apply summable_mu_wgtd => y.
    1: apply /andP; split; [ done |].
    1: apply le1_mu1.
    1: apply summableZr.
    1: apply summable_mu.
    under eq_psum.
    1: intros y; rewrite GRing.mulrDr; over.
    rewrite psumD.
    2,3: intros y; apply Num.Theory.mulr_ge0 => //.
    2: rewrite Num.Theory.invr_ge0 //.
    2: apply summable_mu_wgtd.
    2: intros y; apply /andP; split; [ done |].
    2: apply le1_mu1.
    2: apply summable_mu_wgtd.
    2: intros y; apply /andP; split.
    2: rewrite Num.Theory.invr_ge0 //.
    2: rewrite Num.Theory.invf_le1.
    2: rewrite Num.Theory.ler1n //.
    2: rewrite Num.Theory.ltr0n //.
    apply Num.Theory.lerD => //.
    rewrite psumZr.
    2: rewrite Num.Theory.invr_ge0 //.
    apply Num.Theory.ler_piMl.
    1: rewrite Num.Theory.invr_ge0 //.
    apply le1_mu.
Qed.

Lemma guess2 {A} {n} `{Positive n} :
  ValidPackage (loc A) (IGUESS n) A_export A →
  (AdvOf (GUESS n) A <= n%:R^-1)%R.
Proof.
  intros VA.
  pose (π := fresh ([fmap done] : Locations, as_nom (GUESS n true), as_nom (GUESS n false)) (A, loc A)).
  rewrite -{1}(@rename_alpha _ A π).
  unfold Adv.
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite 2!Pr_Pr_rand 2!resolve_link.

  apply (rename_valid π) in VA.
  assert (H' : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H').

  rewrite Num.Theory.ler_distlC.
  apply /andP; split.
  - rewrite Num.Theory.lerBlDr.
    apply: guess1.
    rewrite fseparate_disj.
    eauto with nominal_db.
  - apply: guess1.
    rewrite fseparate_disj.
    eauto with nominal_db.
Qed.

Definition doneh : Location := (5%N, 'bool).

Definition IGUESSL n `{Positive n} :=
  [interface [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool }].

Definition GUESSL n `{Positive n} l
  : bool → game (IGUESSL n) := λ b,
  [package [fmap done] ;
    [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool } (g) {
      #assert length g <= l ;;
      d ← get done ;;
      #assert ~~ d ;;
      #put done := true ;;
      r ← sample uniform n ;;
      ret (r, b && (r \in g))%B
    }
  ].

Definition GUESSH n `{Positive n} l
  : package (unionm (IPICK nat) (IGUESS n)) (IGUESSL n) :=
  [package [fmap doneh] ;
    [ 3%N ] : { list ('fin n) ~> 'fin n × 'bool } (g) {
      #assert length g <= l ;;
      d ← get doneh ;;
      #assert ~~ d ;;
      #put doneh := true ;;
      i ← call [ 0%N ] tt ;;
      let g := drop i g in
      let h := head (chCanonical _) g in
      let t := behead g in 
      '(r, b) ← call [ 2%N ] h ;;
      ret (r, ((g != nil) && b) || (r \in t))%B
    }
  ].

Lemma Multi_pf b l n `{Positive n} :
  perfect (IGUESSL n) (GUESSL n l b)
    (GUESSH n l ∘ (GUESS n true || PICK (if b then 0 else l))).
Proof.
  ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore [fmap doneh] ⋊ couple_rhs done doneh eq)).
  1: ssprove_invariant.
  1: fmap_solve.
  1: done.
  simplify_eq_rel m.
  - ssprove_code_simpl.
    ssprove_sync => Hlen.
    apply r_get_remember_rhs => d'.
    ssprove_swap_rhs 1%N.
    ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember => d.
    1: admit.
    replace d' with d.
    2: admit.
    ssprove_sync => H'.
    rewrite -(negbK d) {}H' {d d'} /=.
    ssprove_swap_rhs 0%N.
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_sync => r.
    ssprove_restore_mem.
    1: admit.
    apply r_ret => s0 s1 H'; split => //.
    f_equal. destruct b => /=.
    + rewrite drop0.
      by destruct m.
    + rewrite drop_oversize //.
Admitted.
  
Lemma guess_hyb l n `{Positive n} A : 
  ValidPackage (loc A) (IGUESSL n) A_export A →
  AdvOf (GUESSL n l) A = (AdvOf (GUESS n) (A ∘ (GUESSH n l) ∘ (ID (IGUESS n) || RAND (unif l))) *+ l)%R.
Proof.
  intros VA.
  eapply (testing_hybrid (Multi := λ b, GUESSL n l b) (Game := λ b, GUESS n b)).
  1-4: ssprove_valid.
  1,2: apply Multi_pf.
  intros i.
  ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (heap_ignore emptym ⋊ couple_rhs done doneh implb)).
  1: ssprove_invariant.
  1: fmap_solve.
  1: done.
  simplify_eq_rel m.
  - ssprove_code_simpl.
    ssprove_sync => Hlen.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros d.
    ssprove_sync => H'.
    rewrite -(negbK d) {d}H' /=.
    ssprove_swap_lhs 0%N.
    ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember => d'; [ admit |].
    replace d' with false; [| admit ].
    do 2 apply r_put_vs_put.
    ssprove_sync => r.
    ssprove_restore_mem; [ admit |].
    apply r_ret => s0 s1 H'; split => //.
    f_equal.
    change (i.+1) with (1 + i)%N.
    rewrite andbC -drop_drop /= .
    destruct (drop i m) eqn:E; rewrite E //= drop0.
    by destruct l0.
Admitted.

Definition IReplacement n `{Positive n} :=
  [interface [ 3 ] : { 'unit ~> 'fin n }].

Definition WReplacement n `{Positive n}
  : game (IReplacement n) :=
  [package emptym ;
    [ 3 ] : { 'unit ~> 'fin n } (g) {
      r ← sample uniform n ;;
      ret r
    }
  ].

Definition prev_loc n `{Positive n} : Location := (5%N, chList 'fin n).

Definition WOReplacement n `{Positive n}
  : game (IReplacement n) :=
  [package [fmap prev_loc n ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      r ← sample uniform n ;;
      prev ← get prev_loc n ;;
      #assert r \notin prev ;;
      #put prev_loc n := r :: prev ;;
      ret r
    }
  ].

Definition Replacement n `{Positive n} b :=
  if b then WReplacement n else WOReplacement n.

Definition count_loc : Location := (6, 'nat).

Definition Counter n `{Positive n} k
  : package (IReplacement n) (IReplacement n) :=
  [package [fmap count_loc ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      c ← get count_loc ;;
      #assert c < k ;;
      #put count_loc := c.+1 ;;
      r ← call [ 3%N ] tt ;;
      ret r
    }
  ].

Definition HReplacement n `{Positive n} k
  : package (unionm (IGUESSL n) (IPICK nat)) (IReplacement n) :=
  [package [fmap count_loc ; prev_loc n ] ;
    [ 3 ] : { 'unit ~> 'fin n } 'tt {
      c ← get count_loc ;;
      #assert c < k ;;
      #put count_loc := c.+1 ;;
      i ← call [0] tt ;;
      if (c < i)%N then
        r ← sample uniform n ;;
        prev ← get prev_loc n ;;
        #assert r \notin prev ;;
        #put prev_loc n := r :: prev ;;
        ret r
      else if (c > i)%N then
        r ← sample uniform n ;;
        ret r
      else
        prev ← get prev_loc n ;;
        '(r, b) ← call [ 3%N ] prev ;;
        #assert ~~ b ;;
        ret r
    }
  ].

Definition CReplacement n `{Positive n} k b : nom_package :=
  Counter n k ∘ (if b then WReplacement n else WOReplacement n).

Lemma replace_hyb q n `{Positive n} A : 
  ValidPackage (loc A) (IReplacement n) A_export A →
  AdvOf (CReplacement n q) A = ((n + n) %:R^-1 *+ (q - 1) *+ q)%R.
Proof.
  intros VA.
  etransitivity.
  2: shelve.
  eapply (testing_hybrid (Multi := _) (Game := GUESSL n q) (H := HReplacement n q)).
  1-4: ssprove_valid.
  - unfold CReplacement.
    ssprove_share.
    eapply prove_perfect.
    eapply (eq_rel_perf_ind _ _ (heap_ignore emptym)).
    1: ssprove_invariant.
    1: fmap_solve.
    simplify_eq_rel m.
    destruct m => /=.
    ssprove_code_simpl.
    apply r_get_vs_get_remember; [ admit |].
    intros c.
    ssprove_sync => Hk.
    destruct c.
    + simpl.
      ssprove_code_simpl_more.
      ssprove_swap_rhs 0%N.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      admit.
    + simpl.
      apply r_put_vs_put.
      ssprove_sync => r.
      ssprove_restore_mem.
      1: admit.
      by apply r_ret.
  - admit.
  - intros i.
    ssprove_share.
    eapply prove_perfect.
    eapply (eq_rel_perf_ind _ _ (heap_ignore emptym)).
    1: ssprove_invariant.
    1: fmap_solve.
    simplify_eq_rel m.
    destruct m => /=.
    ssprove_code_simpl.
    apply r_get_vs_get_remember; [ admit |].
    intros c.
    ssprove_sync => Hk.
    destruct c.
    1,2: admit.
  Unshelve.
  2: exact q.
  f_equal.
  Search GUESSL.
Admitted.
