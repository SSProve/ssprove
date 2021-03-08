From Coq Require Import
     Relation_Definitions RelationClasses Morphisms Utf8.

From Mon Require Import
     FiniteProbabilities
     SPropMonadicStructures
     SpecificationMonads
     MonadExamples
     SPropBase.

From Relational Require Import
     OrderEnrichedCategory
     OrderEnrichedRelativeMonadExamples
     Commutativity
     GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     Theta_dens
     Theta_exCP
     LaxComp
     FreeProbProg.

Import SPropNotations.
Import Num.Theory.
Import mc_1_10.Num.Theory.

(* Notation "⟦ b ⟧" := (is_true_sprop b). *)
(* Infix "-s>" := (s_impl) (right associativity, at level 86, only parsing). *)

Local Open Scope ring_scope.


Lemma card_non_zero {F : finType} {w0 : F} : #|F|%:~R != 0 :> R.
Proof.
  eapply fintype0 in w0 as h.
  apply /negP. intro n. eapply h.
  rewrite intr_eq0 in n. move: n => /eqP n.
  inversion n. reflexivity.
Qed.

Definition r { F : finType} { w0 : F } : R := (1%:~R) / ((#|F|)%:~R).

Lemma r_nonneg { F : finType} { w0 : F } : 0 <= (@r F w0).
Proof.
  rewrite /r.
  apply: divr_ge0; by apply: ler0n.
Qed.

(* Rem.: TODO: generalize this *)
Lemma sum_const_seq_finType { T : finType } ( J : seq T) (k : R) (Huniq : uniq J) :
  \sum_(j <- J) k = \sum_(j in (seq_sub_finType J)) k.
Proof.
  rewrite /seq_sub_finType. simpl.
  rewrite big_const.
  rewrite big_const_seq.
  rewrite card_seq_sub.
  - simpl.
    rewrite count_predT.
    reflexivity.
  - apply Huniq.
Qed.


Lemma cardinality_bound {T : finType} (J : seq T) (Huniq: uniq J) (k : R) (k_geq0 : 0 <= k) :
  \sum_(j <- J) k <= (#|T|%:~R) * k.
Proof.
  rewrite GRing.mulrC.
  rewrite sum_const_seq_finType.
  2: { exact Huniq. }
  rewrite GRing.sumr_const pmulrn /=.
  have hfoo' :  k *~ #|seq_sub_finType (T:=T) J| =  k * #|seq_sub_finType (T:=T) J|%:~R.
  { by rewrite mulrzr. }
  rewrite hfoo' /=.
  apply: ler_pmul; auto.
  - rewrite ler0z. rewrite lez_nat. reflexivity.
  - rewrite card_seq_sub. 2: eauto.
    rewrite cardT.
    rewrite ler_int. rewrite lez_nat.
    rewrite uniq_leq_size. 1,2: auto.
    intros x hx.
    rewrite mem_enum. reflexivity.
Qed.

Lemma gen_cardinality_bound :
  ∀ {T : finType}
    (J : seq T) (Huniq: uniq J)
    (π : T → R)
    (π_geq0 : ∀ t, 0 <= (π t)),
    \sum_(j <- J) (π j) <= \sum_(j <- enum T) (π j).
Proof.
  (* Basically a rip-off of xfinmap.big_fset_subset *)
  intros T J hu π hπ.
  rewrite [X in _<=X](bigID [pred j : T | j \in J]) /=.
  rewrite ler_paddr ?sumr_ge0 // -[X in _<=X]big_filter.
  rewrite Order.POrderTheory.le_eqVlt; apply/orP; left; apply/eqP/perm_big.
  apply/uniq_perm; rewrite ?filter_uniq //; last move=> i.
  rewrite -enum_setT. apply enum_uniq.
  rewrite mem_filter; case/boolP: (_ \in _) => //=.
  intro. rewrite mem_enum. reflexivity.
Qed.

Lemma is_uniform { F : finType} { w0 : F } : isdistr (fun w : F => (@r F w0)).
Proof.
  split.
  - move => w; apply: r_nonneg.
  - move => J uniq_J. apply /idP.
    apply: ler_trans.
    -- by apply: (cardinality_bound J uniq_J r r_nonneg).
    -- rewrite /r -GRing.invf_div GRing.divr1 GRing.divff.
         by [].
         exact (@card_non_zero F w0).
Qed.

Definition f_dprod { F : finType} { w0 : F } (f : F -> F) : F * F -> R :=
  fun w =>
    if ((f (fst w)) == (snd w)) then (@r F w0) else 0.

Lemma sum_oneq_eq :
  ∀ {I : eqType} (r : seq I) (P : pred I) (F G : I → R),
    (∀ i : I, P i → F i = G i) →
    \sum_(i <- r | P i) F i = \sum_(i <- r | P i) G i.
Proof.
  intros I r P F G eFG.
  induction r as [| a r ihr].
  - rewrite !big_nil. reflexivity.
  - rewrite !big_cons.
    case: ifP=> pa /=.
    + rewrite eFG. 2: auto.
      rewrite ihr. reflexivity.
    + apply ihr.
Qed.

Lemma sum_pred_eq :
  ∀ {I : eqType} (r : seq I) (P Q : pred I) (F : I → R),
    (∀ i : I, P i = Q i) →
    \sum_(i <- r | P i) F i = \sum_(i <- r | Q i) F i.
Proof.
  intros I r P Q F ePQ.
  induction r as [| a r ihr].
  - rewrite !big_nil. reflexivity.
  - rewrite !big_cons.
    case: ifP=> pa /=.
    + rewrite ePQ in pa. rewrite pa.
      rewrite ihr. reflexivity.
    + rewrite ePQ in pa. rewrite pa. apply ihr.
Qed.

(* TODO RENAME *)
Lemma sum_prod_bij
  {T : finType} {f : T -> T}
  (π : (prod_finType T T) -> R)
  (π_geq0 : forall t, 0 <= π t) :
  \sum_(jj <- enum (prod_finType T T)) (if f jj.1 == jj.2 then π jj else 0) =
  \sum_(j <- enum T) (π (j, f j)).
Proof.
  rewrite [X in X=_](bigID [pred jj : prod_finType T T | f jj.1 == jj.2]) /=.
  match goal with
  | |- _ + ?x = _ =>
    assert (e : x == 0)
  end.
  { rewrite psumr_eq0.
    - apply/allP. intros [i j] h. cbn.
      destruct (f i == j).
      + cbn. reflexivity.
      + cbn. apply/eqP. reflexivity.
    - intros [i j]. cbn. intros h.
      destruct (f i == j). 1: discriminate.
      auto.
  }
  move: e => /eqP e. rewrite e. clear e.
  rewrite GRing.Theory.addr0.
  erewrite sum_oneq_eq with (G := fun ij => π (ij.1, ij.2)).
  2:{
    intros [i j]. cbn. intro h. rewrite h. reflexivity.
  }
  rewrite !enumT.
  pose proof pair_big_dep as e.
  specialize e with (F := fun i j => π (i, j)).
  specialize e with (P := λ _, true).
  cbn in e.
  specialize e with (Q := λ i j, f i == j).
  cbn in e. rewrite -e. clear e.
  cbn.
  erewrite sum_oneq_eq with (G := λ i, π (i, f i)).
  2:{
    intros i _.
    erewrite <- big_pred1_eq with (F := λ j, π (i, j)).
    erewrite sum_pred_eq with (Q := λ j, j == f i).
    2:{
      intro j. destruct (f i == j) eqn:e.
      - move: e => /eqP e. subst. destruct (f i == f i) eqn:e.
        + reflexivity.
        + move: e => /eqP e. contradiction.
      - move: e => /eqP e. destruct (j == f i) eqn:e'.
        + move: e' => /eqP e'. subst. contradiction.
        + reflexivity.
    }
    reflexivity.
  }
  reflexivity.
Qed.

(*Rem.: adapting GRing.sumr_const *)
Lemma sumr_const (T : finType) (x : R): \sum_(i <- enum T) x = x * (#|T|%:~R).
Proof.
  rewrite sum_const_seq_finType.
  2: { apply enum_uniq. }
  rewrite GRing.sumr_const pmulrn /=.
  (* Rem.: need to show #|seq_sub (T:=T) (enum T)| = #|T| *)
  rewrite !enumT.
  unfold intmul.
  rewrite GRing.mulrC.
  rewrite GRing.Theory.mulr_natl.
  apply f_equal.
  rewrite card_seq_sub.
  + rewrite cardE.
    rewrite -enumT.
    reflexivity.
  + rewrite -enumT.
    apply enum_uniq.
Qed.

(* the uniform distribution over F *)
Definition uniform_F { F : finType} { w0 : F } : SDistr _ := mkdistr (@is_uniform F w0).

Lemma bijective_isdistr { F : finType} { w0 : F } {f : F -> F} (Hbij : bijective f) :
  isdistr (@f_dprod F w0 f).
Proof.
  rewrite /f_dprod. split.
  move => [w1 w2].
  - destruct (f (w1, w2).1 == (w1, w2).2) eqn: Heq; rewrite Heq.
    -- exact r_nonneg.
    -- trivial.
  - move => J uniq_J.
    apply: ler_trans.
    apply: (gen_cardinality_bound J uniq_J _).
    -- move => [t1 t2] /=.
       destruct (f t1 == t2) eqn:Heq; auto. exact r_nonneg.
    -- rewrite sum_prod_bij.
       rewrite sumr_const /r -GRing.invf_div GRing.divr1 GRing.mulVf. auto.
       exact (@card_non_zero F w0).
       by move => w; exact r_nonneg.
Qed.

Definition sampleFsq_f { F : finType} { w0 : F } {f : F -> F} (f_bij : bijective f) : SDistr _ :=
  (mkdistr (@bijective_isdistr F w0 f f_bij)).

Lemma sampleFsq_f_coupling { F : finType} { w0 : F } { f : F -> F } (f_bij : bijective f):
  coupling (@sampleFsq_f F w0 f f_bij) (@uniform_F F w0) (@uniform_F F w0).
Proof.
  destruct f_bij as [f_inv K1 K2].
  rewrite /sampleFsq_f /f_dprod; split; apply: distr_ext => w /=.
  - rewrite /lmg dfstE /mkdistr psum_sum /=.
    rewrite (sum_seq1 (f w)).
    destruct (f w == f w) eqn: Hfw; auto.
    -- exfalso. by move/idP: Hfw.
    move => y Hy.
    destruct (f w == y) eqn: Hfw; auto.
    -- exfalso. move/eqP: Hy; auto.
    move => x.
    destruct (f w == x) eqn: Hfw; auto.
    exact r_nonneg.
  - rewrite /rmg dsndE /mkdistr psum_sum /=.
    rewrite (sum_seq1 (f_inv w)).
    have Heq: (f (f_inv w) == w) by apply /eqP; apply: (K2 w).
    by rewrite Heq.
    move => y Hy.
    destruct (f y == w) eqn: Hfy.
    -- apply /eqP.
       move/eqP: Hfy => Hfy.
       rewrite -Hfy.
       exact (K1 y).
    -- exfalso. move/eqP: Hy; auto.
       move => x.
       destruct (f x == w) eqn: Hfw; auto.
       exact r_nonneg.
Qed.

Lemma sampleFsq_support { F : finType} { w0 : F }
                        {a1 a2 : F} {f : F -> F}
                        (f_bij : bijective f)
                        (H : 0 < (@sampleFsq_f F w0 f f_bij) (a1, a2)) : f a1 == a2.
Proof.
  simpl in H. rewrite /f_dprod /= in H.
  case (f a1 == a2) eqn:Heq; auto.
    by rewrite ltrr in H.
Qed.

Lemma support_sub_diag_mgs { A : choiceType }
                           ( d : SDistr (prod_choiceType A A) )
                           (Hsupp : forall a1 a2, 0 < d (a1, a2) -> a1 = a2) :
  forall a : A, lmg d a = d (a, a) /\ rmg d a = d (a, a).
Proof.
  move => a.
  rewrite /lmg /rmg dfstE dsndE.
  split.
  - rewrite psum_sum.
    rewrite (sum_seq1 a).
    + reflexivity.
    + move => y Hdd. specialize (Hsupp a y).
      assert (0 < d (a, y)) as Hd.
      { rewrite ltr_def. apply /andP.
        split.
        - assumption.
        - apply (ge0_mu d). }
      specialize (Hsupp Hd). rewrite Hsupp. auto.
    + move => x. apply (ge0_mu d).
  - rewrite psum_sum.
    rewrite (sum_seq1 a).
    + reflexivity.
    + move => y Hdd. specialize (Hsupp y a).
      assert (0 < d (y, a)) as Hd.
      { rewrite ltr_def. apply /andP.
        split.
        - assumption.
        - apply (ge0_mu d).  }
      specialize (Hsupp Hd). rewrite Hsupp. auto.
    + move => x. apply (ge0_mu d).
Qed.


Section prod_uniform.
(* (mkdistrd (λ f : fin_family i * fin_family j, r)) *)

  Let SD_bind
      {A B : choiceType}
      (m : SDistr_carrier A)
      (k : A -> SDistr_carrier B) :=
    SDistr_bind A B k m.
  Let SD_ret {A : choiceType}
      (a : A) :=
    SDistr_unit A a.

  Context {X Y : finType}.
  Context {x0 : X} {y0 : Y}.

  Arguments r _ {_}.

  Lemma prod_uniform :
  @uniform_F (prod_finType X Y) (x0,y0) =
  SD_bind (@uniform_F X x0) (fun x =>
  SD_bind (@uniform_F Y y0) (fun y =>
  SD_ret (x,y))).
  Proof.
    apply distr_ext. move=> [x y].
    rewrite !/SD_bind !/SDistr_bind /dlet /=. unlock.
    rewrite /mlet /=.
    rewrite psumZ. all: revgoals. apply r_nonneg.
    erewrite eq_psum. all: revgoals.
    move=> x1. rewrite psumZ. all: swap 1 2. apply r_nonneg.
    reflexivity.
    rewrite psumZ. all: revgoals. apply r_nonneg.
    rewrite GRing.Theory.mulrA.
    assert ( psum_ret :
psum (λ x1 : X, psum (λ x2 : Y, SD_ret (x1, x2) (x, y))) = 1 ).
    rewrite /SD_ret.
    pose hlp := (  @psum_pair _ X Y
    (fun (x12 : prod_finType X Y) =>
       let (x1,x2) := x12 in 
       SDistr_unit (prod_choiceType X Y) (x1,x2) (x,y))).
    rewrite -hlp.
    unshelve erewrite eq_psum. exact (SDistr_unit _ (x,y)).
    apply psum_SDistr_unit.
    move=> [x1 x2] /=. rewrite /SDistr_unit.
    rewrite !dunit1E.
    rewrite eq_sym. reflexivity.
    unshelve eapply eq_summable. exact (SDistr_unit _ (x,y)).
    move=> [x1 x2] /=. rewrite /SDistr_unit.    
    rewrite !dunit1E. rewrite eq_sym. reflexivity.
    apply summable_mu.
    rewrite psum_ret. rewrite GRing.mulr1.
    rewrite !/r. rewrite card_prod.
    rewrite GRing.Theory.mulf_div.
    rewrite GRing.mulr1.
    f_equal. f_equal.
    by rewrite -intrM. 
Qed. 
    
End prod_uniform.


