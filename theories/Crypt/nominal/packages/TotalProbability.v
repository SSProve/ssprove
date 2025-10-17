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
  Lemma Pr_code_ret {A : choiceType} {x : A} {h} :
    Pr_code (ret x) h = dunit (x, h).
  Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

  Lemma Pr_code_get {B : choiceType} {l : Location} {k : l → raw_code B} {h} :
    Pr_code (x ← get l ;; k x) h = Pr_code (k (get_heap h l)) h.
  Proof. cbn; done. Qed.

  Lemma Pr_code_put {B : choiceType} {l : Location} {a} {k : raw_code B} {h} :
    Pr_code (#put l := a ;; k) h = Pr_code k (set_heap h l a).
  Proof. cbn; done. Qed.

  Lemma Pr_code_call {B : choiceType} {o : opsig} {a : src o}
      {k : tgt o → raw_code B} {h} :
    Pr_code (x ← op o ⋅ a ;; k x) h = Pr_code (k (chCanonical _)) h.
  Proof. cbn; done. Qed.

  Lemma Pr_code_sample {A : choiceType} {op' : Op}
      {k : Arit op' → raw_code A} {h} :
    Pr_code (x ← sample op' ;; k x) h = \dlet_(x <- op'.π2) Pr_code (k x) h. 
  Proof. cbn. rewrite 2!SDistr_rightneutral //. Qed.

  Lemma Pr_code_bind {T T' : choiceType} {c} {f : T → raw_code T'} {h}
    : Pr_code (x ← c ;; f x) h
    = \dlet_(y <- Pr_code c h) Pr_code (f y.1) y.2.
  Proof.
    move: h.
    induction c; cbn [bind]; intros h.
    - rewrite Pr_code_ret dlet_unit_ext //.
    - rewrite 2!Pr_code_call //.
    - rewrite 2!Pr_code_get //.
    - rewrite 2!Pr_code_put //.
    - rewrite 2!Pr_code_sample dlet_dlet_ext.
      by apply eq_dlet.
  Qed.

  Lemma Pr_code_fail {T} {h} : Pr_code (@fail T) h = dnull.
  Proof. rewrite Pr_code_sample dlet_null_ext //. Qed.

  (* Pr_rand *)
  Definition Pr_rand {T} (c : raw_code T ) : distr R T
    := dfst (Pr_code c emptym).

  Lemma Pr_rand_ret {A : choiceType} {x : A} :
    Pr_rand (ret x) = dunit x.
  Proof. rewrite /Pr_rand Pr_code_ret /(dfst _) dlet_unit_ext //. Qed.

  Lemma Pr_rand_sample {A : choiceType} {op' : Op} {k : Arit op' → raw_code A} :
    Pr_rand (x ← sample op' ;; k x) = \dlet_(x <- op'.π2) Pr_rand (k x).
  Proof.  rewrite /Pr_rand Pr_code_sample /(dfst _) dlet_dlet_ext //. Qed.

  Lemma Pr_Pr_rand {G} :
    Pr G true = Pr_rand (resolve G RUN tt) true.
  Proof.
    unfold Pr, SDistr_bind, SDistr_unit, Pr_op, Pr_rand, dfst.
    by apply dlet_f_equal => [[b h]].
  Qed.

  Lemma Pr_code_rand {T T' : choiceType} {c} {f : T → raw_code T'} {h}
    : ValidCode emptym [interface] c
    → Pr_code (x ← c ;; f x) h
    = \dlet_(x <- Pr_rand c) Pr_code (f x) h.
  Proof.
    elim.
    2-4: intros; exfalso; eapply fhas_empty; eassumption.
    - intros x => /=.
      rewrite /Pr_rand Pr_code_ret /(dfst _) 2!dlet_unit_ext //.
    - intros op k VA IH => /=.
      rewrite /Pr_rand 2!Pr_code_sample.
      rewrite 2!dlet_dlet_ext.
      f_equal; extensionality x.
      rewrite IH dlet_dlet_ext //.
  Qed.
End PrCodeLemmas.


Section LosslessCodeLemmas.

  Class LosslessCode {A} (c : raw_code A) :=
    lossless : psum (Pr_rand c) = 1%R.

  #[export] Instance Lossless_ret {A : choiceType} (a : A)
    : LosslessCode (ret a).
  Proof.
    rewrite /LosslessCode Pr_rand_ret.
    apply Couplings.psum_SDistr_unit.
  Qed.

  #[export] Instance Lossless_sample {A} D (k : _ → raw_code A)
    : LosslessOp D
    → (∀ x, LosslessCode (k x))
    → LosslessCode (x ← sample D ;; k x).
  Proof.
    intros H IH. unfold LosslessCode.
    rewrite Pr_rand_sample.
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
End LosslessCodeLemmas.


Lemma Adv_Pr {I} {G G' A : nom_package} `{ValidPackage (loc A) I A_export A} :
  perfect I G G' → Pr' (A ∘ G)%sep true = Pr' (A ∘ G')%sep true.
Proof.
  intros H'.
  apply GRing.Theory.subr0_eq.
  apply Num.Theory.normr0_eq0.
  eapply (H' _ H).
Qed.


(* PICK game *)

Definition pick := 57.

Definition IPICK T := [interface [ pick ] : { 'unit ~> T }].

Definition PICK {T : choice_type} (x : T) : game (IPICK T) :=
  [package emptym ;
    [ pick ] : { 'unit ~> T } 'tt {
      ret x
    } ].

Definition cell T : Location := (0%N, 'option T).

Definition RAND {T : choice_type} (c : code emptym emptym T)
  : game (IPICK T) :=
  [package [fmap cell T] ;
    [ pick ] : { 'unit ~> T } 'tt {
      mr ← get cell T ;;
      match mr with
      | Some r => ret r
      | None =>
        r ← c ;;
        #put cell T := Some r ;;
        ret r
      end
    } ].


Section TotalProbability.

Context {T : choice_type}.
Context (c : code emptym emptym T).


Lemma Pr_code_RAND_Some {LA} {T'} {A : raw_code T'} {f f' : T} {h} :
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
    simplify_linking.
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
    apply eq_dlet => x.
    by apply H0.
Qed.

Lemma Pr_code_RAND {LA} {T'} {A : raw_code T'} {h} :
  fseparate LA [fmap cell T] →
  LosslessCode c →
  ValidCode LA (IPICK T) A →
  get_heap h (cell T) = None →
  Pr_code (code_link A (RAND c)) h
    = \dlet_(f <- Pr_rand c) Pr_code (code_link A (RAND {code ret f})) h.
Proof.
  intros SEP LL VA H'.
  apply distr_ext.
  move: h H'; induction VA.
  - intros h H' y.
    rewrite Pr_code_ret.
    rewrite dletC pr_predT LL GRing.mul1r //.
  - intros h H' y.
    fmap_invert H.
    destruct x.
    cbn [bind code_link].
    simplify_linking.
    rewrite Pr_code_get H'.
    rewrite bind_assoc.
    rewrite Pr_code_rand.
    apply dlet_f_equal => x.
    rewrite Pr_code_put.
    simplify_linking.
    rewrite Pr_code_get H'.
    cbn [bind].
    rewrite Pr_code_put.
    erewrite Pr_code_RAND_Some.
    + reflexivity.
    + apply SEP.
    + apply H0.
    + rewrite get_set_heap_eq //.
  - intros h H' y.
    cbn [code_link].
    rewrite Pr_code_get.
    rewrite H1 //.
  - intros h H' y.
    cbn [code_link].
    rewrite Pr_code_put.
    rewrite IHVA //.
    rewrite get_set_heap_neq //.
    (* TODO: extract rest as lemma *)
    move: (notin_has_separate _ _ _ H SEP) => /dommPn H0.
    apply /eqP => H''.
    by rewrite -H'' in H0.
  - intros h H' y.
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

Lemma Pr_RAND {LA} {A : raw_package} :
  fseparate LA [fmap cell T] →
  LosslessCode c →
  ValidPackage LA (IPICK T) A_export A →
  Pr (A ∘ RAND c) = \dlet_(x <- Pr_rand c) Pr (A ∘ RAND {code ret x}).
Proof.
  intros SEP LL VA.
  apply distr_ext => b.
  unfold Pr, SDistr_bind, SDistr_unit, Pr_op.
  rewrite resolve_link.

  assert (H : fhas A_export RUN); [ fmap_solve |].
  pose proof (valid_resolve _ _ _ _ RUN tt VA H).
  rewrite (Pr_code_RAND SEP LL H0).
  2: rewrite get_empty_heap //.
  rewrite dlet_dlet.
  apply dlet_f_equal => y.
  rewrite resolve_link => //.
Qed.

Lemma PICK_dirac_perfect (x : T) :
  perfect (IPICK T) (RAND {code ret x}) (PICK x).
Proof.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (heap_ignore [fmap cell T]
    ⋊ single_lhs (cell T) (λ v, v = None ∨ v = Some x)) ).
  { ssprove_invariant. by left. }
  simplify_eq_rel m.
  destruct m => /=.
  ssprove_code_simpl; simpl.
  apply r_get_remember_lhs => y.
  ssprove_rem_rel 0.
  elim => ?; subst.
  - apply r_put_lhs.
    ssprove_restore_mem. { ssprove_invariant. }
    by apply r_ret.
  - apply r_forget_lhs.
    by apply r_ret.
Qed.

Lemma TotalProbability {A : nom_package} :
  LosslessCode c →
  ValidPackage (loc A) (IPICK T) A_export A →
  Pr' (A ∘ RAND c)%sep true = (\dlet_(x <- Pr_rand c) Pr' (A ∘ PICK x)%sep) true.
Proof.
  intros LC VA.
  pose (π := fresh (as_nom (RAND c), [fmap cell T] : Locations) (A, loc A)).
  rewrite -{1}(@rename_alpha _ A π).
  rewrite {1}/Pr' -link_sep_link.
  2: eauto with nominal_db.
  rewrite Pr_RAND.
  2: rewrite fseparate_disj; eauto with nominal_db.
  rewrite 2!dletE.
  apply eq_psum => x.
  f_equal.
  rewrite -(Adv_Pr (PICK_dirac_perfect _)).
  rewrite -{2}(@rename_alpha _ A π).
  rewrite {1}/Pr' -link_sep_link //.
  unfold disj.
  change (supp (as_nom (RAND {code ret x})))
    with (supp ([fmap cell T] : Locations)).
  eauto with nominal_db.
Qed.

End TotalProbability.
