From Stdlib Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
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

Section Async.
  Definition PRIME := 55%N.
  Definition TRIGGER := 56%N.

  Definition I_ASYNC (S T : choice_type) :=
    [interface
      [ PRIME  ] : { S ~> 'unit } ;
      [ TRIGGER ] : { 'unit ~> T }
    ].

  Definition eager_loc (T : choice_type) := mkloc 53 (None : option T).
  Definition lazy_loc (S : choice_type) := mkloc 53 (None : option S).

  Context {S T : choice_type}.
  Context (c : S → dist T).
  Context `{LL : ∀ t, LosslessCode (c t)}.

  Definition EAGER :
    game (I_ASYNC S T) :=
    [package [fmap eager_loc T ] ;
      [ PRIME ] : { S ~> 'unit } (t) {
        r ← c t ;;
        #put eager_loc T := Some r ;;
        ret tt
      } ;
      [ TRIGGER ] : { 'unit ~> T } 'tt {
        r ← getSome eager_loc T ;;
        #put eager_loc T := None ;;
        ret r
      }
    ].

  Definition LAZY :
    game (I_ASYNC S T) :=
    [package [fmap lazy_loc S ] ;
      [ PRIME ] : { S ~> 'unit } (t) {
        #put lazy_loc S := Some t ;;
        ret tt
      } ;
      [ TRIGGER ] : { 'unit ~> T } 'tt {
        t ← getSome lazy_loc S ;;
        #put lazy_loc S := None ;;
        r ← c t ;;
        ret r
      }
    ].

  Definition ASYNC b := if b then EAGER else LAZY.

  Lemma neq_fst {L L' : Locations} {l l' : Location}
    : fseparate L L' → fhas L l → fhas L' l' → l.1 != l'.1.
  Proof.
    move=> HSEP HL HL'.
    move: (notin_has_separate _ _ _ HL HSEP) => /negP Hdomm.
    apply /eqP => Heq. apply Hdomm. rewrite Heq. by apply fhas_in.
  Qed.

  Definition tape {U} : option S → (option T → distr R U) → distr R U := λ o f,
    match o with
    | None => f None
    | Some t => \dlet_(x <- Pr_fst (c t)) f (Some x)
    end.

  Lemma set_set h v1 v2 :
    set_heap (set_heap h (lazy_loc S) v1) (eager_loc T) v2 = set_heap h (eager_loc T) v2.
  Proof.
    rewrite /set_heap. apply eq_fmap => x. rewrite 3!setmE.
    simpl. by destruct (x == 53%N)%B.
  Qed.

  Lemma ASYNC_0 LA (A : raw_code bool) h :
    ValidCode LA (I_ASYNC S T) A →
    fseparate LA [fmap eager_loc T] →
    fseparate LA [fmap lazy_loc S] →
    dfst (tape (get_heap h (lazy_loc S))
      (λ y, Pr_code (code_link A EAGER) (set_heap h (eager_loc T) y)))
      = dfst (Pr_code (code_link A LAZY) h).
  Proof.
    intros VA SEP1 SEP2.
    move: h; induction VA => h; cbn [code_link].
    - destruct (get_heap h (lazy_loc S)) => /=.
      + rewrite Pr_code_ret 2!dmarginE dlet_unit_ext /=.
        rewrite dlet_dlet_ext.
        under eq_dlet. { intros ?. rewrite Pr_code_ret dlet_unit_ext /=. over. }
        by rewrite Pr_fstC.
      + by rewrite 2!Pr_code_ret 2!dmarginE 2!dlet_unit_ext.
    - rewrite Pr_code_bind.
      fmap_invert H.
      + simplify_linking.
        destruct (get_heap h (lazy_loc S)) => /=.
        * rewrite bind_assoc.
          under eq_dlet. {
            intros ?. rewrite Pr_code_fst.
            under eq_dlet. {
              intros ?. rewrite Pr_code_put set_heap_contract. over. }
            over. }
          rewrite /= Pr_fstC.
          rewrite Pr_code_put Pr_code_ret dlet_unit_ext /=.
          specialize (H1 tt (set_heap h (lazy_loc S) (Some x))).
          rewrite -H1 get_set_heap_eq /=.
          f_equal. symmetry.
          apply eq_dlet => ?. by rewrite set_set.
        * rewrite bind_assoc Pr_code_fst.
          under eq_dlet. {
            intros ?. rewrite Pr_code_put set_heap_contract.
            over. }
          rewrite /= Pr_code_put Pr_code_ret dlet_unit_ext /=.
          specialize (H1 tt (set_heap h (lazy_loc S) (Some x))).
          rewrite -H1 get_set_heap_eq /=.
          f_equal. apply eq_dlet => ?. by rewrite set_set.
      + simplify_linking.
        destruct x.
        rewrite Pr_code_get.
        destruct (get_heap h (lazy_loc S)) => /=.
        * under eq_dlet. { intros ?.
            rewrite Pr_code_get get_set_heap_eq /=.
            rewrite Pr_code_put set_heap_contract. over. }
          rewrite Pr_code_put Pr_code_fst. symmetry.
          rewrite dlet_dlet_ext.
          under eq_dlet. { intros ?.
            rewrite Pr_code_ret dlet_unit_ext /=. over. }
          rewrite 2!dmarginE dlet_dlet_ext. symmetry.
          rewrite dlet_dlet_ext. apply eq_dlet => t.
          specialize (H1 t (set_heap h (lazy_loc S) None)).
          rewrite 2!dmarginE get_set_heap_eq /= in H1.
          by rewrite -H1 set_set.
        * rewrite Pr_code_get get_set_heap_eq /=.
          rewrite Pr_code_sample /= dlet_null_ext.
          by rewrite Pr_code_fail dlet_null_ext.
    - rewrite Pr_code_get -H1.
      epose proof (neq_fst SEP2 H).
      assert (l.1 != (lazy_loc S).1). { apply H2. fmap_solve. }
      destruct (get_heap h (lazy_loc S)); cbn [tape].
      + under eq_dlet. { intros ?.
          rewrite Pr_code_get.
          rewrite get_set_heap_neq //.
          over. }
        done.
      + rewrite Pr_code_get.
        by rewrite get_set_heap_neq.
    - rewrite Pr_code_put -IHVA.
      epose proof (neq_fst SEP2 H).
      assert ((lazy_loc S).1 != l.1). { rewrite eq_sym. apply H0. fmap_solve. }
      rewrite get_set_heap_neq //.
      destruct (get_heap h (lazy_loc S)); cbn [tape].
      + under eq_dlet. { intros ?. rewrite Pr_code_put set_heap_commut //. over. }
        done.
      + by rewrite Pr_code_put set_heap_commut.
    - rewrite Pr_code_sample.
      destruct (get_heap h (lazy_loc S)) eqn:E; cbn [tape].
      + rewrite 2!dfst_dlet_commut.
        under eq_dlet. { intros ?. rewrite Pr_code_sample dfst_dlet_commut. over. }
        rewrite dlet_commut. apply eq_dlet => v.
        specialize (H0 v h). rewrite -H0. rewrite E. cbn [tape].
        by rewrite dfst_dlet_commut.
      + rewrite Pr_code_sample 2!dfst_dlet_commut.
        apply eq_dlet => v.
        specialize (H0 v h). rewrite -H0 E.
        by cbn [tape].
  Qed.

  Lemma ASYNC_0_Adv LA (A : raw_package) :
    ValidPackage LA (I_ASYNC S T) A_export A →
    fseparate LA [fmap eager_loc T] →
    fseparate LA [fmap lazy_loc S] →
    Pr (A ∘ EAGER) true = Pr (A ∘ LAZY) true.
  Proof.
    intros VA SEP1 SEP2.
    rewrite 2!Pr_Pr_code 2!resolve_link.
    assert (H : fhas A_export RUN); [ fmap_solve |].
    pose proof (valid_resolve _ _ _ _ RUN tt VA H).
    rewrite -(ASYNC_0 _ _ empty_heap H0 SEP1 SEP2).
    rewrite get_empty_heap /heap_init /lazy_loc. cbn [mkloc snd projT2 tape].

    f_equal.
    assert (HNone : get_heap empty_heap (eager_loc T) = None).
    { by rewrite get_empty_heap. }
    move: empty_heap HNone.
    induction H0 => h HNone; cbn [code_link].
    - by rewrite 2!Pr_code_ret 2!dmarginE 2!dlet_unit_ext.
    - rewrite Pr_code_bind.
      fmap_invert H0.
      + simplify_linking.
        rewrite Pr_code_fst dlet_dlet_ext. symmetry.
        rewrite bind_assoc Pr_code_fst.
        rewrite 2!dfst_dlet_commut. apply eq_dlet => x'.
        rewrite Pr_code_put. symmetry. rewrite Pr_code_put Pr_code_ret.
        by rewrite dlet_unit_ext set_heap_contract.
      + simplify_linking.
        destruct x.
        rewrite Pr_code_get HNone /= Pr_code_fail dlet_null_ext.
        rewrite Pr_code_get get_set_heap_eq Pr_code_sample /=.
        by rewrite dlet_null_ext.
    - epose proof (neq_fst SEP2 H0).
      assert (l.1 != (lazy_loc S).1). { apply H3. fmap_solve. }
      rewrite 2!Pr_code_get get_set_heap_neq; auto.
    - rewrite 2!Pr_code_put.
      epose proof (neq_fst SEP1 H0).
      assert ((eager_loc T).1 != l.1). { rewrite eq_sym. apply H2. fmap_solve. }
      rewrite set_heap_commut; auto.
      apply IHvalid_code.
      by rewrite get_set_heap_neq.
    - rewrite 2!Pr_code_sample 2!dfst_dlet_commut. apply eq_dlet.
      intros ?. by apply H1.
  Qed.

  Theorem ASYNC_perfect : perfect (I_ASYNC S T) EAGER LAZY.
  Proof.
    intros A VA. eapply Adv_nom_ind; [| apply VA].
    intros A' LA VA' _ SEP1 SEP2.
    by rewrite /AdvantageE ASYNC_0_Adv // GRing.subrr Num.Theory.normr0.
  Qed.
End Async.
