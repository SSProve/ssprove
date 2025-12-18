From Coq Require Import Utf8.
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


(* PICK game *)

Definition pick := 57.

Definition IPICK T := [interface [ pick ] : { 'unit ~> T }].

Definition PICK {T : choice_type} (x : T) : game (IPICK T) :=
  [package emptym ;
    [ pick ] : { 'unit ~> T } 'tt {
      ret x
    } ].

Definition cell T : Location := mkloc 58 (None : 'option T).

Definition RAND {T : choice_type} (c : dist T)
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
Context (c : dist T).


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
    = \dlet_(f <- Pr_fst c) Pr_code (code_link A (RAND {code ret f})) h.
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
    rewrite Pr_code_fst.
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
  Pr (A ∘ RAND c) = \dlet_(x <- Pr_fst c) Pr (A ∘ RAND {code ret x}).
Proof.
  intros SEP LL VA. apply distr_ext => b.
  rewrite /Pr /SDistr_bind /SDistr_unit /Pr_op resolve_link.
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
  Pr' (A ∘ RAND c)%sep true = (\dlet_(x <- Pr_fst c) Pr' (A ∘ PICK x)%sep) true.
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
  rewrite -(perfect_Pr (PICK_dirac_perfect _)).
  rewrite -{2}(@rename_alpha _ A π).
  rewrite {1}/Pr' -link_sep_link // /disj.
  change (supp (as_nom (RAND {code ret x})))
    with (supp ([fmap cell T] : Locations)).
  eauto with nominal_db.
Qed.

End TotalProbability.
