Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra distr reals realsum boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From Crypt Require Import Axioms.

Import Num.Theory Order.LTheory.

(** Extensionality lemmas *)
Lemma distr_ext : forall (A : choiceType) (mu nu : {distr A/R}),
    distr.mu mu =1 distr.mu nu -> mu = nu.
Proof.
  move=> A [mu +++] [nu +++] /= /funext mu_eq_nu.
  rewrite {}mu_eq_nu; move=> *; f_equal.
  all: apply proof_irrelevance.
Qed.

Lemma eq_dlet [A B : choiceType] (m : {distr A/R})
      (f g : A -> {distr B /R}) :
  f =1 g -> \dlet_(x <- m) f x = \dlet_(x <- m) g x.
Proof.
  move=> fg; apply: distr_ext=> i; rewrite 2!dletE.
  apply: eq_psum=> a; f_equal; by rewrite fg.
Qed.

(** Definition of the model for the unary semantics *)

Section Def.
  Context (S : choiceType).

  (* carrier for unary specifications /
     model for single probabilistic programs with state space S *)
  Definition stsubdistr (A : choiceType) := S -> {distr (A * S) /R}.

  Definition ret [A : choiceType] (a : A) : stsubdistr A :=
    fun s => dunit (a,s).

  Definition bind [A B : choiceType] (m : stsubdistr A) (f : A -> stsubdistr B) :=
    fun s0 => \dlet_(p <- m s0) f p.1 p.2.

  (* Monadic laws -- wrapper around existing lemmas *)
  Lemma bind_ret [A B : choiceType] (a : A) (f : A -> stsubdistr B)
    : bind (ret a) f = f a.
  Proof. extensionality s; apply: distr_ext ; apply: dlet_unit. Qed.

  Lemma ret_bind [A : choiceType] (m : stsubdistr A) : bind m (@ret _) = m.
  Proof.
    extensionality s ; apply: distr_ext=> a; rewrite /bind /ret.
    under eq_dlet do rewrite -surjective_pairing.
    apply: dlet_dunit_id.
  Qed.

  Lemma bind_bind [A B C : choiceType]
        (m : stsubdistr A)
        (f : A -> stsubdistr B)
        (g : B -> stsubdistr C) :
    bind m (fun a => bind (f a) g) = bind (bind m f) g.
  Proof.
    extensionality s; apply distr_ext=> a; rewrite /bind.
    by rewrite dlet_dlet.
  Qed.


  Section Order.
    Context [A : choiceType].

    (* The eqType and choiceType instances are given
       by excluded-middle and the axiom of choice *)
    Canonical stsubdistr_eqType :=
      EqType (stsubdistr A) (equality_mixin_of_Type (stsubdistr A)).
    Canonical stsubdistr_choiceType := choice_of_Type (stsubdistr A).

    (** Order between specifications *)
    Definition stsubdistr_le : rel (stsubdistr A) :=
      fun d0 d1 => `[< forall s0 a s1, (mu (d0 s0) (a, s1) <= mu (d1 s0) (a, s1))%O>].

    (* I don't think I really care about lt so let's put the tautological def *)
    Definition stsubdistr_lt : rel (stsubdistr A) :=
      fun d0 d1 => (d1 != d0) && stsubdistr_le d0 d1.

    Lemma stsubdistr_le_refl : reflexive stsubdistr_le.
    Proof. move=> g; apply/asboolP=> *; apply: le_refl. Qed.

    Lemma stsubdistr_le_anti : antisymmetric stsubdistr_le.
    Proof.
      move=> f g /andP [] /asboolP fg /asboolP gf.
      extensionality s; apply: distr_ext=> -[a s'].
      apply: le_anti; rewrite fg gf //.
    Qed.

    Lemma stsubdistr_le_trans : transitive stsubdistr_le.
    Proof.
      move=> g f h /asboolP gf /asboolP fh; apply/asboolP=> *.
      apply: le_trans; auto.
    Qed.

    Definition stsubdistr_porderMixin :=
      @Order.POrder.Mixin _ _ stsubdistr_le stsubdistr_lt
                          ltac:(reflexivity) stsubdistr_le_refl
                          stsubdistr_le_anti stsubdistr_le_trans.

    Canonical stsubdistr_porderType := POrderType ring_display (stsubdistr A) stsubdistr_porderMixin.

    (* Lemma stsubdistr_distinct (d0 d1 : stsubdistr A) : d0 < d1 ->  exists s0 a s1, (mu (d0 s0) (a, s1) < mu (d1 s0) (a, s1))%O. *)

  End Order.

  Open Scope order_scope.

  (** Bind is monotone with respect to the order we endowed the specs with *)
  Lemma bind_monotone [A B : choiceType]
        (m0 m1 : stsubdistr A) (f0 f1 : A -> stsubdistr B) :
    m0 <= m1 -> (forall a, f0 a <= f1 a) -> bind m0 f0 <= bind m1 f1 :> stsubdistr B.
  Proof.
    move=> /asboolP m01 f01; apply/asboolP=> s0 b s1.
    rewrite /bind 2!dletE.
    apply: le_psum; last apply: summable_mlet.
    move=> [a ?]; apply/andP;split.
    - apply: mulr_ge0; apply: ge0_mu.
    - apply: ler_pmul; try apply: ge0_mu; first apply: m01.
      move: {f01}(f01 a)=> /asboolP //.
  Qed.
End Def.
