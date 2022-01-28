From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra distr reals realsum boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Axioms choice_type pkg_core_definition pkg_heap.

Import Num.Theory Order.LTheory.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(** Extensionality lemmas *)

Lemma distr_ext :
  ∀ (A : choiceType) (mu nu : {distr A/R}),
    distr.mu mu =1 distr.mu nu →
    mu = nu.
Proof.
  move=> A [mu +++] [nu +++] /= /funext mu_eq_nu.
  rewrite {}mu_eq_nu. move=> *. f_equal.
  all: apply proof_irrelevance.
Qed.

Lemma eq_dlet [A B : choiceType] :
  ∀ (m : {distr A/R}) (f g : A -> {distr B /R}),
    f =1 g →
    \dlet_(x <- m) f x = \dlet_(x <- m) g x.
Proof.
  intros m f g fg.
  apply distr_ext. intro i.
  rewrite 2!dletE.
  apply eq_psum. intro a.
  f_equal. rewrite fg. reflexivity.
Qed.

Lemma eq_dlet_partial [A B : choiceType] :
  ∀ (m : {distr A/R}) (f g : A -> {distr B /R}),
    (∀ x, m x ≠ 0%R → f x = g x) →
    \dlet_(x <- m) f x = \dlet_(x <- m) g x.
Proof.
  intros m f g h.
  apply distr_ext. intro i.
  rewrite 2!dletE. apply eq_psum. intro a.
  destruct (m a == 0)%R eqn:e.
  - move: e => /eqP e. rewrite e. rewrite 2!GRing.mul0r. reflexivity.
  - f_equal. rewrite h. 2:{ apply /eqP. rewrite e. reflexivity. }
    reflexivity.
Qed.




(* two helper functions to help with convoy patterns on bool
   (is there an idiomatic ssreflect/mathcomp way to do that ?) *)
Definition bool_depelim (X : Type) (b : bool)
  (htrue : b = true → X) (hfalse : b = false → X) : X :=
  (if b as b0 return b = b0 → X then htrue else hfalse) erefl.

Lemma bool_depelim_true :
  ∀ (X : Type) (b : bool) (htrue : b = true → X) (hfalse : b = false → X)
    (e : b = true),
    bool_depelim X b htrue hfalse = htrue e.
Proof.
  intros. subst. reflexivity.
Qed.

(* helper lemma for multiplication of reals *)
Lemma R_no0div : ∀ (u v : R), (u * v ≠ 0 → u ≠ 0 ∧ v ≠ 0)%R.
Proof.
  intros u v h.
  split. all: revert h. all: apply contra_not. all: intro h. all: subst.
  - apply GRing.mul0r.
  - apply GRing.mulr0.
Qed.

(** Definition of the model for the unary semantics *)

Module Def.

Section Def.

  Context (S : choiceType).

  (* carrier for unary specifications /
     model for single probabilistic programs with state space S *)
  Definition stsubdistr (A : choiceType) := S → {distr (A * S) / R}.

  Definition stsubnull (A : choiceType) : stsubdistr A := fun _ => dnull.

  Definition ret [A : choiceType] (a : A) : stsubdistr A :=
    λ s, dunit (a,s).

  Definition bind [A B : choiceType] (m : stsubdistr A) (f : A → stsubdistr B) :=
    λ s₀, \dlet_(p <- m s₀) f p.1 p.2.

  (* Monadic laws -- wrapper around existing lemmas *)
  Lemma bind_ret [A B : choiceType] :
    ∀ (a : A) (f : A → stsubdistr B),
      bind (ret a) f = f a.
  Proof.
    intros a f.
    extensionality s. apply distr_ext. apply: dlet_unit.
  Qed.

  Lemma ret_bind [A : choiceType] :
    ∀ (m : stsubdistr A), bind m (@ret _) = m.
  Proof.
    intros m.
    extensionality s. apply distr_ext. intro a.
    rewrite /bind /ret.
    under eq_dlet do rewrite -surjective_pairing.
    apply dlet_dunit_id.
  Qed.

  Lemma bind_bind [A B C : choiceType] :
    ∀ (m : stsubdistr A)
      (f : A → stsubdistr B)
      (g : B → stsubdistr C),
      bind m (λ a, bind (f a) g) = bind (bind m f) g.
  Proof.
    intros m f g.
    extensionality s. apply distr_ext. intro a.
    rewrite /bind. rewrite dlet_dlet. reflexivity.
  Qed.

  Lemma bind_not_null [A B : choiceType] :
    ∀ (m : stsubdistr A) (f : A → stsubdistr B) map p,
      bind m f map p ≠ 0%R →
      ∃ p₀, m map p₀ ≠ 0%R ∧ f p₀.1 p₀.2 p ≠ 0%R.
  Proof.
    intros m f map p.
    unfold bind. rewrite dletE.
    move /neq0_psum => [p₀]. move /R_no0div => h.
    exists p₀. assumption.
  Qed.

  Lemma bind_ext [A B : choiceType] (m : stsubdistr A) (f g : A -> stsubdistr B) :
    f =1 g -> bind m f = bind m g.
  Proof. move=> fg; f_equal; extensionality x; apply: fg. Qed.


  (* Actually unused for now... *)
  Section Order.

    Context [A : choiceType].

    (* The eqType and choiceType instances are given
       by excluded-middle and the axiom of choice *)
    Canonical stsubdistr_eqType :=
      EqType (stsubdistr A) (equality_mixin_of_Type (stsubdistr A)).
    Canonical stsubdistr_choiceType := choice_of_Type (stsubdistr A).

    (** Order between specifications *)
    Definition stsubdistr_le : rel (stsubdistr A) :=
      λ d₀ d₁, `[< ∀ s₀ a s₁, (mu (d₀ s₀) (a, s₁) <= mu (d₁ s₀) (a, s₁))%O >].

    (* I don't think I really care about lt so let's put the tautological def *)
    Definition stsubdistr_lt : rel (stsubdistr A) :=
      λ d₀ d₁, (d₁ != d₀) && stsubdistr_le d₀ d₁.

    Lemma stsubdistr_le_refl : reflexive stsubdistr_le.
    Proof.
      intros g.
      apply /asboolP. intros.
      apply le_refl.
    Qed.

    Lemma stsubdistr_le_anti : antisymmetric stsubdistr_le.
    Proof.
      move=> f g /andP [] /asboolP fg /asboolP gf.
      extensionality s. apply: distr_ext => -[a s'].
      apply: le_anti. rewrite fg gf //.
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

    Canonical stsubdistr_porderType :=
      POrderType ring_display (stsubdistr A) stsubdistr_porderMixin.

    (* Lemma stsubdistr_distinct (d0 d1 : stsubdistr A) : d0 < d1 ->  exists s0 a s1, (mu (d0 s0) (a, s1) < mu (d1 s0) (a, s1))%O. *)

  End Order.

  #[local] Open Scope order_scope.

  (** Bind is monotone with respect to the order we endowed the specs with *)
  Lemma bind_monotone [A B : choiceType] :
    ∀ (m₀ m₁ : stsubdistr A) (f₀ f₁ : A → stsubdistr B),
      m₀ <= m₁ →
      (∀ a, f₀ a <= f₁ a) →
      bind m₀ f₁ <= bind m₁ f₁ :> stsubdistr B.
  Proof.
    intros m₀ m₁ f₀ f₁.
    move=> /asboolP m01 f01; apply/asboolP=> s0 b s1.
    rewrite /bind 2!dletE.
    apply: le_psum; last apply: summable_mlet.
    move=> [a ?]; apply/andP;split.
    - apply: mulr_ge0; apply: ge0_mu.
    - apply: ler_pmul; try apply: ge0_mu; first apply: m01.
      move: {f01}(f01 a)=> /asboolP //.
  Qed.

End Def.

Arguments ret [_ _] _.
Arguments bind [_ _ _] _ _.

End Def.


(** Semantic evaluation of code and commands *)
Section Evaluation.
  #[local]
  Notation M := (Def.stsubdistr heap_choiceType).

  (** Assume an interpretation of operations *)
  Context (eval_op : ∀ o, src o → M (tgt o)).

  Definition eval [A : choiceType] : raw_code A → M A.
  Proof.
    elim.
    - apply: Def.ret.
    - intros o x k ih.
      exact (Def.bind (eval_op o x) ih).
    - intros l k ih.
      exact (λ map, let v := get_heap map l in ih v map).
    - intros l v k ih.
      exact (λ map, ih (set_heap map l v)).
    - intros [X sampleX] k ih.
      exact (λ map, \dlet_(x <- sampleX) ih x map).
  Defined.


  (** Hoare triples *)

  Definition precondition := pred heap.
  Definition postcondition A := pred (A * heap).

  Definition unary_judgement [A : choiceType] (pre : precondition) (c : raw_code A) (post : postcondition A) : Prop :=
    forall map, pre map -> forall p, (eval c map p <> 0)%R -> post p.

  Declare Scope Rules_scope.

  (* Is there a way to have a version with and without binder for the result in
  parallel ? *)
  (* Notation "⊨ ⦃ pre ⦄ c ⦃ post ⦄" := *)
  (*   (unary_judgement pre {code c} (post)) *)
  (*     : Rules_scope. *)

  Notation "⊨ ⦃ pre ⦄ c ⦃ p , post ⦄" :=
    (unary_judgement pre c (fun p => post))
      (p pattern) : Rules_scope.
  Open Scope Rules_scope.


  (** Ret rule *)

  Lemma ret_rule [A : choiceType] (a : A) :
    ⊨ ⦃ predT ⦄ ret a ⦃ (r,_), a == r ⦄.
  Proof. move=> ? _ p /dinsuppP /in_dunit -> //. Qed.

  (** Bind rule *)

  (* Note: this rule is much simpler to express in CPS (no existential,
     only composition of function) but is it worth the cost of encoding
     specifications presented by pre/post condition.
     Anyway the two versions could be developped in parallel *)

  Notation bind_pre prem postm pref :=
    (predI prem [pred map | `[<forall p, postm p ==> pref p.1 p.2>]]).
  Notation bind_post postm postf :=
    [pred pf | `[< exists p, postm p ==> postf p.1 pf >]].

  (* the "difficult" part of the effect observation: commutation with bind *)
  Lemma eval_bind [A B : choiceType] (m : raw_code A) (f : A -> raw_code B) :
    eval (bind m f) = Def.bind (eval m) (eval (A:=B) \o f).
  Proof.
    elim: m=> //=.
    - move=> ?; rewrite Def.bind_ret /comp; f_equal.
    - move=> o?? ih; rewrite -Def.bind_bind; apply: Def.bind_ext=> x; apply: ih.
    - move=> l k ih; extensionality map; rewrite (ih _) //.
    - move=> l c k ih; extensionality map; rewrite ih //.
    - move=> [X sampleX] k ih; extensionality map. rewrite /Def.bind.
      apply: distr_ext=> z; rewrite dlet_dlet. do 2 f_equal.
      extensionality x; rewrite (ih x) //.
  Qed.


  Lemma bind_rule [A B : choiceType] (m : raw_code A) (f : A -> raw_code B) prem postm pref postf:
    ⊨ ⦃ prem ⦄ m ⦃ p, postm p ⦄ ->
    (forall a, ⊨ ⦃ pref a ⦄ f a ⦃ p, postf a p ⦄) ->
    ⊨ ⦃ bind_pre prem postm pref ⦄ bind m f ⦃ p, bind_post postm postf p ⦄.
  Proof.
    move=> hm hf map /andP[/= hprem /asboolP hpostmpref].
    rewrite eval_bind => p /Def.bind_not_null [p0 [hevm hevf]].
    apply/asboolP; exists p0. apply/implyP=> hpostm.
    move: (hpostmpref p0); rewrite hpostm /= => hpref.
    apply: (hf _ _ hpref)=> //.
  Qed.


  (** Weaken rule *)

  Lemma weaken_rule
        [A : choiceType]
        [pre wkpre : precondition]
        (c : raw_code A)
        [post wkpost : postcondition A] :
    subpred wkpre pre ->
    subpred post wkpost ->
    ⊨ ⦃ pre ⦄ c ⦃ p, post p ⦄ ->
    ⊨ ⦃ wkpre ⦄ c ⦃ p, wkpost p ⦄.
  Proof.
    move=> hsubpre hsubpost hc ? /hsubpre hpre ? ?; apply: hsubpost.
    by apply: (hc _ hpre).
  Qed.


  (* To continue: get rule, put rule, sampling rule, rule for imported operations ? *)

End Evaluation.


Section ScopedImportEval.
  #[local] Open Scope fset.
  #[local] Open Scope fset_scope.

  #[local]
  Notation M := (Def.stsubdistr heap_choiceType).

  Context (import : Interface).

  (** Taking an interpretation of the imported operation as assumption *)
  Context (import_eval : ∀ o, o \in import → src o → M (tgt o)).

  Definition eval_op : forall o, src o -> M (tgt o) :=
    fun o => bool_depelim _ (o \in import) (fun oval => import_eval o oval) (fun _ _ => Def.stsubnull _ _).

  Let eval := (eval eval_op).

  (* Problem: the notation for the judgement is parametrized by eval, how can I
  have access to this notation instantiated with eval without redefining it ?
  Use a functor ?*)

  (* TODO: Add spec and Rule for imported operations *)

End ScopedImportEval.
