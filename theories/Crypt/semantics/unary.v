Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra distr reals realsum boolp.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Axioms chUniverse pkg_core_definition pkg_heap.

Import Num.Theory Order.LTheory.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

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

Module Def.
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

  #[local] Open Scope order_scope.

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

Arguments ret [_ _] _.
Arguments bind [_ _ _] _ _.
End Def.


(** Semantic evaluation of code and commands *)
Section Evaluation.
  #[local] Open Scope fset.
  #[local] Open Scope fset_scope.
  Context (Loc : {fset Location}).
  Context (import : Interface).

  (* Local shorter names for code and semantics *)
  Let C := code Loc import.
  Let M := (Def.stsubdistr heap_choiceType).

  (** Taking an interpretation of the imported operation as assumption *)
  Context (import_eval : forall o, o \in import -> src o -> M (tgt o)).

  (* Multiple attempts for evaluation. In the end it looks simpler
     defining evaluation on raw_code, and providing the adequate
     rules/hoare triples only on valid code.
   *)
  (* two helper functions for the convoy pattern (is there an idiomatic ssreflect/mathcomp way to do that ?) *)
  Definition bool_depelim (X : Type) (b : bool) (htrue : b = true -> X) (hfalse : b = false -> X) : X :=
    (if b as b0 return b = b0 -> X then htrue else hfalse) erefl.

  Lemma bool_depelim_true (X : Type) (b : bool) (htrue : b = true -> X) (hfalse : b = false -> X) (e : b = true) : bool_depelim X b htrue hfalse = htrue e.
  Proof. by depelim e. Qed.

  Definition eval [A : choiceType] : raw_code A -> M A.
  Proof.
    elim.
    - apply: Def.ret.
    - move=> o x k ih.
      apply: (bool_depelim _ (o \in import) _ (fun _ _=> dnull))=> oval.
      exact (Def.bind (import_eval o oval x) ih).
    - move=> l k ih.
      exact (fun map => let v := get_heap map l in ih v map).
    - move=> l v k ih.
      exact (fun map => ih (set_heap map l v)).
    - move=> [X sampleX] k ih.
      exact (fun map => \dlet_(x <- sampleX) ih x map).
  Defined.



  (* Definition eval [A : choiceType] : C A -> M A. *)
  (* Proof. *)
  (*   move=> []; elim. *)
  (*   - move=> a _ ; exact (ret _ a). *)
  (*   - move=> o x k ih /inversion_valid_opr [oval kval]. *)
  (*     exact (bind _ (import_eval o oval x) (fun v => ih v (kval v))). *)
  (*   - move=> l k ih /inversion_valid_getr [lval kval]. *)
  (*     exact (bind _ (fun map => dunit (get_heap map l, map)) *)
  (*                 (fun v => ih v (kval v))). *)
  (*   - move=> l v k ih /inversion_valid_putr[lval kval]. *)
  (*     exact (bind _ (fun map => dunit (tt, set_heap map l v)) (fun=> ih kval)). *)
  (*   - move=> [X sampleX] ++/inversion_valid_sampler. *)
  (*     rewrite /Arit=> /=k ih kval. *)
  (*     exact (bind _ (fun s => \dlet_(x <- sampleX) dunit (x, s)) (fun x => ih x (kval x))). *)
  (* Defined. *)

  (* Definition eval [A : choiceType] : C A -> M A. *)
  (* Proof. *)
  (*   move=> []; elim. *)
  (*   - move=> a _ ; exact (Def.ret a). *)
  (*   - move=> o x k ih /inversion_valid_opr [oval kval]. *)
  (*     exact (Def.bind (import_eval o oval x) (fun v => ih v (kval v))). *)
  (*   - move=> l k ih /inversion_valid_getr [lval kval]. *)
  (*     exact (fun map => let v := get_heap map l in ih v (kval v) map). *)
  (*   - move=> l v k ih /inversion_valid_putr[lval kval]. *)
  (*     exact (fun map => ih kval (set_heap map l v)). *)
  (*   - move=> [X sampleX] ++/inversion_valid_sampler. *)
  (*     rewrite /Arit=> /=k ih kval. *)
  (*     exact (fun map => \dlet_(x <- sampleX) ih x (kval x) map). *)
  (* Defined. *)

  (** Hoare triples *)

  Definition precondition := pred heap.
  Definition postcondition A := pred (A * heap).

  Definition unary_judgement [A : choiceType] (pre : precondition) (c : C A) (post : postcondition A) : Prop :=
    forall map, pre map -> forall p, (eval c map p <> 0)%R -> post p.

  Declare Scope Rules_scope.

  (* @théo Is there a binding key for the package_scope ?*)
  Open Scope package_scope.

  (* Is there a way to have a version with and without binder for the result in
  parallel ? *)
  (* Notation "⊨ ⦃ pre ⦄ c ⦃ post ⦄" := *)
  (*   (unary_judgement pre {code c} (post)) *)
  (*     : Rules_scope. *)

  Notation "⊨ ⦃ pre ⦄ c ⦃ p , post ⦄" :=
    (unary_judgement pre {code c} (fun p => post))
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
  Lemma eval_bind [A B : choiceType] (m : C A) (f : A -> C B) :
    eval {code bind m f} = Def.bind (eval m) (eval (A:=B) \o f).
  Proof.
    case: m=> []; elim=> //=.
    - move=> ??; rewrite Def.bind_ret /comp; f_equal.
    - move=> o?? ih /inversion_valid_opr [oval kval].
      rewrite 2!bool_depelim_true -Def.bind_bind; f_equal.
      extensionality x; apply: ih; apply: kval.
    - move=> l k ih /inversion_valid_getr [lval kval].
      extensionality map; rewrite (ih _ (kval _)) //.
    - move=> l c k ih /inversion_valid_putr [lval kval].
      extensionality map; rewrite (ih kval) //.
    - move=> [X sampleX] k ih /inversion_valid_sampler kval.
      extensionality map. rewrite /Def.bind.
      apply: distr_ext=> z; rewrite dlet_dlet. do 2 f_equal.
      extensionality x; rewrite (ih x _) //.
  Qed.

  (* Two helper lemmas *)
  Lemma R_no0div : forall u v : R, (u * v <> 0 -> u <> 0 /\ v <> 0)%R.
  Proof.
    move=> u v uv; split; move: uv; apply contra_not=> ->; [apply: GRing.mul0r|apply: GRing.mulr0].
  Qed.

  Lemma bind_not_null [A B : choiceType] (m : M A) (f : A -> M B)
    : forall map p, Def.bind m f map p <> 0%R -> exists p0, m map p0 <> 0%R /\ f p0.1 p0.2 p <> 0%R.
  Proof.
    move=> map p; rewrite /Def.bind dletE=> /neq0_psum [p0] /R_no0div ? ;by exists p0.
  Qed.

  Lemma bind_rule [A B : choiceType] (m : C A) (f : A -> C B) prem postm pref postf:
    ⊨ ⦃ prem ⦄ m ⦃ p, postm p ⦄ ->
    (forall a, ⊨ ⦃ pref a ⦄ f a ⦃ p, postf a p ⦄) ->
    ⊨ ⦃ bind_pre prem postm pref ⦄ bind m f ⦃ p, bind_post postm postf p ⦄.
  Proof.
    move=> hm hf map /andP[/= hprem /asboolP hpostmpref].
    rewrite eval_bind => p /bind_not_null [p0 [hevm hevf]].
    apply/asboolP; exists p0. apply/implyP=> hpostm.
    move: (hpostmpref p0); rewrite hpostm /= => hpref.
    apply: (hf _ _ hpref)=> //.
  Qed.


  (** Weaken rule *)

  Lemma weaken_rule
        [A : choiceType]
        [pre wkpre : precondition]
        (c : C A)
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
