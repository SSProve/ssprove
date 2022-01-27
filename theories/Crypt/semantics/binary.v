Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra boolp reals realsum distr.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Axioms choice_type pkg_core_definition pkg_heap unary.

Import Num.Theory Order.LTheory.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Section Coupling.
  Context [A1 A2 : choiceType].
  Context (d : {distr (A1 * A2) /R}) (d1 : {distr A1 /R}) (d2 : {distr A2/R}).

  Definition coupling := dfst d = d1 /\ dsnd d = d2.

  Context (is_coupling : coupling).

  (* Lemma dlet_coupling [X : choiceType] (f : A1 * A2 -> {distr X /R}) : *)
  (*   \dlet_(a <- d) f a = \dlet_(a1 <- d1) \dlet_(a2 <- d2) f (a1, a2). *)
  (* Proof. *)
  (*   case: is_coupling=> <- <- /=; rewrite /dmargin. *)
  (*   apply: distr_ext=> z; rewrite dlet_dlet. *)

  (*   apply: distr_ext=> z; rewrite 2!dletE psum_pair; last apply: summable_mlet. *)
  (*   apply: eq_psum=> x1; rewrite dletE -psumZ; last apply: ge0_mu. *)
  (*   apply: eq_psum=> x2 /=. *)
  (*   case: is_coupling=> <- <- /=. *)
  (*   etransitivity. *)
  (*   1: apply: eq_dlet=> a; exact (f_equal f (surjective_pairing a)). *)
  (*   move=> /=. *)

End Coupling.

Module CouplingNotation.
Notation "d ~[ d1 , d2 ]" := (coupling d d1 d2) (at level 70) : type_scope.
End CouplingNotation.

Import CouplingNotation.

Section RetCoupling.
  Context [A1 A2 : choiceType].
  Definition ret_coupling (a1 : A1) (a2 : A2) : {distr (A1 * A2) /R} := dunit (a1, a2).

  Lemma ret_coupling_prop a1 a2 : ret_coupling a1 a2 ~[dunit a1, dunit a2].
  Proof. split; apply: distr_ext=> x /=; rewrite dmargin_dunit //. Qed.
End RetCoupling.

Section BindCoupling.
  Context [A1 A2 B1 B2 : choiceType].
  Context (m1 : {distr A1 /R}) (m2: {distr A2/R}) dm (hdm : dm ~[m1, m2]).
  Context (f1 : A1 -> {distr B1 /R}) (f2: A2 -> {distr B2/R})
          (df : A1 * A2 -> {distr (B1 * B2) /R}).

  Definition bind_coupling : {distr (B1 * B2) / R} :=
    \dlet_(a <- dm) df a.

  Lemma bind_coupling_prop
   (hdf : forall a1 a2, df (a1,a2) ~[f1 a1, f2 a2]) :
    bind_coupling ~[\dlet_(x1 <- m1) f1 x1, \dlet_(x2 <- m2) f2 x2].
  Proof.
    case: hdm=> [<- <-]; split; apply: distr_ext=> z.
    all: rewrite dmargin_dlet /bind_coupling dlet_dmargin /=; erewrite eq_dlet; first reflexivity.
    all: move=> [a1 a2] /=; by case: (hdf a1 a2).
  Qed.

  (* Almost the same lemma but with a superficially weaker hypothesis
     on the coupling of the continuations *)
  Lemma bind_coupling_partial_prop
   (hdf : forall a1 a2, dm (a1,a2) <> 0%R -> df (a1,a2) ~[f1 a1, f2 a2]) :
    bind_coupling ~[\dlet_(x1 <- m1) f1 x1, \dlet_(x2 <- m2) f2 x2].
  Proof.
    case: hdm=> [<- <-]; split; apply: distr_ext=> z.
    all: rewrite dmargin_dlet /bind_coupling dlet_dmargin /=; erewrite eq_dlet_partial; first reflexivity.
    all: move=> [a1 a2] h /=; by case: (hdf a1 a2 h).
  Qed.
End BindCoupling.


Section Def.
  #[local] Open Scope fset.
  #[local] Open Scope fset_scope.
  Context (Loc : {fset Location}).
  Context (import : Interface).

  (* Local shorter names for code and semantics *)
  Let C := code Loc import.
  Let M := (Def.stsubdistr heap_choiceType).

  Definition stsubdistr_rel [A1 A2 : choiceType] : M A1 -> M A2 -> Type :=
    fun d1 d2 => forall map1 map2, { d |  d ~[ d1 map1 , d2 map2 ] }.

  (** Taking an interpretation of the imported operation as assumption *)
  Context (import_eval : forall o, o \in import -> src o -> M (tgt o)).

  Let eval [A] := eval import import_eval (A:=A).

  Definition prerelation := rel heap.
  Definition postrelation A1 A2 := (A1 * heap) -> pred (A2 * heap).

  Definition binary_judgement [A1 A2 : choiceType]
             (pre : prerelation)
             (c1 : C A1) (c2 : C A2)
             (post : postrelation A1 A2) :=
    forall map1 map2, pre map1 map2 ->
                 exists d, d ~[eval c1 map1, eval c2 map2] /\
                      forall p1 p2, d (p1,p2) <> 0%R -> post p1 p2.

  Open Scope package_scope.

  (* Bindings in the pre/postcondition looks annoying here *)
  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (binary_judgement pre {code c1} {code c2} post) : Rules_scope.
  Open Scope Rules_scope.

  (** Ret rule *)

  Lemma ret_rel_rule [A1 A2 : choiceType] (a1 : A1) (a2 : A2) :
    ⊨ ⦃ fun _ _ => true ⦄ ret a1 ≈ ret a2 ⦃ fun p1 p2 => (p1.1 == a1) && (p2.1 == a2) ⦄.
  Proof.
    move=> map1 map2 _; exists (dunit ((a1, map1), (a2, map2))); split.
    1: split; apply: distr_ext=> x /=; rewrite dmargin_dunit //.
    move=> p1 p2 /dinsuppP/in_dunit[= -> ->] /=; by rewrite 2!eq_refl.
  Qed.

  (** Weaken rule *)

  Lemma weaken_rule [A1 A2 : choiceType]
        (wkpre : prerelation) (wkpost : postrelation A1 A2)
        (pre : prerelation) (c1 : C A1) (c2 : C A2) (post : postrelation A1 A2) :
    subrel wkpre pre ->
    (forall p1, subpred (post p1) (wkpost p1)) ->
    ⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄ ->
    ⊨ ⦃ wkpre ⦄ c1 ≈ c2 ⦃ wkpost ⦄.
  Proof.
    move=> hsubpre hsubpost hrel map1 map2 /hsubpre/(hrel map1 map2)[d [? hpost]].
    exists d; split=> // ???; apply: hsubpost; by apply: hpost.
  Qed.

  (** Bind rule *)

  Notation bind_prerel prem postm pref :=
    [rel map1 map2 | prem map1 map2 && `[< forall p1 p2, postm p1 p2 ==> pref p1.1 p2.1 p1.2 p2.2 >]].
  Notation bind_postrel postm postf :=
    (fun pf1 pf2 => `[< exists p1 p2, postm p1 p2 ==> postf p1.1 p2.1 pf1 pf2 >]).


  Lemma bind_rule [A1 A2 B1 B2 : choiceType]
        (prem : prerelation) (m1 : C A1) (m2 : C A2) (postm : postrelation A1 A2)
        (pref: A1 -> A2 -> prerelation) (f1 : A1 -> C B1) (f2 : A2 -> C B2)
        (postf : A1 -> A2 -> postrelation B1 B2) :
    ⊨ ⦃ prem ⦄ m1 ≈ m2 ⦃ postm ⦄ ->
    (forall a1 a2, ⊨ ⦃ pref a1 a2 ⦄ f1 a1 ≈ f2 a2 ⦃ postf a1 a2 ⦄) ->
    ⊨ ⦃ bind_prerel prem postm pref ⦄ bind m1 f1 ≈ bind m2 f2 ⦃ bind_postrel postm postf ⦄.
  Proof.
    move=> hm hf map1 map2 /andP[/= /(hm _)[dm [dmcoupling hpostm]]
                                   /asboolP hpostmpref].
    (* 2 difficulties:
       - we only have merely a coupling between the distributions for the
         continuations when we need to provide the coupling witness
         so we use choice at this pointed
         (functional choice should be enough;
          a more radical move would be to have proof relevant relational proofs)
       - we need to incorporate the precondition of the continuation when
         building the coupling witness; this forces an annoying yoga of
         currying/uncurrying
     *)
    set X := (A1 * heap) * (A2 * heap).
    (* set P : pred X := fun '((a1, map1), (a2, map2)) => pref a1 a2 map1 map2. *)
    set P := fun x : X => pref x.1.1 x.2.1 x.1.2 x.2.2.
    have/schoice[df hdf]: forall (z : { x : X | P x }), _
      (* Arghh...*)
      := fun z => hf (val z).1.1 (val z).2.1 (val z).1.2 (val z).2.2 (valP z).
      (* := fun z => let '((a1, map1), (a2, map2)) := val z in *)
      (*     hf a1 a2 map1 map2 (valP z). *)

    set df' := fun x => bool_depelim _ (P x) (fun hx => df (exist _ x hx))
                                    (fun _ => dnull).
    exists (bind_coupling dm df'); split.
    + rewrite /eval 2!eval_bind /Def.bind.
      apply: bind_coupling_partial_prop=> //.
      move=> p1' p2' /(hpostm _ _).
      move: (hpostmpref p1' p2')=> /implyP/[apply] hpref.
      case: (hdf (exist _ (p1', p2') hpref))=> ? _.
      by rewrite /df' bool_depelim_true.
    + move=> p1 p2 /dinsuppP/dinsupp_dlet[[p1' p2'] /dinsuppP hinm hinf].
      apply/asboolP; exists p1', p2'; apply/implyP.
      move: (hpostmpref p1' p2')=> /implyP/[apply] hpref.
      case: (hdf (exist _ (p1', p2') hpref))=> _ h; apply: h.
      move: hinf; by rewrite /df' bool_depelim_true=> /(_ =P _).
  Qed.

End Def.
