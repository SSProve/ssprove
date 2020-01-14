From Coq Require Import ssreflect ssrfun FunctionalExtensionality List Arith ZArith.
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads DijkstraMonadExamples.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Mon.SM Require Import SMMonadExamples.

Import SPropNotations.
Import DijkstraMonadNotations.


(******************************************************************************************)
(* The state monad, and the corresponding Weakest Precondition Dijkstra monad.            *)
(******************************************************************************************)
Section State.

  Variable St : Type.

  Program Definition State : Monad :=
    (* Using the monotonic transformer is overkill here
       (we could probably use the plain one)*)
    (* ST_T St (DiscreteMonad Identity) _ _ _ *)
    @mkMonad (fun X => St -> (X × St))
             (fun X x s => ⟨x, s⟩)
             (fun X Y c f s => let '(npair x s') := c s in f x s') _ _ _.

  (* The get and put operations *)
  Definition get : State St := fun s => ⟨s,s⟩.
  Definition put : St -> State unit := fun s => fun _ => ⟨tt, s⟩.

  Program Definition StProp_alg : MonadAlgebra State :=
    @mkMonadAlgebra State (St -> SProp)
                    (fun (c: State (St -> SProp)) (s:St) =>
                       let '(npair P s') := c s in P s') _ _.

  Program Definition StProp_oalg : OrderedAlgebra State :=
    @mkOrderedAlgebra _ StProp_alg (@Pred_op_order St) _ _.
  Next Obligation. move: H0 ; apply H. Qed.

  (* Weakest preconditions for specifying stateful operations *)
  Definition StateSpec := WPSpecMonad StProp_oalg.

  (* The Dijkstra monad for state, indexed by predicate transformers. *)
  Definition StateWP : Dijkstra StateSpec := @D_wp _ _.

  Eval cbv in StateWP.

  (* A convienient way to specify stateful computations: using pre and
     post conditions. *)
  Program Definition PrePostWP (P : St -> SProp) (Q : St -> St -> SProp)
    : StateSpec unit :=
    ⦑fun (Z : unit -> St -> SProp) s0 => P s0 s/\ forall s1, Q s0 s1 -> Z tt s1⦒.
  Next Obligation. intuition eauto ; move: (q s1 H0) ; apply H. Qed.

  Definition PrePost P (Q : St -> St -> SProp) :=
    StateWP unit (PrePostWP P Q).

  (* Lifting the get and put operations to the Dijkstra monad level;
     Coq automatically works out the predicate transformer lifting. *)
  Definition get' : StateWP _ _ := @lift State StateSpec _ _ get.
  Definition put' (s : St) : StateWP unit _ := @lift State StateSpec _ _ (put s).

  (* A coherence check: if we write a computation in the Dijkstra
     monad for some Pre/Post specification, then the underlying
     computation on states satisfies the usual semantics of a Hoare
     triple.  *)
  Lemma soundness P Q : forall (c : PrePost P Q) s,
      P s -> Q s (nsnd (underlying c s)).
  Proof. 
    move=> [f H] /= s pre_ok.
    move: (H (fun _ => Q s) s).
    cbv; intuition.
  Qed.

  (* Example from Section 3.4 *)
  Definition modify (f : St -> St) :=
    x <- get' ; put' (f x).

End State.
Arguments get' [St].
Arguments put' [St].

(* A toy stateful program, from Swamy et al., 2013. *)
Program Definition incr : PrePost nat
                          (fun _ => sUnit)
                          (fun s0 s1 => s0 s< s1) :=
  wkn (x <- get' ; put' (S x)) _.
Next Obligation. simpl. apply H. constructor. apply sle_refl. Qed.



(******************************************************************************************)
(* Non-determinism, with Angelic and Demonic specifications.                              *)
(******************************************************************************************)
Section NonDeterminism.

  (* Or lists? *)
  (* Definition ND : Monad. *)
  (*   apply (mkMonad (fun X => X -> Prop) *)
  (*                  (fun X x => fun x' => x = x') *)
  (*                  (fun X Y c f => fun y => exists x, c x /\ f x y)). *)
  (*   - intros A B a f. extensionality y. *)
  (*     apply prop_ext. split. *)
  (*     + intros [x [eq H]]. subst. auto. *)
  (*     + intro. exists a. auto. *)
  (*   - intros A c. extensionality a. *)
  (*     apply prop_ext. split. *)
  (*     + intros [x [eq H]]. subst. auto. *)
  (*     + intro. exists a. auto. *)
  (*   - intros A B C m f g. *)
  (*     extensionality c. *)
  (*     apply prop_ext. split. *)
  (*     + intros [b [[a [H1 H2]] H3]]. eauto. *)
  (*     + intros [a [H1 [b [H2 H3]]]]. eauto. *)
  (* Defined. *)

    Lemma concat_map_nil : forall A (l : list A),
      concat (List.map (fun x => x :: nil) l) = l.
    Proof.
      induction l.
      - reflexivity.
      - simpl. rewrite IHl. reflexivity.
    Qed.

  Program Definition ListM : Monad :=
    @mkMonad (fun A => list A)
             (fun A a => a :: nil)
             (fun A B m f => concat (List.map f m)) _ _ _.
  Next Obligation. apply app_nil_r. Qed.
  Next Obligation. apply concat_map_nil. Qed.
  Next Obligation.
    induction c=> //=.
    rewrite map_app concat_app IHc //.
  Qed.

  Definition choose {A} (l : list A) : ListM A := l.
  Definition pick : ListM bool := true :: false :: nil.

  Section Angelic.
    
    Fixpoint or (xs : list SProp) : SProp :=
      match xs with
      | nil => sEmpty
      | P :: Ps => P s\/ or Ps
      end.

    Lemma or_app : forall l1 l2, or (l1 ++ l2) = (or l1 s\/ or l2).
    Proof.
      intros l1 l2; apply SPropAxioms.sprop_ext.
      constructor ; induction l1; simpl; tauto.
    Qed.

    Lemma or_concat : forall l, or (List.map or l) = or (concat l).
    Proof.
      induction l=> //=. rewrite IHl or_app //.
    Qed.

    Program Definition Angelic_alg : MonadAlgebra ListM :=
      @mkMonadAlgebra ListM SProp or _ _.
    Next Obligation. apply SPropAxioms.sprop_ext ; dintuition. Qed.
    Next Obligation.
      rewrite -(@map_map _ _ _ f (fun x => or x :: nil))
              -(@map_map _ _ _ or (fun x => x :: nil))
              concat_map_nil.
        apply or_concat.
    Qed.

    Program Definition Angelic_oalg : OrderedAlgebra ListM :=
      @mkOrderedAlgebra _ Angelic_alg SProp_op_order _ _.
    Next Obligation.
      induction a=> //=. move: H0 => /= [Hy| ?].
      left ; move:Hy ; apply H.
      right ; auto.
    Qed.

    Definition AngelicSpec := WPSpecMonad Angelic_oalg.

    Definition Angelic : Dijkstra AngelicSpec := @D_wp ListM Angelic_oalg.

    Definition pickA : Angelic bool _ := @lift ListM AngelicSpec _ _ pick.
    Definition chooseA {A} (l : list A) : Angelic A _ :=
      @lift ListM AngelicSpec _ _ (choose l).
    Definition failA {A} : Angelic A _ := chooseA nil.

    Program Definition PostAngelic {A} (Q : A -> SProp) : AngelicSpec A :=
      ⦑fun post => forall a, Q a -> post a⦒.
    Next Obligation. apply H ; auto. Qed.

    Definition guardA (b : bool) : Angelic unit _ :=
      ifTE b (dret tt) failA.

    Lemma or_Exists A (P : A -> SProp) xs : or (List.map P xs) -> s∃ x (H:In x xs), P x.
      induction xs => //=.
      move=> [H|H].
      exists a ; eexists; [left ; reflexivity | assumption].
      move: (IHxs H) => [x [Hx HP]]. exists x ; eexists ; [right|] ; assumption.
    Qed.

    Lemma Angelic_soundness {A} (P : A -> SProp) (Q : AngelicSpec A) (c : Angelic A Q) :
      Spr1 Q P -> s∃ x (H:In x (underlying c)), P x.
    Proof.
      destruct Q ; destruct c as [? H]; simpl in *.
      move=> ? ; apply or_Exists. rewrite <- concat_map_nil.
      rewrite map_map. apply H. assumption.
    Qed.

    Lemma Angelic_soundness2 {A} (P : A -> SProp) (c : Angelic A (PostAngelic P))
      : s∃ x (H:In x (underlying c)), P x.
    Proof.
      apply Angelic_soundness. simpl. auto.
    Qed.

  End Angelic.

  Program Definition test_angelic
    : Angelic nat (PostAngelic (fun x => x ≡ 5)) :=
    wkn (chooseA (2 :: 3 :: 5 :: nil)) _.
  Next Obligation. do 2 right ; left ; apply H=> //. Qed.

  Program Definition pytriples : Angelic (nat * nat * nat)%type
                                         (PostAngelic (fun (t:nat * nat * nat) => let '(x,y,z) := t in x*x + y*y ≡ z*z)) :=
    let c :=
        (let l := 1 :: 2 :: 3 :: 4 :: 5 :: nil in
         x <- chooseA l ;
           y <- chooseA l ;
           z <- chooseA l ;
           dret (x, y, z))
    in wkn c _.
  Next Obligation.
    cbv; intuition ltac:(try (apply H ; constructor)).
  Qed.

  Section Demonic.

    Fixpoint and (xs : list SProp) : SProp :=
      match xs with
      | nil => sUnit
      | P :: Ps => P s/\ and Ps
      end.

    Lemma and_app : forall l1 l2, and (l1 ++ l2) = (and l1 s/\ and l2).
    Proof.
      intros l1 l2. apply SPropAxioms.sprop_ext.
      induction l1; simpl; constructor; intuition.
    Qed.

    Lemma and_concat : forall l, and (List.map and l) = and (concat l).
    Proof.
      induction l.
      - reflexivity.
      - simpl. rewrite IHl. rewrite and_app. reflexivity.
    Qed.

    Program Definition Demonic_alg : MonadAlgebra ListM :=
      @mkMonadAlgebra ListM SProp and _ _.
    Next Obligation. apply SPropAxioms.sprop_ext; dintuition. Qed.
    Next Obligation.
        rewrite <- (@map_map _ _ _ f (fun x => and x :: nil)).
        rewrite <- (@map_map _ _ _ and (fun x => x :: nil)).
        rewrite concat_map_nil.
        apply and_concat.
    Qed.

    Program Definition Demonic_oalg : OrderedAlgebra ListM :=
      @mkOrderedAlgebra _ Demonic_alg SProp_op_order _ _.
    Next Obligation.
      move: H0 ; induction a ; constructor ; intuition.
    Qed.

    Definition DemonicSpec := WPSpecMonad Demonic_oalg.

    Definition Demonic : Dijkstra DemonicSpec := @D_wp ListM Demonic_oalg.

    Definition pickD : Demonic bool _ := @lift ListM DemonicSpec _ _ pick.
    Definition chooseD {A} (l : list A) : Demonic A _ :=
      @lift ListM DemonicSpec _ _ (choose l).
    Definition failD {A} : Demonic A _ := chooseD nil.

    Program Definition PostDemonic {A} (Q : A -> SProp) : DemonicSpec A :=
      ⦑fun post => forall a, Q a -> post a⦒.
    Next Obligation. apply H; auto. Qed.

    Definition pick_from {A} (l : list A) : Demonic A (PostDemonic (fun a => Squash (In a l))).
      refine ((fix pick_from (l : list A) : Demonic A (PostDemonic (fun a => Squash (In a l))) :=
                 match l with
                 | nil    => wkn failD _
                 | a :: l => wkn (b <- pickD ; ifTE b (dret a) (pick_from l)) _
                 end) l); simpl; auto.
      - intros P b. simpl. constructor.
      - intros P b. simpl. simpl in b. split.
        + specialize (b a). apply b. constructor.
          left. reflexivity.
        + intuition. apply b. destruct H. constructor.
          right. assumption.
    Defined.

    Definition guardD (b : bool) : Demonic unit _ :=
      ifTE b (dret tt) failD.

  End Demonic.

  Definition test_demonic : Demonic nat (PostDemonic (fun x => 1 s< x s/\ x s< 6)).
    apply (wkn (chooseD (2 :: 3 :: 5 :: nil))).
    intros Q H. simpl. simpl in H.
    intuition ltac:(try (apply H ; do 8 constructor)).
  Defined.

  Program Definition pytriplesD : Demonic (nat * nat * nat)%type
                                  (PostDemonic (fun (t:nat * nat * nat) => match t with (x,y,z) => sEq (x*x + y*y) (z*z) end)) :=
    let c := (let l := 1 :: 2 :: 3 :: 4 :: 5 :: nil in
           x <- pick_from l ;
           y <- pick_from l ;
           z <- pick_from l ;
           _ <- guardD (Nat.eqb (x*x + y*y) (z*z)) ;
           dret (x, y, z)) in wkn c _.
  Next Obligation.
    destruct H0, H1, H2.
    intuition; subst; simpl; intuition; apply H; intuition.
  Defined.

End NonDeterminism.

Section FreeMonad.

  Variable S : Type.
  Variable P : S -> Type.

  Let trace := trace P.
  Import MonadTransformerMonotonic.
  Definition TraceSpec : OrderedMonad := STCont trace.

  Section History.
    Program Definition HistSpec (s:S) : TraceSpec (P s) :=
      fun trace0 => ⦑ fun post => forall p, post ⟨p, existT _ s p :: trace0⟩ ⦒.
    Next Obligation.
     move: (H0 p) ; apply H.
    Qed.

    Definition FreeHist : Dijkstra TraceSpec := @OpSpecWP S P _ HistSpec.

    Definition opHist s : FreeHist (P s) _ :=
      @cont_perform S P _ HistSpec s.
    
  End History.

  Section Future.

    Import EqNotations.
    Program Definition FutureSpec (s : S) : TraceSpec (P s) :=
      fun (t : trace) =>
        ⦑ fun (post : P s × trace -> SProp) =>
            match t return SProp with
            | nil => sEmpty
            | (existT _ s' p) :: t => s∃ (e : s = s'),
                  post ⟨rew <- [P] e in p, t⟩
            end⦒.
    Next Obligation.
      destruct t; [destruct H0|].
      destruct s0; destruct H0 as [He Hy].
      exists He; move: Hy ; apply H.
    Qed.

    Definition FreeFuture : Dijkstra TraceSpec := @OpSpecWP S P _ FutureSpec.

    Definition opFuture s : FreeFuture (P s) _ :=
      @cont_perform S P _ FutureSpec s.

  End Future.

  Section OperationSpecs.

    Variable OpSpecs : forall s, SProp × (P s -> SProp).


    Definition OpSpec := MonoContSProp.

    Definition OpSpecWP : Dijkstra OpSpec :=
      @OpSpecWP S P _ (fun s => PrePostSpec (nfst (OpSpecs s)) (nsnd (OpSpecs s))).

    Definition PrePostOp {A} (P : SProp) (Q : A -> SProp) :=
      OpSpecWP A (PrePostSpec P Q).

    Definition perform : forall s, PrePostOp (nfst (OpSpecs s)) (nsnd (OpSpecs s))
    := @cont_perform S P _ _.

    Program Definition frameConj {A}{Pre}{I}{Q : A -> SProp} :
      PrePostOp Pre Q ->
      PrePostOp (Pre s/\ I) (fun a => Q a s/\ I) := fun c => wkn c _.
    Next Obligation.
      move:H ; simpl ; intuition.
    Qed.

  End OperationSpecs.

End FreeMonad.
Arguments perform [S P OpSpecs].

(******************************************************************************************)
(* Specialising the Free monad to the IO monad                                            *)
(******************************************************************************************)
Section IO.

  Variable Inp : Type.
  Variable Oup : Type.

  Inductive IOop : Type := read : IOop | write : Oup -> IOop.
  Definition IOop_arity (op : IOop) : Type :=
    match op with
    | read => Inp
    | write _ => unit
    end.

  Definition IOSpec := TraceSpec IOop IOop_arity.
  Definition IO : Dijkstra IOSpec := FreeHist IOop IOop_arity.
  Definition read' : IO Inp _ := opHist _ _ read.
  Definition write' (o : Oup) : IO unit _ := opHist _ _ (write o).

  Program Definition mustHaveOccurredSpec (o : Oup) : IOSpec unit :=
    fun history => ⦑fun post => Squash (In (existT _ (write o) tt) history) s/\ post ⟨tt, history⟩ ⦒.
  Next Obligation.
    move: H0 ; simpl ; intuition.
  Qed.

  Program Definition mustHaveOccurred (o : Oup)
    : IO unit (mustHaveOccurredSpec o)
    :=
      wkn (dret tt) _.
  Next Obligation. move:H ; simpl; intuition eauto. Qed.

  Variables oup1 oup2 : Oup.

  Program Definition print_sequence_spec : IOSpec unit :=
    fun history => ⦑fun post => post ⟨tt, existT _ (write oup2) tt :: existT _ (write oup1) tt :: history⟩⦒. 
  Next Obligation. move: H0 ; simpl; intuition. Qed.

  Program Definition print_sequence : IO unit print_sequence_spec :=
    wkn (x <- write' oup1 ; write' oup2) _.
  Next Obligation.
    move: p p0 => [] [] ; assumption.
  Qed.

  (* Print sequence with an assertion *)
  Program Definition print_sequence' : IO unit print_sequence_spec :=
    wkn (x <- write' oup1 ; y <- mustHaveOccurred oup1; write' oup2) _.
  Next Obligation.
    destruct p. split.
    - constructor. left. reflexivity.
    - intros []. assumption.
  Qed.

  (* Print sequence with an assertion and under specified: fails to
     check. *)
  Program Definition print_sequence_spec'' : IOSpec unit :=
    fun=> ⦑fun post => forall history, post ⟨tt, history⟩⦒.
  Next Obligation. simpl ; intuition. Qed.

  (* COrrectly, the proof fails ... *)
  Program Definition print_sequence'' : IO unit print_sequence_spec'' :=
    wkn (y <- mustHaveOccurred oup1; write' oup2) _.
  Next Obligation.
    split. (* stuck here *)
  Reset print_sequence''.

End IO.


(******************************************************************************************)
(* Exceptions (the option monad)                                                          *)
(******************************************************************************************)
Section Exceptions.

  Program Definition Exc : Monad :=
    @mkMonad option (fun A a => Some a)
             (fun A B m f =>
                match m with
                | None => None
                | Some a => f a
                end) _ _ _.
  Next Obligation. destruct c=> //. Qed.
  Next Obligation. destruct c=> //. Qed.

  Definition throw {A} : Exc A := None.

  Section DoubleBarreled.

    Definition ExnSpecCarrier : Type -> Type :=
      fun X => { f : (X -> SProp) -> SProp -> SProp
            ≫ SProper ((X ⇢ SProp_op_order) s==> SProp_op_order s==> SProp_op_order) f}.

    Program Definition ExnSpec_ret : forall A, A -> ExnSpecCarrier A :=
      fun A a => ⦑ fun p pexc => p a ⦒.
    Next Obligation. cbv ; intuition. Qed.

    Program Definition ExnSpec_bind :
      forall A B, ExnSpecCarrier A -> (A -> ExnSpecCarrier B) -> ExnSpecCarrier B :=
      fun A B m f =>
        ⦑ fun p pexc => Spr1 m (fun a => Spr1 (f a) p pexc) pexc ⦒.
    Next Obligation.
      eapply (Spr2 m) ; try eassumption.
      move=> /= ? ; apply (Spr2 (f _)) ; assumption.
    Qed.

    Program Definition ExnSpecU : Monad :=
      @mkMonad ExnSpecCarrier ExnSpec_ret ExnSpec_bind _ _ _.

    Definition ExnSpec_rel A : srelation (ExnSpecU A) :=
      fun m1 m2 => ((A -> SProp) ⇢ (SProp ⇢ SProp_op_order)) (Spr1 m1) (Spr1 m2).

    Instance ExnSpec_order A : PreOrder (ExnSpec_rel A).
    Proof. constructor ; cbv ; intuition. Qed.

    Program Definition ExnSpec : OrderedMonad :=
      @mkOrderedMonad ExnSpecU ExnSpec_rel _ _.
    Next Obligation.
      apply H. move: H1 ; apply (Spr2 y) ; cbv ; intuition.
    Qed.

    Program Definition ExnObservation_U A : Exc A -> ExnSpec A :=
      fun m => match m with
            | None => ⦑ fun _ pexc => pexc⦒
            | Some a => ret a
            end.
    Next Obligation. cbv ; intuition. Qed.

    Program Definition ExnObservation : MonadMorphism Exc ExnSpec :=
     @mkMorphism Exc ExnSpec ExnObservation_U _ _.
    Next Obligation. destruct m ; intuition. Qed.

    Definition ExnDB := @Dθ Exc ExnSpec ExnObservation.

  End DoubleBarreled.

  (******************************************************************************************)
  (* This does exceptions with a pre-chosen exceptional post-condition, as in the           *)
  (* discussion at the end of Section 3.2                                                   *)
  (******************************************************************************************)
  Section PureExnSpecs.

    Variable Q_exn : SProp.

    Program Definition Exc_alg : MonadAlgebra Exc :=
      @mkMonadAlgebra Exc SProp (fun c => match c return SProp with Some p => p | None => Q_exn end) _ _.
    Next Obligation. destruct m ; intuition. Qed.

    Program Definition Exc_oalg : OrderedAlgebra Exc :=
      @mkOrderedAlgebra _ Exc_alg SProp_op_order _ _.
    Next Obligation. destruct a ; try apply H ; auto. Qed.

    Definition ExcSpec := WPSpecMonad Exc_oalg.

    Definition ExcWP : Dijkstra ExcSpec := @D_wp _ _.

    Import SPropNotations.
    Program Definition PrePostExcSpec {A} (P : SProp) (Q : A -> SProp) : ExcSpec A :=
      ⦑fun (Z : A -> SProp) => P s/\ forall a, Q a -> Z a⦒.
    Next Obligation. cbv ; intuition. Qed.

    Definition PrePostExc {A} P (Q : A -> SProp) :=
      ExcWP A (PrePostExcSpec P Q).

    Definition throw' {A} : ExcWP A _ :=
      @lift Exc ExcSpec _ _ (@throw A).

    Lemma soundnessExc {A} P Q : forall (c : @PrePostExc A P Q),
        P -> match underlying c with
             | None => Q_exn
             | Some a => Q a
             end.
    Proof.
      destruct c as [[] H] ;  cbv ; intuition ; apply (H Q) ; cbv ; intuition.
    Qed.

  End PureExnSpecs.

  Program Definition catchSpec {Q_exn'} {A B} :
    forall (P : SProp) (Q : A -> SProp) (Q_exn : SProp),
    (A -> ExcSpec Q_exn' B) ->
    ExcSpec Q_exn' B ->
    ExcSpec Q_exn' B
    :=
      fun P Q Q_exn wp_ret wp_exn =>
        ⦑fun post => P s/\ (forall a, Q a -> Spr1 (wp_ret a) post)
                  s/\ (Q_exn -> Spr1 wp_exn post)⦒.
  Next Obligation.
    destruct H0 as [[]] ; intuition.
  Qed.
End Exceptions.


Program Definition catch {Q_exn Q_exn'} {A B} {P Q} {wp_success: A -> ExcSpec Q_exn' B} {wp_exn} :
  PrePostExc Q_exn P Q ->
  (forall a, ExcWP Q_exn' B (wp_success a)) ->
  (ExcWP Q_exn' B wp_exn) ->
  ExcWP Q_exn' B (catchSpec P Q Q_exn wp_success wp_exn) :=
  fun M N_ret N_exn =>
    match M with
    | ⦑ Some a ⦒ => wkn (N_ret a) _
    | ⦑ None ⦒ => wkn N_exn _
    end.
Next Obligation. 
  destruct H as [[? H0] ?] ; apply H0.
  apply wildcard'; cbv ; intuition.
Qed.
Next Obligation.
  destruct H as [[? ?] H0] ; apply H0. cbv in *. eauto.
Qed.

Program Definition catch2
        {Q_exn Q_exn'} {A B} {P} {Q : A -> SProp} {R : B -> SProp} :
  PrePostExc Q_exn P Q ->
  (forall a, PrePostExc Q_exn' (Q a) R) ->
  PrePostExc Q_exn' Q_exn R ->
  PrePostExc Q_exn' P R
  :=
  fun M H_ret H_exn =>
    match M with
    | ⦑ Some a ⦒ => wkn (H_ret a) _
    | ⦑ None ⦒ => wkn H_exn _
    end.
Next Obligation.
  destruct H ; split. apply wildcard' ; cbv ; intuition. assumption.
Qed.
Next Obligation.
  destruct H ; split. cbv in * ; eauto. assumption.
Qed.


Program Definition test1 {A B P} {Q : A -> SProp} {Q_exn wp2}
           (c1 : PrePostExc Q_exn P Q)
           (c2 : forall a, ExcWP Q_exn B (wp2 a))
  : ExcWP Q_exn B (bind (PrePostExcSpec Q_exn P Q) wp2) :=
  wkn (catch c1 c2 (throw' _)) _.
Next Obligation. cbv ; intuition. Qed.

(******************************************************************************************)
(* An alternative attempt to do Handlers to the one described in the paper                *)
(******************************************************************************************)
Section Handler.

  Variable S : Type.
  Variable P : S -> Type.
  Variable S' : Type.
  Variable P' : S' -> Type.

  Variable Inner : forall s, SProp × (P s -> SProp).
  Variable Outer : forall s, SProp × (P' s -> SProp).

  (* FIXME: does this generalise to more general outer Dijkstra monads? *)
  (* FIXME: does this generalise to when we have some kind of ghost state *)
(*      for the handler? *)
  Import SPropNotations.

  Definition handle {A B}{Pre : SProp}{Q : A -> SProp}{R : B -> SProp}
             (M    : PrePostOp S P Inner Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hops : forall (I : SProp) s,
                 (forall p, PrePostOp S' P' Outer (I s/\ nsnd (Inner s) p) R) ->
                 PrePostOp S' P' Outer (I s/\ nfst (Inner s)) R)
    : PrePostOp S' P' Outer Pre R.
  Proof.
    destruct M as [comp comp_ok].
    generalize Pre comp_ok. clear Pre comp_ok.
    induction comp; intros Pre comp_ok.
    - refine (wkn (Hret a) _).
      intros k [pre_ok H]. split.
      + cbv in comp_ok. apply comp_ok. intuition.
      + assumption.
    - simpl in comp_ok.
      refine
        (wkn (Hops Pre s (fun p => wkn (X p (Pre s/\ nsnd (Inner s) p) _) _)) _);
        simpl.
      + intros k [[H1 H2] H3]. apply comp_ok; cbv ; intuition.
      + intros k [[H1 H2] H3]. cbv ; eauto.
      + intros k [H1 H2]. simpl in comp_ok.
        destruct (comp_ok Q (spair _ _ H1 (fun a q => q))).
        cbv ; intuition eauto.
  Defined.

  (* Post-hoc proof version *)
  Let Outer' := fun s => PrePostSpec (nfst (Outer s)) (nsnd (Outer s)).
  Definition handle' {A B}{Pre : SProp}{Q : A -> SProp}{R : B -> SProp}
             (M    : PrePostOp S P Inner Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hops : forall s, (forall (p : P s), Free P' B) -> Free P' B)
             (Hops' : forall s f,
                 (forall p, OpSpecEffObs Outer' _ (f p)
                         ≤ PrePostSpec (nsnd (Inner s) p) R) ->
                 OpSpecEffObs Outer' _ (Hops s f)
                              ≤ PrePostSpec (nfst (Inner s)) R)
    : PrePostOp S' P' Outer Pre R.
  Proof.
    destruct M as [comp comp_ok].
    exists ((fix handle (m:Free P A) : Free P' B :=
              match m with
              | retFree _ a => Spr1 (Hret a)
              | @opr _ _ _ s k => Hops s (fun p => handle (k p))
              end) comp).
    simpl.
    intros k [H1 H2].
    generalize k H2. clear k H2.
    induction comp; intros.
    - destruct (Hret a) as [Hret_a Hret_a_ok]. simpl in *.
      apply Hret_a_ok. apply comp_ok. simpl. eauto.
    - simpl in *. apply Hops'.
      + intros p k0 [H3 H4]. simpl. apply H.
        * simpl. intros k1 H5. apply comp_ok; eauto.
        * assumption.
      + simpl. destruct (comp_ok Q (spair _ _ H1 (fun a q => q))). auto.
  Defined.

End Handler.
Arguments handle [S P S' P' Inner Outer A B Pre Q R].

Section FwdHandler.

  Variable S : Type.
  Variable P : S -> Type.

  Variable OpSpec : forall s, SProp × (P s -> SProp).

  Program Definition all_fwd {A}{Pre : SProp}{Q : A -> SProp}
             (M : PrePostOp S P OpSpec Pre Q)
    : PrePostOp S P OpSpec Pre Q :=
    handle M (fun a => wkn (dret a) _)
           (fun I s resume => wkn (p <- perform s; resume p) _).
  Next Obligation. cbv ; intuition. Qed.
  Next Obligation. cbv ; intuition. Qed.

End FwdHandler.

Section ExnHandler.

  Inductive exn_op : Type := raise : exn_op.
  Definition exn_ty (op : exn_op) : Type :=
    match op with
    | raise => False
    end.

  Variable Q_exn : SProp.
  Definition exn_spec (op : exn_op) : SProp × (exn_ty op -> SProp) :=
    match op with
    | raise => ⟨Q_exn, fun (emp : False) => match emp with end⟩
    end.

  Variable S' : Type.
  Variable P' : S' -> Type.
  Variable Outer : forall s, SProp × (P' s -> SProp).

  Program Definition catch_gen {A B} {Pre} {Q : A -> SProp} {R : B -> SProp}
             (M    : PrePostOp exn_op exn_ty exn_spec Pre Q)
             (Hret : forall a, PrePostOp S' P' Outer (Q a) R)
             (Hexn : PrePostOp S' P' Outer Q_exn R)
    : PrePostOp S' P' Outer Pre R :=
    handle M Hret
           (fun I s resume =>
              match s with
              | raise => wkn Hexn _
              end).
  Next Obligation. cbv ; intuition. Qed.
End ExnHandler.

Program Definition throw'' {A}{P : SProp}{wp} :
  P -> OpSpecWP exn_op exn_ty (exn_spec P) A wp
  := fun p => ⦑@opr _ _ _ raise (fun (x:False) => match x with end)⦒.
Next Obligation. cbv ; intuition. Qed.

Program Definition div (i j : Z) :
  PrePostOp exn_op exn_ty (exn_spec (Squash (j = 0%Z)))
            sUnit (fun n => Squash (j <> 0%Z /\ n = Z.div i j)) :=
  match Z.eq_dec j 0 with
  | left e => throw'' (squash e)
  | right _ => wkn (dret (Z.div i j)) _
  end.
Next Obligation. simpl in *. apply H. constructor. intuition eauto. Qed.

Program Definition try_div (i j : Z) :
  PrePostOp exn_op exn_ty (exn_spec sEmpty)
            sUnit (fun (n : option Z) => sUnit) :=

  handle (div i j)
         (fun a => wkn (dret (Some a)) _)
         (fun I s resume => wkn (dret None) _).
Next Obligation. simpl in * ; apply H => //. Qed.
Next Obligation. simpl in * ; apply H => //. Qed.

Section FwdingExnHandler.

  Variable S : Type.
  Variable P : S -> Type.
  Variable Inner : forall s, SProp × (P s -> SProp).

  Inductive exn' : Type := raise' : exn' | old : S -> exn'.
  Definition exn'_ty (op : exn') : Type :=
    match op with
    | raise' => False
    | old s  => P s
    end.

  Variable Q_exn : SProp.
  Definition exn'_spec (op : exn') : SProp × (exn'_ty op -> SProp) :=
    match op with
    | raise' => ⟨Q_exn, fun (emp : False) => match emp with end⟩
    | old s  => Inner s
    end.

  Program Definition catch_fwd {A B} {Pre} {Q : A -> SProp} {R : B -> SProp}
             (M    : PrePostOp exn' exn'_ty exn'_spec Pre Q)
             (Hret : forall a, PrePostOp S P Inner (Q a) R)
             (Hexn : PrePostOp S P Inner Q_exn R)
    : PrePostOp S P Inner Pre R
    :=
      handle M Hret (fun I s =>
                      match s with
                      | raise' => fun resume => wkn Hexn _
                      | old s  => fun resume => wkn (p <- perform s; resume p) _
                      end).
  Next Obligation. simpl in * ; intuition. Qed.
  Next Obligation. simpl in * ; intuition. Qed.

End FwdingExnHandler.


Section ConstantChoiceHandler.

  (* A choice handler that always replies 'true', per its spec. *)

  Inductive choice_op : Type := choice : choice_op.
  Definition choice_ty (op : choice_op) :=
    match op with
    | choice => bool
    end.

  Definition choice_spec (op : choice_op) : SProp × (choice_ty op -> SProp) :=
    match op with
    (* Specify that 'choice' always returns 'true' *)
    | choice => ⟨sUnit, fun b => Squash (b = true)⟩
    end.

  Variable S' : Type.
  Variable P' : S' -> Type.
  Variable Outer : forall s, SProp × (P' s -> SProp).

  Program Definition always_true_handler {A}{Pre}{Q : A -> SProp}
             (M : PrePostOp choice_op choice_ty choice_spec Pre Q)
    : PrePostOp S' P' Outer Pre Q
    :=
      handle M (fun a => wkn (dret a) _)
             (fun I op =>
                match op with
                | choice => fun resume => wkn (resume true) _ end).
  Next Obligation. simpl in * ; intuition. Qed.
  Next Obligation. simpl in * ; dintuition. Qed.

End ConstantChoiceHandler.

(* Section StateHandler. *)

(*   (* This doesn't work... *) *)

(*   Inductive state_op := get_op : state_op | put_op : nat -> state_op. *)
(*   Definition state_ty (op : state_op) := *)
(*     match op with *)
(*     | get_op   => nat *)
(*     | put_op _ => unit *)
(*     end. *)
(*   Definition state_spec (op : state_op) : Prop * (state_ty op -> Prop) := *)
(*     (True, fun _ => True). *)

(*   Variable S' : Type. *)
(*   Variable P' : S' -> Type. *)
(*   Variable Outer : forall s, Prop * (P' s -> Prop). *)

(*   Definition state_handler {A}{Pre}{Q : A -> Prop} *)
(*              (M : PrePostOp state_op state_ty state_spec Pre Q) *)
(*     : PrePostOp S' P' Outer Pre *)
(*                 (fun (t : nat -> PrePostOp S' P' Outer True Q) => True). *)
(*   Proof. *)
(*     apply (handle M). *)
(*     - intros a. *)
(*   Abort. (* :( I think I need to do parameterised handlers instead. *) *)

(* End StateHandler. *)

(********************************************************************************)
(*                                                                              *)
(*    Functions polymorphic in the Dijkstra monad                               *)
(*                                                                              *)
(********************************************************************************)

Section DijkstraMonadPolymorphic.
  Context W (D:Dijkstra W).
  Import ListNotations.
  
  Section ListMap.
    Fixpoint list_mapW {A B} (w : A -> W B) (l : list A) : W (list B) :=
      match l with
      | [] => ret []
      | a :: l => bind (w a) (fun b => bind (list_mapW w l) (fun bs => ret (b :: bs)))
      end.

    Fixpoint list_mapD {A B w} (f:forall a:A, D B (w a)) (l : list A)
      : D (list B) (list_mapW w l) :=
      match l with
      | [] => dret []
      | a :: l => b <- f a ; bs <- list_mapD f l ; dret (cons b bs)
      end.
  End ListMap.

  Section Fold.
    Context A B (w : A -> B -> W B) (inv : W B)
            (Hinv : forall a, bind inv (w a) ≤ inv).
    Let w' a wb := bind wb (w a).
    Lemma fold_inv : forall l, fold_right w' inv l ≤ inv.
    Proof.
      induction l as [|a l IH] ; simpl.
      sreflexivity.
      stransitivity (bind inv (w a)).
      apply omon_bind. assumption. intros ; sreflexivity.
      apply Hinv.
    Qed.

    (* A fold where the unit is a computation, which must ensure the invariant *)
    Section MonadicUnit.
      Context (unit : D B inv) (f : forall a b, D B (w a b)).

      Fixpoint foldD l : D B (fold_right w' inv l) :=
        match l with
        | [] => unit
        | a :: l => b <- foldD l ; f a b
        end.

      Definition foldD_inv l := wkn (foldD l) (fold_inv l).
    End MonadicUnit.

    (* A fold where the unit is a value, needs a proof that returning it ensures *)
(*      * the invariant. It is straightforward to implement from the previous one *)
(*      * by weakening. *)
    Section PureUnit.
      Context (unit : B) (f : forall a b, D B (w a b)) (Hb : ret unit ≤ inv).

      Definition foldDp_inv l := foldD_inv (wkn (dret unit) Hb) f l.
    End PureUnit.
  End Fold.

  Section For.
    Context (start len : nat) (inv : W unit)
            (Hinv : bind inv (fun _ => inv) ≤ inv).

    Let bounded_nat := { i : nat ≫ Squash (start <= i < start + len) }.

    Program Fixpoint bseq (len' : nat) (Hlen : len' <= len) : list bounded_nat :=
      match len' with
      | 0 => []
      | S len0 => ⦑start⦒  :: bseq len0 _
      end.
    Next Obligation. dintuition. Qed.
    Next Obligation. apply le_Sn_le. assumption. Qed.

    Context (Hinv0 : ret tt ≤ inv).

    Program Definition for_inv (f : forall i, Squash (start <= i < start + len) -> D unit inv)
      : D unit inv :=
      foldD_inv bounded_nat unit (fun _ _ => inv) inv _ (wkn (dret tt) Hinv0)
                (fun i _ => f (Spr1 i) (Spr2 i)) (bseq len _).
  End For.

  Notation "'For' i 'from' start 'to' endc 'using' inv 'do' c 'done'" :=
    (for_inv start (endc - start) inv _ _ (fun i Hi => c))
      (at level 0, i ident).

  Program Definition loop_unit := For i from 0 to 5 using ret tt do dret tt done.
  Next Obligation. rewrite /bind monad_law1 ; sreflexivity. Qed.
  Next Obligation. sreflexivity. Qed.

End DijkstraMonadPolymorphic.

Section ForState.

  Notation "'For' i 'from' start 'to' endc 'using' inv 'do' c 'done'" :=
    (for_inv _ (StateWP nat) start (endc - start) inv _ _ (fun i Hi => wkn c _))
      (at level 0, i ident).

  Program Definition sum :=
    For i from 0 to 5 using PrePostWP nat (fun _ => sUnit) (fun s0 s1 => s0 s<= s1) do
        s0 <- get' ; put' (s0 + i)
        done.
  Next Obligation. simpl in *. intuition. apply q.
                   estransitivity ; eassumption. Qed.
  Next Obligation. apply H. sreflexivity. Qed.
  Next Obligation.
    apply H; rewrite // Nat.add_comm ; apply sle_lower.
  Qed.
End ForState.

