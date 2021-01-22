From Coq Require Import ssreflect ssrfun FunctionalExtensionality List Arith ZArith.
From Mon Require Import Base.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads DijkstraMonadExamples.
From Mon.SRelation Require Import SRelationClasses SMorphisms.
From Mon.SM Require Import MonadTransformerMonotonic SMMonadExamples.

Import SPropNotations.
Import DijkstraMonadNotations.

(********************************************************************)
(* This file is intended to collect the notions presented in the
   paper and formalised in Coq.                                     *)
(********************************************************************)


(********************************************************************)
(*** The monad Jungle Book *)
(********************************************************************)

(* Definition of monads *)
Print Monad.

Check ret.
Check bind.

(* Classical examples of computational monads *)

(* Partiality, a free monad with one operation Ω *)
Check Div.
Check Ω.

(* Exceptions, also a free monad parametrized by a type E of exceptions *)
Check (Exn _).
Check (raise _).

(* State, parametrized by a type S *)
Check (St _).
Eval cbv in (St _ _).
Check get.
Check put.

(* A version of non-determinism based on predicates *)
Check NDSet.
Eval cbv in (NDSet _).
Check pick_set.

(* Non-determinism, implemented with lists *)
(* it does not satisfy commutativity and idempotency
   but it has a more computational feeling *)
Check ListM.
Eval cbv in (ListM _).
Check pick.

(* IO, a free monad parametrized by the types of Input and Ouput *)
Check (IO _ _).
Check read.
Check write.

(********************************************************************)
(*** Specification Monads *)
(********************************************************************)

Print OrderedMonad.

Check MonoContSProp.
Eval cbv in (MonoContSProp _).
Eval cbv in (_ ≤[MonoContSProp] _).

Eval cbv in (STCont _ _).
Eval cbv in (_ ≤[STCont _] _).

Eval cbv in (ExnSpec _ _).


(********************************************************************)
(*** Effects observations *)
(********************************************************************)

Print MonadMorphism.

Program Definition ExnObservation_U {E} A : Exn E A -> ExnSpec E A :=
  fun m =>
    match m with
    | retFree _ a => ret a
    | @opr _ _ _ (Raise e) _ => ⦑ fun _ pexc => pexc e⦒
    end.
Next Obligation. intuition. Qed.

Program Definition ExnObservation E : MonadMorphism (Exn E) (ExnSpec E) :=
  @mkMorphism (Exn _) (ExnSpec _) ExnObservation_U _ _.
Next Obligation. cbv ; destruct m ; intuition; destruct s=> //. Qed.

(********************************************************************)
(*This does exceptions with a pre-chosen exceptional post-condition,*)
(* as in the discussion at the end of Section 3.2                   *)
(********************************************************************)
Section PureExnSpecs.
  Context {E:Type} (Q_exn : SProp).

  Program Definition ExnQObservation_U A : Exn E A -> MonoContSProp A :=
    fun m =>
      match m with
      | retFree _ a => ret a
      | opr _ => ⦑fun _ => Q_exn ⦒
      end.
  Next Obligation. assumption. Qed.

  Program Definition ExnQObservation : MonadMorphism (Exn E) MonoContSProp :=
    @mkMorphism _ _ ExnQObservation_U _ _.
  Next Obligation. destruct m ; cbv ; intuition. Qed.

End PureExnSpecs.


(********************************************************************)
(*** Examples of Effects observations *)
(********************************************************************)

(********************************************************************)
(* Effect observation provided by a monad transformer               *)
(********************************************************************)

Section EffectObservationFromMonadTransformer.

  Context (T : OrderedMonadTransformer).

  Let M := T (DiscreteMonad Identity).
  Let W := T (MonoContSProp).

  Definition effect_observation_from_monad_transformer :
    MonotonicMonadMorphism M W
    := mt_map T (from_discrete_monad_monotonic (ret_mmorph MonoContSProp)).

End EffectObservationFromMonadTransformer.


(********************************************************************)
(* Non-determinism, with Angelic and Demonic specifications.        *)
(********************************************************************)
Section NonDeterminism.

  Section Angelic.

    Fixpoint or (xs : list SProp) : SProp :=
      match xs with
      | nil => False
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

    Definition AngelicEffectObs : MonadMorphism ListM MonoContSProp
      := mor Angelic_oalg.

  End Angelic.

  Section Demonic.

    Fixpoint and (xs : list SProp) : SProp :=
      match xs with
      | nil => True
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


    Definition DemonicEffectObs : MonadMorphism ListM MonoContSProp
      := mor Demonic_oalg.

  End Demonic.

End NonDeterminism.


(********************************************************************)
(* Effect observations of the IO monad                              *)
(********************************************************************)
Section IOObservations.
  Context (Inp Oup:Type).

  Let IOop := IOS Oup.
  Let IOop_arity := @IOAr Inp Oup.

  Let IO := IO Inp Oup.

  Program Definition θConstantOnWrite (Q:SProp) : MonadMorphism IO MonoContSProp :=
    @OpSpecEffObs IOop IOop_arity MonoContSProp
                  (fun op => match op with
                          | Read _ => ⦑ fun p => forall i, p i ⦒
                          | Write _ => ⦑ fun _ => Q ⦒
                          end).
  Next Obligation. apply H ; apply H0. Qed.
  Next Obligation. assumption. Qed.

  Program Definition θForgetWrite (Q:SProp) : MonadMorphism IO MonoContSProp :=
    @OpSpecEffObs IOop IOop_arity MonoContSProp
                  (fun op => match op with
                          | Read _ => ⦑ fun p => forall i, p i ⦒
                          | Write _ => ⦑ fun p => p tt ⦒
                          end).
  Next Obligation. apply H ; apply H0. Qed.
  Next Obligation. apply H=> //. Qed.

  Program Definition θOptimisticRead : MonadMorphism IO MonoContSProp :=
    @OpSpecEffObs IOop IOop_arity MonoContSProp
                  (fun op => match op with
                          | Read _ => ⦑ fun p => exists i, p i ⦒
                          | Write _ => ⦑ fun _ => True ⦒
                          end).
  Next Obligation. destruct H0 as [? ?] ; eexists ; apply H ; eassumption. Qed.
  Next Obligation. assumption. Qed.

  Let trace := trace IOop_arity.
  Import MonadTransformerMonotonic.

  Definition IOSpec := STCont trace.
  Program Definition θHistST : MonadMorphism IO IOSpec :=
    @OpSpecEffObs IOop IOop_arity IOSpec
                  (fun op => match op with
                          | Read _ =>
                            fun trace => ⦑ fun (p : _ -> SProp) => forall i, p ⟨i, existT _ (Read _) i :: trace⟩ ⦒
                          | Write o =>
                            fun trace => ⦑ fun (p : _ -> SProp) => p ⟨tt, existT IOop_arity (Write o) tt :: trace⟩ ⦒
                          end).
  Next Obligation. apply H ; apply H0. Qed.
  Next Obligation. apply H=> //. Qed.

  Definition IOevent := nsigT IOop_arity.
  Definition HistSpec := LoggerCont IOevent.
  Program Definition θHist : MonadMorphism IO HistSpec :=
    @OpSpecEffObs IOop IOop_arity HistSpec
                  (fun op =>
                     match op with
                     | Read _ =>
                       fun log => ⦑ fun p => forall i, p ⟨ i, Monoid.snil _ ⟩ ⦒
                     | Write o =>
                       fun log => ⦑ fun p => p ⟨tt, Monoid.inject (dpair _ (Write o) tt)⟩⦒
                     end).
  Next Obligation. apply H ; apply H0. Qed.
  Next Obligation. apply H=> //. Qed.

  Definition FrSpec := WrCont IOevent.
  Program Definition θFr : MonadMorphism IO FrSpec :=
    @OpSpecEffObs IOop IOop_arity FrSpec
                  (fun op =>
                     match op with
                     | Read _ =>
                       fun _ => ⦑ fun p => forall i, p ⟨ i, Monoid.snil _ ⟩ ⦒
                     | Write o =>
                       fun _ => ⦑ fun p => p ⟨tt, Monoid.inject (dpair _ (Write o) tt)⟩⦒
                     end).
  Next Obligation. apply H0 ; apply H1. Qed.
  Next Obligation. apply H0=> //. Qed.

End IOObservations.

(********************************************************************)
(*** Recovering Dijkstra Monads  *)
(********************************************************************)

(********************************************************************)
(* The state monad, and the corresponding Weakest Precondition      *)
(* Dijkstra monad.                                                  *)
(********************************************************************)
Section DijkstraState.

  Context (S : Type).

  Let State := St S.

  (* Weakest preconditions for specifying stateful operations *)
  Definition StateSpec := STCont S.

  (* An instance of the construction from a monad transformer *)
  (* special cased in order to compute more efficiently *)
  Program Definition StateEffectObservation : MonadMorphism State StateSpec :=
    @mkMorphism State StateSpec (fun X m s => ⦑fun post => post (m s)⦒) _ _.
  Next Obligation. apply H=> //. Qed.

  (* The Dijkstra monad for state, indexed by predicate transformers. *)
  Definition StateWP : Dijkstra StateSpec := Dθ StateEffectObservation.

  Eval cbv in StateWP _.

  (* A convienient way to specify stateful computations: using pre and
     post conditions. *)
  Program Definition PrePostWP (P : S -> SProp) (Q : S -> S -> SProp)
    : StateSpec unit :=
    fun s0 => ⦑fun (Z : unit × S -> SProp) => P s0 s/\ forall s1, Q s0 s1 -> Z ⟨tt, s1⟩⦒.
  Next Obligation. intuition eauto ; move: (q s1 H0) ; apply H. Qed.

  Definition PrePost P (Q : S -> S -> SProp) :=
    StateWP unit (PrePostWP P Q).

  (* Lifting the get and put operations to the Dijkstra monad level;
     Coq automatically works out the predicate transformer lifting. *)
  Definition get' : StateWP _ _ := @lift State StateSpec _ _ (@get S).
  Definition put' (s : S) : StateWP unit _ := @lift State StateSpec _ _ (put s).

  (* A coherence check: if we write a computation in the Dijkstra
     monad for some Pre/Post specification, then the underlying
     computation on states satisfies the usual semantics of a Hoare
     triple.  *)
  Lemma soundness P Q : forall (c : PrePost P Q) s,
      P s -> Q s (nsnd (proj1_sig c s)).
  Proof.
    move=> [f H] /= s pre_ok.
    cbv in H ; apply H.
    cbv; intuition.
  Qed.

  (* Example from Section 3.4 *)
  Definition modify (f : S -> S) :=
    x <- get' ; put' (f x).

End DijkstraState.
Arguments get' [S].
Arguments put' [S].

(* A toy stateful program, from Swamy et al., 2013. *)
Program Definition incr : PrePost nat
                          (fun _ => True)
                          (fun s0 s1 => s0 < s1) :=
  wkn (x <- get' ; put' (S x)) _.
Next Obligation. simpl. apply H. constructor. apply sle_refl. Qed.


(********************************************************************)
(* Examples of non-deterministic programs using the Dijkstra monad  *)
(* corresponding to the demonic interpretation.                     *)
(********************************************************************)

Section DemonicNonDeterminism.
  Definition Demonic : Dijkstra MonoContSProp := Dθ DemonicEffectObs.

  Definition pickD : Demonic bool _ := @lift ListM _ _ _ pick.
  Definition chooseD {A} (l : list A) : Demonic A _ :=
    @lift ListM _ _ _ (choose l).
  Definition failD {A} : Demonic A _ := chooseD nil.

  Program Definition PostDemonic {A} (Q : A -> SProp) : MonoContSProp A :=
    ⦑fun post => forall a, Q a -> post a⦒.
  Next Obligation. apply H; auto. Qed.

  Program Definition pick_from {A} (l : list A) : Demonic A (PostDemonic (fun a => Squash (In a l))) :=
    (fix pick_from (l : list A) : Demonic A (PostDemonic (fun a => Squash (In a l))) :=
                match l with
                | nil    => wkn failD _
                | a :: l => wkn (b <- pickD ; ifTE b (dret a) (pick_from l)) _
                end) l.
  Next Obligation. by []. Qed.
  Next Obligation.
    simpl in * ; dintuition ; apply H ; constructor ; [left=> //|right=> //].
  Qed.

  Definition guardD (b : bool) : Demonic unit _ :=
    ifTE b (dret tt) failD.

  Program Definition test_demonic
    : Demonic nat (PostDemonic (fun x => 1 < x s/\ x < 6))
    := wkn (chooseD (2 :: 3 :: 5 :: nil)) _.
  Next Obligation.
    simpl in *.
    intuition ltac:(try (apply H ; do 8 constructor)).
  Qed.

  Program Definition pytriplesD
    : Demonic (nat * nat * nat)%type
              (PostDemonic (fun (t:nat * nat * nat) =>
                              match t with (x,y,z) => eq (x*x + y*y) (z*z) end)) :=
    let c := (let l := 1 :: 2 :: 3 :: 4 :: 5 :: nil in
           x <- pick_from l ;
           y <- pick_from l ;
           z <- pick_from l ;
           _ <- guardD (Nat.eqb (x*x + y*y) (z*z)) ;
           dret (x, y, z)) in wkn c _.
  Next Obligation.
    destruct H0, H1, H2.
    intuition; subst; simpl; intuition; apply H; intuition.
  Qed.
End DemonicNonDeterminism.

(********************************************************************)
(* Examples of IO programs using the Dijkstra monad passing the     *)
(* whole state of IO events.                                        *)
(********************************************************************)

Section IO.
  Context (Inp Oup : Type).

  Let IOop := IOS Oup.
  Let IOop_arity := @IOAr Inp Oup.

  Let IO0 := IO Inp Oup.
  Let IOSpec := IOSpec Inp Oup.

  Definition IO : Dijkstra IOSpec := Dθ (θHistST _ _).
  Definition read' : IO Inp _ := lift _ (read _ _).
  Definition write' (o : Oup) : IO unit _ := lift _ (write _ o).

  Program Definition mustHaveOccurredSpec (o : Oup) : IOSpec unit :=
    fun history => ⦑fun post => Squash (In (existT _ (Write o) tt) history) s/\ post ⟨tt, history⟩ ⦒.
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
    fun history => ⦑fun post => post ⟨tt, existT _ (Write oup2) tt :: existT _ (Write oup1) tt :: history⟩⦒.
  Next Obligation. move: H0 ; simpl; intuition. Qed.

  Program Definition print_sequence : IO unit print_sequence_spec :=
    wkn (x <- write' oup1 ; write' oup2) _.
  Next Obligation. assumption. Qed.

  (* Print sequence with an assertion *)
  Program Definition print_sequence' : IO unit print_sequence_spec :=
    wkn (x <- write' oup1 ; y <- mustHaveOccurred oup1; write' oup2) _.
  Next Obligation. intuition. constructor ; left=> //. Qed.

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

(********************************************************************)
(* Examples of IO programs using the Dijkstra monad passing the     *)
(* whole state of IO events.                                        *)
(********************************************************************)

Section StateTMW.
  (* Slightly specializing the state transformer ST_T *)

  Variable M : Monad.
  Variable W : OrderedMonad.
  Variable mm : MonadMorphism M W.
  Variable St : Type.

  Program Definition StTM : Monad := ST_T St (DiscreteMonad M).
  Program Definition StTW : OrderedMonad := ST_T St W.

  Program Definition StateT_mm : MonadMorphism StTM StTW :=
    @mkMorphism StTM StTW (fun _ m s => mm _ (m s)) _ _.
  Next Obligation. extensionality s; apply mon_morph_ret. Qed.
  Next Obligation. extensionality s; apply mon_morph_bind. Qed.

  Definition DStateT : Dijkstra StTW := @Dθ StTM StTW StateT_mm.


  (* The get and put operations *)
  Program Definition StTW_get : StTW St := fun s => @ret W _ ⟨ s , s ⟩.

  Program Definition StTW_put : forall (s : St), StTW unit := fun s => fun _ => ret ⟨ tt , s ⟩.

  Definition DStateT_get : DStateT St (StTW_get).
    exists (fun s => @ret M _ ⟨ s , s ⟩).
    simpl. intros s.
    rewrite mon_morph_ret.
    intuition.
  Defined.


  Definition DStateT_put : forall (s : St), DStateT unit (StTW_put s).
    intros s.
    exists (fun _ => @ret M _ ⟨ tt , s ⟩).
    simpl. intros s'. unfold StTW_put.
    rewrite mon_morph_ret.
    intuition.
  Defined.

  (* The lifting *)
  Program Definition StTM_lift : forall A, M A -> StTM A := fun _ m s => bind m (fun t => ret ⟨ t , s ⟩).

  Definition DStateT_lift : forall b, forall (op : M b), DStateT b _ := fun b op => lift StateT_mm (StTM_lift _ op).

End StateTMW.

Section IOST.
  Let Inp := nat.
  Let Oup := nat.
  Let St := nat.

  (* Let IOSTop := IOS Oup. *)
  (* Let IOSTop_arity := @IOAr Inp Oup. *)
  (* (* Type := readST : IOSTop | writeST : Oup -> IOSTop. *) *)
  (* (* Definition IOSTop_arity (op : IOSTop) : Type := *) *)
  (* (*   match op with *) *)
  (* (*   | readST => Inp *) *)
  (* (*   | writeST _ => unit *) *)
  (* (*   end. *) *)

  (* Let M := @Free IOSTop IOSTop_arity. *)
  (* Let W := @IOSpec Inp Oup. *)
  (* Import MonadTransformerMonotonic. *)

  (* Let mm : MonadMorphism M W := @OpSpecEffObs _ _ _ (IOSpec _ _). *)

  Definition IOST := DStateT _ _ (θHistST Inp Oup) St.

  Definition readIOST : IOST Inp _ :=
    DStateT_lift  _ _ (θHistST Inp Oup) St Inp (read Inp Oup).
  Definition writeIOST : forall (o : Oup), IOST unit _ :=
    fun o => DStateT_lift _ _ (θHistST Inp Oup) St unit (write Inp o).
  Definition getIOST : IOST St _ := DStateT_get _ _ _ _.
  Definition putIOST : forall (s : St), IOST unit _ := fun s => DStateT_put _ _ _ _ s.

  Let W := IOSpec Inp Oup.
  Definition test1_spec : StTW W St unit.
    intros s.
    simpl.
    intros history.
    exists (fun post => post ⟨ ⟨ tt , s ⟩ ,  (existT _ (Write 2) tt :: existT _ (Write 1) tt :: history) ⟩).
    eauto.
  Defined.

  Program Definition test1IOST : IOST unit test1_spec :=
    wkn (x <- writeIOST 1 ; writeIOST 2) _.
  Next Obligation. assumption. Qed.

  Definition do_io_then_roll_back_state_spec : StTW W St unit.
    intros s history.
    exists (fun post => forall i, post ⟨ ⟨ tt , s ⟩ , (existT _ (Write (s + i + 1)) tt :: existT _ (Read Oup) i :: history) ⟩).
    simpl. eauto.
  Defined.

  Program Definition do_io_then_roll_back_state : IOST unit do_io_then_roll_back_state_spec :=
    (wkn (x <- getIOST; y <- readIOST; w <- putIOST (x + y); z <- getIOST; w <- writeIOST (z + 1); putIOST x) _).
  Next Obligation. apply H. Qed.
End IOST.


(********************************************************************)
(*** Basic Specifications Monads  *)
(********************************************************************)

Eval cbv in (PredOM _).
Eval cbv in (PrePost.PP _).
Eval cbv in (StrongestPostcondition.SP _).
Eval cbv in (MonoContSProp _).

Check pred_pp_adjunction.
Check wp_pp_adjunction.


(********************************************************************)
(*** Defining monad transformers  *)
(********************************************************************)

From Mon.SM Require Import SMSyntax.

(********************************************************************)
(* Definition of the SM language : types, terms and equations       *)
(********************************************************************)
Print ctype.
Print icterm.
Print iceq.

(* monad internal to SM *)
Print icmonad.

(********************************************************************)
(* Examples of monad internal to SM                                 *)
(********************************************************************)

(* state *)
Check st_icmonad.

(* monotonic state *)
Check mst_icmonad.

(* update monad on a directed container *)
(* generalises state, monotonic state, reader, writer *)
Check upd_icmonad.

(* continuation *)
Check cont_icmonad.


(********************************************************************)
(*Denotation of SM types, terms and equations to gallina with orders*)
(********************************************************************)

From Mon.SM Require Import SMDenotationsMonotonic.

Check to_preord.
Check icterm_to_monotonic_term.
Check iceq_to_eq.

(********************************************************************)
(* Defining each components of a monad transformer                  *)
(********************************************************************)

From Mon.SM Require Import MonadTransformerMonotonic.

(* Given an icmonad, mapping a monad to a monad *)
Check CMonad.

(* Adding the lift *)
(* this requires the bind of the icmonad to be an algebra morphism *)
Check CMonadUnder.

(* We can map monadic relations to monadic relations *)
Check CMonadIdeal.

(* If C is covariant, mapping monad morphisms to monad morphisms *)
Check CMonadMorph.

(* If C satisfies both covariance and linearity of bind, *)
(* we obtain the full monad transformer *)
Check CMonadTransformer.

(* See SM/SMMonadExamples.v for particular instances of monad transformers *)



(********************************************************************)
(*** Dijkstra monads from effect observations  *)
(********************************************************************)

(* Formal definition of a Dijkstra monad on an ordered monad*)
Print Dijkstra.

(* We do not formalize the full adjunctions
   but our main way to build Dijkstra monads
   follows from that construction *)

Check Dθ.

(********************************************************************)
(*** Algebraic effects and effects handlers  *)
(********************************************************************)

(* Free monad on a signature *)
Check Free.

(* Effect observation on a Free monad *)
Check OpSpecEffObs.

(* Dijkstra monad associated to it and corresponding operations *)
Check OpSpecWP.
Check cont_perform.


(********************************************************************)
(* Exceptions (the option monad) and its handlers                   *)
(********************************************************************)
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

  (*********************************************************************)
  (* This does exceptions with a pre-chosen exceptional post-condition,*)
  (* as in the discussion at the end of Section 3.2                    *)
  (*********************************************************************)
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
        ⦑fun post => P s/\ (forall a, Q a -> proj1_sig (wp_ret a) post)
                  s/\ (Q_exn -> proj1_sig wp_exn post)⦒.
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


(* Sanity checks for axioms *)

Print Assumptions STCont.
Print Assumptions PrePost.PPSpecMonad.
Print Assumptions fib'.