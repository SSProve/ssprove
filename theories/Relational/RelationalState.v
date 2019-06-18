From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
From Mon.SM Require Import SMMonadExamples.
From Mon.Relational Require Import RelativeMonads RelativeMonadExamples GenericRulesSimple.

Set Primitive Projections.
Set Universe Polymorphism.


Section RelationalState.
  Section StateSig.
    Context (loc val : Type).

    Inductive StS :=
    | StGet : loc -> StS
    | StPut : loc -> val -> StS.

    Definition StOp (s:StS) :=
      match s with
      | StGet l => val
      | StPut _ _ => unit
    end.

    Definition FSt := Free StOp.
  End StateSig.

  Definition RelSt (S:Type): RelationalSpecMonad0 :=
    relativeMonad_precomposition
      typeCat_prod
      (ordmonad_to_relmon (STCont S)).


  Context (loc1 loc2 val : Type) (loc:=(loc1+loc2)%type) (S := loc -> val).
  (* Context (eql : loc -> loc -> bool) (eql_spec : forall l1 l2, reflect (l1 = l2) (eql l1 l2) ). *)


  (* Let M1 := FSt loc1 val. *)
  (* Let M2 := FSt loc2 val. *)

  (* Definition inj_st {loc0} (inj : loc0 -> loc)  (s:StS loc0 val) : St S (StOp loc0 val s) := *)
  (*   match s as s0 return St S (StOp loc0 val s0) with *)
  (*   | StGet _ _ l => fun store => ⟨store (inj l), store⟩ *)
  (*   | StPut _ _ l v => fun store => ⟨tt, fun l' => if eql (inj l) l' then v else store l'⟩ *)
  (*   end. *)

  (* Let morph1 := from_free (inj_st inl). *)
  (* Let morph2 := from_free (inj_st inr). *)

  Let M1 := St (loc1 -> val).
  Let M2 := St (loc2 -> val).

  Definition merge s1 s2 (l:loc) : val :=
    match l with
    | inl l1 => s1 l1
    | inr l2 => s2 l2
    end.

  Let res1 (s0:S) := fun l1 => s0 (inl l1).
  Let res2 (s0:S) := fun l2 => s0 (inr l2).

  Import SPropNotations.
  Import FunctionalExtensionality.
  Program Definition θSt : RelationalEffectObservation0 M1 M2 (RelSt S) :=
    mkRelMonMorph _ _ _ _
                  (fun A =>
                     ⦑fun m12 s0 =>
                        ⦑fun post =>
                           let r1 := nfst m12 (res1 s0) in
                           let r2 := nsnd m12 (res2 s0) in
                           post ⟨ ⟨nfst r1, nfst r2⟩, merge (nsnd r1) (nsnd r2)⟩⦒⦒)
                  _ _.
  Next Obligation. move: H0 ; apply H. Qed.
  Next Obligation. induction H=> //. Qed.
  Next Obligation.
    extensionality s0. apply Ssig_eq=> /=.
    congr (@^~ ⟨_,_⟩).
    extensionality p ; extensionality l ; destruct l=> //.
  Qed.

  Definition upd {loc} (eql : loc -> loc -> bool) (l:loc) (v:val) (s :loc -> val) :=
    fun l' => if eql l l' then v else s l'.

  Context (eql1 : loc1 -> loc1 -> bool)
          (eql1_spec : forall l1 l2, reflect (l1 = l2) (eql1 l1 l2) ).
  Context (eql2 : loc2 -> loc2 -> bool)
          (eql2_spec : forall l1 l2, reflect (l1 = l2) (eql2 l1 l2) ).

  Let read1 (l:loc1) : M1 val := fun s => ⟨s l, s⟩.
  Let write1 (l:loc1) (v:val) : M1 unit := fun s => ⟨tt, upd eql1 l v s⟩.
  Let read2 (l:loc2) : M2 val := fun s => ⟨s l, s⟩.
  Let write2 (l:loc2) (v:val) : M2 unit := fun s => ⟨tt, upd eql2 l v s⟩.
  Let skip1 : M1 unit := ret tt.
  Let skip2 : M2 unit := ret tt.

  Let S1 := loc1 -> val.
  Let S2 := loc2 -> val.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θSt _ _ c1 c2 w).

  Program Definition fromPrePost {A1 A2}
          (pre : S1 -> S2 -> SProp)
          (post : A1 -> S1 -> S1 -> A2 -> S2 -> S2 -> SProp)
    : dfst (RelSt S ⟨A1,A2⟩) :=
    fun s0=> ⦑fun p => pre (res1 s0) (res2 s0) s/\
                 forall a1 a2 s, post a1 (res1 s0) (res1 s) a2 (res2 s0) (res2 s)
                            -> p ⟨⟨a1,a2⟩, s⟩⦒.
  Next Obligation. intuition. Qed.

  Lemma read1_rule (l1 : loc1) :
    ⊨ read1 l1 ≈ skip2 [{ fromPrePost (fun s1 s2 => sUnit)
                                     (fun v s1 s1' _ s2 s2' =>
                                        s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s1 l1) }].
  Proof. cbv ; intuition. Qed.

  Lemma read2_rule (l2 : loc2) :
    ⊨ skip1 ≈ read2 l2 [{ fromPrePost (fun s1 s2 => sUnit)
                                     (fun _ s1 s1' v s2 s2' =>
                                        s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s2 l2) }].
  Proof. cbv ; intuition. Qed.

  Lemma write1_rule (l1:loc1) (v:val) :
    ⊨ write1 l1 v ≈ skip2 [{
                              fromPrePost (fun s1 s2 => sUnit)
                                          (fun _ s1 s1' _ s2 s2' =>
                                             s1' ≡ upd eql1 l1 v s1 s/\ s2 ≡ s2')
                          }].
  Proof. cbv ; intuition. Qed.

  Lemma write2_rule (l2:loc2) (v:val) :
    ⊨ skip1 ≈ write2 l2 v [{
                              fromPrePost (fun s1 s2 => sUnit)
                                          (fun _ s1 s1' _ s2 s2' =>
                                             s1' ≡ s1 s/\ s2' ≡ upd eql2 l2 v s2)
                          }].
  Proof. cbv ; intuition. Qed.

End RelationalState.

Section SimpleState.

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
End SimpleState.

Notation "θ ⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θ _ _ c1 c2 w) (at level 85).


Section NonInterference.
  Import SPropNotations.
  Import FunctionalExtensionality.

  Variable St : Type.

  Program Definition θStNI : RelationalEffectObservation0 (State St) (State St) (RelSt (St × St)) :=
    mkRelMonMorph _ _ _ _
                  (fun A =>
                     ⦑fun m12 s0 =>
                        ⦑fun post =>
                           let r1 := nfst m12 (nfst s0) in
                           let r2 := nsnd m12 (nsnd s0) in
                           post ⟨ ⟨nfst r1, nfst r2⟩, ⟨nsnd r1, nsnd r2⟩⟩⦒⦒)
                  _ _.
  Next Obligation.
    intuition.
  Qed.
  Next Obligation.
    destruct H. assumption.
  Qed.

  Program Definition fromPrePostNI {A1 A2} {S1 S2}
          (pre : S1 -> S2 -> SProp)
          (post : A1 -> S1 -> S1 -> A2 -> S2 -> S2 -> SProp)
    : dfst (RelSt (S1 × S2) ⟨A1,A2⟩) :=
    fun s0=> ⦑fun p => pre (nfst s0) (nsnd s0) s/\
                 forall a1 a2 s, post a1 (nfst s0) (nfst s) a2 (nsnd s0) (nsnd s)
                            -> p ⟨⟨a1,a2⟩, s⟩⦒.
  Next Obligation. intuition. Qed.


  Definition NI {A : Type} (c : State St A) := θStNI ⊨ c ≈ c [{ fromPrePostNI (fun s1 s2 => sUnit) (fun i s1 s1' i' s2 s2' => i ≡ i')}].

End NonInterference.

Let prog := bind (put _ 21) (fun _ => ret 42).

Import SPropNotations.
Import FunctionalExtensionality.

Lemma prog_satisfies_NI (H : BindMonotonicRelationalSpecMonad0 (RelSt (nat × nat))) : NI _ prog.
  unfold NI.
  unfold prog.
  eapply weaken_rule2.
  - apply (seq_rule _ _ (RelSt (nat × nat))).
    + unfold semantic_judgement. sreflexivity.
      (* cbv. intros si post. intro. apply H0. sreflexivity. *)
    + intros [] [].
      admit.
  - admit.
  (* cbv. *)
  (* intros [n0 n1] a [[] H]. *)
  (* apply H. *)
  (* reflexivity. *)
Admitted.
