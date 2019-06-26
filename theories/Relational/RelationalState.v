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
    ordmonad_to_relspecmon0 (STCont S).


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
    ⊨ read1 l1 ≈ skip [{ fromPrePost (fun s1 s2 => sUnit)
                                     (fun v s1 s1' _ s2 s2' =>
                                        s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s1 l1) }].
  Proof. cbv ; intuition. Qed.

  Lemma read2_rule (l2 : loc2) :
    ⊨ skip ≈ read2 l2 [{ fromPrePost (fun s1 s2 => sUnit)
                                     (fun _ s1 s1' v s2 s2' =>
                                        s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s2 l2) }].
  Proof. cbv ; intuition. Qed.

  Lemma write1_rule (l1:loc1) (v:val) :
    ⊨ write1 l1 v ≈ skip [{
                             fromPrePost (fun s1 s2 => sUnit)
                                         (fun _ s1 s1' _ s2 s2' =>
                                            s1' ≡ upd eql1 l1 v s1 s/\ s2 ≡ s2')
                         }].
  Proof. cbv ; intuition. Qed.

  Lemma write2_rule (l2:loc2) (v:val) :
    ⊨ skip ≈ write2 l2 v [{
                             fromPrePost (fun s1 s2 => sUnit)
                                         (fun _ s1 s1' _ s2 s2' =>
                                            s1' ≡ s1 s/\ s2' ≡ upd eql2 l2 v s2)
                         }].
  Proof. cbv ; intuition. Qed.

End RelationalState.

Section NonInterference.
  Import SPropNotations.
  Import FunctionalExtensionality.

  Let loc := bool.
  Let HIGH := true.
  Let LOW := false.
  Let val := nat.
  Let eql := Bool.eqb.
  Let eql_spec := Bool.eqb_spec.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ (θSt loc loc val) _ _ c1 c2 w) (at level 85).

  Let fromPrePost' {A B} pre post := @fromPrePost loc loc val eql eql_spec eql eql_spec A B pre post.

  Definition NI {A : Type} (c : St (loc -> val) A) := ⊨ c ≈ c [{ fromPrePost' (fun s1 s2 => sUnit) (fun i s1 s1' i' s2 s2' => s1 false ≡ s2 false -> s1' false ≡ s2' false s/\ i ≡ i')}].

  Let put (l:loc) (v:val) : St (loc -> val) unit := fun s => ⟨tt, upd _ eql l v s⟩.
  Let get (l:loc) : St (loc -> val) val := fun s => ⟨s l, s⟩.

  Lemma get_left_rule {A} {l:loc} {a:A} :
    ⊨ get l ≈ ret a [{ fromPrePost' (fun s1 s2 => sUnit)
                              (fun v s1 s1' x s2 s2' => x ≡ a s/\
                                 s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s1 l) }].
  Proof. cbv ; intuition. Qed.

  Lemma get_right_rule {A} {l:loc} {a:A} :
    ⊨ ret a ≈ get l [{fromPrePost' (fun s1 s2 => sUnit)
                        (fun x s1 s1' v s2 s2' => x ≡ a s/\
                           s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s2 l) }].
  Proof. cbv ; intuition. Qed.

  Lemma put_left_rule (l:loc) (v:nat) {A} {a:A} :
    ⊨ put l v ≈ ret a
        [{fromPrePost' (fun s1 s2 => sUnit)
                        (fun _ s1 s1' x s2 s2' => x ≡ a s/\
                           s1' ≡ upd _ eql l v s1 s/\ s2 ≡ s2')
                        }].
  Proof. cbv ; intuition. Qed.

  Lemma put_right_rule (l:loc) (v:nat) {A} {a:A} :
    ⊨ ret a ≈ put l v
        [{fromPrePost' (fun s1 s2 => sUnit)
                        (fun x s1 s1' _ s2 s2' => x ≡ a s/\
                           s1' ≡ s1 s/\ s2' ≡ upd _ eql l v s2)
                        }].
  Proof. cbv ; intuition. Qed.

  Let prog := bind (get LOW) (fun n => ret n).

  Lemma prog_satisfies_NI : NI prog.
    unfold NI.
    unfold prog.
    - eapply gp_seq_rule=> //.
      typeclasses eauto.
      + eapply apply_left_tot.
        typeclasses eauto.
        apply get_left_rule.
        move=> ? ; apply get_right_rule.
        sreflexivity.
      + move=> ? ? ; apply gp_ret_rule.
        unshelve instantiate (1 := ⦑fun=> ?[x]⦒)=> /=.
        3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.
        intuition.
      + cbv; intuition.
        apply q. intros H.
        move: (f_sEqual2 _ _ q4 (sEq_refl false)) (f_sEqual2 _ _ q1 (sEq_refl false)) (f_sEqual2 _ _ q5 (sEq_refl false)) (f_sEqual2 _ _ q2 (sEq_refl false)).
        destruct q0. destruct p1. destruct q3.
        move=> [] [] [] [].
        split; assumption.
  Qed.
End NonInterference.

(*   Lemma prog_satisfies_NI : NI prog. *)
(*     unfold NI. *)
(*     unfold prog. *)
(*     - eapply gp_seq_rule=> //. *)
(*       typeclasses eauto. *)
(*       + eapply apply_left_tot.  *)
(*         typeclasses eauto. *)
(*         apply get_left_rule. *)
(*         move=> ? ; apply get_right_rule. *)
(*         sreflexivity. *)
(*       + move=> a1 a2. *)
(*         eapply apply_left_tot. *)
(*         typeclasses eauto. *)
(*         ++ apply put_left_rule. *)
(*         ++ move=> a0. apply put_right_rule. *)
(*            Unshelve. *)
(*            cbv. *)
(*            refine (Sexists _ (fun nn mm => ⦑fun=> ?[x]⦒) _). *)
(*            cbv; intuition. intros x y heq s0 n w. *)
(*            destruct heq. *)
(*            apply w. *)
(*         ++ cbv; intuition. *)
(*            destruct a4. destruct p0. destruct a5. *)
(*            destruct a6. destruct p1. *)
(*            unshelve instantiate (1 := (fun nn mm => ⦑fun=> ?[x]⦒)). *)
(*         3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.  *)
(*         intuition. *)
(*       + cbv; intuition. *)
(*         apply q. intros H.  *)
(*         move: (eta_reduce q4 false) (eta_reduce q1 false) => ? ?. *)
(*         move: (eta_reduce q5 false) (eta_reduce q2 false) => ? ?. *)
(*         split. *)
(*         ++ transitivity (s (inl false)). *)
(*            symmetry. *)
(*            assumption. *)
(*            transitivity (a (inl false)). *)
(*            symmetry; assumption. *)
(*            symmetry. *)
(*            transitivity (s (inr false)). *)
(*            symmetry; assumption. *)
(*            transitivity (a (inr false)). *)
(*            symmetry; assumption. symmetry; assumption. *)
(*         ++ transitivity a1. assumption. transitivity (a (inl false)). assumption. *)
(*            symmetry. transitivity (s (inr false)). assumption. *)
(*            transitivity (a (inr false)). *)
(*            symmetry; assumption. symmetry; assumption. *)
(*   Qed. *)
(* End NonInterference. *)

(*   Lemma prog_satisfies_NI : NI prog. *)
(*     unfold NI. *)
(*     unfold prog. *)
(*     - eapply gp_seq_rule=> //. *)
(*       typeclasses eauto. *)
(*       + eapply apply_left_tot.  *)
(*         typeclasses eauto. *)
(*         apply get_left_rule. *)
(*         move=> ? ; apply get_right_rule. *)
(*         sreflexivity. *)
(*       + move=> ? ? ; apply gp_ret_rule. *)
(*         unshelve instantiate (1 := ⦑fun=> ?[x]⦒)=> /=. *)
(*         3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.  *)
(*         intuition. *)
(*       + cbv; intuition. *)
(*         apply q. intros H.  *)
(*         move: (eta_reduce q4 false) (eta_reduce q1 false) => ? ?. *)
(*         move: (eta_reduce q5 false) (eta_reduce q2 false) => ? ?. *)
(*         split. *)
(*         ++ transitivity (s (inl false)). *)
(*            symmetry. *)
(*            assumption. *)
(*            transitivity (a (inl false)). *)
(*            symmetry; assumption. *)
(*            symmetry. *)
(*            transitivity (s (inr false)). *)
(*            symmetry; assumption. *)
(*            transitivity (a (inr false)). *)
(*            symmetry; assumption. symmetry; assumption. *)
(*         ++ transitivity a1. assumption. transitivity (a (inl false)). assumption. *)
(*            symmetry. transitivity (s (inr false)). assumption. *)
(*            transitivity (a (inr false)). *)
(*            symmetry; assumption. symmetry; assumption. *)
(*   Qed. *)


(* Import SPropNotations. *)

(* Lemma get_left_rule {A} {a:A} : *)
(*   θStNI nat ⊨ get _ ≈ ret a [{ fromPrePostNI (fun s1 s2 => sUnit) *)
(*                               (fun v s1 s1' x s2 s2' => x ≡ a s/\ *)
(*                                  s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s1) }]. *)
(* Proof. cbv ; intuition. Qed. *)

(* Lemma get_right_rule {A} {a:A} : *)
(*   θStNI nat ⊨ ret a ≈ get _ *)
(*         [{fromPrePostNI (fun s1 s2 => sUnit) *)
(*                         (fun x s1 s1' v s2 s2' => x ≡ a s/\ *)
(*                            s1 ≡ s1' s/\ s2 ≡ s2' s/\ v ≡ s2) }]. *)
(* Proof. cbv ; intuition. Qed. *)

(* Lemma put_left_rule (v:nat) {A} {a:A} : *)
(*   θStNI _ ⊨ put _ v ≈ ret a *)
(*         [{fromPrePostNI (fun s1 s2 => sUnit) *)
(*                         (fun _ s1 s1' x s2 s2' => x ≡ a s/\ *)
(*                            s1' ≡ v s/\ s2 ≡ s2') *)
(*                         }]. *)
(* Proof. cbv ; intuition. Qed. *)

(* Lemma put_right_rule (v:nat) {A} {a:A} : *)
(*   θStNI _ ⊨ ret a ≈ put _ v *)
(*         [{fromPrePostNI (fun s1 s2 => sUnit) *)
(*                         (fun x s1 s1' _ s2 s2' => x ≡ a s/\ *)
(*                            s1' ≡ s1 s/\ s2' ≡ v) *)
(*                         }]. *)
(* Proof. cbv ; intuition. Qed. *)

(* Let prog := bind (put _ 21) (fun _ => ret 42). *)

(* Import FunctionalExtensionality. *)

(* Lemma prog_satisfies_NI : NI _ prog. *)
(*   unfold NI. *)
(*   unfold prog. *)
(*   - eapply gp_seq_rule=> //. *)
(*     typeclasses eauto. *)
(*     + eapply apply_left_tot.  *)
(*       typeclasses eauto. *)
(*       apply put_left_rule. *)
(*       move=> ? ; apply put_right_rule. *)
(*       sreflexivity. *)
(*     + move=> ? ? ; apply gp_ret_rule. *)
(*       unshelve instantiate (1 := ⦑fun=> ?[x]⦒)=> /=. *)
(*       3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.  *)
(*       intuition. *)
(*     + cbv ; intuition. *)
(* Qed. *)

(* Lemma prog_satisfies_NI' `{BindMonotonicRelationalSpecMonad0 (RelSt (nat × nat))} : NI _ prog. *)
(*   unfold NI. *)
(*   unfold prog. *)
(*   eapply weaken_rule2. *)
(*   - apply (seq_rule _ _ (RelSt (nat × nat))). *)
(*     + unfold semantic_judgement. sreflexivity. *)
(*       (* cbv. intros si post. intro. apply H0. sreflexivity. *) *)
(*     + intros [] []. *)
(*       admit. *)
(*   - admit. *)
(*   (* cbv. *) *)
(*   (* intros [n0 n1] a [[] H]. *) *)
(*   (* apply H. *) *)
(*   (* reflexivity. *) *)
(* Admitted. *)
