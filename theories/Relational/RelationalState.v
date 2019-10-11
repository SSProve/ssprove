(*********************************************************)
(**       Relational reasoning on state                 **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality Arith.PeanoNat.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple.

Set Primitive Projections.
Set Universe Polymorphism.

(* Relational state constructions *)
Section RelationalState.
  (* Free monad on state signature *)
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

  (* Simple relational specification monad based backward predicate transformers *)
  Definition RelSt (S:Type): RelationalSpecMonad0 :=
    ordmonad_to_relspecmon0 (STCont S).

  (* Computational monads for state on two different sets of locations *)
  Context (loc1 loc2 val : Type) (loc:=(loc1+loc2)%type) (S := loc -> val).
  Let M1 := St (loc1 -> val).
  Let M2 := St (loc2 -> val).

  Definition merge s1 s2 (l:loc) : val :=
    match l with
    | inl l1 => s1 l1
    | inr l2 => s2 l2
    end.

  Let res1 (s0:S) := fun l1 => s0 (inl l1).
  Let res2 (s0:S) := fun l2 => s0 (inr l2).

  (* Relational effect observation M1, M2 -> RelSt S *)
  Import SPropNotations.
  Import FunctionalExtensionality.
  Program Definition θSt : RelationalEffectObservation0 M1 M2 (RelSt S) :=
    mkRelMonMorph _ _ _ _
                  (fun A =>
                     ⦑fun m12 =>
                        ⦑fun post s0 =>
                           let r1 := nfst m12 (res1 s0) in
                           let r2 := nsnd m12 (res2 s0) in
                           post ⟨nfst r1, nfst r2⟩ (merge (nsnd r1) (nsnd r2))⦒⦒)
                  _ _.
  Next Obligation. cbv; intuition. Qed.
  Next Obligation. cbv ; intuition; induction H=> //. Qed.
  Next Obligation.
    apply Ssig_eq=> /=; extensionality x; apply Ssig_eq=> /=.
    extensionality post ; extensionality s0; f_equal.
    extensionality l ; destruct l=> //.
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

  (* Semantic judgement notation for θSt above *)
  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θSt _ _ c1 c2 w).

  (* Translation from pre-/postconditions to backward predicate transformers *)
  Program Definition fromPrePost {A1 A2}
          (pre : S1 -> S2 -> SProp)
          (post : A1 -> S1 -> S1 -> A2 -> S2 -> S2 -> SProp)
    : dfst (RelSt S ⟨A1,A2⟩) :=
    ⦑fun p s0 => pre (res1 s0) (res2 s0) s/\
                 forall a1 a2 s, post a1 (res1 s0) (res1 s) a2 (res2 s0) (res2 s)
                            -> p ⟨a1,a2⟩ s⦒.
  Next Obligation. cbv ; intuition. Qed.

  (* Example rules *)
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

(* Noninterference property and examples *)
Section NonInterference.
  Import SPropNotations.
  Import FunctionalExtensionality.

  (* Noninterference builds on a state monad with two locations *)
  Let loc := bool.
  Let HIGH := true.
  Let LOW := false.
  Let val := nat.
  Let eql := Bool.eqb.
  Let eql_spec := Bool.eqb_spec.

  (* Semantic judgement for noninterference *)
  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ (θSt loc loc val) _ _ c1 c2 w) (at level 85).

  (* Translation from pre-/postconditions, fixing parameters *)
  Let fromPrePost' {A B} pre post := @fromPrePost loc loc val (* eql eql_spec eql eql_spec *) A B pre post.

  (* Noninterference property written in term of pre-/postconditions *)
  Definition NI_pre_post {A:Type} :=
    fromPrePost'
      (fun s1 s2 => s1 false ≡ s2 false)
      (fun (i:A) s1 s1' (i':A) s2 s2' =>  s1' false ≡ s2' false s/\ i ≡ i').

  (* Noninterference property *)
  Definition NI {A : Type} (c : St (loc -> val) A) :=
      ⊨ c ≈ c [{ NI_pre_post }].

  Let put (l:loc) (v:val) : St (loc -> val) unit := fun s => ⟨tt, upd _ eql l v s⟩.
  Let get (l:loc) : St (loc -> val) val := fun s => ⟨s l, s⟩.

  (* Effect specific rules for state *)
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

  Lemma put_put_rule (l1 l2:loc) (v1 v2:nat) :
    ⊨ put l1 v1 ≈ put l2 v2
      [{ fromPrePost' (fun s1 s2 => sUnit)
                      (fun x s1 s1' _ s2 s2' =>    s1' ≡ upd _ eql l1 v1 s1
                                              s/\ s2' ≡ upd _ eql l2 v2 s2)
      }].
  Proof.
    rewrite <- (monad_law1 tt (fun _ => put l1 v1)).
    rewrite <- (monad_law2 (put l2 v2)).
    apply_seq.
    - apply put_right_rule.
    - move=> [] [] /=; apply put_left_rule.
    - cbv; intuition; apply q.
      cbv; intuition; apply SPropAxioms.funext_sprop=> [] b /=.
      elim: (f_sEqual2 _ _ q1 (sEq_refl b)).
      exact: (f_sEqual2 _ _ q3 (sEq_refl b)).
      elim: (f_sEqual2 _ _ q2 (sEq_refl b)).
      exact: (f_sEqual2 _ _ q0 (sEq_refl b)).
  Qed.

  Lemma get_get_rule (l1 l2:loc) :
    ⊨ get l1 ≈ get l2
      [{ fromPrePost' (fun s1 s2 => sUnit)
                      (fun x1 s1 s1' x2 s2 s2' =>    s1' ≡ s1 s/\ x1 ≡ s1 l1
                                                s/\ s2' ≡ s2 s/\ x2 ≡ s2 l2)
      }].
  Proof.
    rewrite <- (monad_law1 tt (fun=> get l1)).
    rewrite <- (monad_law2 (get l2)).
    apply_seq.
    - apply get_right_rule.
    - move => a1 a2 /=; apply get_left_rule.
    - cbv ; intuition; apply q.
      cbv ; intuition; try by subst_sEq=> //.
      elim: (sEq_sym q3); ssymmetry ; apply (f_sEqual2 _ _ q2)=> //.
  Qed.

  (* Examples of noninterferent programs with their proofs *)
  Let prog := bind (get LOW) (fun n => ret n).

  Lemma prog_satisfies_NI : NI prog.
    unfold NI.
    unfold prog.
    - apply_seq=> //.
      + eapply apply_left_tot.
        apply get_left_rule.
        move=> ? ; apply get_right_rule.
        sreflexivity.
      + move=> ? ? /=; refine (ret_rule2 _ _ _ _).
      + cbv; intuition; apply q.
        let k x := exact (f_sEqual2 _ _ x (sEq_refl false)) in
        move: (q0) (p1) (q3) ltac:(k q4) ltac:(k q1) ltac:(k q5) ltac:(k q2) p.
        move=> [] [] [] [] [] [] [] //.
  Qed.

  Let prog2 {B} (f : nat -> B) := bind (get LOW) (fun n => ret (f n)).

  Lemma prog2_satisfies_NI : forall {B} (f : nat -> B), NI (prog2 f).
    move=> B f.
    unfold NI.
    unfold prog2.
    - apply_seq=> //.
      + apply get_get_rule.
      + move=> ? ? /= ; refine (ret_rule2 _ _ _ _).
      + cbv; intuition.
        apply q; split.
        move: (f_sEqual2 _ _ q1 (sEq_refl false))
              (f_sEqual2 _ _ p0 (sEq_refl false)) p=> [] [] //.
        elim: (sEq_sym q0); elim: (sEq_sym q2) ; elim: p=> //.
  Qed.

  Let prog3 := bind (get LOW) (fun n => put HIGH n).

  Lemma prog3_satisfies_NI : NI prog3.
    rewrite /NI /prog3.
    - apply_seq=> //.
      + apply get_get_rule.
      + move=> ? ? /=. apply put_put_rule.
      + cbv; intuition; apply q.
        let k x := exact (f_sEqual2 _ _ x (sEq_refl false)) in
        move: a3 a4 q0 q2 ltac:(k q1) ltac:(k p0) ltac:(k p1) ltac:(k q3) p.
        repeat elim=> //=.
  Qed.

  Let prog4 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW 1 else put LOW 1).

  Lemma prog4_satisfies_NI : NI prog4.
  Proof.
    unfold NI.
    unfold prog4.
    apply_seq => //. apply get_get_rule.
    - move=> a1 a2 /=.
      destruct (Nat.eqb a1 1); destruct (Nat.eqb a2 1); apply put_put_rule.
    - cbv; intuition; apply q; destruct a3, a4; intuition.
      move: (f_sEqual2 _ _ q3 (sEq_refl false))
              (f_sEqual2 _ _ p1 (sEq_refl false)) => [] [] //.
  Qed.

  Let prog5 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW h else put LOW 1).

  Lemma prog5_satisfies_NI : NI prog5.
  Proof.
    Import Coq.Arith.PeanoNat.
    rewrite /NI /prog5.
    apply_seq => //. apply get_get_rule.
    - move => a1 a2 /=.
      remember (Nat.eqb a1 1) as H1.
      remember (Nat.eqb a2 1) as H2.
      destruct H1, H2; symmetry in HeqH2; symmetry in HeqH1.
      apply (Nat.eqb_eq a1 1) in HeqH1; apply (Nat.eqb_eq a2 1) in HeqH2.
      4: apply put_put_rule.
      + rewrite HeqH1; rewrite HeqH2; apply put_put_rule.
      + apply (Nat.eqb_eq a1 1) in HeqH1; rewrite HeqH1; apply put_put_rule.
      + apply (Nat.eqb_eq a2 1) in HeqH2; rewrite HeqH2; apply put_put_rule.
    - cbv; intuition; apply q; destruct a3, a4; intuition.
      move: (f_sEqual2 _ _ q3 (sEq_refl false))
              (f_sEqual2 _ _ p1 (sEq_refl false)) => [] [] //.
  Qed.

End NonInterference.

(* Exploration of product programs for state *)
Section ProductState.
  Import SPropNotations.

  (* It builds again on programs with two locations *)
  Let loc := bool.
  Let HIGH := true. (* private information *)
  Let LOW := false. (* public information *)
  Let val := nat.
  Let eql := Bool.eqb.
  Let eql_spec := Bool.eqb_spec.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ (θSt loc loc val) _ _ c1 c2 w) (at level 85).

  Let fromPrePost' {A B} pre post := @fromPrePost loc loc val (* eql eql_spec eql eql_spec *) A B pre post.

  Let put (l:loc) (v:val) : St (loc -> val) unit := fun s => ⟨tt, upd _ eql l v s⟩.
  Let get (l:loc) : St (loc -> val) val := fun s => ⟨s l, s⟩.

  Let St0 A := St (loc -> val) A.
  Let S12 := loc + loc -> val.

  (* Product program relative monad *)
  Let StProd A1 A2 := St S12 (A1 × A2).
  Notation "m1 ;; m2" := (bind m1 (fun=> m2)) (at level 65).

  Let eqll : (loc+loc) -> (loc+loc) -> bool.
  Proof. move=> [l1|l1] [l2|l2]. 1,4:exact (eql l1 l2). all:exact false. Defined.
  Let put' (l:loc+loc) (v:val) : StProd unit unit := fun s => ⟨⟨tt,tt⟩, upd _ eqll l v s⟩.
  Let get' (l:loc+loc) : StProd val unit := fun s => ⟨⟨s l, tt⟩, s⟩.

  (* Inductive definition of the relation c_1 x c_2 ~> c *)
  Inductive st_rel {A1 A2} : St0 A1 -> St0 A2 -> StProd A1 A2 -> SProp :=
  | srRet : forall a1 a2, st_rel (ret a1) (ret a2) (ret ⟨a1,a2⟩)
  | srPutLeft : forall l v m1 m2 mrel,
      st_rel m1 m2 mrel -> st_rel (put l v ;; m1) m2 (put' (inl l) v ;; mrel)
  | srPutRight : forall l v m1 m2 mrel,
      st_rel m1 m2 mrel -> st_rel m1 (put l v ;; m2) (put' (inr l) v ;; mrel)
  | srGetLeft  : forall l m1 m2 mrel,
      (forall v, st_rel (m1 v) m2 (mrel ⟨v,tt⟩)) -> st_rel (bind (get l) m1) m2 (bind (get' (inl l)) mrel)
  | srGetRight  : forall l m1 m2 mrel,
      (forall v, st_rel m1 (m2 v) (mrel ⟨v,tt⟩)) -> st_rel m1 (bind (get l) m2) (bind (get' (inr l)) mrel).

  Definition srBind {A1 A2 B1 B2 : Type} (m1 : St0 A1) (m2 : St0 A2) (mrel:StProd A1 A2) (f1 : A1 -> St0 B1) (f2 : A2 -> St0 B2) (frel : A1 × A2 -> StProd B1 B2) (m : @st_rel A1 A2 m1 m2 mrel) (f : forall a1 a2, st_rel (f1 a1) (f2 a2) (frel ⟨a1,a2⟩)) : @st_rel B1 B2 (bind m1 f1) (bind m2 f2) (bind mrel frel).
    induction m.
    - simpl.
      exact (f a1 a2).
    - unfold bind. rewrite (monad_law3 (put l v) (fun=> m1) f1).
      rewrite (monad_law3 (put' (inl l) v) (fun=> mrel) frel).
      apply (srPutLeft l v (bind m1 f1) (bind m2 f2)).
      apply IHm.
    - unfold bind. rewrite (monad_law3 (put l v) (fun=> m2) f2).
      rewrite (monad_law3 (put' (inr l) v) (fun=> mrel) frel).
      apply (srPutRight l v (bind m1 f1) (bind m2 f2)).
      apply IHm.
    - unfold bind. rewrite (monad_law3 (get l) m1 f1).
      rewrite (monad_law3 (get' (inl l)) mrel frel).
      apply srGetLeft.
      assumption.
    - unfold bind. rewrite (monad_law3 (get l) m2 f2).
      rewrite (monad_law3 (get' (inr l)) mrel frel).
      apply srGetRight.
      assumption.
  Qed.

  (* A coupling is a product program together with a proof that the relation above holds *)
  Definition coupling {A1 A2} c1 c2 := { c : StProd A1 A2 ≫ st_rel c1 c2 c}.

  (* Effect observation for the product programs *)
  Program Definition ζSt {A1 A2} : StProd A1 A2 -> dfst (RelSt S12 ⟨A1,A2⟩) :=
    fun c => ⦑ fun post s => let r := c s in post (nfst r) (nsnd r)⦒.
  Next Obligation. cbv; intuition. Qed.

  (* Soundness theorem for product programs *)
  Import SPropAxioms.
  Lemma coupling_soundness {A1 A2} c1 c2 (c:StProd A1 A2) :
    st_rel c1 c2 c -> forall w, ζSt c ≤ w -> ⊨ c1 ≈ c2 [{ w }].
  Proof.
    induction 1=> w.
    - apply weaken_rule2. apply ret_rule2.
    - move=> Hw ; simple refine (apply_left _ _ _ _ (w1:=ζSt (put' (inl l) v)) (w2:= ζSt mrel) _ (IHst_rel _ _) _)=> //=.
      eapply weaken_rule2. apply put_left_rule.
      cbv ; intuition; destruct a1 ; destruct a2.
      match goal with [H : a _ ?s0 |- _ ] => enough (s ≡ s0) as Hs ; [induction Hs ; apply H|] end.
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q (sEq_refl l'))=>//. sreflexivity.
    - move=> Hw ; simple refine (apply_right _ _ _ _ (w1:=ζSt (put' (inr l) v)) (w2:= ζSt mrel) _ (IHst_rel _ _) _)=> //=.
      eapply weaken_rule2. apply put_right_rule.
      cbv ; intuition; destruct a1 ; destruct a2.
      match goal with [H : a _ ?s0 |- _ ] => enough (s ≡ s0) as Hs ; [induction Hs ; apply H|] end.
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q (sEq_refl l'))=>//. sreflexivity.
    - apply weaken_rule2.
      assert (m2 = skip ;; m2) as -> by (rewrite /bind monad_law1 //).
      apply_seq.
      apply get_left_rule.
      move=> /= ? ?; apply H; sreflexivity.
      cbv ; intuition.
      induction q.
      enough (a0 ≡ s0) as Hs ; [induction Hs ; apply H0|].
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q1 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=>//.
    - apply weaken_rule2.
      assert (m1 = skip ;; m1) as -> by (rewrite /bind monad_law1 //).
      apply_seq.
      apply get_right_rule.
      move=> /= ? ?; apply H; sreflexivity.
      cbv ; intuition.
      induction q.
      enough (a0 ≡ s0) as Hs ; [induction Hs ; apply H0|].
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q1 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=>//.
  Qed.

  Ltac cleanup_st_rel :=
    match goal with [|- st_rel _ _ ?x] => let h := fresh "h" in set (h := x) ; simpl in h ; unfold h ; clear h end.

  Ltac GetRight :=
    apply srGetRight=> ? ; instantiate (1:= fun '(npair v _)=> _) ; cleanup_st_rel.
  Ltac GetLeft :=
    apply srGetLeft=> ? ; instantiate (1:= fun '(npair v _)=> _); cleanup_st_rel.

  (* Examples for showing noninterference using product programs *
   * i.e. public outputs of the program cannot depend on its private inputs *)
  Let prog := bind (get LOW) (fun n => ret n).

  Definition prog_coupling : coupling prog prog.
  Proof.
    eexists. unfold prog. GetRight. GetLeft. apply srRet.
  Defined.

  Goal forall (c:= Spr1 prog_coupling), ζSt c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.

  Goal forall s, s (inl false) = s (inr false) ->
            let c := Spr1 prog_coupling in
            let '(npair ⟨i1,i2⟩ s') := c s in
            s' (inl false) = s' (inr false) /\ i1 = i2.
  Proof. move=> s H ; simpl ; split. assumption. by []. Qed.

  Let prog2 {B} (f : nat -> B) := bind (get LOW) (fun n => ret (f n)).

  Definition prog2_coupling {B} (f:nat -> B) : coupling (prog2 f) (prog2 f).
  Proof.
    eexists. unfold prog2. GetLeft. GetRight. apply srRet.
  Defined.

  Goal forall {B} (f:nat -> B) (c:= Spr1 (prog2_coupling f)),
      ζSt c ≤ NI_pre_post.
  Proof. cbv ; intuition.
         apply q ; intuition. induction p=> //. Qed.

  Let prog3 := bind (get LOW) (fun n => put HIGH n).
  Definition prog3_coupling : coupling prog3 prog3.
  Proof.
    eexists ; unfold prog3.
    GetLeft. GetRight. apply srPutLeft. apply srPutRight. apply srRet.
  Defined.

  Goal forall (c:=Spr1 (prog3_coupling)), ζSt c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.

  Import Coq.Arith.PeanoNat.

  Let prog4 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW 1 else put LOW 1).

  Definition prog4_coupling : coupling prog4 prog4.
  Proof.
    eexists ; unfold prog4.
    GetRight. GetLeft.
    match goal with | [|- st_rel (if ?b then _ else _) _ _] => destruct b end;
    match goal with | [|- st_rel _ (if ?b then _ else _) _] => destruct b end;
    apply srPutRight; apply srPutLeft; apply srRet.
  Defined.

  Goal forall (c:=Spr1 prog4_coupling), ζSt c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.

  Let prog5 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW h else put LOW 1).

  (* with Definition/Qed it was opaque *)
  Definition prog5_coupling : coupling prog5 prog5.
  Proof.
    eexists ; unfold prog5.
    GetRight. GetLeft.
    match goal with | [|- st_rel (if ?b then _ else _) _ _] =>
                      destruct b eqn:Hb1 ; try apply (Nat.eqb_eq _ 1) in Hb1 end;
      match goal with | [|- st_rel _ (if ?b then _ else _) _] =>
                        destruct b eqn:Hb2 ; try apply (Nat.eqb_eq _ 1) in Hb2
      end;
    cycle 3; subst ; apply srPutLeft; apply srPutRight; apply srRet.
  Defined.

  Print prog5_coupling.

  Goal forall (c:=Spr1 prog5_coupling), ζSt c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.
End ProductState.
