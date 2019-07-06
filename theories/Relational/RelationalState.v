From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality Arith.PeanoNat.

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

  Definition NI_pre_post {A:Type} :=
    fromPrePost'
      (fun s1 s2 => s1 false ≡ s2 false)
      (fun (i:A) s1 s1' (i':A) s2 s2' =>  s1' false ≡ s2' false s/\ i ≡ i').

  Definition NI {A : Type} (c : St (loc -> val) A) :=
      ⊨ c ≈ c [{ NI_pre_post }].

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

  Lemma put_put_rule (l1 l2:loc) (v1 v2:nat) :
    ⊨ put l1 v1 ≈ put l2 v2
      [{ fromPrePost' (fun s1 s2 => sUnit)
                      (fun x s1 s1' _ s2 s2' =>    s1' ≡ upd _ eql l1 v1 s1
                                              s/\ s2' ≡ upd _ eql l2 v2 s2)
      }].
  Proof.
    rewrite <- (monad_law1 unit (fun _ => put l1 v1)).
    rewrite <- (monad_law2 (put l2 v2)).
    eapply gp_seq_rule.
    - typeclasses eauto.
    - apply put_right_rule.
    - move=> a1 []. eapply weaken_rule2.
      + apply put_left_rule.
      + unshelve instantiate (1 := ⦑fun=> ?[x]⦒)=> /=.
        3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.
        intuition.
    - cbv; intuition. apply q. cbv; intuition.
      apply SPropAxioms.funext_sprop.
      intros b.
      move: (f_sEqual2 _ _ q3 (sEq_refl b)) (f_sEqual2 _ _ q1 (sEq_refl b)).
      intros. destruct f_sEqual0. assumption.
      apply SPropAxioms.funext_sprop.
      intros b.
      move: (f_sEqual2 _ _ q0 (sEq_refl b)) (f_sEqual2 _ _ q2 (sEq_refl b)).
      intros. destruct f_sEqual0. assumption.
  Qed.

  Lemma get_get_rule (l1 l2:loc) :
    ⊨ get l1 ≈ get l2
      [{ fromPrePost' (fun s1 s2 => sUnit)
                      (fun x1 s1 s1' x2 s2 s2' =>    s1' ≡ s1 s/\ x1 ≡ s1 l1
                                                s/\ s2' ≡ s2 s/\ x2 ≡ s2 l2)
      }].
  Proof. cbv; intuition. Qed.

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
        apply q.
        move: (f_sEqual2 _ _ q4 (sEq_refl false)) (f_sEqual2 _ _ q1 (sEq_refl false)) (f_sEqual2 _ _ q5 (sEq_refl false)) (f_sEqual2 _ _ q2 (sEq_refl false)).
        destruct q0. destruct p1. destruct q3.
        move=> [] [] [] [].
        split; assumption.
  Qed.

  (* General version of the previous program *)
  Let prog2 {B} (f : nat -> B) := bind (get LOW) (fun n => ret (f n)).

  Lemma prog2_satisfies_NI : forall {B} (f : nat -> B), NI (prog2 f).
    move=> B f.
    unfold NI.
    unfold prog2.
    - eapply gp_seq_rule=> //.
      typeclasses eauto.
      + eapply apply_left_tot.
        typeclasses eauto.
        apply get_left_rule.
        move=> ? ; apply get_right_rule.
        sreflexivity.
      + move=> ? ? ; apply gp_ret_rule.
        unshelve instantiate (1 := ⦑fun y => let (v1, v2) := (nfst y, nsnd y) in ?[x]⦒)=> /=.
        3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.
        intuition.
      + cbv; intuition.
        apply q.
        move: (f_sEqual2 _ _ q4 (sEq_refl false)) (f_sEqual2 _ _ q1 (sEq_refl false)) (f_sEqual2 _ _ q5 (sEq_refl false)) (f_sEqual2 _ _ q2 (sEq_refl false)).
        destruct q0. destruct p1. destruct q3.
        move=> [] [] [] [].
        cbv; intuition.
        destruct p.
        sreflexivity.
  Qed.

  Let prog3 := bind (get LOW) (fun n => put HIGH n).

  Lemma prog3_satisfies_NI : NI prog3.
    unfold NI.
    unfold prog3.
    - eapply gp_seq_rule=> //.
      typeclasses eauto.
      + eapply apply_left_tot.
        typeclasses eauto.
        apply get_left_rule.
        move=> ? ; apply get_right_rule.
        sreflexivity.
      + move=> ? ?. eapply weaken_rule2. apply put_put_rule.
        unshelve instantiate (1 := ⦑fun y => let (v1, v2) := (nfst y, nsnd y) in ?[x]⦒)=> /=.
        3:match goal with | [|-?x ≤ ?y] => unify x y end ; sreflexivity.
        intuition.
      + cbv; intuition.
        apply q.
        move: (f_sEqual2 _ _ p2 (sEq_refl false)) (f_sEqual2 _ _ q6 (sEq_refl false)) (f_sEqual2 _ _ q4 (sEq_refl false)) (f_sEqual2 _ _ q1 (sEq_refl false)) (f_sEqual2 _ _ q5 (sEq_refl false)) (f_sEqual2 _ _ q2 (sEq_refl false)).
        destruct q0. destruct p1. destruct q3. destruct a5. destruct a6.
        move=> [] [] [] [] [] [].
        intuition.
  Qed.

  Import Coq.Arith.PeanoNat.

  Let prog4 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW 1 else put LOW 1).
  Lemma prog4_satisfies_NI : NI prog4.
  Proof.
    unfold NI.
    unfold prog4.
    eapply gp_seq_rule.
    - typeclasses eauto.
    - apply get_get_rule.
    - move=> a1 a2.
      eapply weaken_rule2.
      + remember (Nat.eqb a1 1) as H1.
        remember (Nat.eqb a2 1) as H2.
        destruct H1; destruct H2; apply put_put_rule.
      + instantiate (1 := ⦑fun y => let '(npair v1 v2) := y in ?[x]⦒)=> /=.
        sreflexivity.
    - cbv; intuition.
      apply q.
      cbv; intuition.
      move: (f_sEqual2 _ _ p1 (sEq_refl false)) => H1.
      move: (f_sEqual2 _ _ q3 (sEq_refl false)) => H2.
      destruct H1.
      symmetry. assumption.
      destruct a3. destruct a4. reflexivity.
      Unshelve.
      cbv ; intros; assumption.
  Qed.

End NonInterference.

Section ProductState.
  Import SPropNotations.

  Let loc := bool.
  Let HIGH := true.
  Let LOW := false.
  Let val := nat.
  Let eql := Bool.eqb.
  Let eql_spec := Bool.eqb_spec.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ (θSt loc loc val) _ _ c1 c2 w) (at level 85).

  Let fromPrePost' {A B} pre post := @fromPrePost loc loc val eql eql_spec eql eql_spec A B pre post.

  Let put (l:loc) (v:val) : St (loc -> val) unit := fun s => ⟨tt, upd _ eql l v s⟩.
  Let get (l:loc) : St (loc -> val) val := fun s => ⟨s l, s⟩.

  Let St0 A := St (loc -> val) A.
  Let S12 := loc + loc -> val.
  Let StProd A1 A2 := St S12 (A1 × A2).
  Notation "m1 ;; m2" := (bind m1 (fun=> m2)) (at level 65).
  Let eqll : (loc+loc) -> (loc+loc) -> bool.
  Proof. move=> [l1|l1] [l2|l2]. 1,4:exact (eql l1 l2). all:exact false. Defined.
  Let put' (l:loc+loc) (v:val) : StProd unit unit := fun s => ⟨⟨tt,tt⟩, upd _ eqll l v s⟩.
  Let get' (l:loc+loc) : StProd val unit := fun s => ⟨⟨s l, tt⟩, s⟩.

  Inductive st_rel {A1 A2} : St0 A1 -> St0 A2 -> StProd A1 A2 -> SProp :=
  | srRet : forall a1 a2, st_rel (ret a1) (ret a2) (ret ⟨a1,a2⟩)
  | srPutLeft : forall l v m1 m2 mrel,
      st_rel m1 m2 mrel -> st_rel (put l v ;; m1) m2 (put' (inl l) v ;; mrel)
  | srPutRight : forall l v m1 m2 mrel,
      st_rel m1 m2 mrel -> st_rel m1 (put l v ;; m2) (put' (inr l) v ;; mrel)
  | srGetLeft  : forall l m1 m2 mrel,
      (forall v, st_rel (m1 v) m2 (mrel ⟨v,tt⟩)) -> st_rel (bind (get l) m1) m2 (bind (get' (inl l)) mrel)
  | srGetRight  : forall l m1 m2 mrel,
      (forall v, st_rel m1 (m2 v) (mrel ⟨v,tt⟩)) -> st_rel m1 (bind (get l) m2) (bind (get' (inr l)) mrel)
  (* | srBind : forall {B1 B2} m1 m2 (mrel:StProd B1 B2) f1 f2 frel, *)
  (*     @st_rel _ _ m1 m2 mrel -> *)
  (*     (forall a1 a2, st_rel (f1 a1) (f2 a2) (frel ⟨a1,a2⟩)) -> *)
  (*     st_rel (bind m1 f1) (bind m2 f2) (bind mrel frel) *)
  .

  Definition coupling {A1 A2} c1 c2 := { c : StProd A1 A2 ≫ st_rel c1 c2 c}.

  Program Definition θSt12 {A1 A2} : StProd A1 A2 -> dfst (RelSt S12 ⟨A1,A2⟩) :=
    fun c s => ⦑ fun post => post (c s)⦒.
  Next Obligation. move: H0 ; apply H. Qed.

  Import SPropAxioms.
  Lemma coupling_soundness {A1 A2} c1 c2 (c:StProd A1 A2) :
    st_rel c1 c2 c -> forall w, θSt12 c ≤ w -> ⊨ c1 ≈ c2 [{ w }].
  Proof.
    induction 1=> w.
    - apply weaken_rule2. apply ret_rule2.
    - move=> Hw ; simple refine (apply_left _ _ _ _ (w1:=θSt12 (put' (inl l) v)) (w2:= θSt12 mrel) _ (IHst_rel _ _) _)=> //=.
      eapply weaken_rule2. apply put_left_rule.
      cbv ; intuition; destruct a1 ; destruct a2.
      match goal with [H : a0 ⟨_, ?s0⟩ |- _ ] => enough (s ≡ s0) as Hs ; [induction Hs ; apply H|] end.
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q (sEq_refl l'))=>//.
    - move=> Hw ; simple refine (apply_right _ _ _ _ (w1:=θSt12 (put' (inr l) v)) (w2:= θSt12 mrel) _ (IHst_rel _ _) _)=> //=.
      eapply weaken_rule2. apply put_right_rule.
      cbv ; intuition; destruct a1 ; destruct a2.
      match goal with [H : a0 ⟨_, ?s0⟩ |- _ ] => enough (s ≡ s0) as Hs ; [induction Hs ; apply H|] end.
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q (sEq_refl l'))=>//.
    - apply weaken_rule2.
      assert (m2 = skip ;; m2) as -> by (rewrite /bind monad_law1 //).
      eapply gp_seq_rule ; [typeclasses eauto|..].
      apply get_left_rule.
      instantiate (1:= ⦑fun '⟨a1, a2⟩ => _⦒); move=> /= ? ?; apply H; sreflexivity.
      cbv ; intuition.
      induction q.
      enough (a ≡ s0) as Hs ; [induction Hs ; apply H0|].
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q1 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=>//.
    - apply weaken_rule2.
      assert (m1 = skip ;; m1) as -> by (rewrite /bind monad_law1 //).
      eapply gp_seq_rule; [typeclasses eauto|..].
      apply get_right_rule.
      instantiate (1:= ⦑fun '⟨a1, a2⟩ => _⦒); move=> /= ? ?; apply H; sreflexivity.
      cbv ; intuition.
      induction q.
      enough (a ≡ s0) as Hs ; [induction Hs ; apply H0|].
      apply funext_sprop; move=> [l'|l'].
      induction (f_sEqual2 _ _ q1 (sEq_refl l'))=> //.
      induction (f_sEqual2 _ _ q0 (sEq_refl l'))=>//.
      Unshelve. all:cbv ; intuition; destruct y; inversion H0; auto.
  Qed.

  Ltac cleanup_st_rel :=
    match goal with [|- st_rel _ _ ?x] => let h := fresh "h" in set (h := x) ; simpl in h ; unfold h ; clear h end.

  Ltac GetRight :=
    apply srGetRight=> ? ; instantiate (1:= fun '(npair v _)=> _) ; cleanup_st_rel.
  Ltac GetLeft :=
    apply srGetLeft=> ? ; instantiate (1:= fun '(npair v _)=> _); cleanup_st_rel.

  Let prog := bind (get LOW) (fun n => ret n).

  Definition prog_coupling : coupling prog prog.
  Proof.
    eexists. unfold prog. GetRight. GetLeft. apply srRet.
  Defined.

  Goal forall (c:= Spr1 prog_coupling), θSt12 c ≤ NI_pre_post.
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
      θSt12 c ≤ NI_pre_post.
  Proof. cbv ; intuition. apply q ; intuition. induction p=> //. Qed.

  Let prog3 := bind (get LOW) (fun n => put HIGH n).
  Definition prog3_coupling : coupling prog3 prog3.
  Proof.
    eexists ; unfold prog3.
    GetLeft. GetRight. apply srPutLeft. apply srPutRight. apply srRet.
  Defined.

  Goal forall (c:=Spr1 (prog3_coupling)), θSt12 c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.

  Import Coq.Arith.PeanoNat.

  Let prog4 := bind (get HIGH) (fun h => if Nat.eqb h 1 then put LOW 1 else put LOW 1).

  Definition prog4_coupling : coupling prog4 prog4.
  Proof.
    eexists ; unfold prog4.
    GetRight. GetLeft.
    match goal with | [|- st_rel (if ?b then _ else _) _ _] => destruct b end;
    match goal with | [|- st_rel _ (if ?b then _ else _) _] => destruct b end;
    apply srPutRight ; apply srPutLeft ; apply srRet.
  Defined.

  Goal forall (c:=Spr1 prog4_coupling), θSt12 c ≤ NI_pre_post.
  Proof. cbv ; intuition. Qed.

End ProductState.