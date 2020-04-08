(*********************************************************)
(**       Relational reasoning on IO                    **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool Program.Basics.
From Coq Require Import FunctionalExtensionality Arith.PeanoNat List.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads
     Monoid DijkstraMonadExamples.
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples
     GenericRulesSimple Commutativity.

Import SPropNotations.
Import ListNotations.

Set Primitive Projections.
Set Universe Polymorphism.

Section IOs.
  Context {I1 I2 O1 O2 : Type}.

  Let M1 := IO I1 O1.
  Let M2 := IO I2 O2.

  Let Es1 := list (I1+O1).
  Let Es2 := list (I2+O2).
  Let Es12 := Es1 × Es2.
  Let carrier := Es12 -> Prop.

  Definition Wun :=
    @MonoCont carrier (@Pred_op_order _) (@Pred_op_order_prorder _).

  Program Definition wop1 (s:IOS O1) : Wun (IOAr I1 s) :=
    match s with
    | Read _ => ⦑fun p h => forall i, p i ⟨ inl i :: nfst h, nsnd h ⟩⦒
    | Write o => ⦑fun p h => p tt ⟨ inr o :: nfst h, nsnd h ⟩⦒
    end.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ; apply H; apply H0. Qed.

  Program Definition wop2 (s:IOS O2) : Wun (IOAr I2 s) :=
    match s with
    | Read _ => ⦑fun p h => forall i, p i ⟨ nfst h, inl i :: nsnd h ⟩⦒
    | Write o => ⦑fun p h => p tt ⟨ nfst h, inr o :: nsnd h ⟩⦒
    end.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ; apply H; apply H0. Qed.

  Import FunctionalExtensionality.
  Lemma io1_io2_commutation : forall s1 s2, commute (wop1 s1) (wop2 s2).
  Proof.
    move=> [|o1] [|o2] //=.
    cbv; apply Ssig_eq=> /=; extensionality k; extensionality h.
    apply SPropAxioms.sprop_ext; do 2 split; done.
  Qed.

  Let Wrel := Wrel Wun.

  Definition θIO :=
    commute_effObs Wun M1 M2 _ _
                   (fromFreeCommute Wun wop1 wop2 io1_io2_commutation).

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θIO _ _ c1 c2 w).

  Program Definition fromPrePost {A1 A2}
          (pre : Es1 -> Es2 -> Prop)
          (post : A1 -> Es1 -> Es1 -> A2 -> Es2 -> Es2 -> Prop)
    : dfst (Wrel ⟨A1,A2⟩) :=
    ⦑fun p h => pre (nfst h) (nsnd h) s/\
                 forall a1 a2 h', post a1 (nfst h) (nfst h') a2 (nsnd h) (nsnd h')
                            -> p ⟨a1, a2⟩ h'⦒.
  Next Obligation. split; case: H0 => // ? Hy *; apply H, Hy=> //. Qed.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ _ θIO _ _ c1 c2 (fromPrePost pre post)).

  Let read1 := read I1 O1.
  Let write1 := @write I1 O1.
  Let read2 := read I2 O2.
  Let write2 := @write I2 O2.

  Let ttrue : Es1 -> Es2 -> Prop := fun _ _ => sUnit.

  Lemma read1_rule {A2} : forall (a2:A2),
      ⊨ ⦃ ttrue ⦄
        read1 ≈ ret a2
        ⦃ fun i1 h1 h1' a2' h2 h2' =>
            h1' ≡ inl i1 :: h1 s/\ a2' ≡ a2 s/\ h2' ≡ h2 ⦄.
  Proof. cbv; move=> ? ? ? [_ Hpost] ?; by apply: Hpost. Qed.

  Lemma read2_rule {A1} : forall (a1:A1),
      ⊨ ⦃ ttrue ⦄
        ret a1 ≈ read2
        ⦃ fun a1' h1 h1' i2 h2 h2' =>
            h1' ≡  h1 s/\ a1' ≡ a1 s/\ h2' ≡ inl i2 :: h2 ⦄.
  Proof. cbv; move=> ? ? ? [_ Hpost] ?; by apply: Hpost. Qed.

  Lemma write1_rule {A2}: forall (o1 : O1) (a2:A2),
      ⊨ ⦃ ttrue ⦄
        write1 o1 ≈ ret a2
        ⦃ fun _ h1 h1' a2' h2 h2' =>
            h1' ≡ inr o1 :: h1 s/\ a2' ≡ a2 s/\ h2' ≡ h2 ⦄.
  Proof. cbv; move=> ? ? ? ? [_ Hpost] ; by apply: Hpost. Qed.

  Lemma write2_rule {A1}: forall (a1 : A1) (o2:O2),
      ⊨ ⦃ ttrue ⦄
        ret a1 ≈ write2 o2
        ⦃ fun a1' h1 h1' _ h2 h2' =>
            h1' ≡ h1 s/\ a1' ≡ a1 s/\ h2' ≡ inr o2 :: h2 ⦄.
  Proof. cbv; move=> ? ? ? ? [_ Hpost] ; by apply: Hpost. Qed.
End IOs.

Section NI_IO.
  Section IOHigh.
    Context {IPub IPriv Oup : Type}.

    Inductive IOS : Type := ReadLow : IOS | ReadHigh : IOS | Write : Oup -> IOS.
    Definition IOAr (op : IOS) : Type :=
      match op with
      | ReadLow => IPub
      | ReadHigh => IPriv
      | Write _ => unit
      end.

    Definition IO := @Free IOS IOAr.

    Definition readLow : IO IPub := op _ ReadLow.
    Definition readHigh : IO IPriv := op _ ReadHigh.
    Definition write (o : Oup) : IO unit := op _ (Write o).

    Inductive IOTriple : Type := InpPub : IPub -> IOTriple
                               | InpPriv : IPriv -> IOTriple
                               | Out : Oup -> IOTriple.

    Definition isPubInp (i : IOTriple) : bool := match i with
                                              | InpPub _ => true
                                              | _ => false
                                              end.

    Definition isPrivInp (i : IOTriple) : bool := match i with
                                               | InpPriv _ => true
                                               | _ => false
                                               end.

    Definition isNotPrivInp := compose negb isPrivInp.

    Definition isOut (i : IOTriple) : bool := match i with
                                           | Out _ => true
                                           | _ => false
                                           end.
  End IOHigh.

  Context {IPub1 IPriv1 O1 IPub2 IPriv2 O2 : Type}.
  Notation "i1 ⊕ i2 ⊕ o" := (@IOTriple i1 i2 o) (at level 65, i2 at next level).

  Let Es1 := listMonoid (IPub1 ⊕ IPriv1 ⊕ O1).
  Let Es2 := listMonoid (IPub2 ⊕ IPriv2 ⊕ O2).
  Let Es12 := prodMonoid Es1 Es2.
  Let XEs := multAction Es12.

  Definition Wun' := UpdSpec XEs.

  Program Definition wop1' (s:IOS) : Wun' (IOAr s) :=
    match s with
    | ReadLow => ⦑fun p h => forall i, p i ⟨ InpPub i :: [], [] ⟩⦒
    | ReadHigh => ⦑fun p h => forall i, p i ⟨ InpPriv i :: [], [] ⟩⦒
    | Write o => ⦑fun p h => p tt ⟨ Out o :: [], [] ⟩⦒
    end.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ; apply H; apply H0. Qed.

  Program Definition wop2' (s:IOS) : Wun' (IOAr s) :=
    match s with
    | ReadLow => ⦑fun p h => forall i, p i ⟨ [], InpPub i :: [] ⟩⦒
    | ReadHigh => ⦑fun p h => forall i, p i ⟨ [], InpPriv i :: [] ⟩⦒
    | Write o => ⦑fun p h => p tt ⟨ [], Out o :: [] ⟩⦒
    end.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ?; apply H ; apply H0. Qed.
  Next Obligation. move=> ? ? H ? H0 ; apply H; apply H0. Qed.

  Lemma io1_io2_commutation' : forall s1 s2, commute (wop1' s1) (wop2' s2).
  Proof.
    move=> [||o1] [||o2] //=.
    all: cbv; apply Ssig_eq=> /=; extensionality k; extensionality h.
    all: apply SPropAxioms.sprop_ext; do 2 split => //.
  Qed.

  Let M1 := @IO IPub1 IPriv1 O1.
  Let M2 := @IO IPub2 IPriv2 O2.
  Let Wrel := Wrel Wun'.

  Definition θIO' :=
    commute_effObs Wun' M1 M2 _ _
                   (fromFreeCommute Wun' wop1' wop2' io1_io2_commutation').

  Program Definition fromPrePost' {A1 A2}
          (pre : Es1 -> Es2 -> Prop)
          (post : A1 -> Es1 -> Es1 -> A2 -> Es2 -> Es2 -> Prop)
    : dfst (Wrel ⟨A1,A2⟩) :=
    ⦑fun p h => pre (nfst h) (nsnd h) s/\
                 forall a1 a2 h', post a1 (nfst h) (nfst h') a2 (nsnd h) (nsnd h')
                            -> p ⟨a1, a2⟩ h'⦒.
  Next Obligation. split; case: H0 => // ? Hy *; apply H, Hy=> //. Qed.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ _ θIO' _ _ c1 c2 (fromPrePost' pre post)).

  Let ttrue : Es1 -> Es2 -> Prop := fun _ _ => sUnit.

  Lemma readLow_readLow_rule :
      ⊨ ⦃ ttrue ⦄
        readLow ≈ readLow
        ⦃ fun i1 h1 h1' i2 h2 h2' =>
            h1' ≡ InpPub i1 :: [] s/\ h2' ≡ InpPub i2 :: [] ⦄.
  Proof. cbv; move => ? ? H ? ?; apply H; split; sreflexivity. Qed.

  Lemma readHigh_readHigh_rule :
      ⊨ ⦃ ttrue ⦄
        readHigh ≈ readHigh
        ⦃ fun i1 h1 h1' i2 h2 h2' =>
            h1' ≡ InpPriv i1 :: [] s/\ h2' ≡ InpPriv i2 :: [] ⦄.
  Proof. cbv; move => ? ? H ? ?; apply H; split; sreflexivity. Qed.

  Lemma write_write_rule : forall (o1 : O1) (o2 : O2),
      ⊨ ⦃ ttrue ⦄
        write o1 ≈ write o2
        ⦃ fun _ h1 h1' _ h2 h2' =>
            h1' ≡ Out o1 :: [] s/\ h2' ≡ Out o2 :: [] ⦄.
  Proof. cbv; move => ? ? ? ? H; apply H; split; sreflexivity. Qed.
End NI_IO.

Section NI_Examples.
  (* For the purpose of examples, let's just have one type of inputs and outputs *)
  Context (Ty := nat).
  Let θIO' := @θIO' Ty Ty Ty Ty Ty Ty.
  Let Wun' := @Wun' Ty Ty Ty Ty Ty Ty.
  Let readHigh := @readHigh Ty Ty Ty.
  Let readLow := @readLow Ty Ty Ty.
  Let write := @write Ty Ty Ty.
  Let IOTriple := @IOTriple Ty Ty Ty.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ _ θIO' _ _ c1 c2 (fromPrePost' pre post)).

  Fixpoint aux (fp1 fp2 : list IOTriple) (p : Prop) :=
    match (fp1, fp2) with
    | ([], []) => p
    (* alt: could filer them here too, instead of in ni_pred *)
    (* | (InpPriv i1 :: fp1, fp2) *)
    (* | (fp1, InpPriv i2 :: fp2) => aux fp1 fp2 p *)
    | (InpPub i1 :: fp1, InpPub i2 :: fp2) => i1 ≡ i2 -> aux fp1 fp2 p
    | (Out o1 :: fp1, Out o2 :: fp2) => o1 ≡ o2 s/\ aux fp1 fp2 p
    | (_, _) => sEmpty
    end.

  Definition ni_pred (fp1 fp2 : list IOTriple) (p : Prop) : Prop :=
    aux (filter isNotPrivInp (rev fp1)) (filter isNotPrivInp (rev fp2)) p.

  (*
     How does this compare to? It seems equivalent!?
     pub-inputs fp1 =list pub-inputs pf2 ==> pub pf1 =list pub pf2

     fp1 = InpPriv password1; InpPub 42; InpPub 41; OutPub 42 -- breaks determinacy
     fp2 = InpPriv password2; InpPub 42; OutPub password2
     fp3 = InpPriv password2; InpPub 42; OutPub 42 -- leaks secret with respect to fp2

     fp1 = InpPriv password1; InpPub 41; InpPub 41; OutPub 42
     fp3 = InpPriv password2; InpPub 43; OutPub 42

     fp1 = InpPriv password1; InpPub 41;
     fp3 = InpPriv password2; InpPub 41;

     fp1 = InpPriv password1; InpPriv 42
     fp2 = InpPriv password2;

     Determinacy:
     P ~> t1 /\ P ~> t2 ==> t1 = t2 \/ (exists m i1 i2, m :: Input i1 <: t1
                                                     /\ m :: Input i2 <: t2)
   *)

  Lemma aux_ni_pred : forall h1 h2 a1 a2 p, (a1 ≡ a2 -> ni_pred h1 h2 p)
                                       -> ni_pred (h1 ++ [InpPub a1]) (h2 ++ [InpPub a2]) p.
  Proof.
    rewrite {2} /ni_pred => ? ? ? ? ? ?; rewrite 2!rev_app_distr //.
  Qed.

  Lemma filter_distr : forall {A} (f : A -> bool) (a b : list A), filter f (a ++ b) = filter f a ++ filter f b.
  Proof.
    move => ? f a ?; induction a => /=. by reflexivity. destruct f.
    rewrite IHa; by reflexivity. by exact IHa.
  Qed.

  Lemma aux_ni_pred2 : forall h1 h2 a1 a2, ni_pred h1 h2 (a1 ≡ a2) -> ni_pred (Out a1 :: h1) (Out a2 :: h2) sUnit.
  Proof.
    move=> ? ? ? ? ; rewrite /ni_pred /= !filter_distr /=.
    set h1 := filter _ _; set h2:= filter _ _.
    elim: h1 h2 => [|[?|?|?] h1 IH] [|[?|?|?] h2] //=.
    by move=> H /H /IH //. by move=> [? /IH]; split=> //.
  Qed.

  (* Noninterference property *)
  Definition NI {A : Type} (c : IO A) :=
    ⊨ ⦃ fun h1 h2 => filter isPubInp h1 ≡ filter isPubInp h2 ⦄
      c ≈ c
      ⦃ fun _ _ h1' _ _ h2' => ni_pred h1' h2' sUnit ⦄.

  (* Is NI equivalent to the following? (Seems quite close) *)
  (* Definition NI2 {A : Type} (c : IO A) := *)
  (*   ⊨ ⦃ ttrue ⦄ *)
  (*     c ≈ c *)
  (*     ⦃ fun _ h1 h1' _ h2 h2' => ni_pred (h1' ++ h1) (h2' ++ h2) sUnit ⦄. *)

  (* Is NI equivalent to the following? (Seems quite close; and probably equiv to NI2?)*)
  (* Definition NI3 {A : Type} (c : IO A) := *)
  (*   ⊨ ⦃ ttrue ⦄ *)
  (*     c ≈ c *)
  (*     ⦃ fun _ _ h1' _ _ h2' => filter isPubInp h1 ≡ filter isPubInp h2 -> *)
  (*                              ni_pred h1' h2' sUnit ⦄. *)

  Ltac subst_sEq' :=
    repeat match goal with
           | H:_ ≡ _ |- _ => induction (sEq_sym H); clear H
           end.

  Ltac auto_prepost_sEq :=
    let H := fresh "H" in
    move => ? [? ?] [? H]; split => //; simpl; intuition; apply H; subst_sEq' => //=.

  Ltac apply_seq' :=
    (match goal with | [|- _ ⊨ _ ≈ _ [{ ?z }]] => is_evar z end ;
     refine (seq_rule _ _ _ _ (wf:=extend_to_Jprod _ (fun '⟨a1, a2⟩ => _)) _ _)
     => /= [| ? ?]) +
    apply_seq=> /= [|? ?|].

  Ltac hammer :=
    repeat lazymatch goal with
           | |- context c [_ ⊨ bind _ _ ≈ bind _ _ [{ _ }]] => apply_seq'
           | |- context c [_ ⊨ readLow ≈ readLow [{ _ }]] => apply readLow_readLow_rule
           | |- context c [_ ⊨ readHigh ≈ readHigh [{ _ }]] => apply readHigh_readHigh_rule
           | |- context c [_ ⊨ write _ ≈ write _ [{ _ }]] => apply write_write_rule
           end.

  Arguments bind : simpl never.
  Arguments ret : simpl never.

  (* Trivial example *)
  Definition prog1 := bind readLow write.
  Lemma NI_prog1 : NI prog1.
  Proof.
    rewrite /NI /prog1; hammer; auto_prepost_sEq.
  Qed.

  (* Branching on secrets *)
  Definition prog2 := bind readHigh (fun h => if h =? 3 then write 7 else write 13).
  Lemma NI_prog2 : NI prog2.
  Proof.
    rewrite /NI /prog2.
    hammer.
    set b1 := (_ =? _); set b2 := (_ =? _).
    case: b1 b2 => [] [];
                    refine (weaken_rule2 _ _ _ _
                                         (w':=fromPrePost'
                                                (fun _ _ => sUnit)
                                                (fun _ _ h1 _ _ h2 =>
                                                   s∃ n1 n2, h1 ≡ [Out n1] s/\ h2 ≡ [Out n2])) _ _);
    try apply write_write_rule;
    auto_prepost_sEq; do 2 eexists; dintuition.
    cbv -[app filter rev ni_pred]; intuition; apply q.
    move: H => [? [? [? ?]]]; subst_sEq'.
    cbv. intuition.
    (* The conclusion is false *)
  Abort.

  (* Although we branch on secret, the output is the same in both branches *)
  Definition prog2' := bind readHigh (fun h => if h =? 3 then write 127 else write 127).
  Lemma NI_prog2' : NI prog2'.
  Proof.
    rewrite /NI /prog2'; hammer.
    set b1 := (_ =? _); set b2 := (_ =? _); case: b1 b2 => [] []; hammer. auto_prepost_sEq.
  Qed.

  Definition prog3 := bind readLow (fun n => bind readLow (fun m => write (n + m))).
  Lemma NI_prog3 : NI prog3.
  Proof.
    rewrite /NI /prog3; hammer; auto_prepost_sEq; move => ? ?; subst_sEq => //.
  Qed.

  (* An example with functional extensionality *)
  Definition prog4 f := bind readLow (fun n => write (f n)).
  Lemma NI_prog4 : forall f, NI (prog4 f).
  Proof.
    rewrite /NI /prog4 => f; hammer; auto_prepost_sEq; split. f_equiv; assumption.
    destruct a0, a3 => //=.
  Qed.

  (* Public writes depend only on public reads, but return values differ *)
  Definition prog5 := bind readHigh ret.
  Lemma NI_prog5 : NI prog5.
  Proof.
    rewrite /NI /prog5; hammer. apply ret_rule2; auto_prepost_sEq.
    move => ? ? H; induction H => /=; intuition; subst_sEq'. apply q => //=.
  Qed.

  (* Turns out to be trivial *)
  Definition prog6 := bind readHigh (fun => write 23).
  Lemma NI_prog6 : NI prog6.
  Proof.
    rewrite /NI /prog6; hammer; auto_prepost_sEq.
  Qed.

  Definition prog_declasify f := bind readHigh (fun n => write (f n)).
  Lemma NI_prog_declasify : forall f,
    ⊨ ⦃ fun _ _ => sUnit ⦄
      (prog_declasify f) ≈ (prog_declasify f)
      ⦃ fun _ _ h1' _ _ h2' => 
          s∃ i1 i2 o1 o2, h1' ≡ [InpPriv i1; Out o1] s/\
                          h2' ≡ [InpPriv i2; Out o2] s/\
                          (f i1 ≡ f i2 -> o1 ≡ o2) ⦄.
  Proof.
  Admitted.
  (* More on declassification:
     https://www.cse.chalmers.se/~andrei/sabelfeld-sands-jcs07.pdf *)

  (* Next, set up for prog7 *)
  Arguments ni_pred : simpl never.

  (* Read fuel numbers and return the sum *)
  Fixpoint readN sum fuel :=
    match fuel with
    | O => ret sum
    | S fuel => bind readLow (fun m => readN (sum + m) fuel)
    end.

  Lemma aux_readN : forall m n fuel, ⊨ ⦃ fun _ _ => sUnit ⦄
                                  readN m fuel ≈ readN n fuel
                                  ⦃ fun a1 _ h1 a2 _ h2 => m ≡ n -> ni_pred h1 h2 (a1 ≡ a2) ⦄.
  Proof.
    move => m n fuel; hammer; elim: fuel m n => [| fuel IH] m n.
    apply gp_ret_rule. by cbv; intuition.
    simpl; hammer. by apply IH. move => ? ? /= [[] H]. intuition. subst_sEq'.
    apply H => /= mnEq; induction mnEq. apply aux_ni_pred => ?; apply H0; f_sEqual => //=.
  Qed.

  (* Read fuel numbers and write the sum *)
  Definition prog7 (sum fuel : nat) := bind (readN sum fuel) write.
  Lemma NI_prog7 : forall sum fuel, NI (prog7 sum fuel).
  Proof.
    rewrite /NI /prog7 => sum fuel; hammer. apply aux_readN.
    move => ? [? ?] H; simpl in *. intuition; apply q.
    subst_sEq' => /=. replace (tt ≡ tt) with sUnit.
      by apply aux_ni_pred2 => //=. apply SPropAxioms.sprop_ext => //.
  Qed.
End NI_Examples.
