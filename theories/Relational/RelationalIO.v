(*********************************************************)
(**       Relational reasoning on IO                    **)
(*********************************************************)

From Coq Require Import ssreflect ssrfun ssrbool Program.Basics.
From Coq Require Import FunctionalExtensionality Arith.PeanoNat List.

From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads Monoid DijkstraMonadExamples.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

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
  Let carrier := Es12 -> SProp.

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
          (pre : Es1 -> Es2 -> SProp)
          (post : A1 -> Es1 -> Es1 -> A2 -> Es2 -> Es2 -> SProp)
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

  Let ttrue : Es1 -> Es2 -> SProp := fun _ _ => sUnit.

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
    Definition write (o:Oup) : IO unit := op _ (Write o).

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
          (pre : Es1 -> Es2 -> SProp)
          (post : A1 -> Es1 -> Es1 -> A2 -> Es2 -> Es2 -> SProp)
    : dfst (Wrel ⟨A1,A2⟩) :=
    ⦑fun p h => pre (nfst h) (nsnd h) s/\
                 forall a1 a2 h', post a1 (nfst h) (nfst h') a2 (nsnd h) (nsnd h')
                            -> p ⟨a1, a2⟩ h'⦒.
  Next Obligation. split; case: H0 => // ? Hy *; apply H, Hy=> //. Qed.

  Notation "⊨ ⦃ pre ⦄ c1 ≈ c2 ⦃ post ⦄" :=
    (semantic_judgement _ _ _ θIO' _ _ c1 c2 (fromPrePost' pre post)).

  Let ttrue : Es1 -> Es2 -> SProp := fun _ _ => sUnit.

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

  Fixpoint ni_pred (fp1 fp2 : list IOTriple) : SProp :=
    let fix aux fp1 fp2 :=
        match (fp1, fp2) with
        | ([], []) => sUnit
        | (InpPub i1 :: fp1, InpPub i2 :: fp2) => i1 ≡ i2 -> aux fp1 fp2
        | (Out o1 :: fp1, Out o2 :: fp2) => o1 ≡ o2 s/\ aux fp1 fp2
        | (_, _) => sEmpty
        end in
    aux (filter isNotPrivInp (rev fp1)) (filter isNotPrivInp (rev fp2)).

  (* Noninterference property *)
  Definition NI {A : Type} (c : IO A) :=
    ⊨ ⦃ fun h1 h2 => filter isPubInp h1 ≡ filter isPubInp h2 ⦄
      c ≈ c
      ⦃ fun _ _ h1' _ _ h2' => ni_pred h1' h2' ⦄.

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
  Let prog1 := bind readLow write.
  Lemma NI_prog1 : NI prog1.
  Proof.
    rewrite /NI /prog1; hammer; auto_prepost_sEq.
  Qed.

  (* Branching on secrets *)
  Let prog2 := bind readHigh (fun h => if h =? 3 then write 7 else write 13).
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
    simpl.
    (* The conclusion is false *)
  Abort.

  (* Although we branch on secret, the output is the same in both branches *)
  Let prog2' := bind readHigh (fun h => if h =? 3 then write 127 else write 127).
  Lemma NI_prog2' : NI prog2'.
  Proof.
    rewrite /NI /prog2'; hammer.
    set b1 := (_ =? _); set b2 := (_ =? _); case: b1 b2 => [] []; hammer. auto_prepost_sEq.
  Qed.

  Let prog3 := bind readLow (fun n => bind readLow (fun m => write (n + m))).
  Lemma NI_prog3 : NI prog3.
  Proof.
    rewrite /NI /prog3; hammer; auto_prepost_sEq; move => ? ?; subst_sEq => //.
  Qed.

  (* An example with functional extensionality *)
  Let prog4 f := bind readLow (fun n => write (f n)).
  Lemma NI_prog4 : forall f, NI (prog4 f).
  Proof.
    rewrite /NI /prog4 => f; hammer; auto_prepost_sEq; split. f_equiv; assumption. done.
  Qed.

  (* Public writes depend only on public reads; we say nothing about ret in the NI condition *)
  Let prog5 := bind readHigh ret.
  Lemma NI_prog5 : NI prog5.
  Proof.
    rewrite /NI /prog5; hammer. apply ret_rule2. auto_prepost_sEq.
  Qed.

  (* Turns out to be trivial *)
  Let prog6 := bind readHigh (fun => write 23).
  Lemma NI_prog6 : NI prog6.
  Proof.
    rewrite /NI /prog6; hammer; auto_prepost_sEq.
  Qed.

  Fixpoint pubInpSum (iot : list IOTriple) := match iot with
                                              | InpPub a :: rest => a + pubInpSum rest
                                              | _ => O
                                              end.

  (* Read fuel numbers and return the sum *)
  Fixpoint readN sum fuel :=
    match fuel with
    | O => ret sum
    | S fuel => bind readLow (fun m => readN (sum + m) fuel)
    end.
  Lemma aux_readN : forall m n fuel, ⊨ ⦃ fun _ _ => sUnit ⦄
                                  readN m fuel ≈ readN n fuel
                                  ⦃ fun i1 _ h1 i2 _ h2 => m + pubInpSum (rev h1) ≡ i1 s/\
                                                        n + pubInpSum (rev h2) ≡ i2 ⦄.
  Proof.
    move => m n fuel; hammer; elim: fuel m n => [| fuel IH] m n.
    apply gp_ret_rule. cbv -[Nat.add]; intuition; apply q; rewrite 2!Nat.add_0_r //.
    simpl; hammer. apply IH. move => ? ? H; induction H; split => //=; intuition.
    apply q; induction p1, q1 => /=; subst_sEq'. rewrite 2!rev_app_distr /= 2!Nat.add_assoc //.
  Qed.

  (* Read fuel numbers and write the sum *)
  Let prog7 (sum fuel : nat) := bind (readN sum fuel) write.

  Lemma NI_prog7 : forall sum fuel, NI (prog7 sum fuel).
  Proof.
    rewrite /NI /prog7 => sum fuel; hammer; elim: fuel sum => [| fuel ?] sum.
    apply ret_rule2. simpl; hammer. apply aux_readN.
    - move => ? [? ?] H; simpl in H. split => /=; intuition.
      induction (sEq_sym p), (sEq_sym q); clear p q. admit.
    - cbv; intuition; subst_sEq'; apply q => //.
    - admit.
  Admitted.

  (* Two equivalent ways of summing numbers upto n *)
  Fixpoint sumTo sum n : @IO nat nat nat nat :=
    match n with
    | O => ret sum
    | S n => sumTo (sum + n) n
    end.
  Let prog8 (n : nat) := bind readHigh (fun h => if h =? 7 then sumTo O n else ret ((n * (n - 1)) / 2)).
  Lemma NI_prog8 : forall n, NI (prog8 n).
  Proof.
    rewrite /NI /prog8 => n; hammer; elim: n => [|n].
    set b1 := (_ =? _); set b2 := (_ =? _). case: b1 b2 => [] [].
    all: try simpl; try apply ret_rule2.
  Admitted.
End NI_Examples.
