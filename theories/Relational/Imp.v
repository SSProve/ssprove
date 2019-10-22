From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import RelativeMonads OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

Set Primitive Projections.
Set Universe Polymorphism.

Section ImpMonad.
  Context (S:Type).

  Set Implicit Arguments.
  Inductive Imp (A:Type) :=
  | ImpRet : A -> Imp A
  | ImpGet : (S -> Imp A) -> Imp A
  | ImpSet : S -> Imp A -> Imp A
  | ImpDoWhile : Imp bool -> Imp A -> Imp A.

  Fixpoint Imp_bind {A B : Type} (m : Imp A) (f : A -> Imp B) {struct m} : Imp B :=
    match m with
    | ImpRet v => f v
    | ImpGet k => ImpGet (fun s => Imp_bind (k s) f)
    | ImpSet s k => ImpSet s (Imp_bind k f)
    | ImpDoWhile c k => ImpDoWhile c (Imp_bind k f)
    end.

  Import FunctionalExtensionality.
  Program Definition Imp_monad : Monad := @mkMonad Imp ImpRet (@Imp_bind) _ _ _.
  Next Obligation.
    move: c.
    refine (fix IH (c: Imp A) {struct c} := _).
    case:c => //= [?|? ?|? ?]; f_equal; first extensionality s; apply: IH.
  Qed.
  Next Obligation.
    move: c.
    refine (fix IH (c: Imp A) {struct c} := _).
    case:c => //= [?|? ?|? ?]; f_equal; first extensionality s; apply: IH.
  Qed.


  Definition WrelSt := ordmonad_to_relspecmon0 (STCont (S×S)).

  Let W A := dfst (WrelSt A).

  Import SPropNotations.
  Program Definition ffix {A} (f : W A -> W A) : W A := ⦑fun post => fun s0 => forall w, f w ≤ w -> Spr1 w post s0 ⦒.
  Next Obligation.
    cbv; intuition.
    move: (H0 w H1). apply (Spr2 w x y H a)=> //.
  Qed.

  Let one : Type := unit.
  Let bool : Type := bool.

  Definition do_while (body : Imp bool) : Imp unit := ImpDoWhile body (ImpRet tt).

  Program Definition OrdCat_prodlift {A1 A2 B} (f : A1 -> A2 -> dfst B)
    : OrdCat⦅Jprod ⟨A1,A2⟩; B⦆ :=
    Sexists _ (fun '(npair a1 a2) => f a1 a2) _.
  Next Obligation. intros [? ?] [? ?] eq; inversion eq. sreflexivity. Qed.

  Eval cbv in W ⟨one,one⟩.

  Definition Wun := STCont (S × S).
  Definition W' := ordmonad_to_relmon Wun.

  Eval cbv in (Wun bool).
  Notation "x ≊ y" := (x ≤ y s/\ y ≤ x) (at level 70).
  Lemma antisym_W' {A} (w1 w2: dfst (W' A)) : w1 ≊ w2 -> w1 = w2.
  Proof.
    move=> H; apply Ssig_eq; extensionality p; extensionality s;
            apply SPropAxioms.sprop_ext; do 2 split;
              move: H => [H1 H2]; [apply: H2| apply: H1].
  Qed.


  (* FIXME: this is a greatest fixpoint for our choice of order... *)
  Let R (A : Type) := (@omon_rel Wun A).
  Program Definition ffixun {A} (f : Wun A -> Wun A) : Wun A := ⦑fun post s0 => forall w, R (f w) w -> Spr1 w post s0 ⦒.
  Next Obligation.
    cbv; intuition.
    move: (H0 w H1). apply (Spr2 w x y H a)=> //.
  Qed.

  Program Definition tarksi_fix {A} (f : dfst (W' A) --> W' A) : dfst (W' A) :=
    ⦑fun post s0 => s∃ w, f w ≤ w s/\ w∙1 post s0⦒.
  Next Obligation.
    move=> ? ? H ? [w0 [? H']]; exists w0; split=> //; move: H'; apply: (w0∙2)=> //.
  Qed.

  Lemma tarksi_fix_prefixpoint {A} (f : OrdCat⦅W' A; W' A⦆) :
    f∙1 (tarksi_fix f∙1) ≤ tarksi_fix f∙1.
  Proof.
    move=> p s /= [w0 [Hpre]] /Hpre. apply: f∙2.
    move=> ? ? ?; exists w0; intuition.
  Qed.

  Lemma tarksi_fix_fixpoint {A} (f : OrdCat⦅W' A; W' A⦆) :
    f∙1 (tarksi_fix f∙1) = tarksi_fix f∙1.
  Proof.
    apply antisym_W'; split; first apply tarksi_fix_prefixpoint.
    move=> post s H /=; exists (f∙1 (tarksi_fix f∙1)); split=> //.
    apply: f∙2; apply: tarksi_fix_prefixpoint.
  Qed.

  Program Definition WungetL {A : Type} (k : S -> Wun A) : Wun A :=
    ⦑fun post s0 => Spr1 (k (nfst s0)) post s0⦒.
  Next Obligation. cbv; intros x y H [sl sr]; apply: (k _)∙2=> //. Qed.

  Program Definition WungetR {A : Type} (k : S -> Wun A) : Wun A :=
    ⦑fun post s0 => Spr1 (k (nsnd s0)) post s0⦒.
  Next Obligation. cbv; intros x y H [sl sr]; apply: (k _)∙2=> //. Qed.

  Program Definition WunsetL {A : Type} (s : S) (k : Wun A) : Wun A :=
    ⦑fun post s0 => Spr1 k post (npair s (nsnd s0))⦒.
  Next Obligation. cbv; intros x y H s0; apply: k∙2=> //. Qed.

  Program Definition WunsetR {A : Type} (s : S) (k : Wun A) : Wun A :=
    ⦑fun post s0 => Spr1 k post (npair (nfst s0) s)⦒.
  Next Obligation. cbv; intros x y H s0; apply: k∙2=> //. Qed.

  Definition loop (w0 : Wun bool) (wcont : Wun unit) : Wun unit :=
    bind w0 (fun b => if b then wcont else ret tt).

  Fixpoint θunL (A : Type) (c: Imp A) {struct c} : Wun A :=
      match c with
      | ImpRet a => @ret Wun _ a
      | ImpGet k => WungetL (fun s => θunL (k s))
      | ImpSet s k => WunsetL s (θunL k)
      | ImpDoWhile body k =>
        bind (tarksi_fix (loop (θunL body))) (fun _ => (θunL k))
      end.

  Fixpoint θunR (A : Type) (c: Imp A) {struct c} : Wun A :=
      match c with
      | ImpRet a => @ret Wun _ a
      | ImpGet k => WungetR (fun s => θunR (k s))
      | ImpSet s k => WunsetR s (θunR k)
      | ImpDoWhile body k =>
        bind (tarksi_fix (loop (θunR body))) (fun _ => (θunR k))
      end.

  Program Definition θunL_mm : MonadMorphism Imp_monad Wun := @mkMorphism Imp_monad _ θunL _ _.
  Next Obligation.
    move: m.
    refine (fix IH (m: Imp A) {struct m} := _).
    case:m => //= [?|? ?|? ?] ;unfold MonoCont_bind ; apply Ssig_eq; extensionality k=> /=; extensionality s0; rewrite IH //.
  Qed.

  Program Definition θunR_mm : MonadMorphism Imp_monad Wun := @mkMorphism Imp_monad _ θunR _ _.
  Next Obligation.
    move: m.
    refine (fix IH (m: Imp A) {struct m} := _).
    case:m => //= [?|? ?|? ?] ;unfold MonoCont_bind ; apply Ssig_eq; extensionality k=> /=; extensionality s0; rewrite IH //.
  Qed.

  Let M1 := Imp_monad.
  Let M2 := Imp_monad.

  Program Definition θrel := commute_effObs Wun M1 M2 θunL_mm θunR_mm _.
  Next Obligation. admit.
    (* move: c1 c2. *)
    (* refine (fix IH1 (c1: Imp A1) {struct c1} := _). *)
    (* refine (fix IH2 (c2: Imp A2) {struct c2} := _). *)
    (* case c1; case c2. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - cbv; intuition. *)
    (* - intros i i0. *)
    (*   unfold commute. simpl. unfold MonoCont_bind. simpl. *)
  Admitted.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θrel _ _ c1 c2 w).

  Definition omega_seq (A : ordType) := nat -> dfst A.

  Definition omega_chain (A : ordType) :=
    { c : omega_seq A ≫ forall (n : nat), c n ≤ c (1 + n) }.

  Definition underlying_seq {A} (c : omega_chain A) : nat -> _ := c∙1.
  Coercion underlying_seq : omega_chain >-> Funclass.

  Definition upper_seq (A : ordType) (c : omega_seq A) (v : dfst A) : SProp :=
    s∀ n, c n ≤ v.

  Definition sup_seq (A : ordType) (c : omega_seq A) (v : dfst A) : SProp :=
    upper_seq c v s/\ s∀ v', upper_seq c v' -> v ≤ v'.

  (* Suprema in W' *)
  Program Definition sup_Wun {A} (c : omega_chain (W' A)) : Wun A :=
    ⦑fun p s => forall n, (c n)∙1 p s ⦒.
  Next Obligation. move=> ? ? H ? f n; move: (f n); apply: (c n)∙2=> //. Qed.

  Lemma sup_seq_Wun {A} (c : omega_chain (W' A)) : sup_seq c (sup_Wun c).
  Proof. cbv; intuition. Qed.

  Definition sup_W' {A} (c:omega_chain (W' A)) : dfst (W' A) :=
    sup_Wun c.



  Definition apply_seq {A B} (c : omega_seq A) (f : OrdCat⦅A;B⦆) : omega_seq B
    := fun n => f∙1 (c n).

  Program Definition apply_seq' {A B} (c:omega_chain A) (f:OrdCat⦅A;B⦆)
    : omega_chain B := ⦑apply_seq c f⦒.
  Next Obligation. apply: f∙2; apply: c∙2. Qed.

  Definition omega_continuous {A B} (f : OrdCat⦅A;B⦆) :=
    s∀ (c : omega_chain A) v, sup_seq c v -> sup_seq (apply_seq c f) (f∙1 v).

  (*Specialization of omega-continuity for element w : Wun _ *)
  Definition omega_continuous_Wun {A} (w:Wun A) : SProp :=
    forall (c:nat -> _ -> _ -> SProp), (forall n p s, c (1+n) p s -> c n p s) ->
                             forall s, (w∙1 (fun x s => forall n, c n x s) s s<-> forall n, w∙1 (c n) s).



  Program Definition cst_omega_chain {A} (a:dfst A) : omega_chain A := ⦑fun=> a⦒.
  Next Obligation. sreflexivity. Qed.


  Program Definition loop' (w0:Wun bool) : OrdCat⦅W' unit;W' unit⦆ :=
    ⦑loop w0⦒.
  Next Obligation. move=> ? ?  H ? ?; apply: w0∙2=> -[] //; sreflexivity. Qed.

  Lemma loop_omega_continuous (w0:Wun bool) (Hw0 : omega_continuous_Wun w0) (loop := loop' w0) :
    forall (c : omega_chain (W' unit)), sup_seq (apply_seq c loop) (loop∙1 (sup_Wun c)).
  Proof.
    move=> c; split ; first (move=> ? ? ?; apply: w0∙2=> -[]; cbv; intuition).
    move=> w /ltac:(cbv) Hwsup p s Hw. cbv.
    set p' := fun b => _.
    enough (p' = fun b s=> forall n, if b then (c∙1 n)∙1 p s else @^~ tt p s) as ->.
    - apply Hw0; first (move=> ? [] ? //=; apply: (c∙2)).
      move=> n; move: (Hwsup n p s Hw); apply: w0∙2=> -[] ; sreflexivity.
    - extensionality b; extensionality s'.
      apply SPropAxioms.sprop_ext;do 2 split; unfold p'.
      destruct b; intuition.
      destruct b=> // /(fun f=> f 0) //.
  Qed.


  (** Kleene fixpoint *)

  Program Definition botW A : dfst (W' A) := ⦑fun p s => sUnit⦒.
  Next Obligation. cbv; intuition. Qed.

  Lemma botW_smallest A (w : dfst (W' A)) : botW A ≤ w.
  Proof. done. Qed.

  Fixpoint iter {A} (f:OrdCat⦅W' A; W' A⦆) (n:nat) : dfst (W' A) :=
    match n with
    | 0 => botW A
    | Datatypes.S n => f∙1 (iter f n)
    end.

  Program Definition iter_chain {A} (f:OrdCat⦅W' A; W' A⦆) : omega_chain (W' A)
    := ⦑iter f⦒.
  Next Obligation.
    elim: n=> [|/= ? IH]; first apply botW_smallest.
    apply: (f∙2)=> //.
  Qed.

  Definition kleene_fix {A} (f:OrdCat⦅W' A; W' A⦆) : dfst (W' A) :=
    sup_Wun (iter_chain f).

  Lemma kleene_fix_fixpoint {A} (f:OrdCat⦅W' A; W' A⦆)
        (Hcont : forall c, f∙1 (sup_W' c) ≊ sup_W' (apply_seq' c f)) :
    f∙1 (kleene_fix f) = kleene_fix f.
  Proof.
    apply antisym_W'; move: (Hcont (iter_chain f))=> [H1 H2].
    split; unfold kleene_fix; estransitivity.
    apply H1. move=> ? ? H n; apply: (H (1+n)).
    unfold sup_W' in H2. 2:apply H2.
    move=> ? ? H [|n]=> //. apply: (H n).
  Qed.

  Lemma kleene_fix_smallest_fixpoint {A} (f:OrdCat⦅W' A; W' A⦆)
        (wfix: dfst (W' A))
        (Hfix : f∙1 wfix = wfix) : kleene_fix f ≤ wfix.
  Proof.
    move=> p s Hw n; elim: n p s Hw => [//|n IH] p s.
    rewrite -Hfix. apply: f∙2=> ? ?. apply: IH.
  Qed.

  Lemma tarski_smallest_fixpoint {A} (f:dfst (W' A) --> W' A)
        (wfix: dfst (W' A))
        (Hfix : f wfix = wfix) : tarksi_fix f ≤ wfix.
  Proof.
    move=> p s /= H; exists wfix; split=> //; rewrite Hfix; sreflexivity.
  Qed.


  Lemma kleene_vs_tarski {A} (f:OrdCat⦅W' A; W' A⦆)
        (Hcont : forall c, f∙1 (sup_W' c) ≊ sup_W' (apply_seq' c f))
    : kleene_fix f = tarksi_fix (f∙1).
  Proof.
    apply antisym_W'; split.
    - apply: kleene_fix_smallest_fixpoint; apply: tarksi_fix_fixpoint.
    - apply: tarski_smallest_fixpoint; apply: kleene_fix_fixpoint=> //.
  Qed.

  (** Lemmas about omega-continuity of various elements in Wun/W' *)

  Definition preserves_omega_cont {A} (f:OrdCat⦅W' A; W' A⦆) :=
    forall w, omega_continuous_Wun w -> omega_continuous_Wun (f∙1 w).



  Lemma retW_omega_cont_Wun {A} (a:A) : omega_continuous_Wun (@retW W' _ a).
  Proof. cbv; intuition. Qed.

  Lemma bindW_omega_cont_Wun {A B} (w: dfst (W' A)) (f : A --> W' B):
    omega_continuous_Wun w ->
    (forall (a:A), omega_continuous_Wun (f a)) ->
    omega_continuous_Wun (w ≫= to_discr f).
  Proof.
    move=> Hw Hf c Hc s; split.
    move=> H n; move: H; apply w∙2=> ? ?; apply: ((to_discr f)∙1 _)∙2=> ? ? //.
    unshelve epose (Hw (fun n a=> (f a)∙1 (c n)) _ s) as Hw'.
    move=> ? ? ? /= ; apply (f _)∙2=> ? ?; apply: Hc=> //.
    move=> H; apply Hw' in H; move: H. apply: w∙2=> a s0 /=.
    move: (Hf a c Hc s0)=> []//.
  Qed.

  Lemma iter_omega_continuous_Wun {A} (f:OrdCat⦅W' A; W' A⦆)
        (Hf : preserves_omega_cont f) : forall n, omega_continuous_Wun (iter f n).
  Proof. elim=> [//|n IH]; apply Hf=> //. Qed.

  Lemma kleene_fix_omega_cont {A} (f:OrdCat⦅W' A; W' A⦆)
        (Hf : preserves_omega_cont f) :
    omega_continuous_Wun (kleene_fix f).
  Proof.
    move=> c Hc ?; split.
    move=> x n; move: x; apply: (kleene_fix _)∙2=> ? ? //.
    move=> Hfix. unfold kleene_fix, sup_Wun=> /= k.
    apply (iter_omega_continuous_Wun Hf)=> // n.
    apply: (Hfix n k).
  Qed.

  Lemma loop_preserves_omega_cont w0 (Hw0 : omega_continuous_Wun w0):
    preserves_omega_cont (loop' w0).
  Proof.
    move=> w Hwcont c Hc ?; split.
    - move=> H k; move: H; unfold loop', loop=> /=.
      apply w0∙2=> -[] ? //=; apply w∙2=> -[] ? //.
    - move=> H. unfold loop', loop=> /=.
      apply bindW_omega_cont_Wun=> //.
      move=> [] //=.
  Qed.



  Definition preorder_from_type (A : Type) : {R : srelation (Wun A) ≫ PreOrder R}.
    econstructor.
    apply (omon_order Wun A).
  Defined.
  Definition ordertype_from_type (A : Type) : ordType.
    econstructor.
    apply (preorder_from_type A).
  Defined.

  Program Definition bottom_Wun_seq {A : Type} : omega_chain (ordertype_from_type A) := ⦑fun n =>⦑ fun post s0 => sEmpty ⦒ ⦒.
  Next Obligation. cbv; intuition. Qed.
  Next Obligation. sreflexivity. Qed.


End ImpMonad.
