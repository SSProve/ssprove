From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures MonadExamples SpecificationMonads.
(* From Mon.SM Require Import SMMonadExamples.  *)
From Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples GenericRulesSimple Commutativity.

From Equations Require Import Equations.

(* Show Obligation Tactic. *)
(* by default Equations set the obligation tactic to
Tactics.program_simplify; Tactics.equations_simpl; try Tactics.program_solve_wf
*)
Obligation Tactic := Tactics.program_simpl.

Set Primitive Projections.
Set Universe Polymorphism.
Set Implicit Arguments.

Section OmegaCpo.
  Context (A:ordType).
  Import SPropNotations.

  Definition ωchain := { c : nat --> A | forall n, c n ≤ c (S n)}.
  Definition underlying_seq (c:ωchain) : nat --> A := c∙1.
  Coercion underlying_seq : ωchain >-> Funclass.

  Class ωCpo :=
    { bot : dfst A
    ; ωsup : ωchain --> A
    ; bot_smallest : forall a, bot ≤ a
    ; ωsup_ub : forall (c:ωchain) n, c n ≤ ωsup c
    ; ωsup_lub : forall (c:ωchain) a, (forall n, c n ≤ a) -> ωsup c ≤ a
    }.
End OmegaCpo.

Section OmegaContinuous.
  Context {A B : ordType} (f:OrdCat⦅A;B⦆).
  Import SPropNotations.

  Program Definition apply_seq (c:ωchain A) : ωchain B := ⦑f∙1 \o c⦒.
  Next Obligation. apply: f∙2; apply: c∙2. Qed.

  Context `{ωCpo A} `{ωCpo B}.
  Definition ωcontinuous := forall (c:ωchain A), f∙1 (ωsup c) = ωsup (apply_seq c).
End OmegaContinuous.

Definition antisym (A:ordType) :=
  forall (a1 a2: dfst A), a1 ≤ a2 -> a2 ≤ a1 -> a1 = a2.

Definition iter {A:ordType} (f : dfst A --> A) (bot:dfst A) :=
  fix iter (n:nat) : dfst A := if n is S m then f (iter m) else bot.

Section KleeneFixpoint.
  Context (A:ordType) (Hant:antisym A) `{ωCpo A} (f:OrdCat⦅A;A⦆) (fcont : ωcontinuous f).
  Import SPropNotations.

  Let iter := Eval cbn in iter f∙1 (@bot _ _).

  Program Definition iter_chain : ωchain A := ⦑iter⦒.
  Next Obligation.
    elim: n=> [|/= ? IH]; first apply bot_smallest.
    apply: (f∙2)=> //.
  Qed.

  Definition kleene_fix : dfst A := ωsup iter_chain.

  Lemma kleene_fix_fixpoint : f∙1 kleene_fix = kleene_fix.
  Proof.
    rewrite /kleene_fix fcont; apply Hant.
    - apply ωsup_lub=> n /=; rewrite -[f∙1 _]/(iter_chain (S n)); apply ωsup_ub.
    - apply ωsup_lub=> -[|n] /=; first apply bot_smallest.
      rewrite -[f∙1 _]/(apply_seq f iter_chain n); apply: ωsup_ub.
  Qed.

  Lemma kleene_fix_smallest_fixpoint
        (wfix: dfst A) (Hfix : f∙1 wfix = wfix) : kleene_fix ≤ wfix.
  Proof.
    unfold kleene_fix; apply: ωsup_lub.
    elim=>[|n IH] /=; first apply bot_smallest.
    rewrite -Hfix; apply: f∙2=>//.
  Qed.

End KleeneFixpoint.

Section unarySpecStateOmegaCpo.
  Context (S0:Type) {A:Type}.
  Import SPropNotations.
  Definition WSt  := ordmonad_to_relmon (STCont S0).

  Program Definition botWSt : dfst (WSt A) := ⦑fun p s => True⦒.
  Next Obligation. done. Qed.

  Program Definition supWSt (c : ωchain (WSt A)) : dfst (WSt A) :=
    ⦑fun p s => forall n, (c n)∙1 p s ⦒.
  Next Obligation. move=> ? ? H ? f n; move: (f n); apply: (c n)∙2=> //. Qed.

  Global Program Instance stcont_omegacpo : ωCpo (WSt A) :=
    Build_ωCpo botWSt supWSt _ _ _.
  Next Obligation. done. Qed.
  Next Obligation. move=> ? ? //. Qed.
  Next Obligation. move=> ? ? ? ?; now apply: H. Qed.

  Require Import FunctionalExtensionality.
  Lemma antisym_WSt: antisym (WSt A).
  Proof.
    move=> w1 w2 H1 H2; apply sig_eq; extensionality p; extensionality s;
            apply SPropAxioms.sprop_ext; do 2 split; [apply: H2| apply: H1].
  Qed.

  Program Definition kleene_ufix (f : dfst (WSt A) --> WSt A) : dfst (WSt A)
    := ⦑fun p s => forall n, (iter f botWSt n)∙1 p s⦒.
  Next Obligation.
    move=> ? ? H ? H' n; move: (H' n).
    apply: (@iter (WSt A) f botWSt n)∙2; apply H.
  Qed.

  Lemma kleene_fix_ufix_eq (f:OrdCat⦅WSt A;WSt A⦆) : kleene_fix f = kleene_ufix (f∙1).
  Proof. reflexivity. Defined.

  Program Definition tarksi_fix (f : dfst (WSt A) --> WSt A) : dfst (WSt A) :=
    ⦑fun post s0 => exists w, f w ≤ w s/\ w∙1 post s0⦒.
  Next Obligation.
    move=> ? ? H ? [w0 [? H']]; exists w0; split=> //; move: H'; apply: (w0∙2)=> //.
  Qed.

  Lemma tarksi_fix_prefixpoint (f : OrdCat⦅WSt A; WSt A⦆) :
    f∙1 (tarksi_fix f∙1) ≤ tarksi_fix f∙1.
  Proof.
    move=> p s /= [w0 [Hpre]] /Hpre. apply: f∙2.
    move=> ? ? ?; exists w0; intuition.
  Qed.

  Lemma tarksi_fix_fixpoint (f : OrdCat⦅WSt A; WSt A⦆) :
    f∙1 (tarksi_fix f∙1) = tarksi_fix f∙1.
  Proof.
    apply antisym_WSt; first apply tarksi_fix_prefixpoint.
    move=> post s H /=; exists (f∙1 (tarksi_fix f∙1)); split=> //.
    apply: f∙2; apply: tarksi_fix_prefixpoint.
  Qed.
End unarySpecStateOmegaCpo.


Section PropOmegaCpo.
  Import SPropNotations.
  Program Definition prop_op_oT : ordType := dpair _ SProp ⦑SProp_op_order⦒.
  Next Obligation. typeclasses eauto. Defined.

  Global Program Instance prop_ωCpo : ωCpo prop_op_oT :=
    Build_ωCpo True (fun c => forall n, c n) _ _ _.
  Next Obligation. done. Qed.
  Next Obligation. apply. Qed.
  Next Obligation. move=> H' n; exact (H n H'). Qed.

  (* Global Program Instance prop_ωCpo : ωCpo prop_ordType := *)
  (*   Build_ωCpo False (fun c => exists n, c n) _ _ _. *)
  (* Next Obligation. move=> [] //. Qed. *)
  (* Next Obligation. move=> H; eexists; apply H. Qed. *)
  (* Next Obligation. move=> [n H']; exact (H n H'). Qed. *)
End PropOmegaCpo.

Section PointwiseOmegaCpo.
  Import SPropNotations.
  Context A `{ωCpo A} (X:Type).

  Program Definition exp_oT : ordType := dpair _ (X --> A) ⦑pointwise_srelation X (@extract_ord A)⦒.
  Next Obligation. typeclasses eauto. Qed.

  Program Definition eval (x:X) : OrdCat⦅exp_oT;A⦆ := ⦑fun f => f x⦒.
  Next Obligation. cbv ; intuition. Qed.

  Global Program Instance exp_ωCpo : ωCpo exp_oT :=
    Build_ωCpo (fun=> @bot _ _) (fun c x => ωsup (apply_seq (eval x) c)) _ _ _.
  Next Obligation. move=> ? ; apply bot_smallest. Qed.
  Next Obligation.
    move=> ?.
    match goal with | [|- ?l ≤ ωsup ?r] => change l with (r n) end.
    apply: ωsup_ub.
  Qed.
  Next Obligation.
    move=> ?; apply: ωsup_lub=> ?; apply: H0.
  Qed.

End PointwiseOmegaCpo.

Section AsPredTransformer.
  Import SPropNotations.
  Notation "X ⇥ A" := (exp_oT A X) (at level 99, right associativity).

  Definition WSt_dom S A := A ⇥ S ⇥ prop_op_oT.
  Definition WSt_cod S := S ⇥ prop_op_oT.
  Program Definition as_pred_trans {S A} (w:dfst (WSt S A))
    : OrdCat⦅WSt_dom S A; WSt_cod S⦆ :=
    ⦑w∙1⦒.
  Next Obligation. move=> ? ? H ?; apply: w∙2; apply: H. Qed.

  Definition WSt_ωcont {S A} (w:dfst (WSt S A)) :=
    ωcontinuous (as_pred_trans w).
End AsPredTransformer.


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



  Import SPropNotations.

  Let one : Type := unit.
  Let bool : Type := bool.

  Definition do_while (body : Imp bool) : Imp unit := ImpDoWhile body (ImpRet tt).

  Definition Wun := STCont (S × S).
  Definition W' := ordmonad_to_relmon Wun.

  Eval cbv in (Wun bool).
  (* Notation "x ≊ y" := (x ≤ y s/\ y ≤ x) (at level 70). *)

  Definition W0 := STCont S.
  Definition W0' := ordmonad_to_relmon W0.

  (* Program Definition tarksi_fix' {A} (f : dfst (W0' A) --> W0' A) : dfst (W0' A) := *)
  (*   ⦑fun post s0 => exists w, f w ≤ w s/\ w∙1 post s0⦒. *)
  (* Next Obligation. *)
  (*   move=> ? ? H ? [w0 [? H']]; exists w0; split=> //; move: H'; apply: (w0∙2)=> //. *)
  (* Qed. *)

  Program Definition Wgetun {A} (k : S -> W0 A) : W0 A :=
    ⦑fun post s => (k s)∙1 post s⦒.
  Next Obligation. move=> ? ? H ?; apply: (k _)∙2=> ? ? ; apply:H. Qed.

  Program Definition Wsetun {A} (s:S) (k : W0 A) : W0 A :=
    ⦑fun post _ => k∙1 post s⦒.
  Next Obligation. move=> ? ? H ?; apply: k∙2=> ? ? ; apply:H. Qed.

  Definition loop {W:Monad} (w0 : W bool) (wcont : W unit) : W unit :=
    bind w0 (fun b => if b then wcont else ret tt).

  Program Fixpoint θun (A : Type) (c: Imp A) {struct c} : W0 A :=
      match c with
      | ImpRet a => ret a
      | ImpGet k => Wgetun (fun s => θun (k s))
      | ImpSet s k => Wsetun s (θun k)
      | ImpDoWhile body k =>
        bind (kleene_ufix (loop (θun body))) (fun=> θun k)
      end.


  Program Definition injWStL {S1 S2}
    : MonadMorphism (STCont S1) (STCont (S1 × S2)) :=
    @mkMorphism _ _
               (fun A w => ⦑fun post s12 => w∙1 (fun a s1' => post a ⟨s1', nsnd s12⟩) (nfst s12)⦒)
               _ _.
  Next Obligation.
    move=> ? ? H [? ?]; apply: w∙2=> ? ? ; apply: H.
  Qed.

  Program Definition injWStR {S1 S2}
    : MonadMorphism (STCont S2) (STCont (S1 × S2)) :=
    @mkMorphism _ _
               (fun A w => ⦑fun post s12 => w∙1 (fun a s2' => post a ⟨nfst s12, s2'⟩) (nsnd s12)⦒)
               _ _.
  Next Obligation.
    move=> ? ? H [? ?]; apply: w∙2=> ? ? ; apply: H.
  Qed.

  (** Lemmas about omega-continuity of various elements in Wun/W' *)

  Definition preserves_omega_cont {S1 S2 A B} (f:dfst (WSt S1 A) --> WSt S2 B) :=
    forall w, WSt_ωcont w ->  WSt_ωcont (f w).


  Lemma retW_omega_cont {S0 A} (a:A) : WSt_ωcont (@retW (WSt S0) _ a).
  Proof. cbv; intuition. Qed.

  Lemma bindW_omega_cont {S0 A B} (w: dfst (WSt S0 A)) (f : A --> WSt S0 B):
    WSt_ωcont w -> (forall (a:A), WSt_ωcont (f a)) -> WSt_ωcont (w |= to_discr f).
  Proof.
    move=> Hw Hf c /=.
    unshelve epose (cw := ⦑fun n a => (f a)∙1 (c n)⦒:ωchain (WSt_dom S0 A)).
    move=> ? ?; apply: (f _)∙2=> ?; apply: c∙2.
    move: (Hw cw)=> /= <-; f_equal; extensionality a=> /=; apply: (Hf a c).
  Qed.

  Lemma iter_omega_cont {S0 A} (f:OrdCat⦅WSt S0 A; WSt S0 A⦆)
        (Hf : preserves_omega_cont f∙1) : forall n, WSt_ωcont (iter_chain f n).
  Proof.
    elim=> [/= _|n IH] /=; last apply: Hf=> //.
    extensionality u; apply SPropAxioms.sprop_ext; dintuition constructor.
  Qed.

  Lemma kleene_fix_omega_cont {S0 A} (f:OrdCat⦅WSt S0 A; WSt S0 A⦆)
        (Hf : preserves_omega_cont f∙1) : WSt_ωcont (kleene_fix f).
  Proof.
    move=> c. unfold kleene_fix. extensionality s=> /=.
    apply SPropAxioms.sprop_ext; do 2 split; move=> H0 n.
    move=> n0; move: (iter_omega_cont f Hf n0 c) (H0 n0)=>/= -> //.
    move: (iter_omega_cont f Hf n c)=> /= -> ?; apply: H0.
  Qed.

  Program Definition loop' {S0} (W:= WSt S0) (w0:dfst (W bool))
    : OrdCat⦅W unit;W unit⦆ := ⦑loop w0⦒.
  Next Obligation. move=> ? ?  H ? ?; apply: w0∙2=> -[] //; sreflexivity. Qed.

  Lemma loop_preserves_omega_cont {S0} (w0: dfst (WSt S0 _))
        (Hw0 : WSt_ωcont w0): preserves_omega_cont (loop' w0)∙1.
  Proof. move=> w Hwcont c /=; apply: bindW_omega_cont=> // -[] //. Qed.

  Lemma loop_omega_continuous {S0} (w0:dfst (WSt S0 bool)) (Hw0 : WSt_ωcont w0)
        (loop := loop' w0) : ωcontinuous loop.
  Proof.
    move=> c; apply: antisym_WSt;
      last (apply ωsup_lub=> n; apply: loop∙2; apply: ωsup_ub).
    move=> p s /=.
    match goal with
    | [|- SProp_op_order _ (forall n, _ (@?c n) _)] =>
      unshelve epose (cw0 := ⦑c⦒ : ωchain (WSt_dom S0 bool))
    end.
    move=> ? [] ? //; apply: c∙2.
    move: (Hw0 cw0)=> /= /(f_equal (fun f=> f s)) <-.
    apply: w0∙2=> -[] ? //; apply; constructor.
  Qed.


  Lemma θun_omega_cont : forall (A:Type) (c:Imp A), WSt_ωcont (θun c).
  Proof.
    refine (fix IH A c {struct c} := _).
    case: c=> [a|k|s k|body k].
    - apply: retW_omega_cont.
    - hnf=> ?; extensionality s; simpl; rewrite IH=> //.
    - hnf=> ?; extensionality s'; simpl; rewrite IH=> //.
    - apply: bindW_omega_cont; rewrite -/θun.
      change (loop ?f) with ((loop' f)∙1).
      rewrite -kleene_fix_ufix_eq.
      unshelve apply: kleene_fix_omega_cont.
      unshelve apply: loop_preserves_omega_cont.
      apply: (IH bool body).
      move=> [] ; apply IH.
  Qed.

  Lemma injWStL_preserves_omega_cont {S1 S2 A} :
    preserves_omega_cont (@injWStL S1 S2 A).
  Proof.
    move=> w Hw c /=; extensionality s; destruct s as [s1 s2]=> /=.
    match goal with
    | [|- _ = (forall n, _ (@?c n) _)] =>
      unshelve epose (cw := ⦑c⦒ : ωchain (WSt_dom _ _))
    end.
    move=> ? ? ?; apply: c∙2.
    move: (Hw cw) => /= -> //.
  Qed.

  Lemma injWStR_preserves_omega_cont {S1 S2 A} :
    preserves_omega_cont (@injWStR S1 S2 A).
  Proof.
    move=> w Hw c /=; extensionality s; destruct s as [s1 s2]=> /=.
    match goal with
    | [|- _ = (forall n, _ (@?c n) _)] =>
      unshelve epose (cw := ⦑c⦒ : ωchain (WSt_dom _ _))
    end.
    move=> ? ? ?; apply: c∙2.
    move: (Hw cw) => /= -> //.
  Qed.

  Let M1 := Imp_monad.
  Let M2 := Imp_monad.


  Lemma bind_sup {S0 A B} (c:ωchain (WSt S0 A)) (f: A --> WSt S0 B) :
        bind (ωsup c) f = ωsup (apply_seq (ord_relmon_bind _ (to_discr f)) c).
  Proof. done. Qed.

  Lemma bind_sup' {S0 A B} (c:ωchain (WSt S0 A))  :
        bind (ωsup c) = fun(f: A --> WSt S0 B)=> ωsup (apply_seq (ord_relmon_bind _ (to_discr f)) c).
  Proof. extensionality f; done. Qed.

  Program Definition bind_chain {S0 A B}
          (w: dfst (WSt S0 A)) (c: A -> ωchain (WSt S0 B))
    : ωchain (WSt S0 B) :=
    ⦑fun n => bind w (fun x => c x n)⦒.
  Next Obligation. cbv; move=> ? ?; apply: w∙2=> ? ?; apply: (c _)∙2. Qed.

  Lemma bind_cont_sup {S0 A B}
        (w: dfst (WSt S0 A))
        (Hwcont : WSt_ωcont w)
        (c: A -> ωchain (WSt S0 B)) :
    bind w (@ωsup _ _ \o c) = ωsup (bind_chain w c).
  Proof.
    cbv. apply sig_eq; extensionality k; extensionality s=> /=.
    unshelve epose (cw := ⦑fun n a => ((c a) ∙1 n) ∙1 k⦒ : ωchain (WSt_dom S0 A)).
    move=> ? ?; apply: (c _)∙2.
    move: (Hwcont cw)=> /= -> //.
  Qed.

  Lemma commute_kleene_fix {S0 A B}
        (f: OrdCat⦅WSt S0 A; WSt S0 A⦆)
        (w:dfst (WSt S0 B)) (Hwcont : WSt_ωcont w) :
    commute (@botWSt _ A) w -> (forall w', commute w' w -> commute (f∙1 w') w) ->
      commute (kleene_fix f) w.
  Proof.
    move=> Hbot Hind; unfold commute, kleene_fix.
    rewrite bind_sup'.
    rewrite bind_cont_sup=> //.
    f_equal; apply sig_eq; extensionality n.
    elim: n=> [|n IH]; [apply Hbot| apply Hind; apply IH].
  Qed.

  Lemma botWSt_omega_cont {S0 A} : WSt_ωcont (@botWSt S0 A).
  Proof.
    cbv=> ?; extensionality x.
    rewrite (@SPropAxioms.sprop_ext _ _).
    dintuition.
  Qed.

  Ltac myext0 k s :=
    cbv -[θun iter_chain loop]=> /=; apply sig_eq; extensionality k; extensionality s.

  Fixpoint commute_bot {A B: Type} (c:Imp A) {struct c} :
    commute (θun c) (@botWSt _ B).
  Proof.
    case: c=> [a|k|s k|body k].
    - cbv; intuition.
    - myext0 k' s=> /=.
      epose (f_equal (fun f => f∙1 k' _) (commute_bot _ B (k s))) as H0 ;
        simpl in H0 ; apply H0.
    - myext0 k' s'=> /=.
      epose (f_equal (fun f => f∙1 k' _) (commute_bot _ B k)) as H0 ;
        simpl in H0 ; apply H0.
    - simpl; apply: commute_bind; last move=> ? //.
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      apply: commute_kleene_fix=> //.
      apply botWSt_omega_cont.
      move=> w' Hw'; unfold loop', loop.
      apply: commute_bind=> // -[] //.
  Qed.

  Notation θunL := (fun c => injWStL _ (θun c)).
  Notation θunR := (fun c => injWStR _ (θun c)).



  Lemma ttt (f g: nat -> SProp) (H: forall n, f n = g n) :(forall n, f n) = (forall n, g n).
  Proof.
    apply SPropAxioms.sprop_ext; do 2 split; move=> H' n; move: (H n) (H' n)=> -> //.
  Qed.

  Lemma injWStR_kleene_fix {S1 S2} (w:dfst (WSt S2 bool)) :
    @injWStR S1 S2 unit (kleene_fix (loop' w)) = kleene_fix (loop' (injWStR bool w)).
  Proof.
    myext0 k s=> /=. apply: ttt=> n.
    destruct s as [s1 s2].
    elim: n s2 => [|n IHn] s2 //=.
    f_equal. extensionality b; case: b=> //=.
    extensionality s2'.
    apply IHn.
  Qed.

  Lemma injWStL_kleene_fix {S1 S2} (w:dfst (WSt S1 bool)) :
    @injWStL S1 S2 unit (kleene_fix (loop' w)) = kleene_fix (loop' (injWStL bool w)).
  Proof.
    myext0 k s=> /=. apply: ttt=> n.
    destruct s as [s1 s2].
    elim: n s1 => [|n IHn] s1 //=.
    f_equal. extensionality b; case: b=> //=.
    extensionality s1'.
    apply IHn.
  Qed.

  Lemma injWStL_bot {S1 S2 A} : injWStL A (botWSt S1) = botWSt (S1 × S2).
  Proof. done. Qed.

  Lemma injWStR_bot {S1 S2 A} : injWStR A (botWSt S2) = botWSt (S1 × S2).
  Proof. done. Qed.

  Lemma commute_morphism {M M':Monad} (θ:MonadMorphism M M') {A1 A2}:
    forall (c1: M A1) (c2: M A2), commute c1 c2 -> commute (θ _ c1) (θ _ c2).
  Proof.
    move=> c1 c2 /(f_equal (θ _)).
    rewrite !mon_morph_bind.
    unfold commute.
    set f1 := fun a1 => _; set f2 := fun a2 => _;
      set f1' := fun a1 => _; set f2' := fun a2 => _.
    enough (f1 = f1' /\ f2 = f2') as [-> ->]; first done.
    split; extensionality a; unfold f1, f1', f2, f2';
    rewrite mon_morph_bind; f_equal; extensionality b; apply: mon_morph_ret.
  Qed.

  (* Ltac mymatch' thm k := *)
  (*   match goal with *)
  (*   | [|- (θun ?c1)∙1 _ _ = (θun ?c2)∙1 _ _] => *)
  (*     let H0 := fresh "H" in *)
  (*     epose (f_equal (fun f => f∙1 k ⟨_,_⟩) (thm _ c2 _ c1)) as H0; simpl in H0; apply: H0 *)
  (*   end. *)

  (* Local Ltac mytac' thm := *)
  (*   let k := fresh "k" in myext k ; mymatch' thm k. *)


  (* Does not derive the signatures, see issues #246, #249 on Equations bug tracker *)
  (* Derive Signature for Imp. *)


  Inductive size_tree : Type :=
  | STBase
  | STBound : (S -> size_tree) -> size_tree
  | STUnary : size_tree -> size_tree
  | STBin : size_tree -> size_tree -> size_tree.

  Derive NoConfusion for size_tree.
  Derive NoConfusionHom for size_tree.
  Derive Subterm for size_tree.
  Next Obligation.
    move=> a ; apply Transitive_Closure.Acc_clos_trans.
    elim: a=> [|k IH|k IH|k1 IH1 k2 IH2];
               constructor=> ? x ;dependent elimination x=> //.
  Qed.


  Fixpoint sizeImp {A:Type} (c:Imp A) {struct c} : size_tree :=
    match c with
    | ImpRet _ => STBase
    | ImpGet k => STBound (fun s=> sizeImp (k s))
    | ImpSet _ k => STUnary (sizeImp k)
    | ImpDoWhile body k => STBin (sizeImp body) (sizeImp k)
    end.


  (* Problem of universe poly morphism in the section *)
   (* Program Fixpoint test {A} (c:Imp A) {measure (sizeImp c) size_tree_subterm} : nat := *)
   (*  match c with *)
   (*  | ImpRet _ => 1 *)
   (*  | ImpGet k => let f s := test (k s) in 2 *)
   (*  | ImpSet _ k => test k *)
   (*  | ImpDoWhile body k => test body + test k *)
   (*  end. *)

  (* Definition test {A} (c:Imp A) : nat. *)
  (* Proof. *)
  (*   move: {1}(sizeImp _) (erefl : sizeImp c = sizeImp c)=> z. *)
  (*   elim: z  A c=> [|? IH|? IH|? IH1 ? IH2] A [a|k|s k|body k] *)
  (*     ; first exact (fun => 1);  (discriminate + move=> /= [Heq]). *)
  (*   set f := fun s => IH s _ (k s) (f_equal (fun f => f s) Heq). *)
  (*   exact 2. *)
  (*   exact (IH _ k Heq). *)
  (*   move=> Heq' ; exact (IH1 _ body Heq + IH2 _ k Heq'). *)
  (* Defined. *)

  (* From Equations.Prop Require Import Tactics. *)

  Obligation Tactic := Tactics.equations_simpl.

   Equations? test {A} (c:Imp A): nat by wf (sizeImp c) size_tree_subterm :=
     test (ImpRet _) := 1;
     test (ImpGet k) := let f s := test (k s) in 2;
     test (ImpSet k) := test k;
     test (ImpDoWhile body k) := test body + test k.
   Proof.
    constructor; apply: size_tree_direct_subterm_1_1.
   Defined.


   Obligation Tactic := idtac.

  Ltac mymatch thm k :=
    match goal with
    | [|- (θun ?c1)∙1 _ _ = (θun ?c2)∙1 _ _] =>
      let H0 := fresh "H" in
      epose (f_equal (fun f => f∙1 k ⟨_,_⟩) (thm _ _ c1 c2 _)) as H0; simpl in H0; apply: H0
    end.

  Ltac myext k :=
    let s12 := fresh "s12" in
    let s1' := fresh "s1" in
    let s2' := fresh "s2" in
    myext0 k s12; destruct s12 as [s1' s2']=> /=.


  Local Ltac mytac thm :=
    let k := fresh "k" in myext k ; mymatch thm k.

  Obligation Tactic := idtac.
  Equations? commutation_lemma {A1 A2 : Type} (c1 : M1 A1) (c2: M2 A2) :
    commute (θunL c1) (θunR c2) by wf (sizeImp c1, sizeImp c2)
                                      (Subterm.lexprod _ _ size_tree_subterm
                                                      size_tree_subterm) :=
    commutation_lemma c1 c2 := _.
  Proof.
  case: c1 c2 commutation_lemma=> [a1|k1|s1 k1|body1 k1] [a2|k2|s2 k2|body2 k2] commutation_lemma ; try (cbv; reflexivity).
    all: try (mytac commutation_lemma).
    - set c1 := θun _; rewrite /θun-/θun /c1 {c1}.
      apply: commute_sym; rewrite mon_morph_bind.
      apply: commute_bind; last (move=> ?; apply: commute_sym; apply: commutation_lemma ; right; do 2 constructor).
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      rewrite injWStR_kleene_fix; apply: commute_kleene_fix.
      + apply injWStL_preserves_omega_cont, θun_omega_cont.
      + rewrite -injWStL_bot; apply commute_morphism, commute_sym, commute_bot.
      + move=> w' Hw'; unfold loop', loop.
        apply commute_bind; last by move=> [].
        apply: commute_sym; apply: commutation_lemma; right; do 2 constructor.
    - set c1 := θun _; rewrite /θun-/θun /c1 {c1}.
      apply: commute_sym; rewrite mon_morph_bind.
      apply: commute_bind; last (move=> ?; apply: commute_sym; apply: commutation_lemma ; right; do 2 constructor).
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      rewrite injWStR_kleene_fix; apply: commute_kleene_fix.
      + apply injWStL_preserves_omega_cont, θun_omega_cont.
      + rewrite -injWStL_bot; apply commute_morphism, commute_sym, commute_bot.
      + move=> w' Hw'; unfold loop', loop.
        apply commute_bind; last by move=> [].
        apply: commute_sym; apply: commutation_lemma; right; do 2 constructor.
    - set c1 := (c in injWStR _ c) ; rewrite /θun-/θun /c1 {c1}.
      rewrite mon_morph_bind.
      apply: commute_bind; last (move=> ?; apply: commutation_lemma; left; do 2 constructor).
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      rewrite injWStL_kleene_fix; apply: commute_kleene_fix.
      + apply injWStR_preserves_omega_cont, θun_omega_cont.
      + rewrite -injWStR_bot; apply commute_morphism, commute_sym, commute_bot.
      + move=> w' Hw'; unfold loop', loop; apply commute_bind; last by move=> [].
        apply: commutation_lemma; left; do 2 constructor.
    - set c1 := (c in injWStR _ c) ; rewrite /θun-/θun /c1 {c1}.
      rewrite mon_morph_bind.
      apply: commute_bind; last (move=> ?; apply: commutation_lemma; left; do 2 constructor).
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      rewrite injWStL_kleene_fix; apply: commute_kleene_fix.
      + apply injWStR_preserves_omega_cont, θun_omega_cont.
      + rewrite -injWStR_bot; apply commute_morphism, commute_sym, commute_bot.
      + move=> w' Hw'; unfold loop', loop; apply commute_bind; last by move=> [].
        apply: commutation_lemma; left; do 2 constructor.
    - set c1 := (c in injWStR _ c) ; rewrite /θun-/θun /c1 {c1}.
      rewrite mon_morph_bind.
      apply: commute_bind; last (move=> ?; apply: commutation_lemma; left; do 2 constructor).
      change (loop ?f) with ((loop' f)∙1); rewrite -kleene_fix_ufix_eq.
      rewrite injWStL_kleene_fix; apply: commute_kleene_fix.
      + apply injWStR_preserves_omega_cont, θun_omega_cont.
      + rewrite -injWStR_bot; apply commute_morphism, commute_sym, commute_bot.
      + move=> w' Hw'; unfold loop', loop; apply commute_bind; last by move=> [].
        apply: commutation_lemma; left; do 2 constructor.
    Unshelve. all: repeat constructor; apply: size_tree_direct_subterm_1_1.
  Qed.

  Obligation Tactic := Tactics.equations_simpl.

  Program Definition θun_mm : MonadMorphism Imp_monad W0 :=
    @mkMorphism Imp_monad _ θun _ _.
  Next Obligation. do 2 constructor. Qed.
  Next Obligation.
    move: m.
    refine (fix IH (m:Imp A) {struct m} := _).
    case: m=> [a|k|s k|body k] /=;
      unfold MonoCont_bind ; apply sig_eq; extensionality k'=> /=; extensionality s0; rewrite ?IH; try reflexivity.
  Qed.

  Definition θunL_mm : MonadMorphism Imp_monad Wun :=
    comp_monad_morphism θun_mm injWStL.
  Definition θunR_mm : MonadMorphism Imp_monad Wun :=
    comp_monad_morphism θun_mm injWStR.

  Program Definition θPart := commute_effObs Wun M1 M2 θunL_mm θunR_mm _.
  Next Obligation.
    apply: commutation_lemma.
  Qed.

  Notation "⊨ c1 ≈ c2 [{ w }]" := (semantic_judgement _ _ _ θPart _ _ c1 c2 w).

  (* Translation from pre-/postconditions to backward predicate transformers *)
  Program Definition fromPrePost {A1 A2}
          (pre : S -> S -> SProp)
          (post : A1 -> S -> S -> A2 -> S -> S -> SProp)
    : dfst (Wrel Wun ⟨A1,A2⟩) :=
    ⦑fun p s0 => pre (nfst s0) (nsnd s0) s/\
                 forall a1 a2 s, post a1 (nfst s0) (nfst s) a2 (nsnd s0) (nsnd s)
                            -> p ⟨a1,a2⟩ s⦒.
  Next Obligation. cbv ; intuition. Qed.

  Lemma do_while_rule (inv : bool -> bool -> S -> S -> SProp)
        (body1 body2 : Imp bool) :
        ⊨ body1 ≈ body2 [{ fromPrePost (inv true true) (fun b1 _ s1 b2 _ s2 => b1 = b2 s/\ inv b1 b2 s1 s2) }] ->
        ⊨ do_while body1 ≈ do_while body2 [{ fromPrePost (inv true true) (fun 'tt _ s1 'tt _ s2 => inv false false s1 s2) }].
  Proof.
    admit.
  Admitted.



End ImpMonad.
