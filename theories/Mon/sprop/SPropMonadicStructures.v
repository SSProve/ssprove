From Coq Require Import ssreflect ssrfun FunctionalExtensionality.
From Mon Require Export Base.
From Mon Require Import sprop.SPropBase.
From Coq Require Import Relation_Definitions Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

(***************************************************************)
(* Preorder srelations                                         *)
(***************************************************************)


Definition SProp_order : relation Prop := s_impl.
Instance SProp_order_preorder : PreOrder SProp_order.
Proof. constructor ; cbv ; intuition. Qed.

Definition SProp_op_order : relation Prop := Basics.flip s_impl.
Instance SProp_op_order_preorder : PreOrder SProp_op_order.
Proof. unfold SProp_op_order. typeclasses eauto. Qed.

Instance pointwise_preorder A {B} (R:relation B) `{PreOrder _ R} :
  PreOrder (pointwise_relation A R).
Proof. constructor ; cbv ; intuition ; transitivity (y a) ; auto. Qed.

Definition Pred_op_order A : relation (A -> Prop) :=
  pointwise_relation A SProp_op_order.
Instance Pred_op_order_prorder A : PreOrder (@Pred_op_order A).
Proof. unfold Pred_op_order ; typeclasses eauto. Qed.

(***************************************************************)
(* Monads, in Kleisli triple form                              *)
(***************************************************************)

Record Monad : Type :=
  mkMonad
    { monad_tyop :> Type -> Type
    ; monad_ret  : forall A, A -> monad_tyop A
    ; monad_bind : forall A B,
        monad_tyop A -> (A -> monad_tyop B) -> monad_tyop B
    ; monad_law1 : forall A B a (f : A -> monad_tyop B),
        monad_bind (monad_ret a) f = f a
    ; monad_law2 : forall A c, monad_bind c (@monad_ret A) = c
    ; monad_law3 : forall A B C c (f : A -> monad_tyop B) (g : B -> monad_tyop C),
        monad_bind (monad_bind c f) g
        = monad_bind c (fun a => monad_bind (f a) g)
    }.

Definition ret {M : Monad} {A} := @monad_ret M A.
Definition bind {M : Monad} {A} {B} := @monad_bind M A B.
Definition map {M:Monad} {A B} (f : A -> B) (m : M A) : M B :=
  bind m (fun x => ret (f x)).
Notation "f <$> m" := (@map _ _ _ f m) (at level 60).
Ltac intro_map :=
  change (bind ?a (fun x => ret (?f x))) with (f <$> a).

Section StrongBind.
  Context {M:Monad}.
  Context {Γ A B} (m : Γ -> M A) (f : Γ × A -> M B).

  Definition bindStr (γ : Γ) : M B :=
    bind (m γ) (fun a => f ⟨γ,a⟩).
End StrongBind.

Section MapLemmas.
  Context (M : Monad).
  Import FunctionalExtensionality.
  Lemma map_id : forall A (m : M A), id <$> m = m.
  Proof. intros ; rewrite /map /id /= /bind monad_law2 //. Qed.
    
  Lemma map_functorial : forall A B C (f : A -> B) (g : B -> C) (m : M A),
      g <$> (f <$> m) = (fun x => g (f x)) <$> m.
  Proof.
    intros ; cbv. rewrite monad_law3. f_equal. extensionality a.
    rewrite monad_law1. reflexivity.
  Qed.

  Lemma map_bind : forall A B C (f : B -> C) (m:M A) g,
      (f <$> bind m g = bind m (fun x => f <$> (g x))).
  Proof.
    intros ; cbv. rewrite monad_law3. reflexivity.
  Qed.
  Lemma bind_map : forall A B C (f : A -> B) (m:M A) (g : B -> M C),
      bind (f <$> m) g = bind m (fun x => g (f x)).
  Proof.
    intros ; cbv. rewrite monad_law3.
    f_equal ; extensionality a. rewrite monad_law1.
    reflexivity.
  Qed.
End MapLemmas.


(***************************************************************)
(* Ordered Monads, where the bind respects the order           *)
(***************************************************************)

Record OrderedMonad : Type :=
  mkOrderedMonad
    { omon_monad :> Monad
      ; omon_rel : forall A, relation (omon_monad A)
      ; omon_order : forall A, PreOrder (@omon_rel A)
      ; omon_bind  : forall A B,
          Proper (@omon_rel A ==> pointwise_relation A (@omon_rel B) ==> @omon_rel B) bind
    }.

Existing Instance omon_order.
Notation "x ≤[ M ] y" := (@omon_rel M _ x y) (at level 70).
Notation "x ≤ y" := (@omon_rel _ _ x y) (at level 70).

Section DiscreteMonad.
  Import SPropNotations.
  Program Definition DiscreteMonad (M:Monad) : OrderedMonad :=
    @mkOrderedMonad M (fun A x y => x = y) _ _.
  Next Obligation.
    constructor. by cbv.
    cbv. move=> *. etransitivity ; by eassumption.
  Qed.
  Next Obligation.
    compute. move=> x y Exy x0 y0 pe_x0y0.
    rewrite Exy. apply FunctionalExtensionality in pe_x0y0.
    rewrite pe_x0y0. reflexivity.
  Qed.
End DiscreteMonad.

(***************************************************************)
(* Monad algebras, and algebras on ordered monads              *)
(***************************************************************)
Record MonadAlgebra (M : Monad) : Type :=
  mkMonadAlgebra
    { malg_carrier : Type
    ; malg_map     :> M malg_carrier -> malg_carrier
    ; malg_ret     : forall c, malg_map (ret c) = c
    ; malg_bind    : forall X (m : M X) f,
        malg_map (bind m (fun x => ret (malg_map (f x)))) = malg_map (bind m f)
    }.

Record OrderedAlgebra (M : Monad) : Type :=
  mkOrderedAlgebra
    { oalg_alg     :> MonadAlgebra M
    ; oalg_rel     : relation (malg_carrier oalg_alg)
    ; oalg_order   : PreOrder oalg_rel
    ; oalg_mono    : forall A, Proper
                            (pointwise_relation A oalg_rel ==> pointwise_relation (M A) oalg_rel)
                            (fun k m => oalg_alg (map k m))}.

Section OrderedMonadAlgebra.
  Context (OM : OrderedMonad).

  Record OrderedMonadAlgebra : Type :=
    mkOrderedMonadAlgebra
      { omalg_alg     :> MonadAlgebra OM
      ; omalg_rel     : relation (malg_carrier omalg_alg)
      ; omalg_order   : PreOrder omalg_rel
      ; omalg_mono    : forall A, Proper
                              (pointwise_relation A omalg_rel ==> (@omon_rel OM A) ==> omalg_rel)
                              (fun k m => omalg_alg (map k m))}.

End OrderedMonadAlgebra.

Section AssertAssumeStructure.
  Context A (rel : relation A) `{PreOrder _ rel}.

  Notation "x ≤ y" := (rel x y).
  Import SPropNotations.
  Class aa :=
    mkAa
      { assert_p : Prop -> A -> A
      ; assume_p : Prop -> A -> A
      ; aa_assert_stronger : forall p x, assert_p p x ≤ x
      ; aa_assume_weaker : forall p x, x ≤ assume_p p x
      ; aa_assert_assume_adjoint : forall p x1 x2,
          assert_p p x1 ≤ x2 s<-> x1 ≤ assume_p p x2
      }.

End AssertAssumeStructure.

(**************************************************************************)
(* Left/Right kan extensions in the Kleisli category of an ordered monad  *)
(**************************************************************************)

Section KleisliKanExtension.
  Context (W:OrderedMonad) (B C : Type) (f : W C) (p : W B).
  Import SPropNotations.

  (* Right Kan extension of f along p *)
  Definition ran :=
    { ext : B -> W C |
      bind p ext  ≤[W] f s/\
      forall (w' : B -> W C), bind p w' ≤[W] f -> forall b, w' b ≤[W] ext b
    }.

  Definition lan :=
    { ext : B -> W C |
      f ≤ bind p ext s/\
      forall (w' : B -> W C), f ≤ bind p w' -> forall b, w' b ≤ ext b
    }.

End KleisliKanExtension.

Section KanExtensionMonotonic.
  Context (W:OrderedMonad) (B C : Type).
  Context (f : W C) (p : W B) (Hran:ran f p).
  Context (f':W C) (p':W B) (Hran':ran f' p').
  Context (Hf : f ≤ f') (Hp : p' ≤ p).
  Definition ran_mono : forall b, proj1_sig Hran b ≤ proj1_sig Hran' b.
  Proof.
    move:Hran Hran' => [w [H1 H2]] [w' [H1' H2']] b /=.
    apply H2'. transitivity f ; [|assumption].
    transitivity (bind p w).
    apply omon_bind ; [assumption|reflexivity].
    assumption.
  Qed.
End KanExtensionMonotonic.

Section KanExtensionIsoStable.
  Context (W:OrderedMonad) (B C : Type) (f : W C) (p : W B).
  Import SPropNotations.
  Notation "w ≅ w'" := (w ≤ w' s/\ w' ≤ w) (at level 65).
  Context (Hran:ran f p) (f':W C) (p':W B) (Hf : f ≅ f') (Hp : p ≅ p').
  Program Definition ran_iso : ran f' p' := exist _ (proj1_sig Hran) _.
  Next Obligation.
    destruct Hf as [Hf1 Hf2] ; destruct Hp as [Hp1 Hp2] ; destruct (proj2_sig Hran) as [Hran1 Hran2].
    split.
    transitivity (bind p (proj1_sig Hran)).
    apply omon_bind. assumption.  move=> //= ?. reflexivity.
    transitivity f ; assumption.
    move=> w' Hw'. apply Hran2.
    transitivity (bind p' w'). apply omon_bind. assumption.
    move=> //= ? ; reflexivity.
    transitivity f' ; assumption.
  Qed.
End KanExtensionIsoStable.

(***************************************************************)
(* Monad morphisms                                             *)
(***************************************************************)

Record MonadMorphism (M W : Monad) : Type :=
  mkMorphism
    { mon_morph :> forall {A}, M A -> W A
    ; mon_morph_ret : forall A (a : A), mon_morph (ret a) = ret a
    ; mon_morph_bind : forall A B (m : M A) (f : A -> M B),
        mon_morph (bind m f) = bind (mon_morph m) (fun a => mon_morph (f a))
    }.

Program Definition identity_monad_morphism M : MonadMorphism M M :=
  @mkMorphism M M (fun A => id) _ _.

Program Definition comp_monad_morphism {M1 M2 M3}
  : MonadMorphism M1 M2 -> MonadMorphism M2 M3 -> MonadMorphism M1 M3
  := fun f12 f23 => @mkMorphism M1 M3 (fun A a => f23 A (f12 A a)) _ _.
Next Obligation. rewrite !mon_morph_ret //. Qed.
Next Obligation. rewrite !mon_morph_bind //. Qed.

Section MonadMorphismRefinement.
  Context {M : Monad} {W : OrderedMonad} (ϕ ψ : MonadMorphism M W).
  Definition monad_morph_refines :=
    forall A, pointwise_relation (M A) (@omon_rel W A) (ϕ A) (ψ A).
End MonadMorphismRefinement.

Instance mon_morph_refines_preorder M W : PreOrder (@monad_morph_refines M W). 
Proof.
  constructor ; cbv ; intuition. 
  transitivity (y A a) ; auto.
Qed.

Section MonadMorphismNatural.
  Context {M1 M2 : Monad} (θ : MonadMorphism M1 M2).
  Import FunctionalExtensionality.
  Lemma monad_morphism_natural : forall A B f m, f <$> (θ A m) = θ B (f <$> m).
  Proof.
    intros. cbv. rewrite mon_morph_bind. cbv ; f_equal.
    extensionality a. rewrite mon_morph_ret ; reflexivity.
  Qed.
End MonadMorphismNatural.

(***************************************************************)
(* Monotonic Monad morphisms                                   *)
(***************************************************************)

Record MonotonicMonadMorphism (M W : OrderedMonad) : Type :=
  mkMonMorphism
    { monmon_morph :> MonadMorphism M W
    ; monmon_monotonic : forall A,
          Proper (@omon_rel M A ==> @omon_rel W A) (monmon_morph A)
    }.

Program Definition identity_monmon M : MonotonicMonadMorphism M M :=
  @mkMonMorphism _ _ (identity_monad_morphism M) _.
Next Obligation. cbv ; intuition. Qed.

Program Definition comp_monmon {M1 M2 M3}
  : MonotonicMonadMorphism M1 M2 ->
    MonotonicMonadMorphism M2 M3 ->
    MonotonicMonadMorphism M1 M3
  := fun f12 f23 => @mkMonMorphism M1 M3 (comp_monad_morphism f12 f23) _.
Next Obligation.
  cbv ; intuition.
  do 2 apply monmon_monotonic => //.
Qed.

Program Definition from_discrete_monad_monotonic
           (M:Monad) (W:OrderedMonad) (θ : MonadMorphism M W)
  : MonotonicMonadMorphism (DiscreteMonad M) W
  := @mkMonMorphism _ _ θ _.

(* An ordered monad equipped with a morphism from M *)
Record OrderedMonadUnder (M:OrderedMonad) :=
  mkMonadUnder {
    mu_carrier :> OrderedMonad ;
    mu_lift : MonotonicMonadMorphism M mu_carrier
  }.

(***************************************************************)
(* Monad Relations                                             *)
(***************************************************************)

Record MonadRelation (M W : Monad) : Type :=
  mkMonadRelation
    { mrel      :> forall A, M A -> W A -> Prop
    ; mrel_ret  : forall A (a:A), mrel (ret a) (ret a)
    ; mrel_bind : forall A B m w (f : A -> M B)  g,
        mrel m w -> (forall a, mrel (f a) (g a)) -> mrel (bind m f) (bind w g)
    }.

Section MonadIdeal.
  Context (M : Monad) (W:OrderedMonad).
  Record MonadIdeal : Type :=
    mkMonadIdeal
      { mid_rel :> MonadRelation M W
      ; mid_upper_closed : forall A, Proper (pointwise_relation (M A) (@omon_rel W A ==> SProp_order)) (@mid_rel A)
      }.
End MonadIdeal.

Section MonadMorphismToIdeal.
  Context (M : Monad) (W:OrderedMonad) (θ : MonadMorphism M W).
  Program Definition relation_from_mmorph : MonadRelation M W :=
    @mkMonadRelation _ _ (fun A m w => θ A m ≤ w) _ _.
  Next Obligation. rewrite mon_morph_ret. reflexivity. Qed.
  Next Obligation.
    rewrite mon_morph_bind.
    apply omon_bind; [|move=> ?] ; auto.
  Qed.

  Program Definition ideal_from_mmorph : MonadIdeal M W :=
    @mkMonadIdeal _ _ relation_from_mmorph _.
  Next Obligation. cbv ; intuition ; etransitivity ; eassumption. Qed.
    
End MonadMorphismToIdeal.

(***************************************************************)
(* Monad Transformer                                           *)
(***************************************************************)

Record OrderedMonadTransformer :=
  mkOrderedMonadTransformer
    { mt_monad :> forall (M:OrderedMonad), OrderedMonadUnder M
    ; mt_map : forall (M1 M2:OrderedMonad),
        MonotonicMonadMorphism M1 M2 ->
        MonotonicMonadMorphism (mt_monad M1) (mt_monad M2)
    ; mt_map_id : forall M A m,
        mt_map (identity_monmon M) A m = identity_monmon _ A m
    ; mt_map_comp : forall (M1 M2 M3 : OrderedMonad)
                      (θ12 : MonotonicMonadMorphism M1 M2)
                      (θ23 : MonotonicMonadMorphism M2 M3) A m,
        mt_map θ23 _ (mt_map θ12 A m)  = mt_map (comp_monmon θ12 θ23) A m
    ; mt_natural_lift :
        forall (M1 M2 : OrderedMonad) (θ : MonotonicMonadMorphism M1 M2) A m,
          mt_map θ  _(mu_lift (mt_monad M1) A m) 
        = mu_lift (mt_monad M2) _ (θ A m)
    }.

(***************************************************************)
(* Dijkstra Monads over specification (i.e. ordered) monads    *)
(***************************************************************)

Import SPropNotations.
Record Dijkstra (W : OrderedMonad) : Type := mkDM
  { dm_tyop :> forall A, W A -> Type
  ; dm_ret  : forall A, forall (a : A), dm_tyop (ret a)
  ; dm_bind : forall A B (w : W A) (f : A -> W B)
                     (d : dm_tyop w) (g : forall a, dm_tyop (f a)),
      dm_tyop (bind w f)
  ; dm_wkn : forall {A} {w w' : W A}, dm_tyop w -> w ≤[W] w' -> dm_tyop w'
  ; dm_law1 : forall A B (a : A) (f : A -> W B) (g : forall a, dm_tyop (f a)),
      dm_bind (dm_ret a) g =⟨monad_law1 a f⟩ g a 
  ; dm_law2 : forall A c m ,
      dm_bind m (@dm_ret A) =⟨monad_law2 c⟩  m
  ; dm_law3 : forall A B C c f g (m : dm_tyop c)
                     (f' : forall (a : A), dm_tyop (f a))
                     (g' : forall (b : B), @dm_tyop C (g b)),
      dm_bind (dm_bind m f') g' =⟨monad_law3 c f g⟩
                                   dm_bind m (fun a => dm_bind(f' a) g')
  ; dm_law4 : forall A w (m:@dm_tyop A w), dm_wkn m (reflexivity _) = m
  ; dm_law5 : forall A w1 w2 w3 (m:@dm_tyop A w1) (H12 :w1 ≤ w2) (H23 :w2 ≤ w3),
      dm_wkn m (transitivity H12 H23) = dm_wkn (dm_wkn m H12) H23
  ; dm_law6 : forall A B wm wm' wf wf' (m:@dm_tyop A wm) (f : forall (a:A), @dm_tyop B (wf a)) (Hm : wm ≤ wm') (Hf : forall a, wf a ≤ wf' a),
       (dm_wkn (dm_bind m f) (omon_bind Hm Hf) = dm_bind (dm_wkn m Hm) (fun a => dm_wkn (f a) (Hf a)))
  }.

Definition dret {W} {D : Dijkstra W} {A} := @dm_ret W D A.
Definition dbind {W} {D : Dijkstra W} {A} {B} {w} {f} := @dm_bind W D A B w f.
Definition wkn {W} {D : Dijkstra W} {A} {w w'} := @dm_wkn W D A w w'.

(* Generic if-then-else for Dijkstra monads *)
Definition ifTE {A} {W} {D : Dijkstra W} {w1 w2 : W A} :
  forall (b: bool), D A w1 -> D A w2 -> D A (if b then w1 else w2) :=
  fun b tt ff =>
    match b as b return D A (if b then w1 else w2) with
    | true => tt
    | false => ff
    end.

Module DijkstraMonadNotations.
  Notation "x <- m1 ; m2" := (dbind m1 (fun x => m2)) (at level 80, right associativity).
  Notation "'ifDM' b 'then' c1 'else' c2 'end'" := (@ifTE _ _ _ _ _ b c1 c2).
End DijkstraMonadNotations.

(***********************************************************************)
(* Deriving Dijkstra Monads from Effect Observations / Monad morphisms *)
(***********************************************************************)
Section OfMorphism.
  Import SPropNotations.

  Variable M : Monad.
  Variable W : OrderedMonad.
  Variable θ : MonadMorphism M W.

  Definition Dθ_carrier A (w : W A) : Type :=
    { m : M A | θ A m ≤ w }.

  Program Definition Dθ_ret A (a : A): Dθ_carrier (ret a) :=
    exist _ (ret a) _.
  Next Obligation.
    rewrite mon_morph_ret ; reflexivity.
  Qed.

  Program Definition Dθ_bind A B (w : W A) (f : A -> W B)
          (d : Dθ_carrier w) (g : forall a, Dθ_carrier (f a)) :
    Dθ_carrier (bind w f) :=
    exist _ (bind (proj1_sig d) (fun a => proj1_sig ( g a))) _.
  Next Obligation.
    rewrite mon_morph_bind.
    apply (omon_bind (proj2_sig d) (fun a => proj2_sig (g a))).
  Qed.

  Program Definition Dθ_wkn A (w w' : W A) (d: Dθ_carrier w) (H : w ≤[W] w') : Dθ_carrier w' :=
    exist _ (proj1_sig d) _.
  Next Obligation.
    transitivity w. exact (proj2_sig d). assumption.
  Qed.

  Program Definition Dθ : Dijkstra W :=
    @mkDM W Dθ_carrier Dθ_ret Dθ_bind Dθ_wkn _ _ _ _ _ _.
  (* Anomaly when trying to factorize *)
  Next Obligation. apply eq_above_sig ; cbv ; by rewrite monad_law1. Qed.
  Next Obligation. apply eq_above_sig ; cbv ; by rewrite monad_law2. Qed.
  Next Obligation. apply eq_above_sig ; cbv ; by rewrite monad_law3. Qed.
(*in the remaining obligations one use proof_irrelevance, which implies
that equality of sigma types is equivalent to equality of carriers members*)
  Next Obligation. destruct m as (m,e). Print Dθ_wkn.
    compute. About exist.
    have hintUnif :
(Dθ_wkn_obligation_1
       (exist (fun m0 : M A => θ A m0 ≤ w) m e)
       ((let (PreOrder_Reflexive, _) := omon_order W A in
         PreOrder_Reflexive) w)) = e. apply ax_proof_irrel.
    rewrite hintUnif. reflexivity.
Qed.
  Next Obligation. compute.
  have hintUnif : 
(Dθ_wkn_obligation_1 m
       ((let (_, PreOrder_Transitive) := omon_order W A in
         PreOrder_Transitive) w1 w2 w3 H12 H23))
=
(Dθ_wkn_obligation_1
       (exist (fun m0 : M A => θ A m0 ≤ w2)
          (let (w, _) := m in w) (Dθ_wkn_obligation_1 m H12))
       H23). apply ax_proof_irrel. rewrite hintUnif. reflexivity.
Qed.
  Next Obligation. compute.
have hintUnif :
(Dθ_wkn_obligation_1
       (exist (fun m0 : M B => θ B m0 ≤ monad_bind wm wf)
          (monad_bind (let (w, _) := m in w)
             (fun a : A => let (w, _) := f a in w))
          (Dθ_bind_obligation_1 m f)) (omon_bind Hm Hf))
=
(Dθ_bind_obligation_1
       (exist (fun m0 : M A => θ A m0 ≤ wm')
          (let (w, _) := m in w) (Dθ_wkn_obligation_1 m Hm))
       (fun a : A =>
        exist (fun m0 : M B => θ B m0 ≤ wf' a)
          (let (w, _) := f a in w)
          (Dθ_wkn_obligation_1 (f a) (Hf a)))).
apply ax_proof_irrel. rewrite hintUnif. reflexivity.
Qed.

  Program Definition lift {A} (m : M A) : Dθ A (θ A m) := exist _ m _.
  Next Obligation. reflexivity. Qed.

End OfMorphism.

(*****************************************************************)
(* Deriving Dijkstra monads from Monadic Relations               *)
(*****************************************************************)

Section OfRelation.
  Context (M:Monad) (W:OrderedMonad) (R:MonadIdeal M W).
  Import SPropNotations.

  Definition Drel_carrier A (w : W A) :=
    { m : M A | R A m w }.


  Definition Drel_ret A (a : A): Drel_carrier (ret a) :=
    let initCand := (exist _ (@ret M A a) (mrel_ret R a)) in
    initCand.

  Program Definition Drel_bind A B (wm : W A) (wf : A -> W B)
          (m : Drel_carrier wm) (f : forall a, Drel_carrier (wf a)):
    Drel_carrier (bind wm wf) :=
    exist _ (bind (proj1_sig m) (fun a => proj1_sig (f a))) _.
  Next Obligation.
    apply mrel_bind ; [exact (proj2_sig m)| intros a ; apply (proj2_sig (f a))].
  Qed.

  Program Definition Drel_wkn A (w w' : W A) (m : Drel_carrier w) (Hww' : w ≤[W] w')
    : Drel_carrier w' :=
    exist _ (proj1_sig m) (mid_upper_closed Hww' (proj2_sig m)).

  Program Definition Drel : Dijkstra W :=
    @mkDM W Drel_carrier Drel_ret Drel_bind Drel_wkn _ _ _ _ _ _.
  Next Obligation. apply eq_above_sig ; cbv ; rewrite !monad_law1 //. Qed.
  Next Obligation. apply eq_above_sig ; cbv ; rewrite !monad_law2 //. Qed.
  Next Obligation. apply eq_above_sig ; cbv ; rewrite !monad_law3 //. Qed.
  Next Obligation. compute. destruct m as (m,bla). f_equal.
    apply ax_proof_irrel.
  Qed.
  Next Obligation. compute. f_equal. apply ax_proof_irrel. Qed.
  Next Obligation. compute. f_equal. apply ax_proof_irrel. Qed.
End OfRelation.
