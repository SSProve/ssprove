From Coq Require Import ssreflect ssrfun.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Monoid SpecificationMonads DijkstraMonadExamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Section ExtNat.
  Definition extNat := option nat.
  Import SPropNotations.
  Definition extNat_rel : srelation extNat :=
    fun en1 en2 =>
      match en1, en2 return SProp with
      | _, None => sUnit
      | None, Some _ => sEmpty
      | Some n1, Some n2 => n1 s<= n2
      end.
  Global Instance extNat_order : PreOrder extNat_rel.
  Proof.
    constructor ; cbv.
    move=> [?|] //= ; sreflexivity.
    move=> [?|] [?|] [?|] //= ? ?. estransitivity ; eassumption.
  Qed.
End ExtNat.

Section ExtNatSProp.
  Import SPropNotations.
  Definition extNat' := { p : nat -> SProp ≫ SProper (Sle s==> SProp_order) p }.
  Definition extNat'_rel : srelation extNat' :=
    fun n1 n2 => pointwise_srelation nat SProp_order (Spr1 n1) (Spr1 n2).

  Global Instance extNat'_order : PreOrder extNat'_rel.
  Proof. constructor ; cbv ; intuition. Qed.
End ExtNatSProp.

Section Cost.
  Definition CostSpec := @MonoCont extNat' extNat'_rel _.

  Import SPropNotations.

  Fixpoint monus (n m : nat) {struct n} : m s<= n -> nat :=
    match n with
    | 0 => match m with
          | 0 => fun=> 0
          | S _ => fun H => ltac:(enough sEmpty as [] ; inversion H)
          end
    | S n =>
      match m with
      | 0 => fun=> S n
      | S m => fun H => @monus n m ltac:(inversion H ; assumption)
      end
    end.

  Lemma monus_mon n3 : forall n2 n1 H12 (H23 : n2 s<= n3) H13,
      @monus n2 n1 H12 s<= @monus n3 n1 H13.
  Proof.
    induction n3.
    move=> [|?] [|?] //= H H' ; enough sEmpty as [] ;
            [inversion H | inversion H'].
    move=> [|?] [|?] //= H H'.
    enough sEmpty as []; inversion H.
    move=> H''; inversion H; inversion H'; inversion H''.
    apply IHn3; subst; assumption.
  Qed.

  Definition CostS := nat.
  Definition CostAr : CostS -> Type := fun _ => unit.
  Program Definition CostSpecs : forall (s:CostS), CostSpec (CostAr s) :=
    fun n => ⦑fun post => ⦑ fun n' => s∃ (H : Box (n s<= n')), Spr1 (post tt) (@monus n' n (unbox H)) ⦒ ⦒.
  Next Obligation.
    move: H0 => [[H'] p].
    unshelve eexists.
    constructor ; estransitivity ; eassumption.
    move: p ; apply (Spr2 (post tt)) ; apply monus_mon ; assumption.
  Qed.
  Next Obligation.
    move: H0 => [H0 p] ; exists H0 ; move: p; apply H.
  Qed.

  Definition CostD := @OpSpecWP CostS CostAr CostSpec CostSpecs.

  Program Definition costs {A} n (pre : SProp) (post : A -> SProp)
    : CostSpec A :=
    ⦑ fun post' => ⦑fun n0 => pre s/\ s∃ (H : Box (n s<= n0)), forall a, post a -> Spr1 (post' a) (@monus n0 n (unbox H))⦒⦒.
  Next Obligation.
    move: H0 => [? [[H']] p] ; split ; [assumption|].
    unshelve eexists.
    constructor ; estransitivity ; eassumption.
    move=> a Ha.
    move: (p a Ha) ; apply (Spr2 (post' a)) ; apply monus_mon ; assumption.
  Qed.
  Next Obligation.
    move: H0 => [? [H0 p]]; split=> //; exists H0 ; move=> a0 Ha ; move: (p a0 Ha); apply H.
  Qed.

  Program Definition tick (n:nat) : CostD unit (costs n sUnit (fun _ => sUnit)) :=
    dm_wkn (cont_perform CostSpecs n) _.
  Next Obligation.
    simpl in *. intuition.
    move: H => [[?] ?]; unshelve eexists;[constructor=> //| move=> [] ? //].
  Qed.
End Cost.

(* Definition fib_opt (n:nat) : CostD nat  (costs n sUnit (fun _ => sUnit)). *)
(* Proof. *)
(*   refine ((fix fib_aux (n:nat) {struct n} : nat × nat := *)
(*              wkn (x <- tick 1 ; *)
(*                   match n with *)
(*                   | 0 => dm_ret ⟨1,1⟩ *)
(*                   | S (S n) => r1 <- fib_aux (S n) ; r2 <- fib_aux n ; dm_ret r1 *)
(*                   end) _) n) *)
(* Definition fib_triv (n:nat) : CostD *)