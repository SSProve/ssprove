From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase.

Set Primitive Projections.
Set Universe Polymorphism.


Section Rel.
  Notation πl := (fun x => nfst (dfst x)).
  Notation πr := (fun x => nsnd (dfst x)).
  Notation πw := (fun x => dsnd x).
  Notation "⦑ x , y ⦒" := (dpair _ (npair x y) _).
  Notation "⦑ x , y | w ⦒" := (dpair _ (npair x y) w).
  Notation "⦑ x , y | w | Y ⦒" := (dpair (fun p => πw Y (nfst p) (nsnd p)) (npair x y) w).

  (* CwF of relations *)

  (* Objects *)
  Definition Rel : Type := { AB : Type × Type ⫳ nfst AB -> nsnd AB -> Type }.
  Definition mkRel (A B : Type) (R : A -> B -> Type) : Rel :=
    dpair (fun p => nfst p -> nsnd p -> Type) ⟨A , B⟩ R.

  Definition Relw : forall R:Rel, ( _ -> _ -> _) := πw.
  Coercion Relw : Rel >-> Funclass.

  Definition points (X:Rel) : Type := { p : πl X × πr X ⫳ X (nfst p) (nsnd p)}.
  Notation "⟬ X ⟭" := (points X).

  (* Universes *)
  Definition TyRel : Rel := @mkRel Type Type (fun A B => A -> B -> Type).

  Definition ArrRel (X Y : Rel) : Rel :=
    ⦑ πl X -> πl Y, πr X -> πr Y
    | fun fl fr => forall xl xr, X xl xr -> Y (fl xl) (fr xr) | TyRel ⦒.

  Notation "X R=> Y" := (ArrRel X Y) (at level 60).

  Definition arrRel X Y := ⟬X R=> Y⟭.
  Notation "X R==> Y" := (arrRel X Y) (at level 60).

  Program Definition idRel X : X R==> X := ⦑id, id⦒.

  Program Definition compRel {X Y Z : Rel}
          (f : X R==> Y) (g : Y R==> Z) : X R==> Z :=
    ⦑fun x => πl g (πl f x), fun x => πr g (πr f x)
    | fun xl xr xw => πw g _ _ (πw f xl xr xw)⦒.

  (* Defining relational morphisms : *)
  (*      We use a syntactic trick to define relational morphisms *)
  (*      X R==> Y out of plain functions (1 R==> X) -> (1 R==> Y) *)
  (*      such that the value of the function on the left (resp. right) *)
  (*      projection is determined by the value of the argument on its *)
  (*      left (resp. right) projection. *)
  (*    *)
  Notation "[< t | Y >]" :=
    (ltac:(let tl :=
               let t := (eval cbn in (fun x y w => πl (t ⦑x, y| w⦒))) in
               match t with | fun x y w => @?P x =>  P end
           in
           let tr :=
               let t := (eval cbn in (fun x y w => πr (t ⦑x, y| w⦒))) in
               match t with | fun x y w => @?P y =>  P end
           in
           let tw := eval cbn in (fun x y w => πw (t ⦑x, y| w⦒)) in
           exact (dpair (fun p => forall xl xr xw, πw Y (nfst p xl) (nsnd p xr)) ⟨tl, tr⟩ tw))).

  Eval cbv in (TyRel R==> TyRel).
  Check ([< fun x:Rel => @mkRel (πl x × nat) nat (fun _ _ => True) | TyRel >] : TyRel R==> TyRel).

  Definition Hi A : Rel := ⦑ A, A | fun a a' => True | TyRel ⦒.
  Definition Lo A : Rel := ⦑ A, A | fun a a' => a = a' | TyRel ⦒.

  (* Families *)
  Definition dRel (r:Rel) := r R=> TyRel.

  Program Definition applyRel (X Y:Rel) (f :X R==> Y) : ⟬X⟭ -> ⟬Y⟭ :=
    fun x => ⦑πl f (πl x), πr f (πr x) | πw f (πl x) (πr x) (πw x) | Y⦒.

  Notation "f @R x" := (applyRel f x) (at level 85).

  Definition f : Hi nat R==> (Lo nat R=> Lo nat) :=
    [< fun (hi : ⟬Hi nat⟭)  => [< fun lo : ⟬Lo nat⟭ => lo | Lo nat >] | Lo nat R=> Lo nat >].

  (* Notation "[| x | t |]" := (ltac:(let t' := constr:(fun x => t) in idtac t' ; exact 0)) (x ident). *)

  (* Check [| x | x |]. *)

  (* Notation "λ² x ∈ X | Y → t" := ([< constr:(fun x : ⟬ X ⟭ => t) | Y >]) (at level 50, x ident). *)

  (* Definition g := λ² x ∈ Hi nat | Lo nat R=> Lo nat → λ² y ∈ Lo nat | Lo nat → y. *)

End Rel.

Module RelNotations.
  Notation πl := (fun x => nfst (dfst x)).
  Notation πr := (fun x => nsnd (dfst x)).
  Notation πw := (fun x => dsnd x).
  Notation "⦑ x , y ⦒" := (dpair _ (npair x y) _).
  Notation "⦑ x , y | w ⦒" := (dpair _ (npair x y) w).
  Notation "⦑ x , y | w | Y ⦒" := (dpair (fun p => πw Y (nfst p) (nsnd p)) (npair x y) w).
  Notation "⟬ X ⟭" := (points X).
  Notation "X R=> Y" := (ArrRel X Y) (at level 60).
  Notation "X R==> Y" := (arrRel X Y) (at level 60).

  Notation "[< t | Y >]" :=
    (ltac:(let tl :=
               let t := (eval cbn in (fun x y w => πl (t ⦑x, y| w⦒))) in
               match t with | fun x y w => @?P x =>  P end
           in
           let tr :=
               let t := (eval cbn in (fun x y w => πr (t ⦑x, y| w⦒))) in
               match t with | fun x y w => @?P y =>  P end
           in
           let tw := eval cbn in (fun x y w => πw (t ⦑x, y| w⦒)) in
           exact (dpair (fun p => forall xl xr xw, πw Y (nfst p xl) (nsnd p xr)) ⟨tl, tr⟩ tw))).
  Notation "f @R x" := (applyRel f x) (at level 85).
End RelNotations.
