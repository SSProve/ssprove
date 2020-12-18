From ITree Require Import ITree.

Inductive subterm' {E A} : itree E A -> itree' E A -> Prop :=
| VisSub {X} e k (x:X) : subterm' (k x) (VisF e k)
| TauSub t : subterm' t (TauF t).

Definition subterm {E A} t t' := @subterm' E A t (_observe t').

Inductive tree (E : Type -> Type) (R : Type) : Type :=
| RetF : R -> tree E R
| VisF : forall X : Type, E X -> (X -> tree E R) -> tree E R.

From Coq Require Import ssreflect.

Definition extract_finite {E A} (t:itree E A) (H : Acc subterm t) : tree E A.
Proof.
  elim: {t} H => t; rewrite /subterm; case: (_observe t)=> [r|t0|X e k] _ IH.
  by apply:RetF.
  apply: IH; apply: TauSub.
  apply: (VisF _ _ _ e)=> x; apply: IH; by apply: VisSub.
Defined.

(* BUG REPORT *)
(* From Equations Require Import Equations. *)
(* Derive Subterm for itreeF. *)
(* Derive Subterm for itree. *)
