From Coq Require Import ssreflect ssrfun.
From Mon.sprop Require Import SPropBase.

(* Import SPropNotations. *)

Goal forall A P (x x':@Ssig A P), x = x'.
Proof.
  move=> ? ? [? ?] [? ?].
  match goal with
  | [|- context c [Sexists _ _ ?H]] =>
    let H' := fresh "H" in set (H':=H) in * at 1
  end.
  clearbody H.
                 
    
  Goal forall A P (x:@Ssig A P) (f :forall (p:SProp) (H:p), Type), f _ (Spr2 x).
Proof.
  intros.
  destruct x.
  match goal with
  | [|- context c [Sexists _ _ ?H]] =>
    let H' := fresh "H" in set (H':=H)
  end.
  clearbody H.
