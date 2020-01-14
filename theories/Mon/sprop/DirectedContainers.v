From Coq Require Import ssreflect ssrfun.
From Coq Require FunctionalExtensionality.
From Mon Require Export Base.
From Mon.SRelation Require Import SRelation_Definitions SMorphisms.
From Mon.sprop Require Import SPropBase SPropMonadicStructures Monoid.

Set Primitive Projections.

(* Straightforward implementation of
   Update Monads: Cointerpreting Directed Containers. TYPES 2013
   Danel Ahman, Tarmo Uustalu *)
Section DirectedContainer.

  Import EqNotations.
  Record dir_cont_struct A :=
    mkDirectedContainer
      { dc_fib :> A -> Type
      ; dc_act : forall a, dc_fib a -> A
      ; dc_unit : forall {a}, dc_fib a
      ; dc_mult : forall {a} (p:dc_fib a), dc_fib (dc_act a p) -> dc_fib a
      ; dc_law1 : forall a, dc_act a dc_unit = a
      ; dc_law2 : forall a p1 p2, dc_act a (dc_mult p1 p2) = dc_act (dc_act a p1) p2
      ; dc_law3 : forall a (p:dc_fib a), dc_mult p dc_unit = p
      ; dc_law4 : forall a (p:dc_fib (dc_act a dc_unit)),
          dc_mult dc_unit p = rew [dc_fib] dc_law1 a in p
      ; dc_law5 : forall a (p1:dc_fib a) (p2:dc_fib (dc_act a p1)) (p3 : dc_fib (dc_act a (dc_mult p1 p2))),
        dc_mult p1 (dc_mult p2 (rew dc_law2 a p1 p2 in p3)) = dc_mult (dc_mult p1 p2) p3
      }.
End DirectedContainer.

Notation "✪" := (dc_unit _ _).
Notation "p ⊛ p'" := (dc_mult _ _ p p') (at level 65).
Notation "a ↫ p" := (dc_act _ _ a p) (at level 60).

Section StateDirectedContainer.
  Context (S:Type).

  Program Definition st_dc : dir_cont_struct S :=
    mkDirectedContainer S (fun _ => S) (fun s s' => s') (fun s => s) (fun s s' s'' => s'')
                        _ _ _ _ _.
End StateDirectedContainer.

Section MonoidToDirectedContainer.
  Context (M:monoid) (S:monoid_action M).

  Import EqNotations.
  Lemma req_cst {A} (B:Type) {a a' : A} (H: a = a') (b:B) :
    rew [fun=> B] H in b = b.
  Proof. 
    refine (match H as H0 in _ = a0 return rew [fun=> B] H0 in b = b with
            | eq_refl => eq_refl
            end).
  Qed.

  Program Definition monoid_dc : dir_cont_struct S :=
    mkDirectedContainer S (fun _ => M)
                        (fun s m => m ⧕ s)
                        (fun _ => e M) (fun _ m1 m2 => m2 ⋅ m1) _ _ _ _ _.
  Next Obligation. rewrite monact_unit //. Qed.
  Next Obligation. rewrite monact_mult //. Qed.
  Next Obligation. rewrite monoid_law1 //. Qed.
  Next Obligation. rewrite monoid_law2 req_cst //. Qed.
  Next Obligation. rewrite req_cst monoid_law3 //. Qed.

End MonoidToDirectedContainer.


Definition reader_dc S : dir_cont_struct S :=
  monoid_dc oneMonoid (oneAction S).

Definition writer_dc (M:monoid) : dir_cont_struct unit :=
  monoid_dc M (trivialAction M).

Definition logger_dc (M:monoid) : dir_cont_struct M :=
  monoid_dc M (multAction M).

Section Cointerpretation.
  Context A (dc : dir_cont_struct A).

 Definition cointerp_from_eqns pf1 pf2 pf3 : Monad :=
    @mkMonad (fun X => forall (a:A), dc a × X)
             (fun X x a => ⟨✪, x⟩)
             (fun X Y m f a => let '(npair p x) := m a in
                            let '(npair p' y) := f x (a ↫ p) in
                            ⟨p ⊛ p', y⟩)
             pf1 pf2 pf3.

 Import FunctionalExtensionality.
 Import EqNotations.
 Program Definition cointerp := cointerp_from_eqns _ _ _.
 Next Obligation.
   extensionality a0.
   rewrite {2}dc_law1 dc_law4.
   change (f a a0) with ⟨nfst (f a a0), nsnd (f a a0)⟩.
   f_equal.
   refine (match dc_law1 _ dc a0 as H0 in _ = a' return
                 rew [dc] H0 in nfst (f a (a0 ↫ ✪)) = nfst (f a a')
           with
           | eq_refl => eq_refl
           end).
 Qed.
 Next Obligation.
   extensionality a0.
   rewrite dc_law3 //=.
 Qed.
 Next Obligation.
   extensionality a.
   destruct (c a) as [c1 c2].
   destruct (f c2 (a ↫ c1)) as [f1 f2].
   f_equal.
   rewrite -dc_law5. do 2 f_equal.
   refine (match dc_law2 _ dc a c1 f1 as H0 in _ = a' return
                 rew [dc] H0 in nfst (g f2 (a ↫ (c1 ⊛ f1))) = nfst (g f2 a')
           with
           | eq_refl => eq_refl
           end).
   rewrite dc_law2 //=.
 Qed.

End Cointerpretation.