From Equations Require Import Equations.

(* Dependent sum is wellf-founded whenever the base and the fibers are *)
Section LexDepProd.
  Context (A:Type) (B:A -> Type).
  Context (leA : A -> A -> Prop) (leB : forall (a:A), B a -> B a -> Prop).

  Inductive lexdepprod : { x:A & B x } -> { x:A & B x} -> Prop :=
    | left_lex :
      forall (x x':A) (y:B x) (y':B x'),
        leA x x' -> lexdepprod (existT _ x y) (existT _ x' y')
    | right_lex :
      forall (x:A) (y y':B x),
        leB x y y' -> lexdepprod (existT _ x y) (existT _ x y').

  Lemma acc_A_B_lexdepprod :
    forall x:A, Acc leA x -> (forall x, well_founded (leB x)) ->
                forall y:B x, Acc (leB x) y -> Acc lexdepprod (existT _ x y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    dependent elimination H6.
    apply IHAcc. assumption. assumption. apply H2.

    apply IHAcc0. assumption.
  Defined.

  Theorem wf_lexdepprod :
    well_founded leA ->
    (forall x, well_founded (leB x)) -> well_founded lexdepprod.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a. 
    apply acc_A_B_lexdepprod; auto with sets; intros ; apply wfB.
  Defined.
  
End LexDepProd.
Instance wellfounded_lexdepprod A B R S `(wfR : @WellFounded A R, wfS : (forall x, @WellFounded (B x) (S x))) : 
  WellFounded (lexdepprod A B R S) := wf_lexdepprod A B R S wfR wfS.

(* Subset types are wellfounded whenever the base type is *)
Section SigWf.
  Context (A : Type) (P : A -> Prop) (leA : A -> A -> Prop).

  Definition leSigA : {x:A | P x} -> {x:A | P x} -> Prop.
  Proof.
    intros [x _] [y _] ; exact (leA x y).
  Defined.

  Lemma acc_sig_A_B : forall x:A, Acc leA x -> forall H: P x, Acc leSigA (exist _ x H).
  Proof.
    intros ? H ; induction H as [x _ IHAcc].
    intros ; constructor ; intros [] ; simpl ; intros ; apply IHAcc ; assumption.
  Defined.
    
  Theorem wf_sig : well_founded leA -> well_founded leSigA.
  Proof.
    intros wfA ; unfold well_founded ; intros [? ?] ; apply acc_sig_A_B ; auto with sets.
  Defined.

End SigWf.

(* The empty type is wellfounded *)
Section EmptyWf.
  Context (A:Type).
  Definition empty_rel : A -> A -> Prop := fun x y => False.
  Theorem wf_empty_rel : well_founded empty_rel.
  Proof.
    intros ?; constructor ; intros ? H ; inversion H.
  Qed.
End EmptyWf.

Instance wellfounded_empty_rel (A:Type) : WellFounded (empty_rel A) :=
  wf_empty_rel A.
