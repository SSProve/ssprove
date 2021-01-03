(* Global utility *)
(* Partly stolen from MetaCoq *)

From Coq Require Import Utf8.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

(* Simple products *)

(* Notation "x × y" := (prod x y) (at level 80, right associativity). *)


(* Dependent sums *)

(* Use \sum to input ∑ in Company Coq (it is not a sigma Σ). *)
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").


(* Handy rewrite on sig *)

Lemma sig_rewrite_aux :
  ∀ {T A} {P : A → Prop} {x y} (p : T → A) (h : P (p x)) (e : x = y),
    P (p y).
Proof.
  intros T A P x y p h e. subst. auto.
Defined.

Lemma sig_rewrite :
  ∀ {T A} {P : A → Prop} {x y} (p : T → A) (h : P (p x)) (e : x = y),
    exist _ (p x) h = exist _ (p y) (sig_rewrite_aux p h e).
Proof.
  intros T A P x y p h e. subst. reflexivity.
Qed.

Ltac sig_rewrite e :=
  lazymatch type of e with
  | ?x = _ =>
    match goal with
    | |- context [ exist ?P ?p ?h ] =>
      lazymatch p with
      | context [ x ] =>
        lazymatch eval pattern x in p with
        | (fun x => @?q x) ?y =>
          erewrite (sig_rewrite q _ e)
        end
      end
    end
  end.

(** Tactic sig rewrite

  Usage: you have e : x = y as an hypothesis and you want to rewrite e inside
  a term of the form exist _ u v, specifically inside the term u.
  sig rewrite e will replace x by y in u and update v accordingly.

*)
Tactic Notation "sig" "rewrite" hyp(e) :=
  sig_rewrite e.