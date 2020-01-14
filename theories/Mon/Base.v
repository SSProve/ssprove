(* For reasoning with UIP *)
From Coq.Logic Require Import EqdepFacts.

Set Primitive Projections.

(** Specifying a dependent equation *)

Definition eq_above {A} {B : A -> Type} {x y : A}
           (H : x = y) (mx: B x) (my : B y) :=
  eq_rect x B mx y H = my.

Notation "p =⟨ e ⟩ q" := (eq_above e p q) (at level 30).


(** (Negative) Subtypes *)

Record subtype {A} (P : A -> Prop) :=
  subt {
    wit : A ;
    pf : P wit
  }.

Notation "{ x : A ∥ P }" := (subtype (fun (x:A) => P)) (x at level 99).
Arguments wit {_ _} _.
Arguments pf {_ _} _.

Lemma eq_eq_above_eq_subtype :
  forall (U:Type) (P:U -> Prop) (z1 z2 : subtype P),
    forall h : z1.(wit) = z2.(wit),  z1.(pf) =⟨ h ⟩ z2.(pf) -> z1 = z2.
Proof.
  intros U P [w1 p1] [w2 p2]; simpl; intros h <-.
  dependent inversion h.
  reflexivity.
Qed.

Lemma subtype_eq {A B} (f : A -> B) (HB : UIP_ B) (y0:B) (P := (fun x => f x = y0)):
  forall (mx my : subtype P), wit mx = wit my -> mx = my.
  intros ? ? h. 
  exact (eq_eq_above_eq_subtype _ _ _ _ h (HB _ _ _ _)).
Qed.

Lemma transport_subtype : forall {A B} (F : B -> A -> Prop) {x y} h z,
    eq_rect x (fun x => subtype (fun b => F b x)) z y h
    = {| wit := wit z ; pf := eq_ind x (F (wit z)) (pf z) y h |}.
Proof.
  intros.
  dependent inversion h.
  reflexivity.
Qed.

Lemma eq_above_subtype {A B} (f : A -> B) (HB : UIP_ B)
      (G := fun y => {x : A ∥ f x = y}) {y1 y2 : B} {h : y1 = y2}
      {z1 : G y1} {z2 : G y2} :
  z1.(wit) = z2.(wit) -> z1 =⟨ h ⟩ z2.
Proof.
  intro Hz.
  unfold eq_above.
  unfold G in *.
  rewrite (transport_subtype _ h z1).
  eapply (eq_eq_above_eq_subtype _ _ _ _).
  Unshelve. 2: simpl ; assumption.
  apply HB.
Qed.

(** Negative pairs *)

Record nprod (A B : Type) := npair { nfst : A ; nsnd : B }.
Arguments npair {_ _} _ _.
Arguments nfst {_ _} _.
Arguments nsnd {_ _} _.

Notation "A × B" := (nprod A B)%type (at level 80) : type_scope.
Notation "⟨ x , y ⟩" := (npair x y).

Lemma nprod_eq {A B} (z1 z2 : A × B) :
  nfst z1 = nfst z2 -> nsnd z1 = nsnd z2 -> z1 = z2.
Proof.
  change z1 with ⟨nfst z1, nsnd z1⟩ ; change z2 with ⟨nfst z2, nsnd z2⟩.
  simpl ; intros -> -> ; reflexivity.
Defined.

(** (Negative) Sigma types *)

Record nsigT {A} (P : A -> Type) :=
  dpair {
    dfst : A ;
    dsnd : P dfst
  }.

Notation "{ x : A ⫳ P }" := (nsigT (fun (x:A) => P)) (x at level 99).
Arguments dpair {_} _ _ _.
Arguments dfst {_ _} _.
Arguments dsnd {_ _} _.

Lemma transport_nsigT : forall {A B} (F : B -> A -> Type) {x y} h z,
    eq_rect x (fun x => { b : B ⫳ F b x}) z y h
    = {| dfst := dfst z ; dsnd := eq_rect x (F (dfst z)) (dsnd z) y h |}.
Proof.
  intros.
  dependent inversion h.
  reflexivity.
Qed.

Lemma eq_eq_above_eq_nsigT :
  forall (U:Type) (P:U -> Type) (z1 z2 : { u : U ⫳ P u }),
    forall h : dfst z1 = dfst z2,  dsnd z1 =⟨ h ⟩ dsnd z2 -> z1 = z2.
Proof.
  intros U P [w1 p1] [w2 p2]; simpl; intros h <-.
  dependent inversion h.
  reflexivity.
Qed.

Lemma eq_above_nsigT_hprop {A B} (f : A -> B -> Type)
      (hprop_f : forall x y (p q : f x y), p = q)
      (G := fun y => {x : A ⫳ f x y})
      {y1 y2 : B} {h : y1 = y2}
      {z1 : G y1} {z2 : G y2} :
  dfst z1 = dfst z2 -> z1 =⟨ h ⟩ z2.
Proof.
  intro Hz.
  unfold eq_above.
  unfold G in *.
  rewrite (transport_nsigT _ h z1).
  eapply (eq_eq_above_eq_nsigT _ _ _ _).
  Unshelve. 2: simpl ; assumption.
  apply hprop_f.
Qed.
