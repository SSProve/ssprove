(** Package notations

  In this module we define a functor to export user-friendly notations for
  packages and package codes.
  The user doesn't need to instantiate the functor here, and should only rely
  on the Package functor which exports the notations as well.

  Scope of the notations: package_scope
  delimited with %pack.

  Please look at package_usage_example.v for examples of how to use those.

  - Notation for choice types in the choice universe

    This module provides a specific notation for inhabiting the choice
    universe, but only in certain positions that will be described in the
    following notations.
    These types can be described using a syntax closer to the usual Coq
    syntax:
    'nat
    'bool
    'unit
    'option A
    'fin n
    A × B
    {map A → B}
    where A and B follow again the same syntax and n is a natural number
    given using the regular Coq syntax.

  - Notation to provide an inhabitant of 'fin n
    gfin m will try to inhabit 'fin n
    It is best used in a #[program] environment to make sure the proof
    obligation is automatically discharged.

  - Sequence notation for interfaces

    An interface can be provided using the following sequence notation:
    [interface d1 ; ... ; dn]
    where d1 to dn are prototypes or function signatures of the form
    val #[n] : S → T
    where S and T are both given using the type syntax above
    and n is a natural number used as an identifier.

  - Sequence notation for packages

    A package can bve provided using the following sequence notation;
    [package d1 ; ... dn]
    where d1 to dn are function declarations of the form
    def #[n] (x : A) : B {
      e
    }
    where n is a natural number used as an identifier, A and B are types
    following the syntax above and e is a regular Coq expression which has
    x of type (chElement A) in scope.

  - Notation for the code monad

    Additionally we provide some useful notations for writing codes.
    All notations with a binder (x ← ...) can be instantiated with patterns
    instead of new identifiers (e.g. '(x,y) ← ...).

    - Bind:
      x ← c ;; k
      corresponds to binding c to x and continuing with k, an expression
      that may contain x.

      In case k doesn't mention x, we provide a special notation
      c ;; k

    - Managing state:
      put n := u ;; c
      x ← get n ;; c
      correspond respectively to updating and reading the state location n.

    - Sampling:
      x ← sample o ;; c
      obtains x from sampling o and continues with c (which may mention x).
      Alternatively one can use the synonymous notation
      x <$ o ;; c
      from easycrypt.
      It will only be used for parsing, and will still print as
      x ← sample o ;; c.

    - Imported operators:
      x ← op [ o ] n ;; c
      will apply imported operator o to argument n, store the result in x and
      continue with c.
      o is given of the form
      #[ f ] : A → B
      which is the same as declarations in interfaces.
      For instance one can write
      n ← op [ #[0] : nat → nat ] n ;; ret n
**)


From Coq Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice seq.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From Crypt Require Import Prelude Axioms ChoiceAsOrd RulesStateProb
  chUniverse pkg_core_definition pkg_composition.


#[local] Open Scope fset.
#[local] Open Scope fset_scope.

Declare Custom Entry pack_type.
Declare Custom Entry interface.
Declare Custom Entry package.
Declare Custom Entry pack_op.

Module PackageNotation.

  (**
    The `custom entry` engine does not allow a name to be a symbol without
    it being a symbol in the global grammar.
    As a workaround, we define 'bool and such to avoid making it impossible
    to refer to bool by making it a keyword.
  *)

  Notation " 'nat " := (chNat) (in custom pack_type at level 2).
  Notation " 'bool " := (chBool) (in custom pack_type at level 2).
  Notation " 'unit " := (chUnit) (in custom pack_type at level 2).
  Notation " 'option x " := (chOption x) (in custom pack_type at level 2).

  Notation " 'fin n " :=
    (chFin (mkpos n))
    (in custom pack_type at level 2, n constr).

  Notation "{map x → y }" :=
    (chMap x y)
    (in custom pack_type at level 2, format "{map  x  →  y  }").

  Notation " x × y " := (chProd x y) (in custom pack_type at level 2).

  Notation "( x )" := x (in custom pack_type, x at level 2).

  (** Repeat the above notations here for package_scope. *)
  Notation " 'nat " := (chNat) (at level 2) : package_scope.
  Notation " 'bool " := (chBool) (at level 2) : package_scope.
  Notation " 'unit " := (chUnit) (at level 2) : package_scope.
  Notation " 'option x " := (chOption x) (at level 2) : package_scope.

  Notation " 'fin x " :=
    (chFin (mkpos x))
    (at level 2) : package_scope.

  (* Conflicts with this one. *)
  (* Notation "{map x → y }" :=
    (chMap x y)
    (at level 80, format "{map  x  →  y  }") : package_scope. *)

  Notation " x × y " := (chProd x y) (at level 80) : package_scope.

  Notation "[ 'interface' ]" :=
    (fset [::])
    (at level 0, only parsing)
    : package_scope.

  Notation "[ 'interface' x1 ]" :=
    (fset (x1 :: [::]))
    (at level 0, x1 custom interface at level 2,
    format "[ interface  x1  ]")
    : package_scope.

  Notation "[ 'interface' x1 ; x2 ; .. ; xn ]" :=
    (fset (x1 :: x2 :: .. [:: xn] ..))
    (at level 0,
    x1 custom interface at level 2,
    x2 custom interface at level 2,
    xn custom interface at level 2,
    format "[ interface  '[' x1  ;  '/' x2  ;  '/' ..  ;  '/' xn ']'  ]")
    : package_scope.

  Notation "'val' #[ f ] : A → B" :=
    (f, (A, B))
    (in custom interface at level 0,
    f constr, A custom pack_type, B custom pack_type,
    format "val  #[ f ]  :  A  →  B").

  Notation "[ 'package' ]" :=
    (mkpackage (mkfmap [::]) _)
    (at level 0, only parsing)
    : package_scope.

  Notation "[ 'package' x1 ]" :=
    (mkpackage (mkfmap (x1 :: [::])) _)
    (at level 0, x1 custom package at level 2, format "[ package  x1  ]")
    : package_scope.

  Notation "[ 'package' x1 ; x2 ; .. ; xn ]" :=
    (mkpackage (mkfmap (x1 :: x2 :: .. [:: xn] ..)) _)
    (at level 0,
    x1 custom package at level 2,
    x2 custom package at level 2,
    xn custom package at level 2,
    format "[ package  '[' x1  ;  '/' x2  ;  '/' ..  ;  '/' xn  ']' ]")
    : package_scope.

  Notation " 'def' #[ f ] ( x : A ) : B { e }" :=
    ((f, mkdef A B (λ x, e)))
    (in custom package at level 0,
    f constr, e constr, x name, A custom pack_type, B custom pack_type,
    format "def  #[ f ]  ( x : A )  :  B  { '[' '/'  e  '/' ']' }")
    : package_scope.

  Notation " 'def' #[ f ] ( ' p : A ) : B { e }" :=
    ((f, mkdef A B (λ x, let p := x in e)))
    (in custom package at level 0,
    f constr, e constr, p pattern, A custom pack_type, B custom pack_type,
    format "def  #[ f ]  ( ' p : A )  :  B  { '[' '/'  e  '/' ']' }")
    : package_scope.

  Notation "#[ f ] : A → B" :=
    (mkopsig f A B)
    (in custom pack_op at level 0,
    f constr, A custom pack_type, B custom pack_type,
    format "#[ f ]  :  A  →  B").

  Notation "{ 'sig' o }" :=
    (o)
    (at level 0, o custom pack_op at level 2, format "{ sig  o  }")
    : package_scope.

  Notation "x ← c1 ;; c2" :=
    (bind c1 (λ x, c2))
    (at level 100, c1 at next level, right associativity,
    format "x  ←  c1  ;;  '//' c2")
    : package_scope.

  Notation "' p ← c1 ;; c2" :=
    (bind c1 (λ x, let p := x in c2))
    (at level 100, p pattern, c1 at next level, right associativity,
    format "' p  ←  c1  ;;  '//' c2")
    : package_scope.

  Notation "e1 ;; e2" :=
    (_ ← e1 ;; e2)%pack
    (at level 100, right associativity,
    format "e1  ;;  '//' e2")
    : package_scope.

  Notation "'put' n ':=' u ;; c" :=
    (putr n u c)
    (at level 100, u at next level, right associativity,
    format "put  n  :=  u  ;;  '//' c")
    : package_scope.

  Notation "x ← 'get' n ;; c" :=
    (getr n (λ x, c))
    (at level 100, n at next level, right associativity,
    format "x  ←  get  n  ;;  '//' c")
    : package_scope.

  Notation "' p ← 'get' n ;; c" :=
    (getr n (λ x, let p := x in c))
    (at level 100, p pattern, n at next level, right associativity,
    format "' p  ←  get  n  ;;  '//' c")
    : package_scope.

  Notation "x ← 'op' o ⋅ n ;; c" :=
    (opr o n (λ x, c))
    (at level 100, n at next level, o at next level,
    right associativity,
    format "x  ←  op  o  ⋅  n  ;;  '//' c")
    : package_scope.

  Notation "' p ← 'op' o ⋅ n ;; c" :=
    (opr o n (λ x, let p := x in c))
    (at level 100, p pattern, n at next level, o at next level,
    right associativity,
    format "' p  ←  op  o  ⋅  n  ;;  '//' c")
    : package_scope.

  Notation "x ← 'sample' o ;; c" :=
    (sampler o (λ x, c))
    (at level 100, o at next level, right associativity,
    format "x  ←  sample  o  ;;  '//' c")
    : package_scope.

  Notation "' p ← 'sample' o ;; c" :=
    (sampler o (λ x, let p := x in c))
    (at level 100, p pattern, o at next level, right associativity,
    format "' p  ←  sample  o  ;;  '//' c")
    : package_scope.

  Notation "x <$ o ;; c" :=
    (x ← sample o ;; c)%pack
    (at level 100, o at next level, right associativity,
    (* format "x  <$  o  ;;  '//' c", *) only parsing)
    : package_scope.

  Notation "x ← 'cmd' o ;; c" :=
    (cmd_bind o (λ x, c))
    (at level 100, o at next level, right associativity,
    format "x  ←  cmd  o  ;;  '//' c")
    : package_scope.

  Notation "' p ← 'cmd' o ;; c" :=
    (cmd_bind o (λ x, let p := x in c))
    (at level 100, p pattern, o at next level, right associativity,
    format "' p  ←  cmd  o  ;;  '//' c")
    : package_scope.

  (* TODO Use ;; for this, and a longer notation or none at all for
    bind. Bind is just a tool to compose codes while this is to compose
    commands and code, much more practical.
    TODO: Maybe not add things such as get/put/cmd to the grammar.
  *)
  Notation "e1 ;' e2" :=
    (_ ← cmd e1 ;; e2)%pack
    (at level 100, right associativity,
    format "e1  ;'  '//' e2")
    : package_scope.

  Notation "'#import' s 'as' id ;; t" :=
    (let id := λ x, opr s x (λ y, ret y) in t)
    (at level 100, id name, s at next level, right associativity,
    format "#import  s  as  id  ;;  '//' t")
    : package_scope.

  (** Utility for fin types *)

  (** m : 'fin n *)
  Lemma give_fin {m} (n : nat) {h : Lt n m} : ('fin m)%pack.
  Proof.
    cbn. exists n. exact h.
  Defined.

  Notation gfin n := (@give_fin _ n _).

End PackageNotation.
