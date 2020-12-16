(*
  This file provides user friendly syntax for packages.
 *)


From Coq Require Import Utf8.
From mathcomp Require Import choice seq.
From extructures Require Import ord fset fmap.
From Crypt Require Import Prelude Axioms ChoiceAsOrd RulesStateProb
     pkg_chUniverse pkg_core_definition pkg_composition.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module PackageNotation (π : RulesParam).

  Include (PackageComposition π).

  Local Open Scope fset.
  Local Open Scope fset_scope.

  Declare Custom Entry pack_type.

  (* The `custom entry` engine does not allow a name to be a symbol without it being a symbol in
  the global grammar. As a workaround, we define dummy aliases for the names we want to
  re-interpret in the custom entry. *)
  Notation " 'nat' " := nat (at level 2).
  Notation " 'bool' " := bool (at level 2).
  (* Notation " 'zero' " := zero (at level 2). *)
  Notation " 'unit' " := unit (at level 2).

  Notation " 'nat' " := (chNat) (in custom pack_type at level 2).
  Notation " 'bool' " := (chBool) (in custom pack_type at level 2).
  Notation " 'zero' " := (chZero) (in custom pack_type at level 2).
  Notation " 'unit' " := (chUnit) (in custom pack_type at level 2).

  Notation " x × y " := (chProd x y) (in custom pack_type at level 2).

  Notation "( x )" := x (in custom pack_type, x at level 2).

  Declare Custom Entry interface.

  Notation "[ 'interface' ]" :=
    fset0
    (at level 0, only parsing)
    : package_scope.

  Notation "[ 'interface' x1 ]" := (fset (x1 :: [::]))
    (at level 0, x1 custom interface at level 2, format "[ interface  x1  ]")
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

  Declare Custom Entry package.

  Notation "[ 'package' ]" :=
    (mkpack (mkfmap [::]))
    (at level 0, only parsing)
    : package_scope.

  Notation "[ 'package' x1 ]" :=
    (mkpack (mkfmap (x1 :: [::])))
    (at level 0, x1 custom package at level 2, format "[ package  x1  ]")
    : package_scope.

  Notation "[ 'package' x1 ; x2 ; .. ; xn ]" :=
    (mkpack (mkfmap (x1 :: x2 :: .. [:: xn] ..)))
    (at level 0,
    x1 custom package at level 2,
    x2 custom package at level 2,
    xn custom package at level 2,
    format "[ package  '[' x1  ;  '/' x2  ;  '/' ..  ;  '/' xn  ']' ]")
    : package_scope.

  Definition mkdef {L I} (A B : chUniverse) (f : A → program L I B)
    : pointed_vprogram L I :=
    (A ; B ; f).

  Notation " 'def' #[ f ] ( x : A ) : B { e }" :=
    (* ((f, (A ; B ; λ (x : chElement A), (e : program _ _ (chElement B))))) *)
    ((f, mkdef A B (λ x, e)))
    (in custom package at level 0,
    f constr, e constr, x ident, A custom pack_type, B custom pack_type,
    format "def  #[ f ]  ( x : A )  :  B  { '[' '/'  e  '/' ']' }")
    : package_scope.

  Notation "x ← c1 ;; c2" :=
    (bind c1 (λ x, c2))
    (at level 100, c1 at next level, right associativity,
    format "x  ←  c1  ;;  '/' c2")
    : package_scope.

  Notation "' p ← c1 ;; c2" :=
    (bind c1 (λ x, let p := x in c2))
    (at level 100, p pattern, c1 at next level, right associativity,
    format "' p  ←  c1  ;;  '/' c2")
    : package_scope.

  Notation "e1 ;; e2" :=
    (_ ← e1%pack ;; e2%pack)%pack
    (at level 100, right associativity,
    format "e1  ;;  '/' e2")
    : package_scope.

  Notation "'put' n ':=' u ;; c" :=
    (putr n _ u c)
    (at level 100, u at next level, right associativity,
    format "put  n  :=  u  ;;  '/' c")
    : package_scope.

  Notation "x ← 'get' n ;; c" :=
    (getr n _ (λ x, c))
    (at level 100, n at next level, right associativity,
    format "x  ←  get  n  ;;  '/' c")
    : package_scope.

  Declare Custom Entry pack_op.

  Notation "#[ f ] : A → B" :=
    (f, (A, B))
    (in custom pack_op at level 0,
    f constr, A custom pack_type, B custom pack_type,
    format "#[ f ]  :  A  →  B").

  Notation "x ← 'op' [ o ] n ;; c" :=
    (opr o _ n (λ x, c))
    (at level 100, n at next level, o custom pack_op at level 2,
    right associativity,
    format "x  ←  op  [  o  ]  n  ;;  '/' c")
    : package_scope.

End PackageNotation.
