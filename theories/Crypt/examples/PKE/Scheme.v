Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve Require Import NominalPrelude.

Import PackageNotation.
#[local] Open Scope package_scope.


Module PKE.

Record scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip :
      code emptym [interface] Cip
  ; keygen :
      code emptym [interface] (Sec × Pub)
  ; enc : ∀ (k : Pub) (m : Mes),
      code emptym [interface] Cip
  ; dec : ∀ (k : Sec) (c : Cip),
      code emptym [interface] Mes
  }.

Section Defs.
  Context (P : scheme).

  Definition ENCDEC := 0%N.

  Definition I_CORR :=
    [interface [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } ].

  Definition CORR0 :
    game I_CORR :=
    [package emptym ;
      [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
        '(sk, pk) ← P.(keygen) ;;
        c ← P.(enc) pk m ;;
        m' ← P.(dec) sk c ;;
        ret m'
      }
    ].

  Definition CORR1 :
    game I_CORR :=
    [package emptym ;
      [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
        ret m
      }
    ].

  Definition CORR b := if b then CORR0 else CORR1.


  Definition mpk_loc : Location := (1, 'option P.(Pub)).
  Definition GEN := 0%N.
  Definition QUERY := 1%N.

  Definition I_CPA :=
    [interface
      [ GEN ] : { 'unit ~> P.(Pub) } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) }
    ].

  Definition CPA b :
    game I_CPA :=
    [package [fmap mpk_loc ] ;
      [ GEN ] : { 'unit ~> P.(Pub) } 'tt {
        '(_, pk) ← P.(keygen) ;;
        #put mpk_loc := Some pk ;;
        ret pk
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        pk ← getSome mpk_loc ;;
        if b then
          P.(enc) pk m
        else
          P.(sample_Cip)
      }
    ].

  Definition count_loc : Location := (142, 'nat).

  Definition COUNT n :
    package (I_CPA) (I_CPA) :=
    [package [fmap count_loc ] ;
      [ GEN ] : { 'unit ~> P.(Pub) } 'tt {
        call GEN 'unit P.(Pub) tt
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        count ← get count_loc ;; 
        #assert (count < n)%N ;;
        #put count_loc := count.+1 ;;
        call QUERY P.(Mes) P.(Cip) m
      }
    ].
End Defs.

Notation MT_CPA P n := (λ b, COUNT P n ∘ CPA P b)%sep.
Notation OT_CPA P := (λ b, COUNT P 1 ∘ CPA P b)%sep.

End PKE.
