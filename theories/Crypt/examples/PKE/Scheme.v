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

#[local] Open Scope nat.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.


Module PKE.

Record scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip : dist Cip
  ; keygen : dist (Sec × Pub)
  ; enc : Pub → Mes → dist Cip
  ; dec : Sec → Cip → option Mes
  }.

Section Defs.
  Definition ENCDEC := 0.

  Definition ICORR P :=
    [interface [ ENCDEC ] : { P.(Mes) ~> option P.(Mes) } ].

  Definition CORR0 P :
    game (ICORR P) :=
    [package emptym ;
      [ ENCDEC ] : { P.(Mes) ~> option P.(Mes) } (m) {
        '(sk, pk) ← P.(keygen) ;;
        c ← P.(enc) pk m ;;
        ret (P.(dec) sk c)
      }
    ].

  Definition CORR1 P :
    game (ICORR P) :=
    [package emptym ;
      [ ENCDEC ] : { P.(Mes) ~> option P.(Mes) } (m) {
        ret (Some m)
      }
    ].

  Definition CORR b := if b then CORR0 else CORR1.


  Definition mpk_loc P := mkloc 1 (None : option P.(Pub)).
  Definition GEN := 0.
  Definition QUERY := 1.

  Definition ICPA P :=
    [interface
      [ GEN ] : { unit ~> P.(Pub) } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) }
    ].

  Definition CPA P b :
    game (ICPA P) :=
    [package [fmap mpk_loc P ] ;
      [ GEN ] : { unit ~> P.(Pub) } 'tt {
        '(_, pk) ← P.(keygen) ;;
        #put mpk_loc P := Some pk ;;
        ret pk
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        pk ← getSome mpk_loc P ;;
        if b then
          P.(enc) pk m
        else
          P.(sample_Cip)
      }
    ].

  Definition count_loc := mkloc 142 (0 : 'nat).

  Definition COUNT P q :
    package (ICPA P) (ICPA P) :=
    [package [fmap count_loc ] ;
      [ GEN ] : { unit ~> P.(Pub) } (_) {
        call [ GEN ] : { unit ~> P.(Pub) } tt
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        count ← get count_loc ;; 
        #assert count < q ;;
        #put count_loc := count.+1 ;;
        call [ QUERY ] : { P.(Mes) ~> P.(Cip) } m
      }
    ].
End Defs.

Notation MT_CPA P q :=
  (λ b, COUNT P q ∘ CPA P b).
Notation OT_CPA P := 
  (λ b, COUNT P 1 ∘ CPA P b).

End PKE.
