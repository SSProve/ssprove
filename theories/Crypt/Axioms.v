Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals boolp.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)

(* Export to allow the use of equal_f *)
From Stdlib Require Export FunctionalExtensionality.

Local Open Scope ring_scope.

Parameter (R:realType).
Parameter (absord : R -> R -> bool).  (*sealed order on real numbers*)
Parameter (unlock_absord : absord = (fun x y : R => x <= y)). (*unseal with this*)
