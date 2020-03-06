From mathcomp Require Import all_ssreflect all_algebra reals.

Import ssrnum.Num.Theory.
Local Open Scope ring_scope.

Parameter (R:realType).
Parameter  (absord : R -> R -> bool). 
Parameter (unlock_absord : absord = (fun x y : R => x <= y)).
