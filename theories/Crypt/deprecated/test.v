From Coq Require Import ssreflect.
From ITree Require Import ITree ITreeFacts.

Import ITreeNotations.

Section IOEvent.

Inductive IOE : Type -> Type :=
  |Input : IOE nat
  |Output : nat -> IOE unit.

End IOEvent.

CoFixpoint echo : itree IOE void :=
  Vis Input
      (fun (ans:nat) => Vis (Output ans)
                         (fun _ => echo)).

CoFixpoint echo2 : itree IOE void :=
  ans <- (trigger Input) ;;
  (trigger (Output ans)) ;;
  echo.

CoFixpoint echo3 : itree IOE void :=
  x <- trigger Input ;;
  trigger (Output x) ;;
  Tau echo2. (*note the use of tau*)

CoFixpoint loop : itree IOE void :=
  Tau loop.

CoFixpoint probeFor9 : itree IOE unit :=
  ans <- trigger Input ;;
  if Nat.eqb 9 ans then
    Ret tt
  else
    Tau probeFor9.

CoFixpoint probeFor9_bis : itree IOE unit :=
  Vis Input (fun x => if PeanoNat.Nat.eqb 9 x then (Ret tt)
                    else probeFor9_bis).

Goal echo ≈ echo2.
Proof. rewrite /echo /echo2.
Abort.


(* ----------- now an example of itrees containing stateful events ---*)

Section StateEvents.

(*the first layer required to play with effects: a type of external events.*)
Context {S : Type}.

Inductive stateE : Type -> Type :=
 |Get : stateE S (*we provide nothing to the env, and it returns smth
                  of type S, ie a state*)
 |Put : S -> stateE unit. (*we provide a state to the env, and the env
                          no information, ie tt:unit *)

End StateEvents.


Section StateHandlerAndInterpreter.

(*a handler should transform single external events (here stateful events)
into monadic computations. *)

Definition h_state (S:Type)
: (@stateE S) ~>  Monads.stateT S (itree (@stateE S)).
  rewrite /Monads.stateT. intro A. intro eva. intro s0.
  move: eva => [|towrite].
  -  econstructor. econstructor. exact (s0,s0).
  -  econstructor. econstructor. exact (towrite , tt).
Defined.


Definition interp_state {S:Type} : (itree (@stateE S)) ~> Monads.stateT S (itree (@stateE S)) := interp (h_state S).

End StateHandlerAndInterpreter.

Section bla.
Context {S:Type}.

Program Definition synGet := trigger Get.
Next Obligation. exact S. Defined.




