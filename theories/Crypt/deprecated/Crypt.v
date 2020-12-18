(*********************************************************)
(**    Formalization of some cryptographic primitives   **)
(*********************************************************)

From Coq Require Import ssreflect.
From ITree Require Import ITree ITreeFacts.
From Mon.sprop Require Import MonadExamples FiniteProbabilities.
From mathcomp Require Import reals.

Import ITreeNotations.

Section Crypt.
  (* The common definitions *)
  Context {R : realType}.
  Definition I := unit_interval R.

  (* Free state + probabilities monad *)
  Section FreeStPr.
    Context {Input Oup : Type}.

    Inductive StPrSig : Type := Get : StPrSig | Put : Oup -> StPrSig | Bern : I -> StPrSig.
    Definition StPrAr (op : StPrSig) : Type :=
      match op with
      | Get => Input
      | Put _ => unit
      | Bern _ => bool
      end.

    Definition FreeStPr := @Free StPrSig StPrAr.
  End FreeStPr.

  Context {STy : Type}. (* State type can be inferred from the construction *)
  Context {ITy : Type}. (* Probabability type can be inferred from construction *)

  (* Simple state and probability event handlers *)
  Section StPrEventH.
    (* itree accepts a simple `Type -> Type` signature for `E`, and this is technically an interface *)
    Inductive StE : Type -> Type := GetE : StE STy | PutE : STy -> StE unit.
    Inductive PrE : Type -> Type := BernE : ITy -> PrE bool.
    Definition StPrE := StE +' PrE.
  End StPrEventH.

  (* Handling state events that appear in the itree *)
  Section Transformer.
    Context (E : Type -> Type). (* Event handler, of which StE and PrE are instances *)

    (* Here, we answer the question about how to put the data of state into itree *)
    (* RTy is the return type, which we pair together with the state type STy *)
    Definition StT (RTy : Type) : Type := STy -> itree E (STy * RTy)%type.

    (* The get and put monad transformers *)
    Definition GetT : StT STy := fun s => Ret (s, s).
    Definition PutT : STy -> StT unit := fun s' _ => Ret (s', tt).

    (* A handler for state events, mapping back to getT and putT *)
    (* "E ~> F" := forall (T : Type), E T -> F T *)
    Definition handler : StE ~> StT := fun _ e =>
    match e with
    | GetE => GetT
    | PutE s => PutT s
    end.

    (* interp : (E ~> M) -> (itree E ~> M) *)
    (* The plan is to get something of the form (StT (Cont I)) *)
  End Transformer.
End Crypt.
