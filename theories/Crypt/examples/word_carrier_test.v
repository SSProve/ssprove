Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ word.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Crypt Require Import choice_type jasmin_word.

Inductive small_telescope : Type :=
| telescope_end : small_telescope
| telescope_bind : forall carrier : Set,
    (carrier -> small_telescope) -> small_telescope.

Definition word_telescope sz :=
  @telescope_bind (wcarrier sz) (fun _ => telescope_end).

Definition carrier_to_word sz (value : wcarrier sz) : word sz := value.
Definition word_to_carrier sz (value : word sz) : wcarrier sz := value.

Example carrier_round_trip sz (value : wcarrier sz) :
  wrepr sz (wunsigned value) = value.
Proof. exact: wrepr_unsigned. Qed.

Example carrier_type sz : wcarrier sz = word sz :> Type.
Proof. exact: wcarrierE. Qed.
