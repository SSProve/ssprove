(*
  Construction of a few concrete instances of mathcomp's finGroup type
*)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect fingroup.fingroup fintype
     eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".
From HB Require Import structures.
From deriving Require Import deriving.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Module Z2_manual.
  (* A clumsy and somewhat painful manual construction of the group structure
  on Z2, defined as inductive type. This may be of interest when Arthur's
  mathcomp/deriving machinery does not apply, and is probably stylistically bad
  mathcomp, but at least it works.

  Much boilerplate comes not from the definition of the group structure proper,
  but rather its prerequisites: eqType, choiceType, countType, and finally
  finType. See the construction of ordinal_finMixin in ssreflect/fintype for
  reference. *)

  Inductive Z2 := z | o.
  Definition add (x y : Z2) : Z2 :=
    match x, y with
    | z, z => z
    | z, o => o
    | o, z => o
    | o, o => z
    end.
  Definition inv x : Z2 := x.

  Definition Z2_test (u v : Z2) : bool :=
    match u, v with z, z | o, o => true | _, _ => false end.
  Definition Z2_eq : rel Z2 := Z2_test.
  Definition Z2_eqP : Equality.axiom Z2_eq :=
    ltac:(move => [|] [|];
            try solve [ right ; discriminate ];
            try solve [ left ; reflexivity ]).
(*
  Definition Z2_eqMixin := EqMixin Z2_eqP.
  Canonical Z2_eqType : eqType :=
    Eval hnf in EqType Z2 Z2_eqMixin.
*)
  Definition Z2_hasDecEq := hasDecEq.Build Z2 Z2_eqP.
  HB.instance Definition _ := Z2_hasDecEq.

  Definition Z2_pickle x : nat := match x with z => 0 | o => 1 end.
  Definition Z2_unpickle (x : nat) := match x with 0 => Some z | 1 => Some o | _ => None end.
  Lemma Z2_p_u_cancel : @pcancel nat Z2 Z2_pickle Z2_unpickle.
  Proof. move => [|] //. Qed.

  (*
  Definition Z2_choiceMixin := PcanChoiceMixin Z2_p_u_cancel.
  Canonical Z2_choiceType := ChoiceType Z2 Z2_choiceMixin.
   *)
  HB.instance Definition _ := Choice.copy Z2 (pcan_type Z2_p_u_cancel).

  (*
  Definition Z2_countMixin := @choice.Countable.Mixin Z2 Z2_pickle Z2_unpickle Z2_p_u_cancel.
  Canonical Z2_countType := Eval hnf in CountType Z2 Z2_countMixin.
   *)
  Definition Z2_hasCountable := isCountable.Build Z2 Z2_p_u_cancel.
  HB.instance Definition _ := Z2_hasCountable.

  Definition Z2_enum : seq Z2 := [:: z; o].
  Lemma Z2_enum_uniq : uniq Z2_enum.
  Proof. reflexivity. Qed.
  Lemma mem_Z2_enum i : i \in Z2_enum.
  Proof. destruct i; reflexivity. Qed.

  (*
  Definition Z2_finMixin :=
    Eval hnf in UniqFinMixin Z2_enum_uniq mem_Z2_enum.
  Canonical Z2_finType := Eval hnf in FinType Z2 Z2_finMixin.
   *)
  Definition Z2_isFinite := isFinite.Build Z2 (Finite.uniq_enumP Z2_enum_uniq mem_Z2_enum).
  HB.instance Definition _ := Z2_isFinite.

  Lemma assoc_add : associative add.
  Proof. move => [|] [|] [|] //. Qed.
  Lemma lid : left_id z add.
  Proof. move => [|] //. Qed.
  Lemma inv_inv : involutive inv.
  Proof. move => [|] //. Qed.
  Lemma Z2_invgM : {morph inv : a b / add a b >-> add b a}.
  Proof. move => [|] [|] //. Qed.

  (*
  Definition Z2_finGroupBaseMixin :=
    FinGroup.BaseMixin assoc_add lid inv_inv Z2_invgM.

  Canonical Z2_BaseFinGroupType :=
    BaseFinGroupType Z2 Z2_finGroupBaseMixin.
   *)

  Definition Z2_isMulBaseGroup := isMulBaseGroup.Build Z2 assoc_add lid inv_inv Z2_invgM.
  HB.instance Definition _ := Z2_isMulBaseGroup.

  Definition linv : left_inverse z inv add.
  Proof. move => [|] //. Qed.

  (*
  Canonical Z2_finGroup : finGroupType := FinGroupType linv.
   *)

  Definition Z2_BaseFinGroup_isGroup := BaseFinGroup_isGroup.Build Z2 linv.
  HB.instance Definition _ := Z2_BaseFinGroup_isGroup.

End Z2_manual.


Module Z2_bool.
  (* Semi-pedestrian approach to Z2 on the booleans. Most prerequisite
     structures already exist in the mathcomp library. *)
  Definition addb := xorb.

  Definition invb x : bool := x.
  Lemma assoc_addb : associative addb.
  Proof. move => [|] [|] [|] //. Qed.
  Lemma lidb : left_id false addb.
  Proof. move => [|] //. Qed.
  Lemma inv_invb : involutive invb.
  Proof. move => [|] //. Qed.
  Lemma bool_invgM : {morph invb : a b / addb a b >-> addb b a}.
  Proof. move => [|] [|] //. Qed.

  (*
  Definition bool_finGroupBaseMixin :=
    FinGroup.BaseMixin assoc_addb lidb inv_invb bool_invgM.

  Canonical bool_BaseFinGroupType :=
    BaseFinGroupType bool bool_finGroupBaseMixin.
   *)

  Definition bool_isMulBaseGroup := isMulBaseGroup.Build bool assoc_addb lidb inv_invb bool_invgM.
  HB.instance Definition _ := bool_isMulBaseGroup.

  Definition linvb : left_inverse false invb addb.
  Proof. move => [|] //. Qed.

  (*
  Canonical bool_finGroup : finGroupType := FinGroupType linvb.
   *)

  Definition bool_BaseFinGroup_isGroup := BaseFinGroup_isGroup.Build bool linvb.
  HB.instance Definition _ := bool_BaseFinGroup_isGroup.

End Z2_bool.

(* TODO
Section Z3_deriving.
  (* Construction of Z3 using deriving but not the fingroup mixin. *)
  Inductive Z3 := z | o | t.

  Definition Z3_indDef := [indDef for Z3_rect].
  Canonical Z3_indType := IndType Z3 Z3_indDef.
  Definition Z3_eqMixin := [derive eqMixin for Z3].
  Canonical Z3_eqType := EqType Z3 Z3_eqMixin.
  Definition Z3_choiceMixin := [derive choiceMixin for Z3].
  Canonical Z3_choiceType := ChoiceType Z3 Z3_choiceMixin.
  Definition Z3_countMixin := [derive countMixin for Z3].
  Canonical Z3_countType := CountType Z3 Z3_countMixin.
  Definition Z3_finMixin := [derive finMixin for Z3].
  Canonical Z3_finType := FinType Z3 Z3_finMixin.

  Definition add (x y : Z3) : Z3 :=
    match x, y with
    | z, _ => y
    | _, z => x
    | o, o => t
    | o, t
    | t, o => z
    | t, t => o
    end.

  Definition inv x : Z3 := match x with o => t | t => o | z => z end.
  Lemma assoc_add : associative add.
  Proof. move => [||] [||] [||] //. Qed.
  Lemma lid : left_id z add.
  Proof. move => [||] //. Qed.
  Lemma inv_inv : involutive inv.
  Proof. move => [||] //. Qed.
  Lemma Z3_invgM : {morph inv : a b / add a b >-> add b a}.
  Proof. move => [||] [||] //. Qed.

  Definition Z3_finGroupBaseMixin :=
    FinGroup.BaseMixin assoc_add lid inv_inv Z3_invgM.

  Canonical Z3_BaseFinGroupType := BaseFinGroupType Z3 Z3_finGroupBaseMixin.
  Definition linv : left_inverse z inv add.
  Proof. move => [||] //. Qed.

  Canonical Z3_finGroup : finGroupType := FinGroupType linv.
End Z3_deriving.
*)

(* TODO Is this still needed? - Update or delete.
Module Z2.
  (* Minimal (?) construction of Z2 using the fingroup mixin. *)
  Definition invb x : bool := x.
  Fact assoc_xorb : associative xorb.
  Proof. move => [|] [|] [|] //. Qed.
  Fact lidb : left_id false xorb.
  Proof. move => [|] //. Qed.
  Fact linvb : left_inverse false invb xorb.
  Proof. move => [|] //. Qed.
  Canonical bool_finGroup := BaseFinGroupType _ (FinGroup.Mixin assoc_xorb lidb linvb).
  Canonical Z2_finGroup : finGroupType := FinGroupType linvb.
End Z2.
*)

(* TODO
Module Z3.
  (* Z3 using the fingroup mixin and deriving. *)
  Inductive Z3 := z | o | t.

  Definition Z3_indDef := [indDef for Z3_rect].
  Canonical Z3_indType := IndType Z3 Z3_indDef.
  Definition Z3_eqMixin := [derive eqMixin for Z3].
  Canonical Z3_eqType := EqType Z3 Z3_eqMixin.
  Definition Z3_choiceMixin := [derive choiceMixin for Z3].
  Canonical Z3_choiceType := ChoiceType Z3 Z3_choiceMixin.
  Definition Z3_countMixin := [derive countMixin for Z3].
  Canonical Z3_countType := CountType Z3 Z3_countMixin.
  Definition Z3_finMixin := [derive finMixin for Z3].
  Canonical Z3_finType := FinType Z3 Z3_finMixin.

  Definition add (x y : Z3) : Z3 :=
    match x, y with
    | z, _ => y
    | _, z => x
    | o, o => t
    | o, t
    | t, o => z
    | t, t => o
    end.
  Definition inv x : Z3 := match x with o => t | t => o | z => z end.
  Lemma assoc_add : associative add.
  Proof. move => [||] [||] [||] //. Qed.
  Lemma lid : left_id z add.
  Proof. move => [||] //. Qed.
  Lemma linv : left_inverse z inv add.
  Proof. move => [||] //. Qed.

  Canonical Z3_BaseFinGroupType := BaseFinGroupType _ (FinGroup.Mixin assoc_add lid linv).
  Canonical Z3_finGroup : finGroupType := FinGroupType linv.
End Z3.
*)
