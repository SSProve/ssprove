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
  Definition Z2_hasDecEq := hasDecEq.Build Z2 Z2_eqP.
  HB.instance Definition _ := Z2_hasDecEq.

  Definition Z2_pickle x : nat := match x with z => 0 | o => 1 end.
  Definition Z2_unpickle (x : nat) := match x with 0 => Some z | 1 => Some o | _ => None end.
  Lemma Z2_p_u_cancel : @pcancel nat Z2 Z2_pickle Z2_unpickle.
  Proof. move => [|] //. Qed.

  HB.instance Definition _ := Choice.copy Z2 (pcan_type Z2_p_u_cancel).

  Definition Z2_hasCountable := isCountable.Build Z2 Z2_p_u_cancel.
  HB.instance Definition _ := Z2_hasCountable.

  Definition Z2_enum : seq Z2 := [:: z; o].
  Lemma Z2_enum_uniq : uniq Z2_enum.
  Proof. reflexivity. Qed.
  Lemma mem_Z2_enum i : i \in Z2_enum.
  Proof. destruct i; reflexivity. Qed.

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

  Definition Z2_isMulBaseGroup := isMulBaseGroup.Build Z2 assoc_add lid inv_inv Z2_invgM.
  HB.instance Definition _ := Z2_isMulBaseGroup.

  Definition linv : left_inverse z inv add.
  Proof. move => [|] //. Qed.

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

  Definition bool_isMulBaseGroup := isMulBaseGroup.Build bool assoc_addb lidb inv_invb bool_invgM.
  HB.instance Definition _ := bool_isMulBaseGroup.

  Definition linvb : left_inverse false invb addb.
  Proof. move => [|] //. Qed.

  Definition bool_BaseFinGroup_isGroup := BaseFinGroup_isGroup.Build bool linvb.
  HB.instance Definition _ := bool_BaseFinGroup_isGroup.

End Z2_bool.

(* TODO
Section Z3_deriving.
  (* Construction of Z3 using deriving but not the fingroup mixin. *)
  Inductive Z3 := z | o | t.

  Definition Z3_indDef := [indDef for Z3_rect].
  Canonical Z3_indType := IndType Z3 Z3_indDef.
  Definition Z3_eqMixin := [derive hasDecEq for Z3].
  HB.instance Definition _ := Z3_eqMixin.
  Definition Z3_choiceMixin := [derive hasChoice for Z3].
  HB.instance Definition _ := Z3_choiceMixin.
  Definition Z3_countMixin := [derive isCountable for Z3].
  HB.instance Definition _ := Z3_countMixin.
  (* This does not work properly. Please check the output. *)
  Definition Z3_finMixin := [derive isFinite for Z3].

  (* Manual construction *)
  Definition Z3_enum : seq Z3 := [:: z; o; t].
  Lemma Z3_enum_uniq : uniq Z3_enum.
  Proof. reflexivity. Qed.
  Lemma mem_Z3_enum i : i \in Z3_enum.
  Proof. destruct i; reflexivity. Qed.
  Definition Z3_isFinite := isFinite.Build Z3 (Finite.uniq_enumP Z3_enum_uniq mem_Z3_enum).
  HB.instance Definition _ := Z3_isFinite.

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

  Definition Z3_finGroupBaseMixin := isMulBaseGroup.Build Z3 assoc_add lid inv_inv Z3_invgM.

  HB.instance Definition _ := Z3_finGroupBaseMixin.
  Definition linv : left_inverse z inv add.
  Proof. move => [||] //. Qed.

  Definition Z3_finGroup := BaseFinGroup_isGroup.Build Z3 linv.
  HB.instance Definition _ := Z3_finGroup.
End Z3_deriving.
*)
