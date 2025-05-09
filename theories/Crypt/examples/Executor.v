From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

From Coq Require Import ZArith.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl
  Package Prelude RandomOracle.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

(* From Jasmin Require Import word. *)
From SSProve.Crypt Require Import jasmin_word.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

Section Executor.

  Context (sample : ∀ (e : choice_type), nat → option (nat * e)).

  Inductive NatState :=
  | NSUnit
  | NSNat (n : nat)
  | NSOption (A : option NatState)
  | NSProd (A B : NatState).

  Equations? nat_ch_aux (x : NatState) (l : choice_type) : option (Value l) :=
    nat_ch_aux (NSUnit) 'unit := Some tt ;
    nat_ch_aux (NSNat n) 'nat := Some n ;
    nat_ch_aux (NSNat n) 'bool := Some (Nat.odd n) ;
    nat_ch_aux (NSNat n) 'fin n' := Some _ ;
    nat_ch_aux (NSOption (Some a)) ('option l) := Some (nat_ch_aux a l) ;
    nat_ch_aux (NSOption None) ('option l) := Some None ;
    nat_ch_aux (NSProd a b) (l1 × l2) with (nat_ch_aux a l1, nat_ch_aux b l2) := {
         nat_ch_aux (NSProd a b) (l1 × l2) (Some v1, Some v2) := Some (v1, v2) ;
         nat_ch_aux (NSProd a b) (l1 × l2) _ := None ;
      } ;
    nat_ch_aux (NSNat n) ('word u) := Some _ ;
    nat_ch_aux _ _ := None.
  Proof.
    - eapply @Ordinal.
      instantiate (1 := n %% n').
      apply ltn_pmod.
      apply cond_pos0.
    - apply wrepr.
      apply (BinInt.Z.of_nat n).
  Defined.

  Definition nat_ch (x : option NatState) (l : choice_type) : option (Value l) :=
    match x with
    | Some v => nat_ch_aux v l
    | None => None
    end.

  Equations ch_nat (l : choice_type) (v : l) : option NatState :=
    ch_nat 'unit v := Some NSUnit ;
    ch_nat 'nat v := Some (NSNat v) ;
    ch_nat 'bool v := Some (NSNat v) ;
    ch_nat 'fin n v := Some (NSNat v) ;
    ch_nat (l1 × l2) (pair v1 v2) :=
      match (ch_nat l1 v1, ch_nat l2 v2) with
        | (Some v, Some v') => Some (NSProd v v')
        | _ => None
      end ;
    ch_nat 'option l (Some v) :=
      match (ch_nat l v) with
        | Some v' => Some (NSOption (Some v'))
        | _ => None
      end ;
    ch_nat 'option l None := Some (NSOption None) ;
    ch_nat 'word u x := Some (NSNat (BinInt.Z.to_nat (wunsigned x))) ;
    ch_nat _ _ := None.

  Lemma ch_nat_ch l v:
    match (ch_nat l v) with
      | Some k => nat_ch (Some k) l = Some v
      | _ => true
    end.
  Proof.
    funelim (ch_nat l v). all: try easy.
    - simpl. by destruct v.
    - simp ch_nat. simpl. simp nat_ch_aux. by destruct v.
    - simp ch_nat. destruct (ch_nat l1 v1), (ch_nat l2 v2); try easy.
      cbn. simp nat_ch_aux. simpl in *. now rewrite H H0.
    - simp ch_nat. destruct ch_nat; try easy.
      simpl in *. simp nat_ch_aux. now f_equal.
    - simp ch_nat. simpl. simp nat_ch_aux.
      f_equal.
      unfold nat_ch_aux_obligation_1.
      have lv := ltn_ord v.
      apply /eqP.
      erewrite <- inj_eq.
      2: apply ord_inj.
      simpl.
      rewrite modn_small.
      2: assumption.
      done.
    - simp ch_nat. simpl. simp nat_ch_aux.
      f_equal.
      unfold nat_ch_aux_obligation_2.
      rewrite @Znat.Z2Nat.id.
      + rewrite wrepr_unsigned.
        reflexivity.
      + apply (@wunsigned_range u).
  Qed.

  Definition new_state
             (st : Location → option NatState) (l : Location) (v : l) : (Location → option NatState)
    :=
    fun (l' : Location) =>
      if l.1 == l'.1
      then (ch_nat l v)
      else st l'.

  (* I don't understand why it's needed again. *)
  Import pkg_core_definition.

  Fixpoint Run_aux {A : choiceType}
           (c : raw_code A) (seed : nat) (st : Location → option NatState)
    : option A :=
    match c with
    | ret x => Some x
    | sampler o k =>
        match sample (projT1 o) seed with
        | Some (seed', x) => Run_aux (k x) seed' st
        | _ => None
        end
    | opr o x k => None (* Calls should be inlined before we can run the program *)
    | putr l v k => Run_aux k seed (new_state st l v)
    | getr l k =>
        match nat_ch (st l) l with
          | Some v => Run_aux (k v) seed st
          | None => None
        end
    end.

  Definition Run {A} :=
    (fun c seed => @Run_aux A c seed (fun (l : Location) => Some NSUnit)).

End Executor.

#[program] Fixpoint sampler (e : choice_type) (seed : nat) : option (nat * e):=
  match e with
    chUnit => Some (seed, tt)
  | chNat => Some ((seed + 1)%N, seed)
  | chInt => Some ((seed + 1)%nat, BinInt.Z.of_nat seed) (* FIXME: also generate negative numbers *)
  | chBool => Some ((seed + 1)%N, Nat.even seed)
  | chProd A B =>
      match sampler A seed with
      | Some (seed' , x) => match sampler B seed' with
                           | Some (seed'', y) => Some (seed'', (x, y))
                           | _ => None
                           end
      | _ => None
      end
  | chMap A B => None
  | chOption A =>
      match sampler A seed with
      | Some (seed', x) => Some (seed', Some x)
      | _ => None
      end
  | chFin n => Some ((seed + 1)%N, _)
  | chWord n => Some ((seed + 1)%N, _)
  | chList A =>
      match sampler A seed with
      | Some (seed', x) => Some (seed', [:: x])
      | _ => None
      end
  | chSum A B =>
      let '(seed', b) := ((seed + 1)%nat, Nat.even seed) in
      if b
      then
        match sampler A seed' with
        | Some (seed'' , x) => Some (seed'', inl x)
        | _ => None
        end
      else
        match sampler B seed' with
        | Some (seed'' , y) => Some (seed'', inr y)
        | _ => None
        end
  end.
Next Obligation.
  eapply Ordinal.
  instantiate (1 := (seed %% n)%N).
  rewrite ltn_mod.
  apply n.
Defined.
Local Open Scope Z_scope.
Next Obligation.
  eapply word.mkWord.
  instantiate (1 := ((Z.of_nat  seed) mod (word.modulus (nat_of_wsize n) ))%Z).
  pose (Z.mod_bound_pos (Z.of_nat seed) (word.modulus n)
        (Zle_0_nat seed)).
  pose (word.modulus_gt0 (nat_of_wsize n)).
  apply / word.iswordZP.
  apply a.
  move : i => / word_ssrZ.ltzP.
  auto.
Defined.
Close Scope Z_scope.

Section Test.

  Definition loc : Location :=  (1, 'nat).
  Definition locs : Locations := [fmap loc].

  Definition test_prog_sub (x : nat):
    code emptym [interface] 'nat :=
    {code
       k ← sample uniform 20 ;;
       let y := (x + k)%N in
       ret y
    }.

  #[program] Definition test_prog (x : nat):
    code locs [interface] 'nat :=
    {code
       k ← test_prog_sub x ;;
       #put loc := k ;;
       k' ← get loc ;;
       ret k'
    }.
  Next Obligation.
    ssprove_valid.
  Defined.

  (* Compute (Run sampler (test_prog 2) 54). *)

  Lemma interpretation_test1:
    ∀ seed input,
      (Run sampler (test_prog input) seed) = Some (input + seed %% 20)%N.
  Proof.
    done.
  Qed.

  Definition E :=
    [interface
      #val #[ 0 ] : 'nat → 'nat
    ].

  Definition test_pack:
    package [interface] E :=
    [package locs ;
      #def #[ 0 ] (x : 'nat) : 'nat
      {
        k ← sample uniform 20 ;;
        let y := (x + k)%N in
        #put loc := y ;;
        y' ← get loc ;;
        ret y'
      }
    ].

End Test.
