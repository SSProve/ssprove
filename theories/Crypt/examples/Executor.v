
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl
  Package Prelude RandomOracle.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

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

  Context (sample : ∀ (e : chUniverse), nat → option (nat * e)).

  Inductive NatState :=
  | NSUnit
  | NSMap
  | NSNat (n : nat)
  | NSOption (A : option NatState)
  | NSProd (A B : NatState).

  Equations? nat_ch (x : NatState) (l : chUniverse) : option (Value l) :=
    nat_ch (NSUnit) 'unit := Some Datatypes.tt ;
    nat_ch (NSNat n) 'nat := Some n ;
    nat_ch (NSNat n) 'bool := Some (Nat.odd n) ;
    nat_ch (NSNat n) 'fin n' := Some _ ;
    nat_ch (NSOption (Some a)) ('option l) := Some (nat_ch a l) ;
    nat_ch (NSOption None) ('option l) := Some None ;
    nat_ch (NSProd a b) (l1 × l2) with (nat_ch a l1, nat_ch b l2) := {
         nat_ch (NSProd a b) (l1 × l2) (Some v1, Some v2) := Some (v1, v2) ;
         nat_ch (NSProd a b) (l1 × l2) _ := None ;
      } ;
    nat_ch _ _ := None.
  Proof.
    - eapply @Ordinal.
      instantiate (1 := n %% n').
      apply ltn_pmod.
      apply cond_pos0.
  Defined.

  Equations ch_nat (l : chUniverse) (v : l) : NatState :=
    ch_nat 'unit v := NSUnit ;
    ch_nat 'nat v := NSNat v ;
    ch_nat 'bool v := NSNat v ;
    ch_nat 'fin n v := NSNat v ;
    ch_nat (l1 × l2) (pair v1 v2) := NSProd (ch_nat l1 v1) (ch_nat l2 v2) ;
    ch_nat 'option l (Some v) := NSOption (Some (ch_nat l v)) ;
    ch_nat 'option l None := NSOption None ;
    ch_nat _ v := NSMap.

  Compute (nat_ch (ch_nat 'unit Datatypes.tt) 'unit).
  Lemma ch_nat_ch l v:
    let r := nat_ch (ch_nat l v) l in
    if (isSome r) then
      r = Some v
    else true.
  Proof.
    induction l.
    - rewrite ch_nat_equation_1.
      rewrite nat_ch_equation_1.
      by destruct v.
    - rewrite ch_nat_equation_2.
      rewrite nat_ch_equation_10.
      reflexivity.
    - rewrite ch_nat_equation_3.
      rewrite nat_ch_equation_11.
      destruct v ; reflexivity.
    - destruct v.
      rewrite ch_nat_equation_4.
      rewrite nat_ch_equation_33.
      specialize (IHl1 s).
      specialize (IHl2 s0).
  Admitted.

  Definition new_state
             (st : Location → NatState) (l : Location) (v : l) : (Location → NatState)
    :=
    fun (l' : Location) =>
      if l.π2 == l'.π2
      then (ch_nat l v)
      else st l'.

  Fixpoint Run_aux {A : choiceType}
           (c : raw_code A) (seed : nat) (st : Location → NatState)
    : option A :=
    match c with
      ret x => Some x
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
    (fun c seed => @Run_aux A c seed (fun (l : Location) => NSUnit)).

End Executor.

#[program] Fixpoint sampler (e : chUniverse) seed : option (nat * e):=
  match e with
    chUnit => Some (seed, Datatypes.tt)
  | chNat => Some ((seed + 1)%N, seed)
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
  end.
Next Obligation.
  eapply Ordinal.
  instantiate (1 := (seed %% n)%N).
  rewrite ltn_mod.
  apply n.
Defined.

Section Test.

  Definition loc : Location :=  ('nat ; 1)%N.
  Definition locs : {fset Location} := fset [:: loc].

  Definition test_prog_sub (x : nat):
    code fset0 [interface] 'nat :=
    {code
       k ← sample uniform 20 ;;
       let y := (x + k)%N in
       ret y
    }.

  #[program] Definition test_prog (x : nat):
    code locs [interface] 'nat :=
    {code
       k ← test_prog_sub x ;;
       put loc := k ;;
       k' ← get loc ;;
       ret k'
    }.
  Next Obligation.
    ssprove_valid.
  Defined.

  Compute (Run sampler (test_prog 2) 54).

  Lemma interpretation_test1:
    ∀ seed input,
      (Run sampler (test_prog input) seed) = Some (input + seed %% 20)%N.
  Proof.
    done.
  Qed.

  Definition E :=
    [interface
       val #[ 0 ] : 'nat → 'nat
    ].

  Definition test_pack:
    package locs [interface] E :=
    [package
       def #[ 0 ] (x : 'nat) : 'nat
       {
         k ← sample uniform 20 ;;
         let y := (x + k)%N in
         put loc := y ;;
         y' ← get loc ;;
         ret y'
       }
    ].

End Test.
