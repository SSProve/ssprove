(******************************************************************************)
(*                t-Strong Diffie Hellmann (t-SDH)                            *)
(*                                                                            *)
(*  For more details, see the ./README.md.                                    *)
(******************************************************************************)

From SSProve.Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  Package Prelude pkg_composition.

From Stdlib Require Import Utf8 Lia.
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

#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.

Module Type GroupParam.

  Parameter gT : finGroupType.
  Definition ζ : {set gT} := [set : gT].
  Parameter g :  gT.
  Parameter g_gen : ζ = <[g]>.
  Parameter prime_order : prime #[g].
  Parameter positive_order : Positive #[g].
  Parameter order_gr_two : (#[g] > 2)%N.

  Parameter t : nat.

End GroupParam.


Module tSDH (GP : GroupParam).

  Import GP.

  Definition set_up := 0%N.
  Definition guess := 1%N.

  Definition GroupSpace : finType := gT.
  #[local] Instance GroupSpace_pos : Positive #|GroupSpace|.
  Proof.
    apply /card_gt0P; by exists g.
  Defined.

  #[local] Instance order_pos : Positive #[g].
  Proof.
    by rewrite /Positive.
  Qed.

  Definition chGroup : choice_type := 'fin #|GroupSpace|.
  Definition chList := chMap 'nat chGroup.

  Notation " 'list " := (chList) (in custom pack_type at level 2).
  Notation " 'list " := (chList) (at level 2): package_scope.

  Definition order_g_ring := (Zp_trunc (pdiv #[g])).+2.
  Definition elem_Zp := 'fin order_g_ring.

  Lemma eq_order_g_ring : order_g_ring = #[g].
  Proof.
    unfold order_g_ring. unfold Zp_trunc.
    move: prime_order => H.
    apply pdiv_id in H. rewrite H.
    move: order_gr_two => Hg.
    destruct #[g]; try discriminate.
    destruct n; try discriminate.
    simpl. reflexivity.
  Qed.

  Definition i_space := order_g_ring.
  Definition chExp : choice_type := 'fin order_g_ring.

  Notation " 'group " := (chGroup) (in custom pack_type at level 2).
  Notation " 'exp " := (chExp) (in custom pack_type at level 2).

  Definition make_pk (g : GroupSpace) (a : nat) :=
  [seq fto (g^+(a ^ t)) | t <- iota 0 (t+1)].

  #[program] Definition mod_p (a: nat): chExp :=
  @Ordinal _ (a %% #[g]) _.
  Next Obligation.
    rewrite eq_order_g_ring. rewrite ltn_mod. 
    move : order_gr_two => order_gr_two. auto.
    Qed.

  Definition inv_sum (c a : chExp) : nat :=
    1 / (mod_p (c + a)).

  Definition secret_loc : Location := (33, chExp).

  Definition tSDH_loc := [fmap secret_loc ].

  Definition tSDH_E := [
        interface 
            #val #[ set_up ] : 'unit → 'list ;
            #val #[ guess ] : 'exp × 'group → 'bool
  ].

  Definition tSDH_tt :
    package [interface] tSDH_E :=
      [package tSDH_loc;
        #def #[ set_up ] (_: 'unit) : 'list
        {
          a ← sample uniform i_space ;;
          #put secret_loc := a ;;
          let instc := make_pk g a in
          ret (fmap_of_seq instc)
        } ;

        #def #[ guess ] ('(c, g') : ('exp × 'group)) : 'bool
        {
          a ← get secret_loc ;;
          let exp_g := inv_sum c a in
          ret (fto (g ^+ exp_g) == g')
        }
      ].
  
  Definition tSDH_ff :
  package [interface] tSDH_E :=
    [package tSDH_loc;
      #def #[ set_up ] (_: 'unit) : 'list
      {
        a ← sample uniform i_space ;;
        #put secret_loc := a ;;
        let instc := make_pk g a in
        ret (fmap_of_seq instc)
      } ;

      #def #[ guess ] ('(c, g') : ('exp × 'group)) : 'bool
      {
        ret (false)
      }
    ].

    Definition tSDH b : game tSDH_E :=
      if b then tSDH_tt else tSDH_ff.
    
    Definition ϵ_tSDH := Advantage tSDH.

End tSDH.