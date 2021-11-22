(*
   Inspired to "State Separation for Code-Based Game-Playing Proofs" - Brzuska et al.

   Appendix A.

   "Given a pseudorandom function (PRF) we construct a symmetric encryption scheme
    that is indistinguishable under chosen plaintext attacks (IND-CPA). "

*)

(* Rem.: TODO In the SSEP paper packages return (r,c) we only return c *)

From Relational Require Import
     OrderEnrichedCategory
     GenericRulesSimple.
From mathcomp Require Import
     all_ssreflect
     all_algebra
     reals
     distr
     realsum.
From Crypt Require Import
     Axioms
     ChoiceAsOrd
     SubDistr
     Couplings
     UniformDistrLemmas
     FreeProbProg
     Theta_dens
     RulesStateProb
     StdDistr.
From Crypt Require Import
     pkg_core_definition
     chUniverse
     pkg_composition
     pkg_rhl
     Package
     Prelude
     pkg_notation.

From Crypt Require Import pkg_notation.

From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.

(* Local Open Scope ring_scope. *)

Module Type SymmetricSchemeParam.

  Parameter Words_N Key_N : nat.
  Parameter Words_N_pos : Positive Words_N.
  Parameter Key_N_pos : Positive Key_N.
  Existing Instance Words_N_pos.
  Existing Instance Key_N_pos.
  Definition Words := (chFin (mkpos Words_N)).
  Definition Key := chFin (mkpos Key_N).
  Parameter plus : Words -> Key -> Words.
  Notation "m ⊕ k" := (plus m k) (at level 70).
  Parameter plus_involutive : forall m k, (m ⊕ k) ⊕ k = m.

End SymmetricSchemeParam.

(* Symmetric Schemes *)
Module Type SymmetricSchemeRules (π : SymmetricSchemeParam).

  Import π.
  Inductive probEmpty : Type -> Type := .

  Module genparam <: RulesParam.

    Definition probE : Type -> Type := probEmpty.
    Definition chUniverse : Type := void.
    Definition chElement : chUniverse -> choiceType.
    Proof. move => v. inversion v. Defined.
    Definition prob_handler : forall T : choiceType, probE T -> SDistr T.
    Proof. move => T v. inversion v. Defined.
    Definition Hch : forall r : chUniverse, chElement r.
    Proof. move => v. inversion v. Defined.

  End genparam.

  Module MyRules := DerivedRulesUniform genparam.

End SymmetricSchemeRules.

(* Rem.: EXPERIMENT with current chUniverse

   TODO:
   + conclude proof of the lemma
   -> Values? (currently using "encodings" X2val and val2X)
  *)

Module PRF_example.

  Parameter n : nat.

  Module π <: SymmetricSchemeParam.

    Definition Words_N : nat := 2^n.
    Definition Words_N_pos : Positive Words_N := _.
    Definition Words : chUniverse := chFin (mkpos Words_N).
    Definition Key_N : nat := 2^n.
    Definition Key_N_pos : Positive Key_N := _.
    Definition Key : chUniverse := chFin (mkpos Key_N).
    Definition plus : Words -> Key -> Words. Admitted.  (* := xorb. *)
    Notation "m ⊕ k" := (plus m k) (at level 70).
    Lemma plus_involutive : forall m k, (m ⊕ k) ⊕ k = m. Admitted.
    (* Proof. move => m k. by destruct m, k. Qed.   *)
  End π.

  Local Open Scope package_scope.

  Import π.
  Include (SymmetricSchemeRules π).
  Include (Package_Make MyRules.myparamU).

  Module MyPackage := Package_Make (MyRules.myparamU).
  Import MyPackage.

  Definition key_location : Location := (Key; 0).
  Definition plain_location : Location := (Words; 1).
  Definition cipher_location : Location := (Words; 2).
  Definition i0 : nat := 3.
  Definition i1 : nat := 4.
  Definition i2 : nat := 5.
  Definition salt_location : Location := (chNat; 6).
  Definition table_location : Location := (chMap chNat ('fin (2^n)%N); 7).

  Definition rel_loc : {fset Location} :=
    fset [:: key_location; plain_location; cipher_location; salt_location; table_location].
  (* Rem.: i0;  i1; i2 ; -> only memory locations should belong here, not program entries/package oracles *)


  (* Parameter PRF : forall (r: Words) (k : Key), raw_code Key. *)
  (* Parameter PRF_valid : forall r k, ValidCode rel_loc fset0 (PRF r k). *)
  Parameter PRF : Words -> Key -> Key.
  Parameter prf_epsilon : R.

  Definition U (i : positive) : {rchT : MyRules.myparamU.chUniverse & MyRules.myparamU.probE (MyRules.myparamU.chElement rchT)} :=
    (existT (λ rchT : MyRules.myparamU.chUniverse, MyRules.myparamU.probE (MyRules.myparamU.chElement rchT))
            (chFin i) (inl (MyRules.Unif_Fin i))).
  Obligation Tactic := package_obtac.

  Notation " 'chWords' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Notation " 'chKey' " := ('fin (2^n)%N) (in custom pack_type at level 2).
  Definition i_key : nat := 2^n.
  Definition i_words : nat := 2^n.

   #[program] Definition EVAL_opkg_tt : opackage rel_loc [interface] [interface val #[i0] : chWords → chKey ] :=
   [package def #[i0] ( r : chWords) : chKey
   {
     k_init ← get key_location ;;
     match  k_init with
     | None  =>
         k <$ (U (mkpos i_key)) ;;
         put key_location := k ;;
         ret (PRF r k)
     |  Some k_val => ret (PRF r (k_val))
     end
   }
   ].

   (* (* Rem.: this shouldn't belong here, but everything is so convoluted... *) *)
   (* Definition _assert (L : {fset Location}) (I : Interface) (b : bool) : code L I chUnit. *)
   (*   unfold program. *)
   (*   destruct b. *)
   (*   - exact (ret Datatypes.tt). *)
   (*   - unshelve eexists (_sampler _ _). *)
   (*     { unfold Op. hnf. *)
   (*       exists chUnit. *)
   (*       left. apply MyRules.Fail_Unit. } *)
   (*     { intros s. cbn in *. constructor. *)
   (*       exact s. } *)
   (*     cbn. auto. *)
   (* Defined. *)


   (* Notation "'assert' ( b ) ;; c" := *)
   (*   (bind (_assert _ _ b) (λ _, c)) *)
   (*     (at level 100, right associativity, *)
   (*      format "assert  (  b  )  ;;  '/' c") *)
   (*   : package_scope. *)

   (* (* Just an experiment *) *)
   (* #[program] Definition EVAL_opkg_tt_assert : opackage rel_loc [interface] [interface val #[i0] : chWords → chKey ] := *)
   (*   [package def #[i0] ( r : chWords) : chKey *)
   (*                                         { *)
   (*                                           k_init ← get key_location ;; *)
   (*                                           assert (k_init != None) ;; *)
   (*                                           ret (PRF r (val2key (Option.default 0 k_init))) *)
   (*                                         } *)
   (*   ]. *)

  Definition EVAL_pkg_tt : package [interface] [interface val #[i0] : chWords → chKey].
  Proof. exists rel_loc. exact: EVAL_opkg_tt. Defined.

    #[program] Definition EVAL_opkg_ff : opackage rel_loc [interface] [interface val #[i0] : chWords → chKey] :=
   [package def #[i0] ( r : chWords) : chKey
 {
   T ← get table_location or emptym ;; (*Rem.: isn't a bit odd that the table is an option? *)
   (* Rem.: indeed, it's annoying. I've used a default empytm with "or emptym" *)
   match (getm T 0) with
   | None  => T_key <$ (U (mkpos i_key)) ;;
             ret T_key (* Rem.: here's still missing the update to the table? *)
   | Some T_key =>  ret T_key
   end
   }
   ].


  (* #[program] Definition EVAL_opkg_ff : opackage rel_loc [interface] [interface val #[i0] : chWords → chKey] := *)
  (*  [package def #[i0] ( r : chWords) : chKey *)
  (*  { *)
  (*    Tx_init ←  get key_location ;; (* Rem.: not sure this is the right location *) *)
  (*    match Tx_init with *)
  (*        | None  => Tx <$ (U i_key) ;; *)
  (*                   ret Tx *)
  (*        | Some Tx =>  ret (val2key Tx) *)
  (*    end *)
  (*  } *)
  (*  ]. *)

  Definition EVAL_pkg_ff : package [interface] [interface val #[i0] : chWords → chKey].
  Proof. exists rel_loc. exact: EVAL_opkg_ff. Defined.

  Definition EVAL : GamePair  [interface val #[i0] : chWords → chKey] :=
    fun b : bool =>
      if b then EVAL_pkg_tt else EVAL_pkg_ff.

  Let w0 : cipher_location.π1.
    cbn.
  Admitted.

  #[program] Definition ENC_opkg : opackage rel_loc [interface] [interface val #[i2] : chWords × chKey → chWords] :=
    [package def #[i2] ( mk : chWords × chKey) : chWords
             {
               put cipher_location := (fst mk) ⊕ (snd mk) ;;
               c   ← get cipher_location or w0 ;;
               ret c
             }
    ].

  Definition ENC_pkg : package [interface] [interface val #[i2] :  chWords × chKey → chWords].
  Proof. exists rel_loc. exact ENC_opkg. Defined.

 #[program] Definition MOD_CPA_tt : opackage rel_loc [interface val #[i0] : chWords → chKey] [interface val #[i1] : chWords → chWords ] :=
    [package def #[i1] ( m : chWords) : chWords
     {    r <$ (U (mkpos i_words)) ;;
          pad ← op [ #[i0] : chWords → chKey ] r ;;
          put cipher_location := (m ⊕ pad) ;;
          c   ← get cipher_location or w0 ;;
          ret c
      }
    ].


 Definition MOD_CPA_tt_pkg : package  [interface val #[i0] : chWords → chKey] [interface val #[i1] : chWords → chWords ].

  Proof. exists rel_loc. exact:MOD_CPA_tt. Defined.

 #[program] Definition MOD_CPA_ff : opackage rel_loc  [interface val #[i0] : chWords → chKey] [interface val #[i1] : chWords → chWords ]:=
   [package def #[i1] ( m: chWords) : chWords
      {   r  <$ (U (mkpos i_words)) ;;
          m' <$ (U (mkpos i_words)) ;;
          pad ← op [ #[i0] : chWords → chKey ] r ;;
          put cipher_location := (m' ⊕ pad) ;;
          c   ← get cipher_location or w0 ;;
          ret c
      }
   ].

  Definition MOD_CPA_ff_pkg : package  [interface val #[i0] : chWords → chKey] [interface val #[i1] : chWords → chWords ].
  Proof.
    rewrite /package. exists rel_loc. exact:MOD_CPA_ff.
  Defined.

  #[program] Definition IND_CPA_opkg_tt : opackage rel_loc [interface val #[i2] : chWords × chKey → chWords]
                                                           [interface val #[i1] : chWords → chWords ] :=
   [package def #[i1] ( m : chWords ) : chWords
            {
              k ← get key_location ;;
              match k with
                | None => k_val <$ (U (mkpos i_key)) ;;
                          c_val ← op [ #[i2] : chWords × chKey → chWords ] (k_val, m) ;;
                          ret c_val
               | Some k_val => c_val ← op [ #[i2] : chWords × chKey → chWords ] (k_val, m) ;;
                               ret c_val
              end
   } ].

  Definition IND_CPA_pkg_tt : package [interface val #[i2] : chWords × chKey → chWords] [interface val #[i1] : chWords → chWords ].
  Proof. exists rel_loc. exact: IND_CPA_opkg_tt. Defined.


  #[program] Definition IND_CPA_opkg_ff : opackage rel_loc [interface val #[i2] : chWords × chKey → chWords]
                                                           [interface val #[i1] : chWords → chWords ] :=
   [package def #[i1] ( m : chWords ) : chWords
            {
              k ← get key_location ;;
              match k with
                | None => k_val <$ (U (mkpos i_key)) ;;
                          m' <$ (U (mkpos i_words)) ;;
                          c_val ← op [ #[i2] : chWords × chKey → chWords ] (k_val, m') ;;
                          ret c_val
               | Some k_val => m' <$ (U (mkpos i_words)) ;;
                               c_val ← op [ #[i2] : chWords × chKey → chWords ] (k_val, m') ;;
                               ret c_val
              end
   } ].

  Definition IND_CPA_pkg_ff : package [interface val #[i2] : chWords × chKey → chWords] [interface val #[i1] : chWords → chWords ].
  Proof. exists rel_loc. exact: IND_CPA_opkg_ff. Defined.


 Definition IND_CPA : GamePair [interface val #[i1] : chWords → chWords ] :=
   fun b : bool =>
     if b then (link IND_CPA_pkg_tt ENC_pkg)
     else (link IND_CPA_pkg_ff  ENC_pkg).

 Local Open Scope ring_scope.

 Definition PRF_security := forall A {H1} {H2}, (@Advantage _ EVAL A H1 H2) <= prf_epsilon.
 Definition statistical_gap { A } : R := `|Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true|.

Ltac fold_repr :=
  change (repr' ?p ?h) with (repr (exist _ p h)).

Lemma key_location_in_rel_loc : key_location \in rel_loc :|: rel_loc. Admitted.
Lemma cipher_location_in_rel_loc : cipher_location \in rel_loc :|: rel_loc. Admitted.

Lemma perfect_equivalence0 :
  ∀ (A : Adversary4Game [interface val #[i1] : chWords → chWords ])
    { Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) A.π1
                            (IND_CPA false).π1 }
    { Hdisjoint2 : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) A.π1
                            (IND_CPA true).π1 },
    (Pr (A ∘ IND_CPA false) true) =
    (Pr ((A ∘ MOD_CPA_ff_pkg) ∘ (EVAL true)) true).
Proof.
  intros A Hdisjoint1 Hdisjoint2.
  rewrite /IND_CPA.
  rewrite -link_assoc.
  apply: GRing.subr0_eq. apply: normr0_eq0.
  fold (@AdvantageE [interface val #[i1] : chWords → chWords] (IND_CPA_pkg_ff ∘ ENC_pkg) (MOD_CPA_ff_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
  rewrite /IND_CPA_pkg_ff /IND_CPA_opkg_ff /MOD_CPA_ff_pkg /MOD_CPA_ff_pkg /MOD_CPA_ff.
  rewrite (eq_upto_inv_perf_ind' _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
  1,3: auto.
  1:{
    rewrite /=.
    move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
  }
  eq_up_to_inv_simplify.
  (*Rem.: here Coq gets stuck for me! *)
   (* setoid_rewrite code_link_eqmatch_option. *)
  (* Rem.: Now, it looks like something manageable! *)
  simpl injectLocations.
  (******)
  (*Rem.: Is it possible to write a tactic that changes constructors with binds? *)
  rewrite [_ ← sample _ ;; _ ← sample _ ;; _] sampler_bind.
  rewrite [H ← sample _ ;; _ ← sample _ ;; _] sampler_bind.
  rewrite [_ ← get _ ;; _] getr_bind.
  unshelve eapply rrewrite_eqDistrL.
  { apply: bind.
    { apply: getr. { exact : key_location_in_rel_loc. }
      rewrite /= => option_k. apply: ret option_k. }
      move => option_k.
      destruct option_k as [k_val |].
      + apply: bind.
        { apply: (sampler (U (mkpos i_words))) => /= m'. apply: ret m'. }
          move => m'.
          apply: bind.
          { apply: (putr _ cipher_location_in_rel_loc (m' ⊕ k_val)). apply: ret Datatypes.tt. }
          move => tt.
          apply: bind.
          { apply: (getr _ cipher_location_in_rel_loc) => /= c. apply: (ret c). }
          move => /= c.
          destruct c.
        ++ apply: ret o.
        ++ apply: ret w0.
      + apply: bind.
        { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
          move => /= k_val.
          apply: bind.
          { apply: (sampler (U (mkpos i_words))) => /= m'. apply: ret m'. }
          move => m'.
          apply: bind.
          { apply: (putr _ cipher_location_in_rel_loc (m' ⊕ k_val)).  apply: ret Datatypes.tt. }
          move => tt.
          apply: bind.
          { apply: (getr _ cipher_location_in_rel_loc) => /= c. apply: (ret c). }
          move => /= c.
          destruct c.
        ++ apply: ret o.
        ++ apply: ret w0. }
   2: { admit. (*Rem.: not as immediate as expected *) }
  + unshelve eapply rrewrite_eqDistrR.
    { apply: (sampler (U (mkpos i_words))) => /= r.
      apply: bind.
    { apply: getr. { exact : key_location_in_rel_loc. }
      rewrite /= => option_k. apply: ret option_k. }
      move => option_k.
      destruct option_k as [k_val |].
      + apply: bind.
        { apply: (sampler (U (mkpos i_words))) => /= m'. apply: ret m'. }
          move => m'.
          apply: bind.
          { apply: (putr _ cipher_location_in_rel_loc (m' ⊕ k_val)). apply: ret Datatypes.tt. }
          move => tt.
          apply: bind.
          { apply: (getr _ cipher_location_in_rel_loc) => /= c. apply: (ret c). }
          move => /= c.
          destruct c.
        ++ apply: ret o.
        ++ apply: ret w0.
      + apply: bind.
        { apply: (sampler (U (mkpos i_key))) => /= k_val. apply: ret k_val. }
          move => /= k_val.
          apply: bind.
          { apply: (sampler (U (mkpos i_words))) => /= m'. apply: ret m'. }
          move => m'.
          apply: bind.
          { apply: (putr _ cipher_location_in_rel_loc (m' ⊕ k_val)).  apply: ret Datatypes.tt. }
          move => tt.
          apply: bind.
          { apply: (getr _ cipher_location_in_rel_loc) => /= c. apply: (ret c). }
          move => /= c.
          destruct c.
        ++ apply: ret o.
        ++ apply: ret w0. }
  2: { admit. }
  apply: rdead_sampler_eliminationL.
    eapply (rpost_weaken_rule _ (fun as1 as2 => as1 = as2)).
    { exact: rreflexivity_rule. }
   move => [w1 h1] [w2 h2] [Heq1 Heq2]. by subst.
 Admitted.
(*     rewrite /IND_CPA. *)
(*     rewrite -link_assoc. *)
(*     apply: GRing.subr0_eq. apply: normr0_eq0. *)
(*     fold (@AdvantageE [interface val #[i1] : chWords → chWords] (IND_CPA_pkg_ff ∘ ENC_pkg) (MOD_CPA_ff_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2). *)
(*     rewrite (eq_upto_inv_perf_ind _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ). *)
(*     1,3: auto. *)
(*     1:{ *)
(*       rewrite /=. *)
(*       move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2. *)
(*     } *)
(*     rewrite /eq_up_to_inv. move => i chU1 chU2 H p1 p2 h1 hpg1 h2 hpg2 arg. *)
(*     simpl in h1,h2. *)
(*     (* *) *)
(*     have Hi : i = i1 by admit. subst. *)
(*     (* *) *)
(*     unfold i1 in *. *)
(*     rewrite raw_link_trim_commut in h1. *)
(*     subst. *)
(*     apply trim_get_inv in h1. destruct h1 as [h11 h12]. *)
(*     inversion h11 as [[foo1 foo2 Heq]]. *)
(*     subst. *)
(*     repeat (apply Eqdep.EqdepTheory.inj_pair2 in Heq). *)
(*     subst. *)
(*     (* *) *)
(*     (* (*Rem.: the LHS of the judjement has the form { raw_code | ValidCode }  *) *) *)
(*     (* (*       while we want a code to use the Rules *)  *) *)
(*     have key_location_in_rel_loc : key_location \in rel_loc :|: rel_loc. *)
(*     { rewrite in_fsetU. apply /orP. left. package_obtac. } *)
(*     have cipher_location_in_rel_loc : cipher_location \in rel_loc :|: rel_loc. *)
(*     { rewrite in_fsetU. apply /orP. left. package_obtac. } *)
(*     (* (* have i2_in_Game_import : i2 \in Game_import.  *) *) *)
(*     (* have prgL : code (rel_loc :|: rel_loc) Game_import ('fin (2 ^ n)). *) *)
(*     (* { apply: getr. { exact: key_location_in_rel_loc. } *) *)
(*     (*  move => option_k. destruct option_k as [k | k_bot ] eqn:Hk.    *) *)
(*     (*   + apply: (sampler (U i_words)) => /= m'.  *) *)
(*     (*     apply: ret ((val2key k) ⊕ (val2word m')).  *) *)
(*     (*   + apply (sampler (U i_key)) => /= k. *) *)
(*     (*     apply: (sampler (U i_words)) => /= m'.  *) *)
(*     (*     apply: ret ((val2key k) ⊕ (val2word m')). } *) *)

(*     (* rewrite /IND_CPA_pkg_ff.π1. *) *)
(*     (* have hfoo : prgL = *) *)
(*     (*             ((exist (ValidCode (IND_CPA_pkg_ff.π1 :|: ENC_pkg.π1) Game_import) *) *)
(*     (*   (_getr key_location *) *)
(*     (*      (λ x : option nat, *) *)
(*     (*         raw_code_link *) *)
(*     (*           (sval *) *)
(*     (*              (if x == None *) *)
(*     (*               then k_val ← sample U i_key ;; m' ← sample U i_words ;; *) *)
(*     (*               c_val ← op [ #[i2] : chKey × chWords → chWords ] (val2key k_val, val2word m') ;; *) *)
(*     (*               ret (val2word c_val) *) *)
(*     (*               else m' ← sample U i_words ;; *) *)
(*     (*               c_val ← op [ #[i2] : chKey × chWords → chWords ] (val2key x, val2word m') ;; *) *)
(*     (*               ret (val2word c_val))) *) *)
(*     (*           (mapm (T:=nat_ordType) (λ '(So; To; f), (So; To; λ x0 : So, sval (f x0))) *) *)
(*     (*              (setm (T:=nat_ordType) emptym i2 *) *)
(*     (*                 (mkdef ('fin (2 ^ n) × 'fin (2 ^ n)) 'fin (2 ^ n) (λ mk : 'I_(2 ^ n) * 'I_(2 ^ n), ret (mk.1 ⊕ mk.2))))))) *) *)
(*     (*   (hpg1 arg))).           *) *)

(*     (* (* *) *) *)
(*     unfold i1 in *. *)
(*     rewrite raw_link_trim_commut in h2. *)
(*     subst. *)
(*     apply trim_get_inv in h2. destruct h2 as [h21 h22]. *)
(*     inversion h21 as [Heq]. *)
(*     subst. *)
(*     repeat (apply Eqdep.EqdepTheory.inj_pair2 in Heq). *)
(*     subst. *)
(*     (* *) *)
(*     pose Hrefl := (chUniverse_eqP (chFin (2 ^ n)) (chFin (2 ^ n))). *)
(*     pose Hrefl' := (chUniverse_eqP (chProd (chFin (2 ^ n)) (chFin (2 ^ n))) (chProd (chFin (2 ^ n)) (chFin (2 ^ n)))). *)
(*     destruct (chUniverse_eqP (chFin (2 ^ n)) (chFin (2 ^ n))). *)
(*     - destruct (chUniverse_eqP (chProd (chFin (2 ^ n)) (chFin (2 ^ n))) (chProd (chFin (2 ^ n)) (chFin (2 ^ n)))). *)
(*       + clear Hrefl Hrefl' h11 h12 h21 h22 H. *)




(*         unshelve eapply rrewrite_eqDistrR. *)
(*         1:{ *)
(*           rewrite /=. *)
(*           apply (sampler (U i_words)) => /= m'.  *)
(*           apply: getr. { exact: key_location_in_rel_loc. } *)
(*           rewrite /= => option_k. destruct option_k as [k_val | ]. *)
(*            + apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*              apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*              apply: (ret (val2word c)). *)
(*            + apply (sampler (U i_key)) => /= k_val. *)
(*              apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*              apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*              apply: (ret (val2word c)). *)
(*         } *)
(*         2:{ *)
(*           move => s. *)
(*           apply: (rcoupling_eq _ _ (fun '(h1, h2) => h1 = h2)); auto. *)
(*           code fold. *)
(*           Opaque sampler getr putr ret bind. *)
(*           repeat code setoid fold. simpl. *)
(*           unshelve setoid_rewrite fold_bind. *)
(*           { simpl. move => y. split; auto. } *)
(*           (* Here I wanted to use cast_fun_K but it doesn't work *) *)
(*           (* setoid_rewrite cast_fun_K. *) *)
(*           pose proof (Classes.uip e erefl) as ee. subst. *)
(*           change (cast_fun erefl erefl ?f) with f. *)
(*           repeat code setoid fold. *)
(*           eapply (rpost_weaken_rule _ (fun '(x, h1) '(y, h2) =>  x = y /\ h1 = h2)). *)
(*           - (*Rem.: this is a hack, we are trying to "rewrite" more nicely the code by hand *) *)
(*             unshelve eapply rrewrite_eqDistrR.  *)
(*             1:{ *)
(*               apply (sampler (U i_words)) => r'. *)
(*               apply (sampler (U i_words)) => m'. *)
(*               apply: getr. { exact: key_location_in_rel_loc. } *)
(*               rewrite /= => option_k. destruct option_k as [k_val | ]. *)
(*               + apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*                 apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*                 apply: (ret (val2word c)). *)
(*               + apply (sampler (U i_key)) => /= k_val. *)
(*                 apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*                 apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*                 apply: (ret (val2word c)). *)
(*             } *)
(*             1:{ *)
(*               (* now the two codes differ in some dead code in the RHS *) *)
(*               simpl. *)
(*               apply: rdead_sampler_eliminationL. *)
(*               apply: (rpost_weaken_rule _ eq). *)
(*               + exact: rreflexivity_rule. *)
(*               + move => [a1 s1] [a2 s2] [Heq1 Heq2]. by subst. *)
(*             } *)
(*             move => s'.  *)
(*             f_equal. f_equal. f_equal. *)
(*             (* Rem.: the two codes should be syntactically equal  *) *)
(*             (* Rem.: It seems they are not? *) *)
(*             (* Rem.: right, in the RHS we do put;; get  *) *)
(*   (*                  and thus the val2word does a casting... *) *)
(*             Transparent sampler getr bind ret putr. *)
(*             apply code_ext. cbn. f_equal. extensionality x. *)
(*             f_equal. extensionality y. f_equal. extensionality z. *)
(*             destruct z. *)
(*             + cbn. f_equal.  *)
(*             + cbn. f_equal. extensionality a. give_up. *)
(*           - simpl. move => [x h1] [y h2] [Heq1 Heq2]. by subst. *)
(*         } *)
(*         unshelve eapply rrewrite_eqDistrL. *)
(*         1:{ *)
(*           rewrite /=. *)
(*           apply (sampler (U i_words)) => /= m'. *)
(*           apply: getr. { exact: key_location_in_rel_loc. } *)
(*           rewrite /= => option_k. destruct option_k as [k_val | ] eqn:Hk. *)
(*           - apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*             apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*             apply: (ret (val2word c)). *)
(*           - apply (sampler (U i_key)) => /= k_val. *)
(*             apply: (putr _ cipher_location_in_rel_loc ((val2word m') ⊕ (val2key k_val))). *)
(*             apply: (getr _ cipher_location_in_rel_loc) => /= c. *)
(*             apply: (ret (val2word c)). *)
(*         } *)
(*         2:{ *)
(*           move => s. *)
(*           apply: (rcoupling_eq _ _ (fun '(h1, h2) => h1 = h2)); auto. *)
(*           admit. *)
(*         } *)
(*         apply: (rpost_weaken_rule _ eq). *)
(*         2:{ move => [a1 h1] [a2 h2] [H1 H2]. split; assumption. } *)
(*         admit. (*Rem.: this proof should be "T correctly implements PRF" *) *)
(*       + inversion Hrefl'. contradiction. *)
(*     - inversion Hrefl. contradiction. *)
(*   } *)
(* Admitted. *)


Lemma perfect_equivalence1  ( A : Adversary4Game [interface val #[i1] : chWords → chWords ]  )
   { Hdisjoint1 : fdisjoint (T:= tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) A.π1
                            (IND_CPA false).π1 }
   { Hdisjoint2 : fdisjoint (T:=tag_ordType (I:=chUniverse_ordType) (λ _ : chUniverse, nat_ordType)) A.π1
                            (IND_CPA true).π1 } :
  (Pr (A ∘ IND_CPA true) true) = (Pr ((A ∘ MOD_CPA_tt_pkg) ∘ (EVAL true)) true).
Proof.
  rewrite -link_assoc.
  apply: GRing.subr0_eq. apply: normr0_eq0.
  rewrite /IND_CPA.
  fold (@AdvantageE [interface val #[i1] : chWords → chWords] (IND_CPA_pkg_tt ∘ ENC_pkg) (MOD_CPA_tt_pkg ∘ EVAL true) A Hdisjoint1 Hdisjoint2).
  rewrite (eq_upto_inv_perf_ind _ _  (fun '(L1, L2) => L1 = L2) _ _ _ ).
  1,3 : auto.
  1:{
      rewrite /=.
      move => L1 L2. split; move => L1_eq_L2; by rewrite L1_eq_L2.
    }
  apply: eq_up_to_inv_from_alt. move => id S T h x.
  have hident : id = i1 by admit. subst.
  (* similar to perfect_equivalence0 *) admit.
Admitted.


Theorem security_based_on_prf (Hprf : PRF_security) :
  ∀ A : Adversary4Game [interface val #[i1] : chWords → chWords ],
  ∀ Hdisjoint1 Hdisjoint2,
    (@Advantage _ IND_CPA A Hdisjoint1 Hdisjoint2) <=
    prf_epsilon + (@statistical_gap A + prf_epsilon).
Proof.
  rewrite /Advantage => A Hdisjoint1 Hdisjoint2.
  rewrite (@perfect_equivalence0 A Hdisjoint1 Hdisjoint2).
  rewrite (@perfect_equivalence1 A Hdisjoint1 Hdisjoint2).

  have sum_sub : `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true| =
                 `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL true) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL false) true +
                   Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL false) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL true) true|
    by rewrite  GRing.subrK.
  rewrite sum_sub. clear sum_sub.
  apply: ler_trans. { rewrite -GRing.addrA. apply: ler_norm_add. }
  apply: ler_add.
  - rewrite distrC.
    (* simpl in Hdisjoint1, Hdisjoint2.  *)
    (* have hfoo : rel_loc :|: rel_loc = rel_loc. { apply: fsetUidPr. by apply: fsubsetxx. }   *)
    (* rewrite hfoo in Hdisjoint1, Hdisjoint2. clear hfoo. *)
    (* have hfoo :  A.π1 =  A.π1 :|: rel_loc by admit. *)
    (* (*Rem.: if the attacker accesses to all rel_locations then it is *)
    (* trivially true. If the attacker does not then disjointness should *)
    (* still hold *) *)
    (* rewrite hfoo in Hdisjoint1, Hdisjoint2. clear hfoo. *)
    apply: (Hprf (A ∘ MOD_CPA_ff_pkg)); rewrite /=; admit.
    (*Rem.: the "new" attacker has disjotint memory *)
  - have sum_sub : `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL_pkg_tt) true| =
                   `|Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_ff) true - Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_tt) true +
                     Pr ((A ∘ MOD_CPA_ff_pkg) ∘ EVAL_pkg_tt) true - Pr ((A ∘ MOD_CPA_tt_pkg) ∘ EVAL_pkg_tt) true|
      by rewrite GRing.subrK.
    rewrite sum_sub. clear sum_sub.
    apply: ler_trans. { rewrite -GRing.addrA. apply: ler_norm_add. }
    rewrite GRing.addrC.
    apply: ler_add.
    + rewrite /statistical_gap distrC /EVAL. exact: lerr.
    + apply: (Hprf (A ∘ MOD_CPA_ff_pkg)); rewrite /=; admit.
 Admitted.

End PRF_example.
