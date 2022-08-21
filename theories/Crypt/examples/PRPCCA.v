(**
  This formalises Claim 9.4 from "The Joy of Cryptography" (p. 172). It is a
  CCA-secure scheme based on a Strong Pseudo-Random Permutation (SPRP). It is
  significantly more complicated than MACCCA.v, but relies only on one,
  somewhat low-level, cryptographic primitive.

  It shows how to do sampling without replacement in SSProve. It follows the
  proof from the book rather closely, with only a minor diversion (see
  [CTXT_HYB_pkg_2]), and most of the proofs are relatively easy to follow.

  As with PRFMAC.v it shows the advantage is at most the sum of the
  [prp_epsilon] and a [statistical_gap]. The first is negligible by assumption,
  the latter requires additional analysis to prove, which is not yet supported
  by SSProve.
*)

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.
From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude.

From extructures Require Import ord fset fmap.

Import SPropNotations.

Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Section PRPCCA_example.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Definition fset_to_chset {T: ordType} (s: {fset T}): {fmap T -> 'unit} :=
  mkfmap [seq (i, tt) | i <- s].

Lemma domm_fset_to_chset {T}:
  cancel (@fset_to_chset T) (@domm T 'unit).
Proof.
  move=> [m Hm] /=.
  apply: fsval_eq.
  have H: (fst \o pair^~ tt =1 id) => //.
  by rewrite /fset_to_chset val_domm mkfmapK /unzip1 -map_comp (eq_map (H T)) map_id.
Qed.

(**
  A core part of the proof is sampling without replacement. This is implemented
  by keeping track of a set of sampled items, and then sampling from the
  complement of that set.

  [compl] computes the complement of a set of integers modulo [n].
*)
Definition compl {n} (r: {fset 'I_n}): {fset 'I_n} :=
  fset (ord_enum n) :\: r.

Lemma in_compl {n} (a: 'I_n) (s: {fset 'I_n}):
  (a \in compl s) = (a \notin s).
Proof.
  by rewrite in_fsetD in_fset mem_ord_enum Bool.andb_true_r.
Qed.

(**
  We cannot sample directly from a set in SSProve, so instead we sample an
  integer less than the size of the set, and then pick the corresponding
  element.
*)
Definition sample_subset {n} `{Positive n} {r: seq 'I_n} (k: 'I_(size r)): 'fin n :=
  nth (chCanonical ('fin n)) r (nat_of_ord k).

Lemma sample_subset_in {n} `{Positive n} {r: seq 'I_n} (k: 'I_(size r)):
  sample_subset k \in r.
Proof.
  by apply: mem_nth.
Qed.

(**
  This implements sampling without replacement, by sampling from the complement
  of [r].

  The input to [uniform] must be positive, and since [r] changes at runtime that
  won't necessarily be the case. We handle this with an [#assert], which means
  if [r'] is empty (i.e., we've sampled the entire set) the program will crash,
  which is the only reasonable way to handle the case. (In fact, [#assert] is
  implemented as sampling from an empty distribution.)
*)
Definition samp_no_repl {n} `{Positive n} {L} (r: {fset ('fin n)}): code L [interface] ('fin n) :=
  {code
    let r' := compl r in
    #assert (0 < size r') as H ;;
    i <$ @uniform _ H ;;
    ret (sample_subset i)
  }.

Variable (n l: nat).

Definition Word_N: nat := 2^n.
Definition Word: choice_type := 'fin Word_N.

Definition Key_N: nat := 2^l.
Definition Key: choice_type := 'fin Key_N.

(**
  Ciphertexts are technically a [Word * Key] pair, but since we want to be able
  to sample random ciphertexts, we define them as [n+l]-bit integers.
*)
Definition Ciph_N: nat := 2^(n + l).
Definition Ciph: choice_type := 'fin Ciph_N.

(**
  We can then define functions to convert between the two.
*)
#[program]
Definition ciph_to_pair (c: Ciph): Word * Key :=
  (@Ordinal _ (c %% Word_N) _, @Ordinal _ (c %/ Word_N) _).
Next Obligation.
  by rewrite ltn_mod PositiveExp2.
Qed.
Next Obligation.
  by rewrite ltn_divLR ?PositiveExp2 // -expnD addnC.
Qed.

#[program]
Definition mkciph (m: Word) (r: Key): Ciph :=
  @Ordinal _ (r * Word_N + m) _.
Next Obligation.
  apply: (@leq_trans (r * Word_N + Word_N)).
  - by rewrite ltn_add2l.
  - by rewrite /Ciph_N expnD addnC -mulSn mulnC leq_pmul2l ?PositiveExp2.
Qed.

Lemma mkciph_ciph_to_pair (c: Ciph):
  mkciph (ciph_to_pair c).1 (ciph_to_pair c).2 = c.
Proof.
  apply: ord_inj.
  case: c => [c Hc] /=.
  by rewrite -divn_eq.
Qed.

Lemma ciph_to_pair_mkciph (m: Word) (r: Key):
  ciph_to_pair (mkciph m r) = (m, r).
Proof.
  rewrite /mkciph /ciph_to_pair /=.
  f_equal.
  all: apply: ord_inj => /=.
  - by rewrite modnMDl modn_small.
  - by rewrite divnMDl ?PositiveExp2 ?divn_small ?addn0.
Qed.

Lemma mkciph_eq (m m': Word) (r r': Key):
  (mkciph m r == mkciph m' r') = (m == m') && (r == r').
Proof.
  case: (eq_dec ((m == m') && (r == r')) true).
  1: {
    move=> /andP [/eqP -> /eqP ->].
    by rewrite !eq_refl.
  }
  move /eqP.
  rewrite eqb_id => /nandP [/negPf Hneq|/negPf Hneq].
  all: rewrite Hneq ?Bool.andb_false_r /=.
  all: move /eqP in Hneq.
  all: apply /eqP => contra.
  all: apply (f_equal ciph_to_pair) in contra.
  all: rewrite !ciph_to_pair_mkciph in contra.
  all: by case: contra.
Qed.

Context (PRP:  Key -> Ciph -> Ciph).
Context (PRP': Key -> Ciph -> Ciph).

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Notation " 'key " := (Key) (in custom pack_type at level 2).
Notation " 'key " := (Key) (at level 2): package_scope.

Notation " 'ciph " := (Ciph) (in custom pack_type at level 2).
Notation " 'ciph " := (Ciph) (at level 2): package_scope.

Definition k_loc: Location := ('option 'key ; 0).
Definition T_loc: Location := (chMap 'ciph 'ciph ; 1).
Definition Tinv_loc: Location := (chMap 'ciph 'ciph ; 2).
Definition Tinv'_loc: Location := (chMap 'ciph 'ciph ; 3).
Definition S_loc: Location := ('set 'ciph ; 4).
Definition R_loc: Location := ('set 'key ; 5).
Definition samp: nat := 6.
Definition ctxt: nat := 7.
Definition decrypt: nat := 8.
Definition lookup: nat := 9.
Definition invlookup: nat := 10.

Definition mkpair {Lt Lf E}
  (t: package Lt [interface] E) (f: package Lf [interface] E):
  loc_GamePair E := fun b => if b then {locpackage t} else {locpackage f}.

(**
  The [SAMP] packages define sampling with ([true]), and without ([false])
  replacement.
*)
Definition SAMP_pkg_tt (p: nat) `{Positive p}:
  package fset0 [interface]
    [interface
      #val #[samp]: 'set ('fin p) → ('fin p) ] :=
  [package
    #def #[samp] (S: 'set ('fin p)): ('fin p) {
      s <$ uniform p ;;
      ret s
    }
  ].

Definition SAMP_pkg_ff (p: nat) `{Positive p}:
  package fset0 [interface]
    [interface
      #val #[samp]: 'set ('fin p) → ('fin p) ] :=
  [package
    #def #[samp] (S: 'set ('fin p)): ('fin p) {
      s ← samp_no_repl (domm S) ;;
      ret s
    }
  ].

Definition SAMP (p: nat) `{Positive p} :=
  mkpair (SAMP_pkg_tt p) (SAMP_pkg_ff p).

Definition kgen: raw_code 'key :=
  k_init ← get k_loc ;;
  match k_init with
  | None =>
      k <$ uniform Key_N ;;
      #put k_loc := Some k ;;
      ret k
  | Some k => ret k
  end.

Lemma kgen_valid {L I}:
  k_loc \in L ->
  ValidCode L I kgen.
Proof.
  move=> H.
  apply: valid_getr => [// | [k|]].
  1: by apply: valid_ret.
  apply: valid_sampler => k.
  apply: valid_putr => //.
  by apply: valid_ret => //.
Qed.

Hint Extern 1 (ValidCode ?L ?I kgen) =>
  eapply kgen_valid ;
  auto_in_fset
  : typeclass_instances ssprove_valid_db.

Definition EVAL_locs_tt := (fset [:: k_loc]).
Definition EVAL_locs_ff := (fset [:: T_loc; Tinv_loc]).

(**
  Next, we define the packages for the SPRP, [EVAL]. They follow the definitions
  from the book exactly.

  They are computationally indistinguishable by assumption.
*)
Definition EVAL_pkg_tt:
  package EVAL_locs_tt
    [interface]
    [interface
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ] :=
  [package
    #def #[lookup] (x: 'ciph): 'ciph {
      k ← kgen ;;
      ret (PRP k x)
    } ;
    #def #[invlookup] (y: 'ciph): 'ciph {
      k ← kgen ;;
      ret (PRP' k y)
    }
  ].

Definition EVAL_pkg_ff:
  package EVAL_locs_ff
    [interface]
    [interface
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ] :=
  [package
    #def #[lookup] (x: 'ciph): 'ciph {
      T ← get T_loc ;;
      match getm T x with
      | None =>
          y ← samp_no_repl (codomm T) ;;
          Tinv ← get Tinv_loc ;;
          #put T_loc := setm T x y ;;
          #put Tinv_loc := setm Tinv y x ;;
          ret y
      | Some y => ret y
      end
    } ;
    #def #[invlookup] (y: 'ciph): 'ciph {
      Tinv ← get Tinv_loc ;;
      match getm Tinv y with
      | None =>
          x ← samp_no_repl (codomm Tinv) ;;
          T ← get T_loc ;;
          #put T_loc := setm T x y ;;
          #put Tinv_loc := setm Tinv y x ;;
          ret x
      | Some x => ret x
      end
    }
  ].

Definition EVAL_SAMP_pkg:
  package EVAL_locs_ff
    [interface
      #val #[samp]: 'set 'ciph → 'ciph ]
    [interface
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ] :=
  [package
    #def #[lookup] (x: 'ciph): 'ciph {
      T ← get T_loc ;;
      match getm T x with
      | None =>
          #import {sig #[samp]: 'set 'ciph → 'ciph } as samp ;;
          y ← samp (fset_to_chset (codomm T)) ;;
          Tinv ← get Tinv_loc ;;
          #put T_loc := setm T x y ;;
          #put Tinv_loc := setm Tinv y x ;;
          ret y
      | Some y => ret y
      end
    } ;
    #def #[invlookup] (y: 'ciph): 'ciph {
      Tinv ← get Tinv_loc ;;
      match getm Tinv y with
      | None =>
          #import {sig #[samp]: 'set 'ciph → 'ciph } as samp ;;
          x ← samp (fset_to_chset (codomm Tinv)) ;;
          T ← get T_loc ;;
          #put T_loc := setm T x y ;;
          #put Tinv_loc := setm Tinv y x ;;
          ret x
      | Some x => ret x
      end
    }
  ].

Definition EVAL := mkpair EVAL_pkg_tt EVAL_pkg_ff.

Definition CTXT_locs := (fset [:: k_loc; S_loc]).

(**
  We now get to the main definitions of the proof. We are trying to prove the
  [CTXT] packages are computationally indistinguishable.
*)
Definition CTXT_pkg_tt:
  package CTXT_locs
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      r <$ uniform Key_N ;;
      k ← kgen ;;
      let c := PRP k (mkciph m r) in
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      k ← kgen ;;
      ret (ciph_to_pair (PRP' k c)).1
    }
  ].

Definition CTXT_pkg_ff:
  package CTXT_locs
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      c <$ uniform Ciph_N ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      k ← kgen ;;
      ret (ciph_to_pair (PRP' k c)).1
    }
  ].

Definition CTXT := mkpair CTXT_pkg_tt CTXT_pkg_ff.

Definition CTXT_EVAL_locs := (fset [:: S_loc]).

Definition CTXT_EVAL_pkg_tt:
  package CTXT_EVAL_locs
    [interface
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      #import {sig #[lookup]: 'ciph → 'ciph } as lookup ;;
      r <$ uniform Key_N ;;
      c ← lookup (mkciph m r) ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      #import {sig #[invlookup]: 'ciph → 'ciph } as invlookup ;;
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      mr ← invlookup c ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

Definition CTXT_EVAL_SAMP_locs := (fset [:: S_loc; R_loc]).

Definition CTXT_EVAL_SAMP_pkg:
  package CTXT_EVAL_SAMP_locs
    [interface
      #val #[samp]: 'set 'key → 'key ;
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      #import {sig #[samp]: 'set 'key → 'key } as samp ;;
      #import {sig #[lookup]: 'ciph → 'ciph } as lookup ;;
      R ← get R_loc ;;
      r ← samp R ;;
      c ← lookup (mkciph m r) ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      #put R_loc := setm R r tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      #import {sig #[invlookup]: 'ciph → 'ciph } as invlookup ;;
      R ← get R_loc ;;
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      mr ← invlookup c ;;
      let (m, r) := ciph_to_pair mr in
      #put R_loc := setm R r tt ;;
      ret m
    }
  ].

(**
  This package is interesting. It is a parallel composition ([par]) of [EVAL]
  and [SAMP Key_N], i.e. it provides both sampling of keys and a strong
  pseudo-random permutation of ciphertext.

  [b] controls whether they use sampling with, or without replacement, but there
  is a catch: They are reversed! If keys are sampled with replacement then the
  ciphertext sampling is without replacement and vice-versa. This is
  unintuitive, but it matches the use of Lemma 4.12 from the proof in the book
  (p. 174).
*)
Definition EVAL_SAMP (b: bool):
  package EVAL_locs_ff [interface]
    [interface
      #val #[samp]: 'set 'key → 'key ;
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ].
Proof.
  apply (mkpackage (par (EVAL_SAMP_pkg ∘ SAMP Ciph_N b) (SAMP Key_N (~~ b)))).
  ssprove_valid => //=.
  all: case: b.
  1-2: by fdisjoint_auto.
  1-2: by apply: fsubsetxx.
  1-2: by apply: fsub0set.
  1-2: by rewrite fsetU0 fsubsetxx.
  1-2: by rewrite /Game_import -fset0E fsetU0 fsubsetxx.
  1-2: by rewrite fset_cons fsetUC fset1E fsubsetxx.
Defined.

Definition CTXT_HYB_locs_1 := (fset [:: S_loc; R_loc; T_loc; Tinv_loc]).

Definition CTXT_HYB_pkg_1:
  package CTXT_HYB_locs_1
    [interface
      #val #[samp]: 'set 'key → 'key ]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      #import {sig #[samp]: 'set 'key → 'key } as samp ;;
      R ← get R_loc ;;
      r ← samp R ;;
      let mr := mkciph m r in
      T ← get T_loc ;;
      c <$ uniform Ciph_N ;;
      Tinv ← get Tinv_loc ;;
      S ← get S_loc ;;
      #put T_loc := setm T mr c ;;
      #put Tinv_loc := setm Tinv c mr ;;
      #put S_loc := setm S c tt ;;
      #put R_loc := setm R r tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      R ← get R_loc ;;
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      Tinv ← get Tinv_loc ;;
      mr ← match getm Tinv c with
      | None =>
          mr <$ uniform Ciph_N ;;
          T ← get T_loc ;;
          #put T_loc := setm T mr c ;;
          #put Tinv_loc := setm Tinv c mr ;;
          ret mr
      | Some mr => ret mr
      end ;;
      let (m, r) := ciph_to_pair mr in
      #put R_loc := setm R r tt ;;
      ret m
    }
  ].

Definition CTXT_HYB_locs_2 := (fset [:: S_loc; T_loc; Tinv_loc; Tinv'_loc]).

(**
  This is where the proof diverges from the book. The proof in the book removes
  the writes to [T] and [Tinv] from the [ctxt] function because [T] is never
  read, and [Tinv] is only read when [c] _isn't_ in [S], and we add it to [S]
  right after. The second argument, while sound, isn't directly expressible in
  SSProve, so we have to spread this into a few steps:
   - We add a new variable [Tinv'] which is the same as [Tinv] except for the
     write in [ctxt]. I.e., it is equivalent to the one from the book after the
     removal of the write.
   - We replace [getm Tinv c] with [getm Tinv' c] in the [match] inside
     [decrypt]. This is valid since we only reach that point if [c] isn't [S],
     and in that case they have the same value.
   - Now, we can remove the write to [Tinv] in [ctxt], as well as remove [T]
     entirely.
   - Then we can go back to using [Tinv] inside the [match]. [Tinv] and [Tinv']
     are exactly equal at this point.
   - Finally, we can get rid of [Tinv'] completely.
*)
Definition CTXT_HYB_pkg_2:
  package CTXT_HYB_locs_2
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      r <$ uniform Key_N ;;
      let mr := mkciph m r in
      T ← get T_loc ;;
      c <$ uniform Ciph_N ;;
      Tinv ← get Tinv_loc ;;
      S ← get S_loc ;;
      #put T_loc := setm T mr c ;;
      #put Tinv_loc := setm Tinv c mr ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      Tinv ← get Tinv_loc ;;
      Tinv' ← get Tinv'_loc ;;
      mr ← match getm Tinv c with
      | None =>
          mr <$ uniform Ciph_N ;;
          T ← get T_loc ;;
          #put T_loc := setm T mr c ;;
          #put Tinv_loc := setm Tinv c mr ;;
          #put Tinv'_loc := setm Tinv' c mr ;;
          ret mr
      | Some mr => ret mr
      end ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

Definition CTXT_HYB_pkg_3:
  package CTXT_HYB_locs_2
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      r <$ uniform Key_N ;;
      let mr := mkciph m r in
      T ← get T_loc ;;
      c <$ uniform Ciph_N ;;
      Tinv ← get Tinv_loc ;;
      S ← get S_loc ;;
      #put T_loc := setm T mr c ;;
      #put Tinv_loc := setm Tinv c mr ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      Tinv ← get Tinv_loc ;;
      Tinv' ← get Tinv'_loc ;;
      mr ← match getm Tinv' c with
      | None =>
          mr <$ uniform Ciph_N ;;
          T ← get T_loc ;;
          #put T_loc := setm T mr c ;;
          #put Tinv_loc := setm Tinv c mr ;;
          #put Tinv'_loc := setm Tinv' c mr ;;
          ret mr
      | Some mr => ret mr
      end ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

Definition CTXT_HYB_pkg_4:
  package CTXT_HYB_locs_2
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      r <$ uniform Key_N ;;
      let mr := mkciph m r in
      c <$ uniform Ciph_N ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      Tinv ← get Tinv_loc ;;
      Tinv' ← get Tinv'_loc ;;
      mr ← match getm Tinv' c with
      | None =>
          mr <$ uniform Ciph_N ;;
          T ← get T_loc ;;
          #put T_loc := setm T mr c ;;
          #put Tinv_loc := setm Tinv c mr ;;
          #put Tinv'_loc := setm Tinv' c mr ;;
          ret mr
      | Some mr => ret mr
      end ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

Definition CTXT_HYB_pkg_5:
  package CTXT_HYB_locs_2
    [interface]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      r <$ uniform Key_N ;;
      let mr := mkciph m r in
      c <$ uniform Ciph_N ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      Tinv ← get Tinv_loc ;;
      Tinv' ← get Tinv'_loc ;;
      mr ← match getm Tinv c with
      | None =>
          mr <$ uniform Ciph_N ;;
          T ← get T_loc ;;
          #put T_loc := setm T mr c ;;
          #put Tinv_loc := setm Tinv c mr ;;
          #put Tinv'_loc := setm Tinv' c mr ;;
          ret mr
      | Some mr => ret mr
      end ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

Definition CTXT_EVAL_pkg_ff:
  package CTXT_EVAL_locs
    [interface
      #val #[lookup]: 'ciph → 'ciph ;
      #val #[invlookup]: 'ciph → 'ciph ]
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ] :=
  [package
    #def #[ctxt] (m: 'word): 'ciph {
      c <$ uniform Ciph_N ;;
      S ← get S_loc ;;
      #put S_loc := setm S c tt ;;
      ret c
    } ;
    #def #[decrypt] (c: 'ciph): 'word {
      #import {sig #[invlookup]: 'ciph → 'ciph } as invlookup ;;
      S ← get S_loc ;;
      #assert (c \notin domm S) ;;
      mr ← invlookup c ;;
      let (m, r) := ciph_to_pair mr in
      ret m
    }
  ].

(**
  The rest is the equivalence proofs and the final security statement. They are
  all fairly straight forward, although they can get a bit long.
*)
Lemma CTXT_equiv_true:
  CTXT true ≈₀ CTXT_EVAL_pkg_tt ∘ EVAL true.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: by apply: rreflexivity_rule.
Qed.

Lemma CTXT_EVAL_equiv_true:
  CTXT_EVAL_pkg_tt ∘ EVAL false ≈₀ CTXT_EVAL_SAMP_pkg ∘ EVAL_SAMP false.
Proof.
  apply eq_rel_perf_ind_ignore with (fset [:: R_loc]).
  1: by rewrite -fset1E /CTXT_EVAL_SAMP_locs fsub1set !fset_cons !in_fsetU !in_fset1 eq_refl !Bool.orb_true_r.
  simplify_eq_rel m.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: rewrite cast_fun_K.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  all: apply: r_get_remember_rhs => R.
  - ssprove_sync=> r.
    ssprove_sync=> T.
    case: (getm T (mkciph m r)) => [c|].
    + ssprove_sync=> S.
      ssprove_sync.
      shelve.
    + ssprove_code_simpl_more.
      rewrite domm_fset_to_chset.
      ssprove_sync=> H1.
      ssprove_sync=> c.
      ssprove_sync=> Tinv.
      ssprove_swap_seq_lhs [:: 1; 0].
      ssprove_swap_seq_rhs [:: 1; 0].
      ssprove_sync=> S.
      do 3 ssprove_sync.
      shelve.
  - ssprove_sync=> S.
    ssprove_sync=> H1.
    ssprove_sync=> Tinv.
    case: (getm Tinv m) => [c|].
    + shelve.
    + ssprove_code_simpl_more.
      rewrite domm_fset_to_chset.
      ssprove_sync=> H2.
      ssprove_sync=> c.
      ssprove_sync=> T.
      do 2 ssprove_sync.
      shelve.
    Unshelve.
    all: apply: r_put_rhs.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    all: by ssprove_invariant.
Qed.

Lemma CTXT_HYB_equiv_1:
  CTXT_EVAL_SAMP_pkg ∘ EVAL_SAMP true ≈₀ CTXT_HYB_pkg_1 ∘ SAMP Key_N false.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs T_loc R_loc
      (fun T R => forall m r,
        r \notin domm R -> getm T (mkciph m r) = None)
  ).
  1: {
    ssprove_invariant=> //.
    all: by rewrite /CTXT_HYB_locs_1 !fset_cons !in_fsetU !in_fset1 eq_refl !Bool.orb_true_r.
  }
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  1: rewrite cast_fun_K.
  all: ssprove_code_simpl.
  all: apply: r_get_vs_get_remember => R.
  all: ssprove_code_simpl_more.
  - ssprove_sync=> H1.
    ssprove_sync=> r.
    apply: r_get_vs_get_remember => T.
    apply: (r_rem_couple_rhs T_loc R_loc) => Hinv.
    rewrite Hinv -?in_compl ?sample_subset_in //.
    ssprove_sync=> c.
    ssprove_sync=> [|Tinv];
      first by move=> ? ? ->.
    ssprove_swap_seq_lhs [:: 1; 0].
    ssprove_sync=> [|S];
      first by move=> ? ? ->.
    do 4 apply: r_put_vs_put.
    all: ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant=> m' r'.
    rewrite domm_set in_fsetU => /norP [H H'].
    rewrite setmE mkciph_eq.
    rewrite in_fset1 in H.
    move: H => /negPf ->.
    by rewrite Bool.andb_false_r Hinv.
  - ssprove_sync=> [|S];
      first by move=> ? ? ->.
    ssprove_sync=> H1.
    ssprove_sync=> [|Tinv];
      first by move=> ? ? ->.
    case: (getm Tinv m) => [c|].
    + apply: r_put_vs_put.
      all: ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> s0 s1 [[/= Hinv <-] <-] m' r'.
      rewrite get_set_heap_eq domm_set in_fsetU => /norP [H H'].
      rewrite get_set_heap_neq.
      2: by apply /eqP.
      by rewrite Hinv.
    + ssprove_sync=> c.
      apply: r_get_vs_get_remember => T.
      apply: (r_rem_couple_rhs T_loc R_loc) => Hinv.
      do 3 apply: r_put_vs_put.
      all: ssprove_restore_mem;
        last by apply: r_ret.
      ssprove_invariant=> m' r'.
      rewrite domm_set in_fsetU => /norP [H H'].
      rewrite setmE -(mkciph_ciph_to_pair c) mkciph_eq.
      rewrite in_fset1 in H.
      move /negPf in H.
      by rewrite H Bool.andb_false_r Hinv.
Qed.

Lemma CTXT_HYB_equiv_2:
  CTXT_HYB_pkg_1 ∘ SAMP Key_N true ≈₀ CTXT_HYB_pkg_2.
Proof.
  apply eq_rel_perf_ind_ignore with (R_loc |: fset1 Tinv'_loc).
  1: by rewrite fsubU1set /CTXT_HYB_locs_1 /CTXT_HYB_locs_2 fsub1set !fset_cons !in_fsetU !in_fset1 !eq_refl !Bool.orb_true_r.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  all: apply: r_get_remember_lhs => R.
  - ssprove_sync=> r.
    ssprove_sync=> [|T];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    ssprove_sync=> c.
    ssprove_sync=> [|Tinv];
    first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    ssprove_sync=> [|S];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    do 3 ssprove_sync.
    shelve.
  - ssprove_sync=> [|S];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    ssprove_sync=> H1.
    ssprove_sync=> [|Tinv];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    apply: r_get_remember_rhs => Tinv'.
    case: (getm Tinv m) => [c|].
    1: shelve.
    ssprove_sync=> c.
    ssprove_sync=> [|T];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    do 2 ssprove_sync.
    apply: r_put_rhs.
    shelve.
  Unshelve.
  all: apply: r_put_lhs.
  all: ssprove_restore_mem;
    last by apply: r_ret.
  all: by ssprove_invariant.
Qed.

Lemma CTXT_HYB_equiv_3:
  CTXT_HYB_pkg_2 ≈₀ CTXT_HYB_pkg_3.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    triple_rhs S_loc Tinv_loc Tinv'_loc
      (fun S Tinv Tinv' => forall c,
        c \notin domm S -> getm Tinv c = getm Tinv' c)
  ).
  1: {
    ssprove_invariant=> //.
    all: by rewrite /CTXT_HYB_locs_2 !fset_cons !in_fsetU !in_fset1 eq_refl !Bool.orb_true_r.
  }
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  - ssprove_sync=> r.
    ssprove_sync=> [|T];
      first by move=> [? ?] [? ?] ->.
    ssprove_sync=> c.
    apply: r_get_vs_get_remember => Tinv.
    apply: r_get_vs_get_remember => S.
    ssprove_sync;
      first by move=> [? ?] [? ?] ->.
    apply: r_put_vs_put.
    apply: r_put_vs_put.
    ssprove_restore_mem;
      last by apply: r_ret.
    ssprove_invariant=> s0 s1 [[[[Hinv _] <-] _] <-] c'.
    specialize (Hinv c').
    rewrite get_set_heap_eq domm_set in_fsetU => /norP [H H'].
    rewrite get_set_heap_neq.
    2: by apply /eqP.
    rewrite get_set_heap_eq !get_set_heap_neq.
    2,3: by apply /eqP.
    rewrite in_fset1 in H.
    move /negPf in H.
    by rewrite setmE H Hinv.
  - apply: r_get_vs_get_remember => S.
    ssprove_sync=> H1.
    apply: r_get_vs_get_remember => Tinv.
    apply: r_get_vs_get_remember => Tinv'.
    apply: (r_rem_triple_rhs S_loc Tinv_loc Tinv'_loc) => Hinv.
    rewrite Hinv //.
    case: (Tinv' m) => [c|].
    1: {
      ssprove_forget_all.
      by apply: r_ret.
    }
    ssprove_sync=> c.
    ssprove_sync=> [|T];
      first by move=> ? ? ->.
    ssprove_sync;
      first by move=> ? ? ->.
    apply: r_put_vs_put.
    apply: r_put_vs_put.
    ssprove_restore_mem;
      last by apply: r_ret.
    apply: preserve_update_mem_conj.
    1: by ssprove_invariant.
    move=> s0 s1 [[[[[[/= A B] Heq] C] D] E] F] c'.
    rewrite 3?get_set_heap_neq.
    2-4: by apply /eqP.
    rewrite !get_set_heap_eq !setmE Heq.
    case: (c' == m) => //.
    by apply: Hinv.
Qed.

Lemma CTXT_HYB_equiv_4:
  CTXT_HYB_pkg_3 ≈₀ CTXT_HYB_pkg_4.
Proof.
  apply eq_rel_perf_ind_ignore with (T_loc |: fset1 Tinv_loc).
  1: by rewrite fsubU1set /CTXT_HYB_locs_2 fsub1set !fset_cons !in_fsetU !in_fset1 !eq_refl !Bool.orb_true_r.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  - ssprove_sync=> r.
    apply: r_get_remember_lhs => T.
    ssprove_sync=> c.
    apply: r_get_remember_lhs => Tinv.
    ssprove_sync=> [|S];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    do 2 apply: r_put_lhs.
    shelve.
  - ssprove_sync=> [|S];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    ssprove_sync=> H1.
    apply: r_get_remember_lhs => Tinv_l.
    apply: r_get_remember_rhs => Tinv_r.
    ssprove_sync=> [|Tinv'];
      first by rewrite in_fsetU !in_fset1; apply /norP; split; apply /eqP.
    case: (getm Tinv' m) => [c|].
    + ssprove_forget_all.
      by apply: r_ret.
    + ssprove_sync=> c.
      apply: r_get_remember_lhs => Tl.
      apply: r_get_remember_rhs => Tr.
      apply: r_put_lhs.
      apply: r_put_rhs.
      apply: r_put_vs_put.
      shelve.
    Unshelve.
    all: ssprove_restore_mem;
      first by ssprove_invariant.
    all: ssprove_sync.
    all: by apply: r_ret.
Qed.

Lemma CTXT_HYB_equiv_5:
  CTXT_HYB_pkg_4 ≈₀ CTXT_HYB_pkg_5.
Proof.
  apply eq_rel_perf_ind with (
    (fun '(h0, h1) => h0 = h1) ⋊
    couple_rhs Tinv_loc Tinv'_loc eq
  ).
  1: {
    ssprove_invariant=> //.
    all: by rewrite /CTXT_HYB_locs_2 !fset_cons !in_fsetU !in_fset1 eq_refl !Bool.orb_true_r.
  }
  simplify_eq_rel m.
  - apply: (@r_reflexivity_alt _ (S_loc |: fset1 R_loc)) => [loc H|loc v H].
    all: ssprove_invariant;
      first by move=> ? ? ->.
    all: rewrite in_fsetU !in_fset1 in H.
    all: apply /eqP.
    all: by move: H => /orP [/eqP|/eqP] ->.
  - ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_sync=> [|S];
      first by move=> ? ? ->.
    ssprove_sync=> H1.
    apply: r_get_vs_get_remember => Tinv.
    apply: r_get_vs_get_remember => Tinv'.
    apply: (r_rem_couple_rhs Tinv_loc Tinv'_loc) => ->.
    case: (getm Tinv' m) => [c|].
    + ssprove_forget_all.
      by apply: r_ret.
    + ssprove_sync=> c.
      ssprove_sync=> [|T];
        first by move=> ? ? ->.
      ssprove_sync;
        first by move=> ? ? ->.
      do 2 apply: r_put_vs_put.
      ssprove_restore_mem;
        last by apply: r_ret.
      by ssprove_invariant.
Qed.

Lemma CTXT_HYB_equiv_6:
  CTXT_HYB_pkg_5 ≈₀ CTXT_EVAL_pkg_ff ∘ EVAL_SAMP_pkg ∘ SAMP Ciph_N true.
Proof.
  apply eq_rel_perf_ind_ignore with (fset [:: Tinv'_loc]).
  1: by rewrite -fset1E /CTXT_HYB_locs_2 /EVAL_locs_ff fsub1set !fset_cons !in_fsetU !in_fset1 !eq_refl !Bool.orb_true_r /=.
  simplify_eq_rel m.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  - apply: r_dead_sample_L.
    apply: (@r_reflexivity_alt _ (fset1 S_loc)) => [loc H|loc v H].
    all: ssprove_invariant.
    rewrite in_fset1 in H.
    move /eqP in H.
    rewrite H -fset1E in_fset1.
    by apply /eqP.
  - ssprove_sync=> S.
    ssprove_sync=> H1.
    ssprove_sync=> Tinv.
    apply: r_get_remember_lhs => Tinv'.
    case: (Tinv m) => [c|] /=.
    1: {
      ssprove_forget_all.
      by apply: r_ret.
    }
    ssprove_sync=> c.
    ssprove_sync=> T.
    do 2 ssprove_sync.
    apply: r_put_lhs.
    ssprove_restore_mem;
      last by apply: r_ret.
    by ssprove_invariant.
Qed.

Lemma CTXT_EVAL_equiv_false:
  CTXT_EVAL_pkg_ff ∘ EVAL_SAMP_pkg ∘ SAMP Ciph_N false ≈₀ CTXT_EVAL_pkg_ff ∘ EVAL false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: ssprove_code_simpl.
  2: rewrite cast_fun_K.
  2: ssprove_code_simpl.
  2: ssprove_code_simpl_more.
  2: ssprove_sync_eq=> S.
  2: ssprove_sync_eq=> H1.
  2: ssprove_sync_eq=> Tinv.
  2: rewrite domm_fset_to_chset.
  all: by apply: rreflexivity_rule.
Qed.

Lemma CTXT_equiv_false:
  CTXT_EVAL_pkg_ff ∘ EVAL true ≈₀ CTXT false.
Proof.
  apply: eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: ssprove_code_simpl.
  2: ssprove_code_simpl.
  2: ssprove_code_simpl_more.
  all: by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRP, i.e. the chance by
  which an adversary can distinguish the PRP from a truly random function.
  Negligible by assumption.
*)
Definition prp_epsilon := Advantage EVAL.

(**
  The advantage an adversary can gain in the [SAMP] games.
  This is negligible, but not yet provable in SSProve.
*)
Definition statistical_gap A :=
  Advantage EVAL_SAMP (A ∘ CTXT_EVAL_SAMP_pkg) +
  Advantage (SAMP Key_N) (A ∘ CTXT_HYB_pkg_1) +
  Advantage (SAMP Ciph_N) (A ∘ CTXT_EVAL_pkg_ff ∘ EVAL_SAMP_pkg).

Theorem security_based_on_prp LA A:
  ValidPackage LA
    [interface
      #val #[ctxt]: 'word → 'ciph ;
      #val #[decrypt]: 'ciph → 'word ]
    A_export A ->
  fdisjoint LA (
    EVAL_locs_tt :|: EVAL_locs_ff :|: CTXT_locs :|:
    CTXT_EVAL_locs :|: CTXT_EVAL_SAMP_locs :|:
    CTXT_HYB_locs_1 :|: CTXT_HYB_locs_2
    ) ->
  Advantage CTXT A <=
  prp_epsilon (A ∘ CTXT_EVAL_pkg_tt) +
  statistical_gap A +
  prp_epsilon (A ∘ CTXT_EVAL_pkg_ff).
Proof.
  move=> vA H.
  rewrite Advantage_E Advantage_sym.
  ssprove triangle (CTXT true) [::
    CTXT_EVAL_pkg_tt ∘ EVAL true ;
    CTXT_EVAL_pkg_tt ∘ EVAL false ;
    CTXT_EVAL_SAMP_pkg ∘ EVAL_SAMP false ;
    CTXT_EVAL_SAMP_pkg ∘ EVAL_SAMP true ;
    CTXT_HYB_pkg_1 ∘ SAMP Key_N false ;
    CTXT_HYB_pkg_1 ∘ SAMP Key_N true ;
    pack CTXT_HYB_pkg_2 ;
    pack CTXT_HYB_pkg_3 ;
    pack CTXT_HYB_pkg_4 ;
    pack CTXT_HYB_pkg_5 ;
    CTXT_EVAL_pkg_ff ∘ EVAL_SAMP_pkg ∘ SAMP Ciph_N true ;
    CTXT_EVAL_pkg_ff ∘ EVAL_SAMP_pkg ∘ SAMP Ciph_N false ;
    CTXT_EVAL_pkg_ff ∘ EVAL false ;
    CTXT_EVAL_pkg_ff ∘ EVAL true
  ] (CTXT false) A as ineq.
  apply: le_trans.
  1: by apply: ineq.
  rewrite !fdisjointUr in H.
  move: H => /andP [/andP [/andP [/andP [/andP [/andP [H1 H2] H3] H4] H5] H6] H7].
  move: {ineq H1 H2 H3 H4 H5 H6 H7} (H1, H2, H3, H4, H5, H6, H7, fdisjoints0) => H.
  rewrite CTXT_equiv_true ?fdisjointUr ?H // GRing.add0r.
  rewrite CTXT_EVAL_equiv_true ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_1 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_2 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_3 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_4 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_5 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_HYB_equiv_6 ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_EVAL_equiv_false ?fdisjointUr ?H // GRing.addr0.
  rewrite CTXT_equiv_false ?fdisjointUr ?H // GRing.addr0.
  rewrite /prp_epsilon /statistical_gap !Advantage_E !GRing.addrA.
  rewrite -!Advantage_link !link_assoc.
  by rewrite (Advantage_sym (EVAL true)) (Advantage_sym (SAMP Ciph_N true)).
Qed.

End PRPCCA_example.
