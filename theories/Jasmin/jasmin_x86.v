Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import expr compiler_util values sem.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths".
(* Silencing the following warning: *)
(* New coercion path [Pbool] : bool >-> pexpr is ambiguous with existing  *)
(* [nat_of_bool; Posz; int_to_Z; Pconst] : bool >-> pexpr. *)
From Jasmin Require Import expr_facts.
Set Warnings "ambiguous-paths".

From Coq Require Import Utf8.

From Crypt Require Import Prelude Package.
Import PackageNotation.

From Equations Require Import Equations.
Set Equations With UIP.
Set Equations Transparent.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.
Set Default Proof Using "Type".

From JasminSSProve Require Import jasmin_translate jasmin_asm.

From Jasmin Require Import
  x86_instr_decl
  x86_extra
  x86_params
  x86_params_proof
  x86_decl
  x86_lowering
  x86.

From Jasmin Require Import
  arch_sem
  compiler
  compiler_proof.

Section x86_correct.

  Lemma id_tin_instr_desc :
    ∀ (a : asm_op_msb_t),
      id_tin (instr_desc a) = id_tin (x86_instr_desc a.2).
  Proof.
    intros [[ws|] a].
    - simpl. destruct (_ == _). all: reflexivity.
    - reflexivity.
  Qed.

  Definition cast_sem_prod_dom {ts tr} ts' (f : sem_prod ts tr) (e : ts = ts') :
    sem_prod ts' tr.
  Proof.
    subst. exact f.
  Defined.

  Lemma cast_sem_prod_dom_K :
    ∀ ts tr f e,
      @cast_sem_prod_dom ts tr ts f e = f.
  Proof.
    intros ts tr f e.
    assert (e = erefl).
    { apply eq_irrelevance. }
    subst. reflexivity.
  Qed.

  Lemma sem_correct_rewrite :
    ∀ R ts ts' f e,
      sem_correct ts' (cast_sem_prod_dom ts' f e) →
      @sem_correct R ts f.
  Proof.
    intros R ts ts' f e h.
    subst. rewrite cast_sem_prod_dom_K in h.
    assumption.
  Qed.

  Lemma no_arr_correct {R} ts s :
    List.Forall (λ t, ∀ len, t != sarr len) ts →
    @sem_correct R ts s.
  Proof.
    intros h.
    induction h as [| t ts ht h ih].
    - constructor.
    - constructor.
      + intros v.
        pose proof unembed_embed t v as e.
        destruct t as [| | len |].
        1,2,4: rewrite e ; reflexivity.
        specialize (ht len). move: ht => /eqP. contradiction.
      + intros v.
        apply ih.
  Qed.

  Lemma x86_correct :
    ∀ (o : asm_op_t),
      sem_correct (tin (sopn.get_instr_desc (Oasm o))) (sopn_sem (Oasm o)).
  Proof.
    intros o.
    simpl. destruct o as [a | e].
    - Opaque instr_desc. simpl.
      pose proof (id_tin_instr_desc a) as e.
      eapply sem_correct_rewrite with (e := e).
      destruct a as [o x]. simpl in *.
      eapply no_arr_correct.
      destruct x ; simpl.
      all: repeat constructor.
      Transparent instr_desc.
    - destruct e ; simpl ; repeat constructor.
      destruct w ; repeat constructor.
  Qed.

Context
  {syscall_state : Type}
    {sc_sem : syscall.syscall_sem syscall_state}
    {gf : glob_decls}
    {asm_scsem : asm_syscall_sem (call_conv:=x86_linux_call_conv)}
    (cparams : compiler_params fresh_vars lowering_options).

  Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
  Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
  Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

  Definition equiv_to_x86 := @equiv_to_asm syscall_state sc_sem gf _ _ _ _ _ _ _ _ x86_linux_call_conv _ _ _ _ x86_h_params cparams print_uprogP print_sprogP print_linearP x86_correct.

End x86_correct.
