(* A trash file that I still would like to keep as an experiment *)

Section OriginalLemma_rSamplerC.
(* ------------------Lemma----------------- *)
(* Lemma rsamplerC { A : ord_choiceType }§ { L : {fset Location} }  (o : Op) *)
(*                 (c : program L Game_import A): *)
(*   r⊨ ⦃ fun '(h1,h2) => h1 = h2 ⦄ *)
(*        a ← c ;; r ← (r ← sample o ;; ret r) ;;  (ret (a, r)) ≈ *)
(*        r ← (r ← sample o ;; ret r) ;; a ← c ;;  (ret (a, r)) *)
(*    ⦃ eq ⦄. *)
(* Proof. *)
(*   apply: rrewrite_eqDistrL. *)
(*   - apply: rreflexivity_rule.  *)
(*   - move => s. f_equal. *)
(*     (*CA: we should be able to rewrite smMonequ1/2 ? and have the equality? *) *)

(* ---------------stuck on goal--------------------------- *)
  (* getLocations := λ (I E : Interface) '(locs; _), locs *)
  (*  : ∀ I E : Interface, package I E → {fset Location} *)
  (* A : ord_choiceType *)
  (* L : {fset Location} *)
  (* o : Op *)
  (* c : program L Game_import A *)
  (* s : heap_choiceType *)
  (* ============================ *)
  (* θ_dens (θ0 (repr (r ← (r ← sample o ;; ret r) ;; a ← c ;; ret (a, r))) s) = *)
  (* θ_dens (θ0 (repr (a ← c ;; r ← (r ← sample o ;; ret r) ;; ret (a, r))) s) *)


(* -------------------- repr header ------------------ *)
    (* Equations? repr' {B : choiceType} {L : {fset Location}} *)
    (*   (p : raw_program B) (h : valid_program L Game_import p) *)
    (* : rFreeF (ops_StP heap_choiceType) (ar_StP heap_choiceType) B := *)


(* ----------------- repr sample ------------------- *)
      (* | _sampler op k := bindrFree _ _ *)
      (*                              (ropr (inr op) (fun v => retrFree v)) *)
      (*                              (λ s, repr' (k s) _) *)

 (* ------------------- Op ---------------------------- *)
(* Op = Prob_ops_collection probE rel_choiceTypes chEmb *)
(*      : Type *)


(* ------------------- some equations ----------------- *)
(* repr (r <- (r <- sample o ;; ret r) ;; a <- c ;; ret (a, r)) *)
(* = *)
(* repr ( r <- sample o ;; a <- c ;; ret (a,r) ) *)
(* = *)
(* repr ( a <- ( r <-  sample o ;; a <- c )  *)

End OriginalLemma_rSamplerC.

Section PipelineOperation.
Infix "-*-" := prod_choiceType (at level 80, right associativity).

Context {M : ord_relativeMonad choice_incl}.

Notation η := (ord_relmon_unit M).

Definition mybind {X Y} (m : M X) (k : X -> M Y) := (ord_relmon_bind M) k m.

Definition pipel {A B} (f : M A) (g : M B) :=
mybind f (fun a =>
mybind g (fun b =>
η _ (a,b)   )).

End PipelineOperation.

Check pipel.
 
Infix ">>>>" := pipel (at level 80).


Section θ0_vs_pipel.
Notation η M := (ord_relmon_unit M).
Notation dnib M := (ord_relmon_bind M).

Arguments bindrFree { _ _ _ _ } _ _.
Arguments ropr {_ _ _ } _ _.
Arguments callrFree {_ _} _.
Arguments retrFree {_ _ _} _.

Arguments rFreeF { _ _ }.

Context {S : choiceType} (X Y : choiceType).

Let θ0 := @θ0 S.
Let stT_Frp_ := @stT_Frp probE rel_choiceTypes chEmb S.

Context (m : FrStP S X) (k : X -> FrStP S Y).

(* (dnib (FrStP S)  k) m *)
Lemma θ0_vs_bind:
θ0 _ (bindrFree m k) =
(dnib stT_Frp_) (fun x:X => θ0 _ (k x)) (θ0 _ m).
Proof.
  assert ( to_dnib : bindrFree m k = (dnib (FrStP S)  k) m ).
    reflexivity.
  rewrite to_dnib.
  rewrite /θ0 /DerivedRules.θ0.
  pose bla :=
rmm_law2 _ _ _ _ (@unaryIntState probE rel_choiceTypes chEmb S)
         X Y k.
  rewrite /= in bla.
  unshelve eapply equal_f in bla. exact m.
  rewrite /=. assumption.
Qed.

Let Opst := (ops_StP S).
Let Arst := (ar_StP S).

Context (z1 : FrStP S X) (z2 : FrStP S Y).
Lemma θ0_vs_pipel : (θ0 _ (z1 >>>> z2)) = ((θ0 _ z1) >>>> (θ0 _ z2)).
  rewrite /pipel.
  rewrite /θ0 /DerivedRules.θ0.
  rewrite /mybind.
  unshelve epose ( bla :=
rmm_law2 _ _ _ _ (@unaryIntState probE rel_choiceTypes chEmb S)
         X (prod_choiceType X Y) _ ).
  exact (fun a : X => dnib (FrStP S) (fun b : Y => η (FrStP S) (prod_choiceType X Y) (a, b)) z2).
  unshelve eapply equal_f in bla. exact z1.
  rewrite /= in bla. rewrite /=. rewrite bla. clear bla.  
  (* unshelve eapply equal_f in bla. shelve. clear bla. *)
  rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  apply boolp.funext ; move=> s.
  rewrite /FreeProbProg.rFree_obligation_2.
  apply f_equal. apply boolp.funext. move=> [x sf].
  Check @UniversalFreeMap.outOfFree _ _ _ sigMap.
  unshelve epose ( bla :=
rmm_law2 _ _ _ _ (@UniversalFreeMap.outOfFree _ _ _ sigMap) ).
  exact probE ; exact rel_choiceTypes ; exact chEmb. exact rel_choiceTypes.
  exact chEmb. exact S.
  specialize (bla Y (prod_choiceType X Y)
  (fun b : Y =>
        FreeProbProg.rFree_obligation_1 (StateTransformingLaxMorph.ops_StP S)
          (StateTransformingLaxMorph.ar_StP S) (prod_choiceType X Y) (x, b)) ).
  unshelve eapply equal_f in bla. exact z2.  
  rewrite /= in bla. rewrite /FreeProbProg.rFree_obligation_2 in bla.
  rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1 in bla.
  unshelve eapply equal_f in bla. exact sf. assumption.
Qed.

End θ0_vs_pipel.





Section θdens_vs_bind.
Notation η M := (ord_relmon_bind M).
Notation dnib M := (ord_relmon_bind M).

Arguments bindrFree { _ _ _ _ } _ _.
Arguments ropr {_ _ _ } _ _.
Arguments callrFree {_ _} _.
Arguments retrFree {_ _ _} _.

Arguments rFreeF { _ _ }.

Context {S : choiceType} (X Y : choiceType).

Let θ_dens_ := @θ_dens S.
Let Frp := rFreePr probE rel_choiceTypes chEmb.
Let stT_Frp_fld := @stT_Frp probE rel_choiceTypes chEmb S.

Context (m : Frp (prod_choiceType X S) )
(k : prod_choiceType X S -> Frp (prod_choiceType Y S)).

(* (dnib Frp)  k) m *)
Lemma θ_dens_vs_bind:
θ_dens_  _ (bindrFree m k) =
(dnib SDistr) (fun xs => θ_dens_  _ (k xs)) (θ_dens_ _ m).
Proof.
  assert ( to_dnib : bindrFree m k = (dnib Frp  k) m ).
    reflexivity.
  rewrite to_dnib.
  rewrite /θ_dens_ /θ_dens.
  pose bla :=
rmm_law2 _ _ _ _
(@Theta_dens.unary_theta_dens probE rel_choiceTypes chEmb prob_handler)
(prod_choiceType X S) (prod_choiceType Y S) k.
  rewrite /= in bla.
  unshelve eapply equal_f in bla. exact m.
  rewrite /=. assumption.
Qed.

End θdens_vs_bind.

(* Context (z1 : stT_Frp_fld X) (z2 : stT_Frp_fld Y) (si : S). *)


(* (* Goal True. *) *)
(* (*   pose bla := (  θ_dens  ( (z1 >>>> z2) si ) ). *) *)
(* (*   rewrite /= in bla. *) *)
(* (*   pose blou := (  (  θ_dens (z1 si)  ) >>>> (θ_dens (z2 si) )  ). *) *)
(* (*   rewrite /= in bla. *) *)

(* Check z1 >>>> z2. *)
(* Check ( (z1 >>>> z2) si ) *)

(* Local Program Definition LHS : SDistr_carrier (F_choice_prod_obj ⟨ prod_choiceType X Y, S ⟩) := *)
(* (  θ_dens  ( (z1 >>>> z2) si ) ). *)

(* Local Program Definition RHS : SDistr_carrier (F_choice_prod_obj ⟨ prod_choiceType X Y, S ⟩) := *)
(* (  (  θ_dens (z1 si)  ) >>>> (θ_dens (z2 si) )  ). *)
(* Next Obligation. *)
(*   rewrite /=. *)
(* Defined. *)

(* Lemma θ_dens_vs_pipel : @eq (SDistr_carrier (F_choice_prod_obj ⟨ prod_choiceType X Y, S ⟩)) *)
(* (  θ_dens  ( (z1 >>>> z2) si ) ) *)
(* = *)
(* (  (  θ_dens (z1 si)  ) >>>> (θ_dens (z2 si) )  ). *)
(* End θdens_vs_bind. *)


Section Experiment_samplerC.
Notation dnib := ord_relmon_bind.
Infix "-*-" := prod_choiceType (at level 80, right associativity).

Arguments dnib { _ _ _ _ _ _}.

(*operations for proba, proba + state*)
Let Op := Prob_ops_collection probE rel_choiceTypes chEmb.
Let Ar := Prob_arities probE rel_choiceTypes chEmb.

Context { A : ord_choiceType }  {S : choiceType}.

Let Opst := (ops_StP S).
Let Arst := (ar_StP S).

Context (o : Op) (c : FrStP S A).

Arguments bindrFree { _ _ _ _ } _ _.
Arguments ropr {_ _ _ } _ _.
Arguments callrFree {_ _} _.
Arguments retrFree {_ _ _} _.

Let stT_Frp := @stT_Frp probE rel_choiceTypes chEmb S.


Local Definition c_sample_ret :=
c >>>> (callrFree (inr o)).
Check c_sample_ret.

Local Definition sample_c_ret  :=
@pipel (FrStP S) _ _ (callrFree (inr o)) c.



Arguments Prob_arities {_ _ _} _.

Theorem sub_samplerC (s : S) :
θ_dens ( θ0 sample_c_ret s ) =
θ_dens ( θ0 c_sample_ret s ).
Proof.
  rewrite /sample_c_ret /c_sample_ret.
  rewrite !θ0_vs_pipel.

(*   rewrite !θ0_vs_bind. *)
(*   rewrite /=. *)
(*   rewrite /OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1. *)
(*   rewrite /FreeProbProg.rFree_obligation_2. *)
(*   pose bla := ( rmm_law2 _ _ _ _ *)
(*  (@Theta_dens.unary_theta_dens probE rel_choiceTypes chEmb prob_handler) ). *)
(*   rewrite !θ_dens_vs_bind. *)
(*   rewrite /=. *)
(*   rewrite /SubDistr.SDistr_obligation_2 /=. *)
(*   apply distr_ext. move=> y. cbn in y. *)
(*   destruct y as [a z sf]. *)
(*   rewrite /SDistr_bind. rewrite /dlet. unlock. rewrite /=. *)
  
(* (fun xs : Prob_arities o * S => *)
(*      θ_dens (let (z, s0) := xs in θ0 (bindrFree c (fun a1 : A => retrFree (a1, z))) s0)) *)
  
  



End samplerC.
