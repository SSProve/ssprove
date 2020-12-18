From Relational Require Import OrderEnrichedCategory.
From Coq Require Import ssreflect ssrfun ssrbool.



(* (*********************************************************) *)
(* (**   Natural transformations, id, comp, whiskering     **) *)
(* (*********************************************************) *)
 Section NaturalTrans.
   Context {C D : ord_category} (F G : ord_functor C D).

   Record natTrans :=
     mkNatTrans
       { nt_map :> forall {A}, D⦅F A;G A⦆
       ; nt_natural : forall {A B} (f : C⦅A ; B⦆),
           nt_map ∙ ofmap F f = ofmap G f ∙ nt_map
       }.

 End NaturalTrans.

 Section NaturalTransformationId.
   Context {C D : ord_category} (F : ord_functor C D). 

   Program Definition natTrans_id : natTrans F F := 
     mkNatTrans _ _ (fun bla => Id _) _. 
   Next Obligation. rewrite ord_cat_law1. rewrite ord_cat_law2. reflexivity. Qed. 

 End NaturalTransformationId. 

 Section NaturalTransformationComp. 
   Context {C D : ord_category} {F G H : ord_functor C D} 
           (phi : natTrans F G) (psi : natTrans G H). 

   Program Definition natTrans_comp : natTrans F H :=
     mkNatTrans _ _ (fun A => psi A ∙ phi A) _. 
   Next Obligation. 
     rewrite -ord_cat_law3 nt_natural ord_cat_law3 nt_natural !ord_cat_law3. 
     reflexivity.
   Qed. 
 End NaturalTransformationComp. 

 Section NaturalTransformationRightWhiskering. 
   Context {C D E: ord_category} {F G : ord_functor C D} (H : ord_functor D E) 
           (phi : natTrans F G). 

   Program Definition natTrans_whisker_right : natTrans (ord_functor_comp F H) (ord_functor_comp G H) := 
     mkNatTrans _ _ (fun A => ofmap H (phi A)) _. 
   Next Obligation. 
     rewrite -!ord_functor_law2 !nt_natural ; reflexivity. 
   Qed. 
 End NaturalTransformationRightWhiskering. 

 Section NaturalTransformationLeftWhiskering. 
   Context {C D E: ord_category} {F G : ord_functor D E}  
           (phi : natTrans F G) (H : ord_functor C D). 

   Program Definition natTrans_whisker_left : natTrans (ord_functor_comp H F) (ord_functor_comp H G) := 
     mkNatTrans _ _ (fun A => phi (H A)) _. 
   Next Obligation. rewrite nt_natural. reflexivity. Qed. 

 End NaturalTransformationLeftWhiskering. 
