(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :  
                	
           
************************************************************)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Definition is_iso_of_precats {C D: precategory}(F : functor C D) := 
   dirprod (isweq F) (forall a b, isweq (@functor_on_morphisms _ _ F a b)).

Lemma isaprop_is_iso_of_precats : forall (C D : precategory) (F : functor C D), 
   isaprop (is_iso_of_precats F).
Proof.
  intros C D F.
  apply isapropdirprod.
  - apply isapropisweq.
  - do 2 (apply impred; intro). apply isapropisweq.
Qed.

Definition iso_of_precats (C D : precategory) : UU := total2 (
    fun F : functor C D => is_iso_of_precats F).

Definition from_iso_to_id (C D : precategory) :  
    ob C == ob D -> C == D.
Proof.
  intro H.
  apply total2_paths_hProp.
  - intro a; apply isaprop_is_precategory.
  -  refine (total2_paths _ _ ).
      
  - apply H.


















