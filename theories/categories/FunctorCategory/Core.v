Require Import Category.Core Category.Strict Functor.Core NaturalTransformation.Core Functor.Paths.
(** These must come last, so that [identity], [compose], etc., refer to natural transformations. *)
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Identity NaturalTransformation.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Section functor_category.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Context `{forall x y, IsHSet (morphism D x y)}.

  (** There is a category Fun(C, D) of functors from [C] to [D]. *)

  Definition functor_category : PreCategory
    := @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (fun _ _ _ _ => @associativity _ C D _ _ _ _ _)
                          (@left_identity _ C D _)
                          (@right_identity _ C D _)
                          (*_*).
End functor_category.

Local Notation "C -> D" := (functor_category C D) : category_scope.

Lemma isstrict_functor_category `{Funext} C `{IsStrictCategory D} `{forall x y, IsHSet (morphism D x y)}
: IsStrictCategory (C -> D).
Proof.
  typeclasses eauto.
Defined.

Module Export FunctorCategoryCoreNotations.
  (*Notation "C ^ D" := (functor_category D C) : category_scope.
  Notation "[ C , D ]" := (functor_category C D) : category_scope.*)
  Notation "C -> D" := (functor_category C D) : category_scope.
End FunctorCategoryCoreNotations.
