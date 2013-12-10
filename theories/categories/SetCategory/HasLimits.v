Require Import Category.Core Category.Strict.
Require Import Functor.Core NaturalTransformation.Core.
Require Import Limits.Core SetCategory.Core UniversalProperties KanExtensions.Core.
Require Import InitialTerminalCategory.
Require Import HProp HSet types.Universe.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope morphism_scope.

Section has_limits.
  Context `{fs1 : Funext}.
  Context `{fs2 : Funext}.
  Context `{fs3 : Funext}.
  Variable D : PreCategory.

  Section set_cat.
    Variable F : Functor D (@set_cat fs1).
    Print IsLimit.

    Definition set_cat_limit_object
      := BuildhSet
           { limF : forall d, F d
           | forall s d (m : morphism D s d),
               (F _1 m) (limF s) = limF d }
           _.

    Definition set_cat_limit_object_functor : Functor _ (@set_cat fs1)
      := !(set_cat_limit_object : set_cat).

    Definition set_cat_limit : { x : _ & @IsLimit fs2 _ _ F x }.
      esplit.
      apply @Build_IsTerminalMorphism_uncurried.
      Grab Existential Variables.
      simpl.
      exists (set_cat_limit_object_functor).
      simpl.
      Print fs1.
/      exists (
,.      Print IsRightKanEx
      unfold IsLimit.
      unfold IsRightKanExtensionAlong.
      simpl.
