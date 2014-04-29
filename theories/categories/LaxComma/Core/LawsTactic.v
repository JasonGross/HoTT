(** * Tactics for proving the laws for making a lax comma category *)
Require Export Category.Core Functor.Core NaturalTransformation.Core.
Require Functor.Identity.
Require Export Category.Strict.
Require Export Functor.Composition.Core.
Require Export NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Export Category.Morphisms FunctorCategory.Core.
Require Export Pseudofunctor.Core Pseudofunctor.RewriteLaws.
Require Export NaturalTransformation.Composition.Laws.
Require Export FunctorCategory.Morphisms.
Require LaxComma.Core.Parts.
Require Export types.Record Trunc HoTT.Tactics types.Paths types.Sigma.

Export Functor.Identity.FunctorIdentityNotations.
Export LaxComma.Core.Parts.LaxCommaCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Ltac t_do_work :=
  repeat match goal with
           | _ => reflexivity
           | [ |- appcontext[components_of ?T^-1 ?x] ]
             => progress change (T^-1 x) with ((T x)^-1)
           | [ |- appcontext[?F _1 ?m^-1] ]
             => progress change (F _1 m^-1) with ((F _1 m)^-1)
           | _ => progress repeat iso_collapse_inverse_right'
         end.

Ltac t_start :=
  simpl in *;
  repeat match goal with
           | [ H : ?x = _ |- _ ] => rewrite H; clear H; try clear x
         end;
  path_natural_transformation;
  simpl in *;
  rewrite !Category.Core.left_identity, !Category.Core.right_identity;
  rewrite !composition_of.

Ltac t :=
  t_start;
  rewrite <- !Category.Core.associativity;
  (** A reflective simplifier would be really useful here... *)
  repeat match goal with
           | _ => progress t_do_work
           | [ |- appcontext[components_of ?T ?x] ]
             => simpl rewrite <- !(commutes_pT_F T)
           | [ |- appcontext[components_of ?T ?x] ]
             => simpl rewrite <- !(commutes T)
           | _ => iso_move_inverse
         end.
