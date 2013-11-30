Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import KanExtensions.Core KanExtensions.Functors.
Require Import Limits.Core Limits.Functors.
Require Import Adjoint.UniversalMorphisms.
Require Import FunctorCategory.Core.
Require Import Adjoint.Core.
Require Import InitialTerminalCategory NatCategory.
Require Import Comma.Core Cat.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** (co)limits assemble into functors from [Cat / C] *)

Local Open Scope category_scope.

Section functors.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Hypothesis PC : P C.

  Section colimit.
    Context `(has_colimits
              : forall D (F : Functor D C),
                  @IsColimit _ C D F (colimits D F)).

    Definition colimit_comma_functor_object_of : (Cat / ((C; PC) : Cat)) -> C.
    Proof.
      simpl.
      intros [a b f].
      simpl in *.
      (** Write intro rules for functors (f / g) -> C and C -> (f / g).  Maybe also for general sigma categories. *)

    Definition colimit_comma_functor : Functor (Cat / ((C; PC) : Cat)) C.
      := left_kan_extension_functor has_colimits.

    Definition colimit_adjunction
    : colimit_functor -| diagonal_functor _ _
      := left_kan_extension_adjunction has_colimits.
  End colimit.

  Section limit.
    Context `(has_limits
              : forall F : Functor D C,
                  @IsLimit _ C D F (limits F)).

    (** TODO(jgross): We'll probably want to compose this with the
        functor from [1 -> C] to [C], and then compose the adjunctions
        similarly.  This will require turning the equality in the
        exponential laws into an adjunction. Probably not very
        hard. *)

    Definition limit_functor : Functor (D -> C) (1 -> C)
      := right_kan_extension_functor has_limits.

    Definition limit_adjunction
    : diagonal_functor _ _ -| limit_functor
      := right_kan_extension_adjunction has_limits.
  End limit.
End functors.
