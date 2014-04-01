Require Import Category.Core Functor.Core FunctorCategory.Core FunctorCategory.Morphisms NaturalTransformation.Core.
Require Import Category.Objects.
Require Import Adjoint.Core.
Require Import Adjoint.UnitCounit Adjoint.UnitCounitCoercions.
Require Import Adjoint.Hom Adjoint.HomCoercions.
Require Import Adjoint.Dual.
Require Import Functor.Composition.Core.
Require Import Functor.Identity.
Require Import Category.Morphisms.
Require Import Category.Dual Functor.Dual.
Require Import HProp types.Forall Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section unviversal_objects_iso.
  (** If two categories are isomorphic, then being initial/terminal in one is
      logically equivalent to being initial/terminal in the other. *)
  Local Open Scope equiv_scope.
  Local Open Scope functor_scope.
  Section initial.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.

    Lemma left_adjoint_preserves_isinitial x
    : IsInitialObject C x -> IsInitialObject D (F x).
    Proof.
      intros H' x'.
      eapply contr_equiv'.
      apply (equiv_hom_set_adjunction A).
      apply H'.
    Defined.
  End initial.

  Section terminal.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.

    Definition right_adjoint_preserves_isterminal x
    : IsTerminalObject D x -> IsTerminalObject C (G x)
      := left_adjoint_preserves_isinitial A^op x.
  End terminal.
