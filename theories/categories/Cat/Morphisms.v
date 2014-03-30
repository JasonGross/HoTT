(** * Morphisms in cat *)
Require Import Category.Core Functor.Core FunctorCategory.Core FunctorCategory.Morphisms NaturalTransformation.Core.
Require Import Category.Objects.
Require Import Adjoint.Core Adjoint.UnitCounit.
Require Import Functor.Composition.Core.
Require Import Functor.Identity.
Require Import Category.Morphisms.
Require Import Category.Dual Functor.Dual.
Require Import HProp.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

(** ** Lemmas relationship between transporting the action of functors on objects, and [idtoiso] *)
Section iso_lemmas.
  Context `{Funext}.

  Variable C : PreCategory.

  Variables s d : C.
  Variables m1 m2 : morphism C s d.
  Variable p : m1 = m2.

  Variable Fs : PreCategory.
  Variable Fd : PreCategory.
  Variable Fm : morphism C s d -> Functor Fs Fd.

  Lemma transport_Fc_to_idtoiso
        s' d' u
  : @transport _ (fun m => morphism _ (Fm m s') d') _ _ p u
    = u o components_of (Category.Morphisms.idtoiso (_ -> _) (ap Fm p) : morphism _ _ _)^-1 s'.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.

  Lemma transport_cF_to_idtoiso
        s' d' u
  : @transport _ (fun m => morphism _ s' (Fm m d')) _ _ p u
    = components_of (Category.Morphisms.idtoiso (_ -> _) (ap Fm p) : morphism _ _ _) d' o u.
  Proof.
    case p; clear p; simpl; autorewrite with morphism; reflexivity.
  Qed.
End iso_lemmas.

Section unviversal_objects_iso.
  (** If two categories are isomorphic, then being initial/terminal in one is
      logically equivalent to being initial/terminal in the other. *)
  Local Open Scope equiv_scope.
  Local Open Scope functor_scope.
  Section initial.
    Context `{Funext}.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable F : Functor C D.
    Variable G : Functor D C.
    Variable A : F -| G.

    Lemma isinitial_iso x
    : IsInitialObject C x <~> IsInitialObject D (F x).
    Proof.
      apply equiv_iff_hprop; intros H' x'.
      - specialize (H' (G x')).
        apply contr_inhabited_hprop.
        + apply hprop_allpath.
          intros m0 m1.
          pose proof (ap (fun m => F _1 m)
                         (@allpath_hprop (morphism C x (G x')) _
                                         (G _1 m0 o unit A x)%morphism
                                         (G _1 m1 o unit A x)%morphism));
            simpl in *.
          pose (unit_counit_equation_1 A).
          rewrite <- (commutes (unit A)) in X.
          apply hprop_allpath in X.
        apply hprop_allpath.
        intros ? ?.
        pose proof (apD (@morphism_of _ _) H0).
        apply (ap (@morphism_of _ _ G _ _)).
 by typeclasses eauto.
        specialize (H' (G x')).
