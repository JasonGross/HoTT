(** * Grothendieck Construction of a functor to Set *)
Require Import Category.Core Functor.Core.
Require Import Category.Univalent.
Require Import Category.Morphisms.
Require Import SetCategory.Core.
Require Import Grothendieck.ToSet.
Require Import Basics.Trunc HSet Types.Sigma TruncType UnivalenceImpliesFunext Types.Universe Basics.Equivalences Basics.PathGroupoids HoTT.Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Univalence}.

  Variable C : PreCategory.
  Context `{IsCategory C}.
  Variable F : Functor C set_cat.

  Instance iscategory_grothendieck_toset : IsCategory (Grothendieck.ToSet.category F).
  Proof.
    intros s d.
    refine (isequiv_adjointify _ _ _ _).
    { intros [m [m' ? ?]].
      destruct s as [s s'], d as [d d']; simpl in *.
      transparent assert (H' : (s = d)).
      { apply (Morphisms.idtoiso C (x := s) (y := d))^-1%function.
        exists m.1.
        exists m'.1.
        { exact (ap projT1 left_inverse). }
        { exact (ap projT1 right_inverse). } }
      { transitivity {| x := transport (fun x => F x) H' s' |}.
        { apply (@transportD _ (fun s => F s) (fun d d' => {| c := s; x := s' |} = {| c := d; x := d' |}) _ _ H' s').
          exact 1. }
        { apply ap.
          subst H'.
          simpl.
          admit. } } }
    { intro.
      simpl in x.
      simpl.
      apply path_isomorphic; simpl.
      admit. }
    { intro.
      hnf in s, d.
      destruct x.
      simpl.
      destruct s; simpl.
      SearchAbout (transportD _ _ _ _).

          apply idtoiso_of_transport.
          Check transport_forall_constant.
          SearchAbout transport idtoiso.
          SearchAbout
          Unset Printing Notations.
          Set Printing Implicit.
          SearchAbout isotoid.
          simpl in *.
        Require Import HoTT. Locate transportD.
      simpl.

End Grothendieck.
