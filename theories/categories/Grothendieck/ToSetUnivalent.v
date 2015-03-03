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

  Record Pair :=
    {
      c : C;
      x : F c
    }.

  Local Notation morphism s d :=
    { f : morphism C s.(c) d.(c)
    | morphism_of F f s.(x) = d.(x) }.

  Definition compose_H s d d'
             (m1 : morphism d d')
             (m2 : morphism s d)
  : (F _1 (m1 .1 o m2 .1)) s.(x) = d'.(x).
  Proof.
    etransitivity; [ | exact (m1.2) ].
    etransitivity; [ | apply ap; exact (m2.2) ].
    match goal with
      | [ |- ?f ?x = ?g (?h ?x) ] => change (f x = (g o h) x)
    end.
    match goal with
      | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g)
    end.
    apply (composition_of F).
  Defined.

  Definition compose s d d'
             (m1 : morphism d d')
             (m2 : morphism s d)
  : morphism s d'.
  Proof.
    exists (m1.1 o m2.1).
    apply compose_H.
  Defined.

  Definition identity_H s
    := apD10 (identity_of F s.(c)) s.(x).

  Definition identity s : morphism s s.
  Proof.
    exists 1.
    apply identity_H.
  Defined.

  Global Arguments compose_H : simpl never.
  Global Arguments identity_H : simpl never.
  Global Arguments identity _ / .
  Global Arguments compose _ _ _ _ _ / .

  (** ** Category of elements *)
  Definition category : PreCategory.
  Proof.
    refine (@Build_PreCategory
              Pair
              (fun s d => morphism s d)
              identity
              compose
              _
              _
              _
              _);
    abstract (
        repeat intro;
        apply path_sigma_uncurried; simpl;
        ((exists (associativity _ _ _ _ _ _ _ _))
           || (exists (left_identity _ _ _ _))
           || (exists (right_identity _ _ _ _)));
        exact (center _)
      ).
  Defined.

  (** ** First projection functor *)
  Definition pr1 : Functor category C
    := Build_Functor
         category C
         c
         (fun s d => @pr1 _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).
End Grothendieck.
