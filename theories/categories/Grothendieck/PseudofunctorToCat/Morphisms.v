(** * Classification of morphisms of the Grothendieck Construction of a pseudofunctor to cat *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core.
Require Import NaturalTransformation.Composition.Core.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core.
Require Import Cat.Core.
Require Import Grothendieck.PseudofunctorToCat.Core.
Require Import HoTT.Basics.Equivalences HoTT.Types.Sigma HoTT.Basics.PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.
  Context {C : PreCategory}
          {F : Pseudofunctor C}
          {s d : category F}.

  Definition isequiv_sigma_category_isomorphism_f
  : { e : (s.(c) <~=~> d.(c))%category | (p_morphism_of F e s.(x) <~=~> d.(x))%category } -> (s <~=~> d)%category.
  Proof.
    { intro m.
      exists (m.1 : morphism _ _ _ ; m.2 : morphism _ _ _).
      eexists (m.1^-1 : morphism _ _ _;
               ((p_identity_of F _) (x s))
                 o (((idtoiso (ap (p_morphism_of F) (@left_inverse _ _ _ m.1 m.1))) : morphism _ _ _) (x s))
                 o ((p_composition_of F (c s) (c d) (c s) (m.1)^-1 m.1)^-1 (x s))
                 o ((p_morphism_of F (m.1)^-1) _1 (m.2^-1)));
        simpl.
      { apply path_sigma_uncurried; simpl.
        exists left_inverse.
        refine (Morphisms.transport_Fc_to_idtoiso _ _ _ _ _ _ _ _ @ _).
        abstract admit. }
      { apply path_sigma_uncurried; simpl.
        exists right_inverse.
        refine (Morphisms.transport_Fc_to_idtoiso _ _ _ _ _ _ _ _ @ _).
        abstract admit. } }
  Defined.

  Definition isequiv_sigma_category_isomorphism_g
  : (s <~=~> d)%category -> { e : (s.(c) <~=~> d.(c))%category | (p_morphism_of F e s.(x) <~=~> d.(x))%category }.
  Proof.
    { intro m.
      refine (_; _).
      { exists (m : morphism _ _ _).1.
        exists (m^-1).1.
        { exact (ap projT1 (@left_inverse _ _ _ m _)). }
        { exact (ap projT1 (@right_inverse _ _ _ m _)). } }
      { exists (m : morphism _ _ _).2.
        exists ((p_morphism_of F (m : morphism _ _ _).1 _1 (m^-1).2)
                  o ((p_composition_of F _ _ _ (m : morphism _ _ _).1 (m^-1).1) (x d))
                  o (((idtoiso (ap (p_morphism_of F) (ap projT1 (@right_inverse _ _ _ m m)^)))
                      : morphism _ _ _)
                       (x d))
                  o ((p_identity_of F _)^-1 (x d))).
        { (*pose ((p_morphism_of F (m : morphism _ _ _).1 (*_1 (m^-1).2*))).
          pose (m^-1).2. simpl in *.*)
          admit. }
        { admit. } } }
  Defined.

  Definition isequiv_sigma_category_isomorphism_eisretr
  : Sect isequiv_sigma_category_isomorphism_g isequiv_sigma_category_isomorphism_f.
  Proof.
    { intro x; apply path_isomorphic; reflexivity. }
  Qed.

  Definition isequiv_sigma_category_isomorphism_eissect
  : Sect isequiv_sigma_category_isomorphism_f isequiv_sigma_category_isomorphism_g.
  Proof.
    { intro x; apply path_sigma_uncurried; refine (_; _).
      apply path_isomorphic; reflexivity.
      apply path_isomorphic.
      match goal with
        | [ |- context[transport ?P ?p ?x] ]
          => rewrite (transport_compose
                        (fun e : morphism _ _ _ =>
                           ((p_morphism_of F e) (PseudofunctorToCat.Core.x s) <~=~>
                                                PseudofunctorToCat.Core.x d)%category)
                        (fun e : (c s <~=~> c d)%category => e : morphism _ _ _)
                        p)
      end.
      rewrite ap_morphism_isomorphic_path_isomorphic.
      change (transport ?P 1 ?x) with x.
      reflexivity. }
  Qed.

  Definition isequiv_sigma_category_isomorphism
  : { e : (s.(c) <~=~> d.(c))%category | (p_morphism_of F e s.(x) <~=~> d.(x))%category } <~> (s <~=~> d)%category.
  Proof.
    refine (equiv_adjointify isequiv_sigma_category_isomorphism_f
                             isequiv_sigma_category_isomorphism_g
                             isequiv_sigma_category_isomorphism_eisretr
                             isequiv_sigma_category_isomorphism_eissect).
  Defined.
End Grothendieck.
