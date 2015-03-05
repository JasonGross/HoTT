(** * Saturation of the Grothendieck Construction of a functor to cat *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Univalent.
Require Import Category.Morphisms.
Require Import Pseudofunctor.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Isomorphisms.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core.
Require Import Cat.Core.
Require Import Grothendieck.PseudofunctorToCat.Core Grothendieck.PseudofunctorToCat.Morphisms.
From HoTT.Basics Require Import Equivalences Trunc PathGroupoids.
From HoTT.Types Require Import Universe Paths Sigma.
Require Import HoTT.UnivalenceImpliesFunext.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section Grothendieck.
  Context `{Funext}.
  Context {C : PreCategory}
          `{IsCategory C}
          {F : Pseudofunctor C}
          `{forall c, IsCategory (F c)}.

  Definition category_isotoid_helper {s d} (a : c s = c d)
  : (transport (fun c : C => F c) a (x s) = x d)
      <~> ((p_morphism_of F (Category.Morphisms.idtoiso C a)) (x s) <~=~> x d)%category.
  Proof.
    generalize (x d).
    destruct a; simpl.
    intro xd.
    refine (_ oE equiv_concat_l _ _); shelve_unifiable; cycle 1.
    { exact (isotoid _ _ _ {| morphism_isomorphic := (p_identity_of F (c s)) (x s) |}). }
    { exists (@Category.Morphisms.idtoiso _ _ _).
      exact _. }
  Defined.

  Arguments category_isotoid_helper : simpl never.

  Definition category_isotoid {s d : category F}
  : s = d <~> (s <~=~> d)%category.
  Proof.
    refine (isequiv_sigma_category_isomorphism oE _ oE (equiv_ap' (issig_pair F)^-1 s d)).
    refine (_ oE (equiv_path_sigma _ _ _)^-1).
    simpl.
    refine (equiv_functor_sigma' _ _).
    { exists (@Category.Morphisms.idtoiso C _ _).
      exact _. }
    { exact category_isotoid_helper. }
  Defined.

  Global Instance preservation : IsCategory (category F).
  Proof.
    intros s d.
    refine (@isequiv_homotopic _ _ category_isotoid (Category.Morphisms.idtoiso (category F) (x:=s) (y:=d)) (@equiv_isequiv _ _ category_isotoid) _).
    intro x.
    destruct x; apply path_isomorphic, path_sigma_uncurried.
    exists idpath.
    simpl.
    unfold pr2_path; simpl.
    abstract (rewrite concat_p1, eisretr; reflexivity).
  Defined.
End Grothendieck.
