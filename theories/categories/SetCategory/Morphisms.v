(** * Morphisms in [set_cat] *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Morphisms NaturalTransformation.Paths.
Require Import Category.Univalent.
Require Import SetCategory.Core.
Require Import Overture types.Record types.Sigma HProp HSet types.Universe Equivalences HoTT.Misc UnivalenceImpliesFunext.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Lemma isisomorphism_set_cat_natural_transformation_paths
      `{fs : Funext} (X : set_cat) C D F G
      `{HD : forall s d, IsHSet (morphism D s d)}
      (T1 T2 : morphism set_cat X (BuildhSet (@NaturalTransformation C D F G) (@trunc_natural_transformation _ _ _ _ _ _ _)))
      (H : forall x y, T1 x y = T2 x y)
      `{@IsIsomorphism set_cat _ _ T1}
: @IsIsomorphism set_cat _ _ T2.
Proof.
  exists (T1^-1)%morphism;
  abstract (
      first [ apply @iso_moveR_Vp
            | apply @iso_moveR_pV ];
      repeat first [ intro
                   | progress unfold Overture.compose
                   | solve [ auto
                           | symmetry; auto ]
                   | apply @path_forall
                   | path_natural_transformation ]
    ).
Defined.

Section equiv_iso_set_cat.
  (** ** Isomorphisms in [set_cat] are eqivalent to equivalences. *)
  Context `{Funext}.

  Definition isiso_isequiv s d (m : morphism set_cat s d)
             `{IsEquiv _ _ m}
  : IsIsomorphism m
    := Build_IsIsomorphism
         set_cat s d
         m m^-1%equiv
         (path_forall _ _ (eissect _))
         (path_forall _ _ (eisretr _)).

  (*Definition isequiv_isiso s d (m : morphism set_cat s d)
             `{IsIsomorphism _ _ _ m}
  : IsEquiv m
    := BuildIsEquiv
         _ _
         m m^-1%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (fun _ => allpath_hprop _ _).

  Definition iso_equiv (s d : set_cat) (m : s <~> d)
  : s <~=~> d
    := Build_Isomorphic
         (@isiso_isequiv s d m m).

  Global Instance isequiv_isiso_isequiv s d
  : IsEquiv (@iso_equiv s d) | 0.
  Proof.
    refine (isequiv_adjointify
              (@iso_equiv s d)
              (fun m => BuildEquiv _ _ _ (@isequiv_isiso s d m m))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv; simpl;
        apply ap;
        apply allpath_hprop
      ).
  Defined.*)

  (*Lemma path_idtoequiv_idtoiso (s d : set_cat) (p : s = d)
  : iso_equiv s d (equiv_path _ _ (ap setT p)) = idtoiso set_cat p.
  Proof.
    apply path_isomorphic.
    case p.
    reflexivity.
  Defined.*)
End equiv_iso_set_cat.

Section equiv_iso_prop_cat.
  (** ** Isomorphisms in [prop_cat] are eqivalent to equivalences. *)
  Context `{Funext}.

  Definition isiso_isequiv_prop s d (m : morphism prop_cat s d)
             `{IsEquiv _ _ m}
  : IsIsomorphism m
    := Build_IsIsomorphism
         prop_cat s d
         m m^-1%equiv
         (path_forall _ _ (eissect _))
         (path_forall _ _ (eisretr _)).

  Definition isequiv_isiso_prop s d (m : morphism prop_cat s d)
             `{IsIsomorphism _ _ _ m}
  : IsEquiv m
    := BuildIsEquiv
         _ _
         m m^-1%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (fun _ => allpath_hprop _ _).

  Definition iso_equiv_prop (s d : prop_cat) (m : s <~> d)
  : s <~=~> d
    := Build_Isomorphic
         (@isiso_isequiv_prop s d m m).

  Global Instance isequiv_isiso_isequiv_prop s d
  : IsEquiv (@iso_equiv_prop s d) | 0.
  Proof.
    refine (isequiv_adjointify
              (@iso_equiv_prop s d)
              (fun m => BuildEquiv _ _ _ (@isequiv_isiso_prop s d m m))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv_prop; simpl;
        apply ap;
        apply allpath_hprop
      ).
  Defined.

  (*Lemma path_idtoequiv_idtoiso_prop (s d : prop_cat) (p : s = d)
  : iso_equiv_prop s d (equiv_path _ _ (ap hproptype p)) = idtoiso prop_cat p.
  Proof.
    apply path_isomorphic.
    case p.
    reflexivity.
  Defined.*)
End equiv_iso_prop_cat.

Local Close Scope morphism_scope.
(*Instance iscategory_set_cat `{Univalence}
: IsCategory set_cat.
Proof.
  intros C D.
  eapply @isequiv_homotopic; [ | intro; apply path_idtoequiv_idtoiso ].
  change (IsEquiv (iso_equiv C D o equiv_path C D o @ap _ _ setT C D)).
  typeclasses eauto.
Defined.

Instance iscategory_prop_cat `{Univalence}
: IsCategory prop_cat.
Proof.
  intros C D.
  eapply @isequiv_homotopic; [ | intro; apply path_idtoequiv_idtoiso_prop ].
  change (IsEquiv (iso_equiv_prop C D o equiv_path C D o @ap _ _ hproptype C D)).
  typeclasses eauto.
Defined.
*)
