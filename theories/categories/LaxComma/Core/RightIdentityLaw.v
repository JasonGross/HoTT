(** * Right identity law in a lax comma category *)
Require Import LaxComma.Core.LawsTactic.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

(** Quoting David Spivak:

    David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ∘ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]

     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ∘ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)

Module Import LaxCommaCategory.
  Section lax_comma_category_parts.
    Context `{Funext}.
    Variable A : PreCategory.
    Variable B : PreCategory.

    Variable S : Pseudofunctor A.
    Variable T : Pseudofunctor B.

    Context `{forall a b, IsHSet (Functor (S a) (T b))}.

    Local Notation object := (@object _ A B S T).
    Local Notation morphism := (@morphism _ A B S T).
    Local Notation compose := (@compose _ A B S T).
    Local Notation identity := (@identity _ A B S T).

    (** To generate the type of this helper lemma, we used:
<<
      Lemma right_identity (s d : object) (m : morphism s d)
      : compose m (identity _) = m.
      Proof.
        refine (@path_morphism' _ _
                               (compose m (identity _)) m
                               (Category.Core.right_identity _ _ _ _)
                               (Category.Core.right_identity _ _ _ _)
                               _).
        simpl in *.
        repeat match goal with
                 | [ |- appcontext[@morphism_inverse
                                     _ _ _ _
                                     (@isisomorphism_isomorphic
                                        _ _ _
                                        (Category.Morphisms.idtoiso
                                           ?C0
                                           (ap (p_morphism_of ?F (s:=_) (d:=_))
                                               (Category.Core.right_identity ?C ?x ?y ?f))))] ]
                   => generalize (@p_right_identity_of_coherent_inverse_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.right_identity C x y f)))
                 | [ |- appcontext[Category.Morphisms.idtoiso
                                     ?C0
                                     (ap (p_morphism_of ?F (s:=_) (d:=_))
                                         (Category.Core.right_identity ?C ?x ?y ?f))] ]
                   => generalize (@p_right_identity_of_coherent_for_rewrite _ C F x y f);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.right_identity C x y f)))
               end.
        simpl.
        destruct_head morphism.
        destruct_head object.
        simpl in *.
        repeat match goal with
                 | [ |- appcontext[p_composition_of ?F ?x ?y ?z ?m1 ?m2] ]
                   => generalize dependent (p_composition_of F x y z m1 m2)
                 | [ |- appcontext[p_identity_of ?F ?x] ]
                   => generalize dependent (p_identity_of F x)
                 | [ |- appcontext[p_morphism_of ?F ?x] ]
                   => generalize dependent (p_morphism_of F x)
                 | [ |- appcontext[p_object_of ?F ?x] ]
                   => generalize dependent (p_object_of F x)
               end.
        simpl.
        clear.
        repeat (let H := fresh "x" in intro H).
        repeat match goal with H : _ |- _ => revert H end.
        intro.
>> *)

    Lemma right_identity_helper
          {x x0 : PreCategory} {x1 : Functor x0 x}
          {x2 x3 : PreCategory} {x4 : Functor x3 x2} {x5 x6 : Functor x3 x0}
          {x7 : Functor x2 x} {x8 : NaturalTransformation (x7 o x4) (x1 o x6)}
          {x9 : Functor x2 x} {x10 : Functor x3 x3} {x11 : Functor x2 x2}
          {x12 : @Isomorphic (_ -> _) x11 1%functor} {x13 : @Isomorphic (_ -> _) x10 1%functor}
          {x14 : @Isomorphic (_ -> _) x9 (x7 o x11)%functor} {x15 : @Isomorphic (_ -> _) x5 (x6 o x10)%functor}
          {x16 : @Isomorphic (_ -> _) x5 x6}
          {x17 : (x16 : Category.Core.morphism _ _ _) =
                 (right_identity_natural_transformation_1 x6 o (x6 oL (x13 : Category.Core.morphism _ _ _) o (x15 : Category.Core.morphism _ _ _)))%natural_transformation}
          {x18 : @Isomorphic (_ -> _) x9 x7}
          {x19 : x18 ^-1 =
                 (x14 ^-1 o (x7 oL x12 ^-1)
                      o inverse (right_identity_natural_transformation_1 x7))%natural_transformation}
    : (x1 oL (x16 : Category.Core.morphism _ _ _)
          o (x1 oL x15 ^-1 o associator_1 x1 x6 x10 o (x8 oR x10)
                o associator_2 x7 x4 x10
                o (x7
                     oL (x4 oL x13 ^-1 o right_identity_natural_transformation_2 x4
                            o left_identity_natural_transformation_1 x4 o
                            ((x12 : Category.Core.morphism _ _ _) oR x4))) o associator_1 x7 x11 x4 o
                ((x14 : Category.Core.morphism _ _ _) oR x4)) o (x18 ^-1 oR x4))%natural_transformation = x8.
    Proof.
      Time t. (* 3.26 s *)
    Qed.

    Lemma right_identity (s d : object) (m : morphism s d)
    : compose m (identity _) = m.
    Proof.
      refine (@path_morphism' _ A B S T _ _
                              (compose m (identity _)) m
                              (Category.Core.right_identity _ _ _ _)
                              (Category.Core.right_identity _ _ _ _)
                              _).
      simpl.
      Time refine right_identity_helper.
      - exact (p_right_identity_of_coherent_for_rewrite _ _ _ _).
      - exact (p_right_identity_of_coherent_inverse_for_rewrite _ _ _ _).
    Defined.
  End lax_comma_category_parts.
End LaxCommaCategory.
