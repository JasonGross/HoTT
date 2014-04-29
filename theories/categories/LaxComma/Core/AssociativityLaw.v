(** * Associativity of composition in a lax comma category *)
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

    (** Ugh. The following code constructs the type of the helper lemma:
<<
      Lemma associativity x1 x2 x3 x4
            (m1 : morphism x1 x2) (m2 : morphism x2 x3) (m3 : morphism x3 x4)
      : compose (compose m3 m2) m1 = compose m3 (compose m2 m1).
      Proof.
        refine (@path_morphism' _ _
                                (compose (compose m3 m2) m1)
                                (compose m3 (compose m2 m1))
                                (Category.Core.associativity _ _ _ _ _ _ _ _)
                                (Category.Core.associativity _ _ _ _ _ _ _ _)
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
                                               (Category.Core.associativity ?C ?x1 ?x2 ?x3 ?x4 ?m1 ?m2 ?m3))))] ]
                   => generalize (@p_composition_of_coherent_inverse_for_rewrite _ C F x1 x2 x3 x4 m1 m2 m3);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.associativity C x1 x2 x3 x4 m1 m2 m3)))
                 | [ |- appcontext[Category.Morphisms.idtoiso
                                     ?C0
                                     (ap (p_morphism_of ?F (s:=_) (d:=_))
                                         (Category.Core.associativity ?C ?x1 ?x2 ?x3 ?x4 ?m1 ?m2 ?m3))] ]
                   => generalize (@p_composition_of_coherent_for_rewrite _ C F x1 x2 x3 x4 m1 m2 m3);
                     generalize (Category.Morphisms.idtoiso
                                   C0
                                   (ap (p_morphism_of F (s:=_) (d:=_))
                                       (Category.Core.associativity C x1 x2 x3 x4 m1 m2 m3)))
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

    Lemma associativity_helper
          {x x0 : PreCategory} {x1 : Functor x0 x}
          {x2 x3 : PreCategory} {x4 : Functor x3 x2} {x5 x6 : PreCategory}
          {x7 : Functor x6 x5} {x8 x9 : PreCategory} {x10 : Functor x9 x8}
          {x11 : Functor x9 x6} {x12 : Functor x9 x3} {x13 : Functor x0 x6}
          {x14 : Functor x9 x6} {x15 : Functor x8 x5} {x16 : Functor x x5}
          {x17 : Functor x9 x0} {x18 : Functor x8 x}
          {x19 : NaturalTransformation (x18 o x10) (x1 o x17)}
          {x20 : Functor x0 x3} {x21 : Functor x x2}
          {x22 : NaturalTransformation (x21 o x1) (x4 o x20)}
          {x23 : Functor x8 x2} {x24 : Functor x3 x6} {x25 : Functor x2 x5}
          {x26 : NaturalTransformation (x25 o x4) (x7 o x24)}
          {x27 : Functor x8 x5} {x28 : @Isomorphic (_ -> _) x27 (x25 o x23)%functor}
          {x29 : @Isomorphic (_ -> _) x23 (x21 o x18)%functor}
          {x30 : @Isomorphic (_ -> _) x16 (x25 o x21)%functor}
          {x31 : @Isomorphic (_ -> _) x15 (x16 o x18)%functor}
          {x32 : @Isomorphic (_ -> _) x14 (x13 o x17)%functor}
          {x33 : @Isomorphic (_ -> _) x13 (x24 o x20)%functor}
          {x34 : @Isomorphic (_ -> _) x12 (x20 o x17)%functor}
          {x35 : @Isomorphic (_ -> _) x11 (x24 o x12)%functor}
          {x36 : @Isomorphic (_ -> _) x14 x11}
          (x37 : (x36 : Category.Core.morphism _ _ _) =
                 (x35 ^-1
                      o (x24 oL x34 ^-1 o (associator_1 x24 x20 x17 o ((x33 : Category.Core.morphism _ _ _) oR x17 o (x32 : Category.Core.morphism _ _ _)))))%natural_transformation)
          {x38 : @Isomorphic (_ -> _) x15 x27}
          (x39 : x38 ^-1 =
                 (x31 ^-1 o (x30 ^-1 oR x18) o inverse (associator_1 x25 x21 x18)
                      o (x25 oL (x29 : Category.Core.morphism _ _ _)) o (x28 : Category.Core.morphism _ _ _))%natural_transformation)
    : (x7 oL (x36 : Category.Core.morphism _ _ _)
          o (x7 oL x32 ^-1 o associator_1 x7 x13 x17
                o (x7 oL x33 ^-1 o associator_1 x7 x24 x20 o (x26 oR x20)
                      o associator_2 x25 x4 x20 o (x25 oL x22) o
                      associator_1 x25 x21 x1 o ((x30 : Category.Core.morphism _ _ _) oR x1) oR x17)
                o associator_2 x16 x1 x17 o (x16 oL x19) o associator_1 x16 x18 x10
                o ((x31 : Category.Core.morphism _ _ _) oR x10)) o (x38 ^-1 oR x10))%natural_transformation =
      (x7 oL x35 ^-1 o associator_1 x7 x24 x12 o (x26 oR x12)
          o associator_2 x25 x4 x12
          o (x25
               oL (x4 oL x34 ^-1 o associator_1 x4 x20 x17 o (x22 oR x17)
                      o associator_2 x21 x1 x17 o (x21 oL x19)
                      o associator_1 x21 x18 x10 o ((x29 : Category.Core.morphism _ _ _) oR x10)))
          o associator_1 x25 x23 x10 o ((x28 : Category.Core.morphism _ _ _) oR x10))%natural_transformation.
    Proof.
      Time t. (* 18.647s *)
    Qed.

    Lemma associativity x1 x2 x3 x4
          (m1 : morphism x1 x2) (m2 : morphism x2 x3) (m3 : morphism x3 x4)
    : compose (compose m3 m2) m1 = compose m3 (compose m2 m1).
    Proof.
      refine (@path_morphism' _ A B S T _ _
                              (compose (compose m3 m2) m1)
                              (compose m3 (compose m2 m1))
                              (Category.Core.associativity _ _ _ _ _ _ _ _)
                              (Category.Core.associativity _ _ _ _ _ _ _ _)
                              _).
      simpl.
      Time apply associativity_helper.
      - Time exact (p_composition_of_coherent_for_rewrite _ _ _ _ _ _ _ _).
      - Time exact (p_composition_of_coherent_inverse_for_rewrite _ _ _ _ _ _ _ _).
    Defined.
  End lax_comma_category_parts.
End LaxCommaCategory.
