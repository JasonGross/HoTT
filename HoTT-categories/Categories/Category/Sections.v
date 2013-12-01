Require Export Category.Core Functor.Core.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

Class IsSectionOf C x y (s : Morphism C x y) (r : Morphism C y x)
  := is_sect_morphism : r ∘ s = Identity _.

Arguments IsSectionOf [C x y] s r.

Instance trunc_IsSectionOf C x y s r
: IsHProp (@IsSectionOf C x y s r).
Proof.
  unfold IsSectionOf.
  typeclasses eauto.
Defined.

Structure SectionOf {C x y} (r : Morphism C y x) :=
  {
    SectionMorphism :> Morphism C x y;
    SectionIsSection : IsSectionOf SectionMorphism r
  }.

Existing Instance SectionIsSection.

Bind Scope section_scope with SectionOf.

Arguments Build_SectionOf {C x y} r _ {_}, {C x y r} _ {_}.

Local Ltac sect_t' :=
  solve [ autorewrite with morphism;
          reflexivity
        | repeat (rewrite_hyp;
                  autorewrite with morphism);
          reflexivity ].

Local Ltac sect_t :=
  first [ sect_t'
        | try_associativity_quick sect_t' ].

Section is_sections.
  Variable C : PreCategory.

  Section properties.
    Global Instance IdentityIsSection (x : C)
    : IsSectionOf (Identity x) (Identity x)
      := IdentityIdentity _ _.

    Global Instance IsSectionComposition x y z
           `(@IsSectionOf C y z s1 r1)
           `(@IsSectionOf C x y s2 r2)
    : IsSectionOf (s1 ∘ s2) (r2 ∘ r1).
    Proof.
      unfold IsSectionOf in *.
      transitivity (r2 ∘ (r1 ∘ s1) ∘ s2);
        sect_t.
    Qed.
  End properties.
End is_sections.

Hint Immediate @IdentityIsSection @IsSectionComposition : category morphism.

Section sections.
  Variable C : PreCategory.

  Definition IdentitySection (x : C) : SectionOf (Identity x)
    := Build_SectionOf (Identity x).

  Definition ComposeSections
             `(s1 : @SectionOf C y z r1)
             `(s2 : @SectionOf C x y r2)
  : SectionOf (r2 ∘ r1)
    := Build_SectionOf (s1 ∘ s2).

  Definition ComposeSectionsAssociativity
  :
