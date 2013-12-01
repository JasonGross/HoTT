Require Export Category Functor UniversalProperties Functor.Composition.Functorial Functor.Product.
Require Import Common FunctorCategory NaturalTransformation.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.
Local Open Scope category_scope.

Section KanExtensions.
  Context `{Funext}.
  Variable C : Category.
  Variable D : Category.
  Variable S : Category.

  Section Δ.
    Definition PullbackAlongFunctor : [[C, D], [[D, S], [C, S]]]%category
      := FunctorialComposition C D S.
    Definition PullbackAlong (F : Functor C D) : [[D, S], [C, S]]%category
      := Eval hnf in PullbackAlongFunctor F.
  End Δ.

  Section Kan.
    Definition IsRightKanExtension F
      := IsTerminalMorphism (U := PullbackAlong F) (X := F).

  Definition Colimit := @InitialMorphism (C ^ D) _ F (DiagonalFunctor C D).
  Definition IsColimit := @IsInitialMorphism (C ^ D) _ F (DiagonalFunctor C D).
  (*  Definition Colimit (c : C) :=
    { t : SmallNaturalTransformation F ((DiagonalFunctor C D) c) &
      forall X : C, forall s : SmallNaturalTransformation F ((DiagonalFunctor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((DiagonalFunctor C D).(MorphismOf) s') t = s
        }
    }.*)

  Section coercions.
    Definition Limit_IsLimit : forall o : Limit, IsLimit o
      := fun o => TerminalMorphism_IsTerminalMorphism o.
    Definition IsLimit_Limit : forall o, IsLimit o -> Limit
      := fun o H => IsTerminalMorphism_TerminalMorphism H.

    Global Coercion Limit_IsLimit : Limit >-> IsLimit.
    Global Coercion IsLimit_Limit : IsLimit >-> Limit.

    Definition Colimit_IsColimit : forall o : Colimit, IsColimit o
      := fun o => InitialMorphism_IsInitialMorphism o.
    Definition IsColimit_Colimit : forall o, IsColimit o -> Colimit
      := fun o H => IsInitialMorphism_InitialMorphism H.

    Global Coercion Colimit_IsColimit : Colimit >-> IsColimit.
    Global Coercion IsColimit_Colimit : IsColimit >-> Colimit.
  End coercions.

  Section AbstractionBarrier.
    Variable l : Limit.
    Variable c : Colimit.

    Definition LimitObject := TerminalMorphism_Object l.
    Definition LimitMorphism := TerminalMorphism_Morphism l.
    Definition LimitProperty_Morphism := TerminalProperty_Morphism l.
    Definition LimitProperty := TerminalProperty l.

    Definition ColimitObject := InitialMorphism_Object c.
    Definition ColimitMorphism := InitialMorphism_Morphism c.
    Definition ColimitProperty_Morphism := InitialProperty_Morphism c.
    Definition ColimitProperty := InitialProperty c.
  End AbstractionBarrier.
End Limit.

Section LimitMorphisms.
  Variable C : Category.
  Variable D : Category.
  Variable F : Functor D C.

  Definition MorphismBetweenLimits (L L' : Limit F) : C.(Morphism) (LimitObject L) (LimitObject L').
    unfold Limit, LimitObject in *.
    intro_universal_morphisms.
    intro_universal_property_morphisms.
    match goal with
      | [ |- Morphism _ ?a ?b ] => pose a; pose b
    end.
    specialized_assumption idtac.
  Defined.

  Definition MorphismBetweenColimits (c c' : Colimit F) : C.(Morphism) (ColimitObject c) (ColimitObject c').
    unfold Colimit, ColimitObject in *.
    intro_universal_morphisms.
    intro_universal_property_morphisms.
    match goal with
      | [ |- Morphism _ ?a ?b ] => pose a; pose b
    end.
    specialized_assumption idtac.
  Defined.
End LimitMorphisms.
