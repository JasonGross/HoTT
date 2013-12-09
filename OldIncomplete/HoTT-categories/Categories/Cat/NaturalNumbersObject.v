Require Export Cat HoTT.Categories.NaturalNumbersObject NatCategory DiscreteCategory InitialTerminalCategory.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section NNO.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{forall C, IsHProp (P C)}.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Print NaturalNumbersObject.
