(** * Discrete category *)
Require Import Category.Core Functor.Core.
Require Import GroupoidCategory.Core GroupoidCategory.Elim.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** A discrete category is a groupoid which is a 0-type *)
Module Export Core.
  Definition discrete_category X `{IsHSet X} := groupoid_category X.

  Arguments discrete_category X {_} / .
End Core.

(** ** Functors out of discrete categories *)
Module Export Elim.
  Definition discrete_rec X `{IsHSet X} (D : PreCategory) (object_of : X -> D)
  : Functor (discrete_category X) D
    := groupoid_rec D object_of.

  Arguments discrete_rec X {_} [D] object_of / .
End Elim.

(** ** [discrete_category] assembles into a functor
