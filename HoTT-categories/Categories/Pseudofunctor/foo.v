Set Printing Universes.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Inductive Unit : Type :=
    tt : Unit.

Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Record PreCategory :=
  {
    Object :> Type;
    Morphism : Object -> Object -> Type
  }.

Definition DiscreteCategory X : PreCategory
  := @Build_PreCategory X
                        (@paths X).

Definition IndiscreteCategory X : PreCategory
  := @Build_PreCategory X
                         (fun _ _ => Unit).
Print IndiscreteCategory.
Definition NatCategory (n : nat) :=
  match n with
    | 0 => (fun X : PreCategory => @Build_PreCategory X
                         (fun _ _ => Unit)) Unit
    | _ => DiscreteCategory Bool
  end.
