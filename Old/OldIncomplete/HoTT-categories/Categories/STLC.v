Require Export Category.Core Functor.Core FunctorCategory.
Require Import Common.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Inductive Fin : nat -> Type :=
| Zero : forall n, Fin (S n)
| Next : forall n, Fin n -> Fin (S n).

Inductive Term (n : nat) :=
| Var : Fin n -> Term n
| App : Term n -> Term n -> Term n
| Lambda : Term (S n) -> Term n.

Inductive Type

Fixpoint TermDenote n (t : Term n)
