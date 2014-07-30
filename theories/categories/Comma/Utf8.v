(** * Unicode notations for comma categories *)
Require Import Comma.Core.
Require Export Comma.Notations.

Local Open Scope category_scope.

(** Set some notations for printing *)
Notation "C ↓ a" := (@slice_category_over C a) (at level 70, no associativity) : category_scope.
Notation "a ↓ C" := (@coslice_category_over C a) : category_scope.
Notation "x ↓ F" := (coslice_category x F) : category_scope.
Notation "F ↓ x" := (slice_category x F) : category_scope.
Notation "S ↓ T" := (comma_category S T) : category_scope.
(** Set the notation for parsing. *)
Notation "S ↓ T" := (S / T) (only parsing) : category_scope.
(*Set Printing All.
Require Import Category.Core Functor.Core.
Check (fun (C : PreCategory)(D : PreCategory)(E : PreCategory)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : PreCategory)(E : PreCategory)(S : Functor E D) (x : D) => (x ↓ S)%category).
Check (fun (D : PreCategory)(E : PreCategory)(S : Functor E D) (x : D) => (S ↓ x)%category).*)
