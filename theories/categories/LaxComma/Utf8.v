(** * Unicode notations for comma categories *)
Require Import LaxComma.Core.
Require Export LaxComma.Notations.

(** Set some notations for printing *)
Notation "'CAT' ⇓ a" := (@lax_slice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
Notation "'CAT' ⇑ a" := (@lax_coslice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
Notation "a ⇓ 'CAT'" := (@lax_coslice_category_over _ _ _ a _) (at level 40, left associativity) : category_scope.
Notation "x ⇓ F" := (lax_coslice_category x F) (at level 40, left associativity) : category_scope.
Notation "F ⇓ x" := (lax_slice_category x F) : category_scope.
Notation "S ⇓ T" := (lax_comma_category S T) : category_scope.
(** Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
Notation "S ⇓ T" := (get_LCC S T) : category_scope.
