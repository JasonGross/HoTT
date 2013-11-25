(** * Kan Extensions *)
(** ** Definitions *)
Require KanExtensions.Core.
(** ** Kan Extensions assemble into functors *)
Require KanExtensions.Functors.
Require KanExtensions.Pointwise.

Include KanExtensions.Core.
Include KanExtensions.Functors.
Include KanExtensoins.Pointwise.
