(** * Lax Comma Categories *)
(** Since there are only notations in [LaxComma.Notations], we can just export those. *)
Require Export LaxComma.Notations.

(** ** Definitions *)
Require LaxComma.Core.

Include LaxComma.Core.
(** We don't want to make utf-8 notations the default, so we don't export them. *)

(** We export the components that go into core, because they don't
    define any top-level constants, and we want nice access to the
    names to unfold them. *)
Export LaxComma.Core.Parts.
Export LaxComma.Core.AssociativityLaw.
Export LaxComma.Core.LeftIdentityLaw.
Export LaxComma.Core.RightIdentityLaw.
