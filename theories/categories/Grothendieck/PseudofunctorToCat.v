(** * Grothendieck Construction of a pseudofunctor to Cat *)
(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** construction *)
Require Grothendieck.PseudofunctorToCat.Core.

(** ** classification of morphisms *)
Require Grothendieck.PseudofunctorToCat.Morphisms.

(** ** preservation of saturation *)
Require Grothendieck.PseudofunctorToCat.Univalent.

Include Grothendieck.PseudofunctorToCat.Core.
