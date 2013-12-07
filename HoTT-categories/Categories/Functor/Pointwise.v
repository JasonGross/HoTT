(** Removed already-ported things from top *)

Section notations.
  (** We do some black magic with typeclasses to make notations play
      well.  The cost is extra verbosity, but it will all disappear
      with [simpl]. *)

  Global Class PointwiseFunctor_Typable `{Funext} A B (a : A) (b : B) (T : Type) (term : T) := {}.

  Definition PointwiseFunctor_Typable_term `{@PointwiseFunctor_Typable H A B a b T term} := term.
  Global Arguments PointwiseFunctor_Typable_term / .

  Global Instance PointwiseFunctor_FunctorFunctor `{Funext} C C' D D' (F : Functor C C') (G : Functor D D')
  : PointwiseFunctor_Typable F G (PointwiseFunctor F G) | 1000.

  Global Instance PointwiseFunctor_CategoryFunctor `{Funext} C D D' (G : Functor D D')
  : PointwiseFunctor_Typable C G (PointwiseFunctorWhiskerL C G) | 100.

  Global Instance PointwiseFunctor_FunctorCategory `{Funext} C C' (F : Functor C C') D
  : PointwiseFunctor_Typable F D (PointwiseFunctorWhiskerR F D) | 100.

  Global Instance PointwiseFunctor_CategoryCategory `{Funext} C D
  : PointwiseFunctor_Typable C D (FunctorCategory C D) | 10.
End notations.

Hint Unfold PointwiseFunctor_Typable_term : typeclass_instances.

(** Set some notations for printing *)
Notation "G ^ F" := (PointwiseFunctor F G) : functor_scope.
Notation "D ^ F" := (PointwiseFunctorWhiskerR F D) : functor_scope.
Notation "G ^ C" := (PointwiseFunctorWhiskerL C G) : functor_scope.
(** Included for completeness, but not required, because we want the version in category_scope to dominate. *)
Notation "D ^ C" := (FunctorCategory C D) (only parsing) : functor_scope.
Notation "[ F , G ]" := (PointwiseFunctor F G) : functor_scope.
Notation "[ F , D ]" := (PointwiseFunctorWhiskerR F D) : functor_scope.
Notation "[ C , G ]" := (PointwiseFunctorWhiskerL C G) : functor_scope.
(** Included for completeness, but not required, because we want the version in category_scope to dominate. *)
Notation "[ C , D ]" := (FunctorCategory C D) (only parsing) : functor_scope.

(* Notation for parsing *)
Notation "G ^ F"
  := (@PointwiseFunctor_Typable_term _ _ _ F%functor G%functor _ _ _) : functor_scope.
Notation "[ F , G ]"
  := (@PointwiseFunctor_Typable_term _ _ _ F%functor G%functor _ _ _) : functor_scope.
