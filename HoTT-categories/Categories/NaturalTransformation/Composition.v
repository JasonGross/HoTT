(** Removed already ported things *)

Section notations.
  (** We do some black magic with typeclasses to make notations play
      well.  The cost is extra verbosity, but it will all disappear
      with [simpl]. *)

  Global Class NTC_Composable A B (a : A) (b : B) (T : Type) (term : T) := {}.

  Definition NTC_Composable_term `{@NTC_Composable A B a b T term} := term.
  Global Arguments NTC_Composable_term / .

  Global Instance NTC_FunctorComposition C D E (F : Functor D E) (G : Functor C D)
  : NTC_Composable F G (ComposeFunctors F G) | 1000.

  Global Instance NTC_NTComposition C D (F F' F'' : Functor C D)
         (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F')
  : NTC_Composable T' T (NTComposeT T' T) | 10.

  Global Instance NTC_NTWhiskerL C D E (F : Functor D E) (G G' : Functor C D)
         (T : NaturalTransformation G G')
  : NTC_Composable F T (NTWhiskerL F T) | 100.

  Global Instance NTC_NTWhiskerR C D E (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
  : NTC_Composable T G (NTWhiskerR T G) | 100.
End notations.

Hint Unfold NTC_Composable_term : typeclass_instances.

(* ASCII notations *)
(* Set some notations for printing *)
Infix "o" := NTComposeT : natural_transformation_scope.
Infix "o" := NTWhiskerL : natural_transformation_scope.
Infix "o" := NTWhiskerR : natural_transformation_scope.
Infix "o" := ComposeFunctors : natural_transformation_scope.
(* Notation for parsing *)
Notation "T 'o' U"
  := (@NTC_Composable_term _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.


(* Unicode Notations *)
(* Set some notations for printing *)
Infix "∘" := NTComposeT : natural_transformation_scope.
Infix "∘" := NTWhiskerL : natural_transformation_scope.
Infix "∘" := NTWhiskerR : natural_transformation_scope.
Infix "∘" := ComposeFunctors : natural_transformation_scope.
(* Notation for parsing *)
Notation "T ∘ U"
  := (@NTC_Composable_term _ _ T%natural_transformation U%natural_transformation _ _ _)
     : natural_transformation_scope.

(*
Unset Printing Notations.
Eval simpl in (_ ∘ _)%natural_transformation. (* should be NTComposeT *)
Eval simpl in (_ ∘ (_ : Functor _ _))%natural_transformation. (* should be NTWhiskerR *)
Eval simpl in ((_ : Functor _ _) ∘ _)%natural_transformation. (* should be NTWhiskerL *)
Eval simpl in ((_ : Functor _ _) ∘ (_ : Functor _ _))%natural_transformation. (* should be ComposeFunctors *)
Check (fun C D E (F : Functor D E) (G : Functor C D) => (F ∘ G)%natural_transformation).
Eval simpl in (fun C D E (F : Functor D E) (G : Functor C D) => (F ∘ G)%natural_transformation).
Check (fun B C D E (F : Functor D E) (G : Functor C D) (H : Functor B C) => (F ∘ G ∘ H)%natural_transformation).
Eval simpl in (fun B C D E (F : Functor D E) (G : Functor C D) (H : Functor B C) => (F ∘ G ∘ H)%natural_transformation).
Check (fun C D E (F : Functor D E) (G G' : Functor C D) (T : NaturalTransformation G G') => (F ∘ T)%natural_transformation).
Eval simpl in (fun C D E (F : Functor D E) (G G' : Functor C D) (T : NaturalTransformation G G') => (F ∘ T)%natural_transformation).
*)
