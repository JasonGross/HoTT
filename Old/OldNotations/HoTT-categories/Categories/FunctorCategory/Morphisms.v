(** Removed already ported things *)

Global Instance NTC_NI_R `{Funext} A (a : A)
       `(T : @NaturalIsomorphism _ C D F G)
       `{@NTC_Composable _ _ a (T : Morphism _ _ _) T' term}
: @NTC_Composable A _ a T T' term | 0.

Global Instance NTC_NI_L `{Funext} A (a : A)
       `(T : @NaturalIsomorphism _ C D F G)
       `{@NTC_Composable _ _ (T : Morphism _ _ _) a T' term}
: @NTC_Composable _ _ T a T' term | 0.
