(** Removed ported stuff *)

Ltac find_composition_to_identity :=
  match goal with
    | [ H : @Compose _ _ _ _ ?a ?b = @Identity _ _ |- appcontext[@Compose ?B ?C ?D ?E ?c ?d] ]
      => let H' := fresh in
         assert (H' : b = d /\ a = c) by (split; reflexivity); clear H';
         assert (H' : @Compose B C D E c d = @Identity _ _)
           by (
               exact H ||
                     (simpl in H |- *; exact H || (rewrite H; reflexivity))
             );
         first [ rewrite H'
               | simpl in H' |- *; rewrite H'
               | let H'T := type of H' in fail 2 "error in rewriting a found identity" H "[" H'T "]"
               ]; clear H'
  end.
