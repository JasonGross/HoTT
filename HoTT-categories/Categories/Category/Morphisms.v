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


Section AssociativityComposition.
  Variable C : PreCategory.
  Variables x0 x1 x2 x3 x4 : C.

  Lemma compose4associativity_helper
    (a : Morphism C x3 x4) (b : Morphism C x2 x3)
    (c : Morphism C x1 x2) (d : Morphism C x0 x1)
  : (a ∘ b) ∘ (c ∘ d) = (a ∘ ((b ∘ c) ∘ d)).
  Proof.
    rewrite !Associativity; reflexivity.
  Qed.

  Lemma compose4associativity_helper2
    (a : Morphism C x3 x4) (b : Morphism C x2 x3)
    (c : Morphism C x1 x2) (d : Morphism C x0 x1)
  : a ∘ b ∘ c ∘ d = (a ∘ ((b ∘ c) ∘ d)).
  Proof.
    rewrite !Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (a ∘ ((b ∘ c) ∘ d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- (?a ∘ ?b) ∘ (?c ∘ ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = (?a ∘ ?b) ∘ (?c ∘ ?d) ] => compose4associativity' a b c d
  end.
