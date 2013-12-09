(* Remove ported things *)

(** * Version of [Associativity] that avoids going off into the weeds in the presence of unification variables *)

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar (C : PreCategory) x1 x2 x3 x4
      (m1 : C.(Morphism) x1 x2)
      (m2 : C.(Morphism) x2 x3)
      (m3 : C.(Morphism) x3 x4)
: NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> (m3 ∘ m2) ∘ m1 = m3 ∘ (m2 ∘ m1).
Proof.
  intros; apply Associativity.
Qed.

Ltac noEvar_tauto :=
  (eassumption
     || (left; noEvar_tauto)
     || (right; noEvar_tauto)).

Ltac noEvar := match goal with
                 | [ |- context[NoEvar ?X] ]
                   => (has_evar X; fail 1)
                        || cut (NoEvar X); [ intro; noEvar_tauto | constructor ]
               end.

Hint Rewrite @AssociativityNoEvar using noEvar : category.
Hint Rewrite @AssociativityNoEvar using noEvar : morphism.

Ltac try_associativity_quick tac := try_rewrite Associativity tac.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.
Ltac try_associativity_quick_rewrite H := try_associativity_quick ltac:(rewrite H).
Ltac try_associativity_quick_rewrite_rev H := try_associativity_quick ltac:(rewrite <- H).
Ltac try_associativity_rewrite H := try_associativity ltac:(rewrite H).
Ltac try_associativity_rewrite_rev H := try_associativity ltac:(rewrite <- H).
