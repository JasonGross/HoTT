Require Eqdep_dec JMeq ProofIrrelevance Setoid FunctionalExtensionality Eqdep.
Module Common.
Import JMeq ProofIrrelevance Eqdep_dec.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq (at level 70).

 
Section sig.
  Definition sigT_of_sigT2 A P Q (x : @sigT2 A P Q) := let (a, h, _) := x in existT _ a h.
  Global Coercion sigT_of_sigT2 : sigT2 >-> sigT.
  Definition projT3 A P Q (x : @sigT2 A P Q) :=
    let (x0, _, h) as x0 return (Q (projT1 x0)) := x in h.

  Definition sig_of_sig2 A P Q (x : @sig2 A P Q) := let (a, h, _) := x in exist _ a h.
  Global Coercion sig_of_sig2 : sig2 >-> sig.
  Definition proj3_sig A P Q (x : @sig2 A P Q) :=
    let (x0, _, h) as x0 return (Q (proj1_sig x0)) := x in h.
End sig.

 
Tactic Notation "not_tac" tactic(tac) := (tac; fail 1) || idtac.

 
Tactic Notation "test_tac" tactic(tac) := not_tac (not_tac tac).

 
Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => pose proof defn
    end.

 
Tactic Notation "has_no_body" hyp(H) :=
  not_tac (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "has_body" hyp(H) :=
  not_tac (has_no_body H).

 
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

 
Ltac t' := repeat progress (simpl in *; intros; try split; trivial).
Ltac t'_long := repeat progress (simpl in *; intuition).

Ltac t_con_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_con_rev_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite <- H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_with tac := t_con_with @eq tac.

Ltac t_rev_with tac := t_con_rev_with @eq tac.

Ltac t := t_with t'; t_with t'_long.

 
Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

 
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in  *) .
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

 
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).

Ltac destruct_hypotheses_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | ex _ => idtac
      | and _ _ => idtac
      | prod _ _ => idtac
    end.
Ltac destruct_hypotheses := destruct_all_matches destruct_hypotheses_matcher.

Ltac destruct_sig_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | @sig _ _ => idtac
      | @sigT _ _ => idtac
      | @sig2 _ _ _ => idtac
      | @sigT2 _ _ _ => idtac
    end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_hypotheses_matcher HT || destruct_sig_matcher HT
).

 
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @ex;
  match goal with
    | [ |- @ex ?T _ ] => destruct_exists' T
    | [ |- @sig ?T _ ] => destruct_exists' T
    | [ |- @sigT ?T _ ] => destruct_exists' T
    | [ |- @sig2 ?T _ _ ] => destruct_exists' T
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

 
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique_pose (H x)
         end.

Ltac try_rewrite_by rew_H by_tac tac :=
  (repeat rewrite rew_H by by_tac; tac) ||
    (repeat rewrite <- rew_H by by_tac; tac).

Lemma sig_eq A P (s s' : @sig A P) : proj1_sig s = proj1_sig s' -> s = s'.
admit.
Defined.

Lemma sig2_eq A P Q (s s' : @sig2 A P Q) : proj1_sig s = proj1_sig s' -> s = s'.
admit.
Defined.

Lemma sigT_eq A P (s s' : @sigT A P) : projT1 s = projT1 s' -> projT2 s == projT2 s' -> s = s'.
admit.
Defined.

Lemma sigT2_eq A P Q (s s' : @sigT2 A P Q) :
  projT1 s = projT1 s'
  -> projT2 s == projT2 s'
  -> projT3 s == projT3 s'
  -> s = s'.
admit.
Defined.

Lemma injective_projections_JMeq (A B A' B' : Type) (p1 : A * B) (p2 : A' * B') :
  fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
admit.
Defined.

Ltac clear_refl_eq :=
  repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
         end.

 
Ltac simpl_eq' :=
  apply sig_eq
        || apply sig2_eq
        || ((apply sigT_eq || apply sigT2_eq); intros; clear_refl_eq)
        || apply injective_projections
        || apply injective_projections_JMeq.

Ltac simpl_eq := intros; repeat (
  simpl_eq'; simpl in *
).

 
Ltac subst_eq_refl_dec :=
  repeat match goal with
           | [ H : ?a = ?a |- _ ] => clear H
           | [ H : ?a = ?a |- _ ] => assert (eq_refl = H)
                                    by abstract solve
                                                [ apply K_dec;
                                                  solve [ try decide equality; try congruence ]
                                                | assumption
                                                | easy ];
                                    subst H
         end.

 
Ltac generalize_eq_match :=
  repeat match goal with
           | [ |- appcontext[match ?f ?x with eq_refl => _ end] ] =>
             let H := fresh in
             progress set (H := f x);
               clearbody H
         end.

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

 
Inductive Common_sigT (A : Type) (P : A -> Type) : Type :=
    Common_existT : forall x : A, P x -> Common_sigT P.
Definition Common_projT1 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (a, _) := x in a.
Definition Common_projT2 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (x0, h) as x0 return (P (Common_projT1 x0)) := x in h.

Lemma fg_equal A B (f g : A -> B) : f = g -> forall x, f x = g x.
admit.
Defined.

Section telescope.
  Inductive telescope :=
  | Base : forall (A : Type) (B : A -> Type), (forall a, B a) -> (forall a, B a) -> telescope
  | Quant : forall A : Type, (A -> telescope) -> telescope.

  Fixpoint telescopeOut (t : telescope) :=
    match t with
      | Base _ _ x y => x = y
      | Quant _ f => forall x, telescopeOut (f x)
    end.

  Fixpoint telescopeOut' (t : telescope) :=
    match t with
      | Base _ _ f g => forall x, f x = g x
      | Quant _ f => forall x, telescopeOut' (f x)
    end.

  Theorem generalized_fg_equal : forall (t : telescope),
    telescopeOut t
    -> telescopeOut' t.
admit.
Defined.
End telescope.

Lemma f_equal_helper A0 (A B : A0 -> Type) (f : forall a0, A a0 -> B a0) (x y : forall a0, A a0) :
  (forall a0, x a0 = y a0) -> (forall a0, f a0 (x a0) = f a0 (y a0)).
admit.
Defined.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
admit.
Defined.

Lemma sigT2_eta : forall A (P Q : A -> Type) (x : sigT2 P Q),
  x = existT2 _ _ (projT1 x) (projT2 x) (projT3 x).
admit.
Defined.

Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
admit.
Defined.

Lemma sig2_eta : forall A (P Q : A -> Prop) (x : sig2 P Q),
  x = exist2 _ _ (proj1_sig x) (proj2_sig x) (proj3_sig x).
admit.
Defined.

Lemma prod_eta : forall (A B : Type) (x : A * B),
  x = pair (fst x) (snd x).
admit.
Defined.

Ltac rewrite_eta_in Hf :=
  repeat match type of Hf with
           | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
           | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf
           | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
           | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
           | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
         end.

Ltac intro_proj2_sig_from_goal_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
         end; simpl in *.
Ltac intro_proj2_sig_from_goal := intro_proj2_sig_from_goal_by unique_pose.

Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

 
Ltac existential_to_evar x :=
  is_evar x;
  let x' := fresh in
  set (x' := x) in *.

 
Ltac existentials_to_evars_in_goal :=
  repeat match goal with
           | [ |- context[?x] ] => existential_to_evar x
         end.

 
Ltac existentials_to_evars_in_hyps :=
  repeat match goal with
           | [ H : context[?x] |- _ ] => existential_to_evar x
         end.

 
Ltac existentials_to_evars_in H :=
  repeat match type of H with
           | context[?x] => existential_to_evar x
         end.

Tactic Notation "existentials_to_evars" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "|-" "*" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "*" := existentials_to_evars_in_goal; existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" "*" "|-" := existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" "*" := existentials_to_evars_in H; existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" hyp(H) := existentials_to_evars_in H.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" := existentials_to_evars_in H.

Ltac do_for_each_hyp' tac fail_if_seen :=
  match goal with
    | [ H : _ |- _ ] => fail_if_seen H; tac H; try do_for_each_hyp' tac ltac:(fun H' => fail_if_seen H'; match H' with | H => fail 1 | _ => idtac end)
  end.
Ltac do_for_each_hyp tac := do_for_each_hyp' tac ltac:(fun H => idtac).

 
Tactic Notation "change_in_all" constr(from) "with" constr(to) :=
  change from with to; do_for_each_hyp ltac:(fun H => change from with to in H).

 
Ltac expand :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

 
Ltac hideProof' pf :=
  match goal with
    | [ x : _ |- _ ] => match x with
                          | pf => fail 2
                        end
    | _ => generalize pf; intro
  end.

 
Tactic Notation "hideProofs" constr(pf)
  := hideProof' pf.
Tactic Notation "hideProofs" constr(pf0) constr(pf1)
  := progress (try hideProof' pf0; try hideProof' pf1).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4) constr(pf5)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4; try hideProof' pf5).

Section unique.
  Definition uniqueT (A : Type) (P : A -> Type) (x : A)
    := P x + {forall x' : A, P x' -> x = x'}.
End unique.

Section True.
  Lemma True_singleton (u : True) : u = I.
admit.
Defined.

  Lemma True_eq (u u' : True) : u = u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma True_eq_singleton (u u' : True) (H : u = u') : H = True_eq _ _.
    destruct u; destruct H; reflexivity.
  Defined.

  Lemma True_eq_eq (u u' : True) (H H' : u = u') : H = H'.
    transitivity (@True_eq u u');
    destruct_head @eq; subst_body; destruct_head True; reflexivity.
  Defined.

  Lemma True_JMeq (u u' : True) : u == u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma True_eqT_eq (u u' v v' : True) : @eq Type (u = u') (v = v').
admit.
Defined.

  Lemma True_eqS_eq (u u' v v' : True) : @eq Set (u = u') (v = v').
admit.
Defined.

  Lemma True_eqP_eq (u u' v v' : True) : @eq Prop (u = u') (v = v').
admit.
Defined.

  Lemma True_eq_JMeq (u u' v v' : True) (H : u = u') (H' : v = v') : H == H'.
admit.
Defined.

  Lemma False_eq (a b : False) : a = b.
    destruct a.
  Defined.

  Lemma False_JMeql (a : False) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma False_JMeqr T (a : T) (b : False) : a == b.
    destruct b.
  Defined.
End True.

Section unit.
  Lemma unit_singleton (u : unit) : u = tt.
admit.
Defined.

  Lemma unit_eq (u u' : unit) : u = u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma unit_eq_singleton (u u' : unit) (H : u = u') : H = unit_eq _ _.
    destruct u; destruct H; reflexivity.
  Defined.

  Lemma unit_eq_eq (u u' : unit) (H H' : u = u') : H = H'.
    transitivity (@unit_eq u u');
    destruct_head @eq; subst_body; destruct_head unit; reflexivity.
  Defined.

  Lemma unit_JMeq (u u' : unit) : u == u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma unit_eqT_eq (u u' v v' : unit) : @eq Type (u = u') (v = v').
admit.
Defined.

  Lemma unit_eqS_eq (u u' v v' : unit) : @eq Set (u = u') (v = v').
admit.
Defined.

  Lemma unit_eqP_eq (u u' v v' : unit) : @eq Prop (u = u') (v = v').
admit.
Defined.

  Lemma unit_eq_JMeq (u u' v v' : unit) (H : u = u') (H' : v = v') : H == H'.
admit.
Defined.

  Lemma Empty_set_eq (a b : Empty_set) : a = b.
    destruct a.
  Defined.

  Lemma Empty_set_JMeql (a : Empty_set) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma Empty_set_JMeqr T (a : T) (b : Empty_set) : a == b.
    destruct b.
  Defined.
End unit.

Hint Rewrite True_singleton.
Hint Extern 0 (@eq True _ _) => apply True_eq.
Hint Extern 0 (@eq (@eq True _ _) _ _) => apply True_eq_eq.
Hint Extern 0 (@JMeq True _ True _) => apply True_JMeq.
Hint Extern 0 (@JMeq (@eq True _ _) _ (@eq True _ _) _) => apply True_eq_JMeq.
Hint Extern 0 (@eq Set (@eq True _ _) (@eq True _ _)) => apply True_eqS_eq.
Hint Extern 0 (@eq Prop (@eq True _ _) (@eq True _ _)) => apply True_eqP_eq.
Hint Extern 0 (@eq Type (@eq True _ _) (@eq True _ _)) => apply True_eqT_eq.
Hint Extern 0 True => constructor.
Hint Extern 0 (@eq False _ _) => apply False_eq.
Hint Extern 0 (@JMeq False _ _ _) => apply False_JMeql.
Hint Extern 0 (@JMeq _ _ False _) => apply False_JMeqr.

Hint Rewrite unit_singleton.
Hint Extern 0 (@eq unit _ _) => apply unit_eq.
Hint Extern 0 (@eq (@eq unit _ _) _ _) => apply unit_eq_eq.
Hint Extern 0 (@JMeq unit _ unit _) => apply unit_JMeq.
Hint Extern 0 (@JMeq (@eq unit _ _) _ (@eq unit _ _) _) => apply unit_eq_JMeq.
Hint Extern 0 (@eq Set (@eq unit _ _) (@eq unit _ _)) => apply unit_eqS_eq.
Hint Extern 0 (@eq Prop (@eq unit _ _) (@eq unit _ _)) => apply unit_eqP_eq.
Hint Extern 0 (@eq Type (@eq unit _ _) (@eq unit _ _)) => apply unit_eqT_eq.
Hint Extern 0 unit => constructor.
Hint Extern 0 (@eq Empty_set _ _) => apply Empty_set_eq.
Hint Extern 0 (@JMeq Empty_set _ _ _) => apply Empty_set_JMeql.
Hint Extern 0 (@JMeq _ _ Empty_set _) => apply Empty_set_JMeqr.

End Common.

Module Notations.
Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y == z" (at level 70, no associativity, y at next level).

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x ~= y ~= z" (at level 70, no associativity, y at next level).

Reserved Notation "i ⁻¹" (at level 10).
Reserved Notation "C ᵒᵖ" (at level 10).

Reserved Notation "C ★^ M D" (at level 70, no associativity).
Reserved Notation "C ★^{ M } D" (at level 70, no associativity).

Reserved Notation "S ↓ T" (at level 70, no associativity).

Reserved Notation "S ⇑ T" (at level 70, no associativity).
Reserved Notation "S ⇓ T" (at level 70, no associativity).
Reserved Notation "'CAT' ⇑ D" (at level 70, no associativity).
Reserved Notation "'CAT' ⇓ D" (at level 70, no associativity).

Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ⊗m y" (at level 40, left associativity).

Reserved Notation "f ○ g" (at level 70, right associativity).

Reserved Notation "x ~> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x ∏ y" (at level 40, left associativity).
Reserved Notation "x ∐ y" (at level 50, left associativity).

Reserved Notation "∏_{ x } f" (at level 0, x at level 99).
Reserved Notation "∏_{ x : A } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x : A } f" (at level 0, x at level 99).

 
Reserved Notation "F ⟨ c , - ⟩" (at level 70, no associativity).
Reserved Notation "F ⟨ - , d ⟩" (at level 70, no associativity).

 
Reserved Notation "[ x ]" (at level 0, x at level 200).

Reserved Notation "∫ F" (at level 0).

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope natural_transformation_scope with natural_transformation.

Delimit Scope graph_scope with graph.
Delimit Scope group_elements_scope with group.
Delimit Scope groups_scope with groups.
Delimit Scope vertex_scope with vertex.
Delimit Scope edge_scope with edge.

End Notations.

Module FEqualDep.
Export FunctionalExtensionality JMeq.
Import Common Notations.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section f_equal_dep.
  Theorem f_type_equal {A B A' B'} : A = A' -> B = B' -> (A -> B) = (A' -> B').
admit.
Defined.

  Theorem forall_extensionality_dep : forall {A}
    (f g : A -> Type),
    (forall x, f x = g x) -> (forall x, f x) = (forall x, g x).
admit.
Defined.

  Theorem forall_extensionality_dep_JMeq : forall {A B}
    (f : A -> Type) (g : B -> Type),
    A = B -> (A = B -> forall x y, x == y -> f x == g y) -> (forall x, f x) = (forall x, g x).
admit.
Defined.


  Lemma JMeq_eqT A B (x : A) (y : B) : x == y -> A = B.
admit.
Defined.

  Lemma fg_equal_JMeq A B B' (f : forall a : A, B a) (g : forall a : A, B' a) x :
    f == g -> (f == g -> B = B') -> f x == g x.
admit.
Defined.

  Lemma f_equal_JMeq A A' B B' a b (f : forall a : A, A' a) (g : forall b : B, B' b) :
    f == g -> (f == g -> A' == B') -> (f == g -> a == b) -> f a == g b.
admit.
Defined.

  Lemma f_equal1_JMeq A0 B a0 b0 (f : forall (a0 : A0), B a0) :
    a0 = b0
    -> f a0 == f b0.
admit.
Defined.

  Lemma f_equal2_JMeq A0 A1 B a0 b0 a1 b1 (f : forall (a0 : A0) (a1 : A1 a0), B a0 a1) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> f a0 a1 == f b0 b1.
admit.
Defined.

  Lemma f_equal3_JMeq A0 A1 A2 B a0 b0 a1 b1 a2 b2 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1), B a0 a1 a2) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> f a0 a1 a2 == f b0 b1 b2.
admit.
Defined.

  Lemma f_equal4_JMeq A0 A1 A2 A3 B a0 b0 a1 b1 a2 b2 a3 b3 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2), B a0 a1 a2 a3) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> f a0 a1 a2 a3 == f b0 b1 b2 b3.
admit.
Defined.

  Lemma f_equal5_JMeq A0 A1 A2 A3 A4 B a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2) (a4 : A4 a0 a1 a2 a3), B a0 a1 a2 a3 a4) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3 -> a4 == b4)
    -> f a0 a1 a2 a3 a4 == f b0 b1 b2 b3 b4.
admit.
Defined.

  Lemma eq_JMeq T (A B : T) : A = B -> A == B.
admit.
Defined.

  Theorem functional_extensionality_dep_JMeq : forall {A} {B1 B2 : A -> Type},
    forall (f : forall x : A, B1 x) (g : forall x : A, B2 x),
      (forall x, B1 x = B2 x)
      -> (forall x, f x == g x) -> f == g.
admit.
Defined.

  Theorem functional_extensionality_dep_JMeq' : forall {A1 A2} {B1 : A1 -> Type} {B2 : A2 -> Type},
    forall (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      A1 = A2
      -> (A1 = A2 -> forall x y, x == y -> B1 x = B2 y)
      -> (A1 = A2 -> forall x y, x == y -> f x == g y) -> f == g.
admit.
Defined.
End f_equal_dep.

Inductive identity_dep (A : Type) (a : A) : forall B : Type, B -> Type :=
  identity_dep_refl : identity_dep a a.

Section f_identity_dep.
  Local Infix "~" := identity (at level 50).
  Local Infix "~~" := identity_dep (at level 50).
  Definition f_identity (A B : Type) (f : A -> B) (x y : A) (H : x ~ y) : f x ~ f y
    := match H in (_ ~ y0) return (f x ~ f y0) with
         | identity_refl => identity_refl (f x)
       end.

  Definition f_type_identity {A B A' B'} : A ~ A' -> B ~ B' -> (A -> B) ~ (A' -> B').
    intros; destruct_head identity; reflexivity.
  Defined.

  Axiom functional_extensionality_dep_identity : forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
                                                   (forall x : A, f x ~ g x) -> f ~ g.

  Axiom identity_dep_identity : forall A (x y : A), x ~~ y -> x ~ y.

  Definition functional_extensionality_identity {A B : Type} := fun (f g : A -> B) (H : forall x : A, f x ~ g x) => functional_extensionality_dep_identity f g H.

  Theorem forall_extensionality_dep_identity : forall {A}
                                                      (f g : A -> Type),
                                                 (forall x, f x ~ g x) -> (forall x, f x) ~ (forall x, g x).
admit.
Defined.

  Theorem forall_extensionality_dep_identity_dep : forall {A B}
                                                          (f : A -> Type) (g : B -> Type),
                                                     A ~ B -> (A ~ B -> forall x y, x ~~ y -> f x ~~ g y) -> (forall x, f x) ~ (forall x, g x).
admit.
Defined.

  Definition identity_dep_identityT A B (x : A) (y : B) : x ~~ y -> A ~ B
    := fun H => match H in (_ ~~ b) return _ with
                  | identity_dep_refl => identity_refl A
                end.
End f_identity_dep.

Ltac JMeq_eq :=
  repeat match goal with
           | [ |- _ == _ ] => apply eq_JMeq
           | [ H : _ == _ |- _ ] => apply JMeq_eq in H
         end.

Section misc.
  Lemma sig_JMeq A0 A1 B0 B1 (a : @sig A0 A1) (b : @sig B0 B1) : A1 == B1 -> proj1_sig a == proj1_sig b -> a == b.
admit.
Defined.
End misc.

End FEqualDep.

Module StructureEquality.
Import FunctionalExtensionality ProofIrrelevance JMeq.
Import Common Notations FEqualDep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Ltac structures_eq_simpl_step_with tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; simpl; JMeq_eq.

Ltac structures_eq_step_with_tac structures_equal_tac tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- _ = _ ] => expand; structures_equal_tac
    | [ |- _ == _ ] => expand; structures_equal_tac
    | _ => structures_eq_simpl_step_with tac
  end.

End StructureEquality.

Module Category.
Import JMeq ProofIrrelevance.
Export Notations.
Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Record ComputationalCategory (obj : Type) :=
  Build_ComputationalCategory {
      Object :> _ := obj;
      Morphism : obj -> obj -> Type;

      Identity : forall x, Morphism x x;
      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
    }.

Bind Scope category_scope with ComputationalCategory.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object C%category / : rename.
Arguments Morphism !C%category s d : rename.
 
Arguments Identity [!C%category] x%object : rename.
Arguments Compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Class IsCategory (obj : Type) (C : ComputationalCategory obj) : Prop :=
  {
    Associativity : forall o1 o2 o3 o4
                           (m1 : Morphism C o1 o2)
                           (m2 : Morphism C o2 o3)
                           (m3 : Morphism C o3 o4),
                      Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1);
     
    Associativity_sym : forall o1 o2 o3 o4
                               (m1 : Morphism C o1 o2)
                               (m2 : Morphism C o2 o3)
                               (m3 : Morphism C o3 o4),
                          Compose m3 (Compose m2 m1) = Compose (Compose m3 m2) m1;
    LeftIdentity : forall a b (f : Morphism C a b), Compose (Identity b) f = f;
    RightIdentity : forall a b (f : Morphism C a b), Compose f (Identity a) = f
  }.

Record > Category (obj : Type) :=
  Build_Category' {
      UnderlyingCCategory :> ComputationalCategory obj;
      UnderlyingCCategory_IsCategory :> IsCategory UnderlyingCCategory
    }.

Hint Extern 0 (IsCategory _) => solve [ apply UnderlyingCCategory_IsCategory ].

Existing Instance UnderlyingCCategory_IsCategory.

Ltac specialized_category_is_specialized :=
  solve [ apply UnderlyingCCategory_IsCategory ].

Bind Scope category_scope with Category.

Section CategoryInterface.
  Definition Build_Category (obj : Type)
    (Morphism : obj -> obj -> Type)
    (Identity' : forall o : obj, Morphism o o)
    (Compose' : forall s d d' : obj, Morphism d d' -> Morphism s d -> Morphism s d')
    (Associativity' : forall (o1 o2 o3 o4 : obj) (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
      Compose' o1 o2 o4 (Compose' o2 o3 o4 m3 m2) m1 = Compose' o1 o3 o4 m3 (Compose' o1 o2 o3 m2 m1))
    (LeftIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a b b (Identity' b) f = f)
    (RightIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a a b f (Identity' a) = f) :
    @Category obj
    := Eval hnf in
        let C := (@Build_ComputationalCategory obj
                                               Morphism
                                               Identity' Compose') in
        @Build_Category' obj
                                    C
                                    (@Build_IsCategory obj C
                                                                  Associativity'
                                                                  (fun _ _ _ _ _ _ _ => eq_sym (Associativity' _ _ _ _ _ _ _))
                                                                  LeftIdentity'
                                                                  RightIdentity').
End CategoryInterface.

 
Create HintDb category discriminated.
 
Create HintDb morphism discriminated.

Hint Extern 1 => symmetry : category morphism.
 

Hint Immediate UnderlyingCCategory_IsCategory : category morphism.

Hint Resolve @LeftIdentity @RightIdentity @Associativity : category morphism.
Hint Rewrite @LeftIdentity @RightIdentity using try specialized_category_is_specialized : category.
Hint Rewrite @LeftIdentity @RightIdentity using try specialized_category_is_specialized : morphism.

 
Definition LocallyCategory (obj : Type)   := Category obj.
Definition Category (obj : Set)   := Category obj.
Identity Coercion LocallyCategory_Category_Id : LocallyCategory >-> Category.
Identity Coercion Category_LocallyCategory_Id : Category >-> Category.

Section Categories_Equal.
  Lemma Category_contr_eq' `(C : @Category objC) `(D : @Category objC)
        (C_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism C s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : forall (HM : Morphism C = Morphism D),
      match HM in (_ = y) return (forall x : C, y x x) with
        | eq_refl => Identity (C := C)
      end = Identity (C := D)
      -> match
        HM in (_ = y) return (forall s d d' : C, y d d' -> y s d -> y s d')
      with
        | eq_refl => Compose (C := C)
      end = Compose (C := D)
      -> C = D.
admit.
Defined.

  Lemma Category_contr_eq `(C : @Category objC) `(D : @Category objC)
        (C_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism C s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
        (C_morphism_type_contr
         : forall s d (pf1 pf2 : Morphism C s d = Morphism C s d),
             pf1 = pf2)
  : forall (HM : forall s d, Morphism C s d = Morphism D s d),
      (forall x,
         match HM x x in (_ = y) return y with
           | eq_refl => Identity (C := C) x
         end = Identity (C := D) x)
      -> (forall s d d' (m : Morphism D d d') (m' : Morphism D s d),
            match HM s d' in (_ = y) return y with
              | eq_refl =>
                match HM s d in (_ = y) return (y -> Morphism C s d') with
                  | eq_refl =>
                    match
                      HM d d' in (_ = y) return (y -> Morphism C s d -> Morphism C s d')
                    with
                      | eq_refl => Compose (d':=d')
                    end m
                end m'
            end = Compose m m')
      -> C = D.
admit.
Defined.

  Lemma Category_eq `(C : @Category objC) `(D : @Category objC) :
    Morphism C = Morphism D
    -> Identity C == Identity D
    -> Compose C == Compose D
    -> C = D.
admit.
Defined.

  Lemma Category_JMeq `(C : @Category objC) `(D : @Category objD) :
    objC = objD
    -> Morphism C == Morphism D
    -> Identity C == Identity D
    -> Compose C == Compose D
    -> C == D.
admit.
Defined.
End Categories_Equal.

 

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar `(C : @Category obj) : forall (o1 o2 o3 o4 : C) (m1 : C.(Morphism) o1 o2)
  (m2 : C.(Morphism) o2 o3) (m3 : C.(Morphism) o3 o4),
  NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1).
admit.
Defined.

Ltac noEvar := try specialized_category_is_specialized;
              match goal with
                | [ |- context[NoEvar ?X] ] => (has_evar X; fail 1)
                                                 || cut (NoEvar X); [ intro; tauto | constructor ]
              end.

Hint Rewrite @AssociativityNoEvar using noEvar : category.
Hint Rewrite @AssociativityNoEvar using noEvar : morphism.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.

 

Section Category.
  Context `(@IsCategory obj C).

   
  Definition IsEpimorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) y z), Compose m1 m = Compose m2 m ->
      m1 = m2.
  Definition IsMonomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), Compose m m1 = Compose m m2 ->
      m1 = m2.

  Section properties.
    Lemma IdentityIsEpimorphism x : IsEpimorphism _ _ (Identity x).
admit.
Defined.

    Lemma IdentityIsMonomorphism x : IsMonomorphism _ _ (Identity x).
admit.
Defined.

    Lemma EpimorphismComposition s d d' m0 m1 :
      IsEpimorphism _ _ m0
      -> IsEpimorphism _ _ m1
      -> IsEpimorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
admit.
Defined.

    Lemma MonomorphismComposition s d d' m0 m1 :
      IsMonomorphism _ _ m0
      -> IsMonomorphism _ _ m1
      -> IsMonomorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
admit.
Defined.
  End properties.
End Category.

Hint Immediate @IdentityIsEpimorphism @IdentityIsMonomorphism @MonomorphismComposition @EpimorphismComposition : category morphism.

Arguments IsEpimorphism [C x y] m.
Arguments IsMonomorphism [C x y] m.

Section AssociativityComposition.
  Variable C : Category.
  Variables o0 o1 o2 o3 o4 : C.

  Lemma compose4associativity_helper
    (a : Morphism C o3 o4) (b : Morphism C o2 o3)
    (c : Morphism C o1 o2) (d : Morphism C o0 o1) :
    Compose (Compose a b) (Compose c d) = (Compose a (Compose (Compose b c) d)).
admit.
Defined.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (Compose a (Compose (Compose b c) d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- Compose (Compose ?a ?b) (Compose ?c ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = Compose (Compose ?a ?b) (Compose ?c ?d) ] => compose4associativity' a b c d
  end.

End Category.

Module CategoryIsomorphisms.
Import ProofIrrelevance Setoid.
Export Category.
Import Common StructureEquality.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section Category.
  Context {C : Category}.

   
   
  Definition IsInverseOf1 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m' m = Identity s.
  Definition IsInverseOf2 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m m' = Identity d.

  Global Arguments IsInverseOf1 / _ _ _ _.
  Global Arguments IsInverseOf2 / _ _ _ _.

  Definition IsInverseOf {s d : C} (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop := Eval simpl in
    @IsInverseOf1 s d m m' /\ @IsInverseOf2 s d m m'.

  Lemma IsInverseOf_sym s d m m' : @IsInverseOf s d m m' -> @IsInverseOf d s m' m.
admit.
Defined.

   
   
  Section IsomorphismOf.
     
    Record IsomorphismOf {s d : C} (m : C.(Morphism) s d) := {
      IsomorphismOf_Morphism :> C.(Morphism) s d := m;
      Inverse : C.(Morphism) d s;
      LeftInverse : Compose Inverse m = Identity s;
      RightInverse : Compose m Inverse = Identity d
    }.

    Hint Resolve RightInverse LeftInverse : category.
    Hint Resolve RightInverse LeftInverse : morphism.

    Definition IsomorphismOf_sig2 {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf s d m) :
      { m' | Compose m' m = Identity s & Compose m m' = Identity d }.
      exists (Inverse i);
        [ apply LeftInverse | apply RightInverse ].
    Defined.

    Definition IsomorphismOf_sig {s d : C} (m : C.(Morphism) s d) := { m' | Compose m' m = Identity s & Compose m m' = Identity d }.

    Global Identity Coercion Isomorphism_sig : IsomorphismOf_sig >-> sig2.

    Definition sig2_IsomorphismOf {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf_sig s d m) :
      @IsomorphismOf s d m.
      exists (proj1_sig i);
        [ apply (proj2_sig i) | apply (proj3_sig i) ].
    Defined.

    Global Coercion IsomorphismOf_sig2 : IsomorphismOf >-> sig2.
    Global Coercion sig2_IsomorphismOf : IsomorphismOf_sig >-> IsomorphismOf.

    Definition IsomorphismOf_Identity (c : C) : IsomorphismOf (Identity c).
      exists (Identity _); auto with morphism.
    Defined.

    Definition InverseOf {s d : C} (m : C.(Morphism) s d) (i : IsomorphismOf m) : IsomorphismOf (Inverse i).
      exists (i : Morphism C _ _); auto with morphism.
    Defined.

    Definition ComposeIsomorphismOf {s d d' : C} {m1 : C.(Morphism) d d'} {m2 : C.(Morphism) s d} (i1 : IsomorphismOf m1) (i2 : IsomorphismOf m2) :
      IsomorphismOf (Compose m1 m2).
      exists (Compose (Inverse i2) (Inverse i1));
      abstract (
          simpl; compose4associativity;
          destruct i1, i2; simpl;
          repeat (rewrite_hyp; autorewrite with morphism);
          trivial
        ).
    Defined.
  End IsomorphismOf.

  Section Isomorphism.
    Record Isomorphism (s d : C) := {
      Isomorphism_Morphism : C.(Morphism) s d;
      Isomorphism_Of :> IsomorphismOf Isomorphism_Morphism
    }.

    Global Coercion Build_Isomorphism : IsomorphismOf >-> Isomorphism.
  End Isomorphism.

  Section IsIsomorphism.
    Definition IsIsomorphism {s d : C} (m : C.(Morphism) s d) : Prop :=
      exists m', IsInverseOf m m'.

    Lemma IsomrphismOf_IsIsomorphism {s d : C} (m : C.(Morphism) s d) : IsomorphismOf m -> IsIsomorphism m.
admit.
Defined.

    Lemma IsIsomorphism_IsomrphismOf {s d : C} (m : C.(Morphism) s d) : IsIsomorphism m -> exists _ : IsomorphismOf m, True.
admit.
Defined.
  End IsIsomorphism.

  Section Isomorphic.
    Definition Isomorphic (s d : C) : Prop :=
      exists (m : C.(Morphism) s d) (m' : C.(Morphism) d s), IsInverseOf m m'.

    Lemma Isomrphism_Isomorphic s d : Isomorphism s d -> Isomorphic s d.
admit.
Defined.

    Lemma Isomorphic_Isomorphism s d : Isomorphic s d -> exists _ : Isomorphism s d, True.
admit.
Defined.

    Local Ltac t_iso' := intros;
      repeat match goal with
               | [ i : Isomorphic _ _ |- _ ] => destruct (Isomorphic_Isomorphism i) as [ ? [] ] ; clear i
               | [ |- Isomorphic _ _ ] => apply Isomrphism_Isomorphic
             end.

    Local Ltac t_iso:= t_iso';
      repeat match goal with
               | [ i : Isomorphism _ _ |- _ ] => unique_pose (Isomorphism_Of i); try clear i
               | [ |- Isomorphism _ _ ] => eapply Build_Isomorphism
             end.

    Hint Resolve @IsomorphismOf_Identity @InverseOf @ComposeIsomorphismOf : category morphism.
    Local Hint Extern 1 => eassumption.

    Lemma Isomorphic_refl c : Isomorphic c c.
admit.
Defined.

    Lemma Isomorphic_sym s d : Isomorphic s d -> Isomorphic d s.
admit.
Defined.

    Lemma Isomorphic_trans s d d' : Isomorphic s d -> Isomorphic d d' -> Isomorphic s d'.
admit.
Defined.

    Global Add Parametric Relation : _ Isomorphic
      reflexivity proved by Isomorphic_refl
      symmetry proved by Isomorphic_sym
      transitivity proved by Isomorphic_trans
        as Isomorphic_rel.
  End Isomorphic.

   
  Lemma iso_is_epi s d (m : _ s d) : IsIsomorphism m -> IsEpimorphism (C := C) m.
admit.
Defined.

   
  Lemma iso_is_mono s d (m : _ s d) : IsIsomorphism m -> IsMonomorphism (C := C) m.
admit.
Defined.
End Category.

Hint Resolve @RightInverse @LeftInverse @IsomorphismOf_Identity @ComposeIsomorphismOf : category morphism.

Section CategoryObjects1.
  Variable C : Category.

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', IsIsomorphism m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | IsIsomorphism m & is_unique m }.

  Section terminal.
     
    Definition IsTerminalObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o' o, True.

    Definition IsTerminalObject (o : C) :=
      forall o', { m : C.(Morphism) o' o | is_unique m }.

    Record TerminalObject :=
      {
        TerminalObject_Object' : obj;
        TerminalObject_Morphism : forall o, Morphism C o TerminalObject_Object';
        TerminalObject_Property : forall o, is_unique (TerminalObject_Morphism o)
      }.

    Definition TerminalObject_Object : TerminalObject -> C := TerminalObject_Object'.

    Global Coercion TerminalObject_Object : TerminalObject >-> Object.

    Definition TerminalObject_IsTerminalObject (o : TerminalObject) : IsTerminalObject o
      := fun o' => exist _ (TerminalObject_Morphism o o') (TerminalObject_Property o o').

    Definition IsTerminalObject_TerminalObject o : IsTerminalObject o -> TerminalObject
      := fun H => @Build_TerminalObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion TerminalObject_IsTerminalObject : TerminalObject >-> IsTerminalObject.
    Global Coercion IsTerminalObject_TerminalObject : IsTerminalObject >-> TerminalObject.
  End terminal.

  Section initial.
     
    Definition IsInitialObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o o', True.

    Definition IsInitialObject (o : C) :=
      forall o', { m : C.(Morphism) o o' | is_unique m }.

    Record InitialObject :=
      {
        InitialObject_Object' :> obj;
        InitialObject_Morphism : forall o, Morphism C InitialObject_Object' o;
        InitialObject_Property : forall o, is_unique (InitialObject_Morphism o)
      }.

    Definition InitialObject_Object : InitialObject -> C := InitialObject_Object'.

    Global Coercion InitialObject_Object : InitialObject >-> Object.

    Definition InitialObject_IsInitialObject (o : InitialObject) : IsInitialObject o
      := fun o' => exist _ (InitialObject_Morphism o o') (InitialObject_Property o o').

    Definition IsInitialObject_InitialObject o : IsInitialObject o -> InitialObject
      := fun H => @Build_InitialObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion InitialObject_IsInitialObject : InitialObject >-> IsInitialObject.
    Global Coercion IsInitialObject_InitialObject : IsInitialObject >-> InitialObject.
  End initial.
End CategoryObjects1.

Arguments UniqueUpToUniqueIsomorphism {_ C} P.
Arguments IsInitialObject' {_ C} o.
Arguments IsInitialObject {_ C} o.
Arguments IsTerminalObject' {_ C} o.
Arguments IsTerminalObject {_ C} o.

Section CategoryObjects2.
  Variable C : Category.

  Ltac unique := hnf; intros; specialize_all_ways; destruct_sig;
    unfold is_unique, unique, uniqueness in *;
      repeat (destruct 1);
      repeat match goal with
               | [ x : _ |- _ ] => exists x
             end; eauto with category; try split; try solve [ etransitivity; eauto with category ].

   
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (IsTerminalObject (C := C)).
admit.
Defined.

   
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (IsInitialObject (C := C)).
admit.
Defined.
End CategoryObjects2.

End CategoryIsomorphisms.

Module Category.
Export Category.
Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Record > Category := {
  CObject : Type;

  UnderlyingCategory :> @Category CObject
}.

Record > Category := {
  SObject : Set;

  SUnderlyingCategory :> @Category SObject
}.

Record > LocallyCategory := {
  LSObject : Type;

  LSUnderlyingCategory :> @LocallyCategory LSObject
}.

Bind Scope category_scope with Category.
Bind Scope category_scope with Category.
Bind Scope category_scope with LocallyCategory.



 

 

Ltac saturate := repeat match goal with
                          | [ H : @eq (Morphism _ _ _) ?M ?N |- _ ] =>
                            let tryIt G :=
                              match goal with
                                | [ _ : G |- _ ] => fail 1
                                | [ |- context[G] ] => fail 1
                                | _ => let H' := fresh "H" in assert (H' : G) by eauto; generalize dependent H'
                              end in
                              repeat match goal with
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose M m = Compose N m)
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose m M = Compose m N)
                                     end; generalize dependent H
                        end; intros; autorewrite with core in *.

 

Ltac extractMorphisms G :=
  match G with
    | Compose ?G1 ?G2 =>
      extractMorphisms G1;
      extractMorphisms G2
    | _ =>
      match goal with
        | [ x := G |- _ ] => idtac
        | [ x : _ |- _ ] =>
          match x with
            | G => idtac
          end
        | _ => pose G
      end
  end.

 

Ltac createVariables :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?X ?Y ] =>
      extractMorphisms X;
      extractMorphisms Y
  end.

 

Ltac removeVariables :=
  repeat match goal with
           | [ x := _ |- _ ] => subst x
         end.

 

Tactic Notation "morphisms" integer(numSaturations) :=
  t; createVariables; do numSaturations saturate; removeVariables; eauto 3.

End Category.

Module DefinitionSimplification.
Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

 
Definition focus A (_ : A) := True.

 
Ltac simpl_definition_by_tac_and_exact defn tac :=
  assert (Hf : focus defn) by constructor;
    let defnH := head defn in try unfold defnH in Hf; try tac; simpl in Hf;
      rewrite_eta_in Hf;
      match type of Hf with
        | focus ?V => exact V
      end.

 

End DefinitionSimplification.

Module Functor.
Import JMeq ProofIrrelevance FunctionalExtensionality.
Export Notations Category Category.
Import Common StructureEquality FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section Functor.
  Variable C : Category.
  Variable D : Category.

   
  Record Functor :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                          MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1);
      FIdentityOf : forall x, MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
    }.
End Functor.

Section Functor.
  Variable C : Category.
  Variable D : Category.

  Definition Functor := Functor C D.
End Functor.

Bind Scope functor_scope with Functor.
Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Identity Coercion Functor_Functor_Id : Functor >-> Functor.
Definition GeneralizeFunctor C D (F : @Functor C D) : Functor C D := F.
Coercion GeneralizeFunctor : Functor >-> Functor.

 
Arguments GeneralizeFunctor [C D] F /.
Hint Extern 0 => unfold GeneralizeFunctor : category functor.

Arguments Functor C D.
Arguments Functor C D.
Arguments ObjectOf {C%category D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments FCompositionOf [C D] F _ _ _ _ _ : rename.
Arguments FIdentityOf [C D] F _ : rename.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf : category.
Hint Rewrite @FIdentityOf : functor.

Ltac functor_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               ObjectOf := _;
                               MorphismOf := _;
                               FCompositionOf := ?pf0;
                               FIdentityOf := ?pf1
                             |}] ] =>
               hideProofs pf0 pf1
         end.

Section Functors_Equal.
  Lemma Functor_contr_eq' C D (F G : @Functor C D)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : forall HO : ObjectOf F = ObjectOf G,
      match HO in (_ = f) return forall s d, Morphism C s d -> Morphism D (f s) (f d) with
        | eq_refl => MorphismOf F
      end = MorphismOf G
      -> F = G.
admit.
Defined.

  Lemma Functor_contr_eq C D (F G : @Functor C D)
        (D_object_proof_irrelevance
         : forall (x : D) (pf : x = x),
             pf = eq_refl)
        (D_morphism_proof_irrelevance
         : forall s d (m1 m2 : Morphism D s d) (pf1 pf2 : m1 = m2),
             pf1 = pf2)
  : forall HO : (forall x, ObjectOf F x = ObjectOf G x),
      (forall s d (m : Morphism C s d),
         match HO s in (_ = y) return (Morphism D y _) with
           | eq_refl =>
             match HO d in (_ = y) return (Morphism D _ y) with
               | eq_refl => MorphismOf F m
             end
         end = MorphismOf G m)
      -> F = G.
admit.
Defined.

  Lemma Functor_eq' C D : forall (F G : @Functor C D),
    ObjectOf F = ObjectOf G
    -> MorphismOf F == MorphismOf G
    -> F = G.
admit.
Defined.

  Lemma Functor_eq C D :
    forall (F G : @Functor C D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
admit.
Defined.

  Lemma Functor_JMeq C D C' D' :
    forall (F : @Functor C D) (G : @Functor C' D'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> ObjectOf F == ObjectOf G
      -> MorphismOf F == MorphismOf G
      -> F == G.
admit.
Defined.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functor_eq || apply Functor_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.
Ltac functor_eq := functor_hideProofs; functor_eq_with idtac.

Section FunctorComposition.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Hint Rewrite @FCompositionOf : functor.

  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.
    refine (Build_Functor C E
                                     (fun c => G (F c))
                                     (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                                     _
                                     _);
    abstract (
        intros; autorewrite with functor; reflexivity
      ).
  Defined.
End FunctorComposition.

Section IdentityFunctor.
  Variable C : Category.

   
  Definition IdentityFunctor : Functor C C.
    refine {| ObjectOf := (fun x => x);
              MorphismOf := (fun _ _ x => x)
           |};
    abstract t.
  Defined.
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Variable C : Category.
  Variable D : Category.

  Lemma LeftIdentityFunctor (F : Functor D C) : ComposeFunctors (IdentityFunctor _) F = F.
admit.
Defined.

  Lemma RightIdentityFunctor (F : Functor C D) : ComposeFunctors F (IdentityFunctor _) = F.
admit.
Defined.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Variable B : Category.
  Variable C : Category.
  Variable D : Category.
  Variable E : Category.

  Lemma ComposeFunctorsAssociativity (F : Functor B C) (G : Functor C D) (H : Functor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
admit.
Defined.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.

End Functor.

Module DiscreteCategory.
Export Category.
Import Common.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section DCategory.
  Variable O : Type.

  Local Ltac simpl_eq := subst_body; hnf in *; simpl in *; intros; destruct_type @inhabited; simpl in *;
    repeat constructor;
      repeat subst;
        auto;
          simpl_transitivity.

  Let DiscreteCategory_Morphism (s d : O) := s = d.

  Definition DiscreteCategory_Compose (s d d' : O) (m : DiscreteCategory_Morphism d d') (m' : DiscreteCategory_Morphism s d) :
    DiscreteCategory_Morphism s d'.
    simpl_eq.
  Defined.

  Definition DiscreteCategory_Identity o : DiscreteCategory_Morphism o o.
    simpl_eq.
  Defined.

  Global Arguments DiscreteCategory_Compose [s d d'] m m' /.
  Global Arguments DiscreteCategory_Identity o /.

  Definition DiscreteCategory : @Category O.
    refine (@Build_Category _
                                       DiscreteCategory_Morphism
                                       DiscreteCategory_Identity
                                       DiscreteCategory_Compose
                                       _
                                       _
                                       _);
    abstract (
        unfold DiscreteCategory_Compose, DiscreteCategory_Identity;
        simpl_eq
      ).
  Defined.
End DCategory.

End DiscreteCategory.

Module NatCategory.
Export Category DiscreteCategory.
Import Common.

Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | O => Empty_set
    | 1 => unit
    | S n' => (CardinalityRepresentative n' + unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Definition NatCategory (n : nat) := Eval unfold DiscreteCategory, DiscreteCategory_Identity in DiscreteCategory n.

Coercion NatCategory : nat >-> Category.

End NatCategory.

Module InitialTerminalCategory.
Export Category Functor.
Import Common Notations NatCategory.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section InitialTerminal.
   Definition InitialCategory : Category _ := 0.
   Definition TerminalCategory : Category _ := 1.
End InitialTerminal.

Section Functors.
  Variable C : Category.

  Definition FunctorTo1 : Functor C 1
    := Build_Functor C 1 (fun _ => tt) (fun _ _ _ => eq_refl) (fun _ _ _ _ _ => eq_refl) (fun _ => eq_refl).
  Definition FunctorToTerminal : Functor C TerminalCategory := FunctorTo1.

  Definition FunctorFrom1 (c : C) : Functor 1 C
    := Build_Functor 1 C (fun _ => c) (fun _ _ _ => Identity c) (fun _ _ _ _ _ => eq_sym (@RightIdentity _ _ _ _ _ _)) (fun _ => eq_refl).
  Definition FunctorFromTerminal (c : C) : Functor TerminalCategory C := FunctorFrom1 c.

  Definition FunctorFrom0 : Functor 0 C
    := Build_Functor 0 C (fun x => match x with end) (fun x _ _ => match x with end) (fun x _ _ _ _ => match x with end) (fun x => match x with end).
  Definition FunctorFromInitial : Functor InitialCategory C := FunctorFrom0.
End Functors.

Section FunctorsUnique.
  Variable C : Category.

  Lemma InitialCategoryFunctorUnique
  : forall F F' : Functor InitialCategory C,
      F = F'.
admit.
Defined.

  Lemma InitialCategoryFunctor'Unique
  : forall F F' : Functor C InitialCategory,
      F = F'.
admit.
Defined.

  Lemma InitialCategoryInitial
  : forall F, F = FunctorFromInitial C.
admit.
Defined.

  Lemma TerminalCategoryFunctorUnique
  : forall F F' : Functor C TerminalCategory,
      F = F'.
admit.
Defined.

  Lemma TerminalCategoryTerminal
  : forall F, F = FunctorToTerminal C.
admit.
Defined.
End FunctorsUnique.

End InitialTerminalCategory.

Module ProductCategory.
Export Category Functor.
Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section ProductCategory.
  Variable C : Category.
  Variable D : Category.

  Definition ProductCategory : @Category (objC * objD)%type.
    refine (@Build_Category _
                                       (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                                       (fun o => (Identity (fst o), Identity (snd o)))
                                       (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))
                                       _
                                       _
                                       _);
    abstract (intros; simpl_eq; auto with morphism).
  Defined.
End ProductCategory.

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Context {C : Category}.
  Context {D : Category}.

  Definition fst_Functor : Functor (C * D) C.
    refine (Build_Functor (C * D) C
      (@fst _ _)
      (fun _ _ => @fst _ _)
      _
      _
    );
    abstract eauto.
  Defined.

  Definition snd_Functor : Functor (C * D) D.
    refine (Build_Functor (C * D) D
      (@snd _ _)
      (fun _ _ => @snd _ _)
      _
      _
    );
    abstract eauto.
  Defined.
End ProductCategoryFunctors.

End ProductCategory.

Module CommaCategory.
Import JMeq ProofIrrelevance.
Export Category Category Functor ProductCategory.
Import Common Notations InitialTerminalCategory FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section CommaCategory.
   
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

   

   
   
  Record CommaCategory_Object := { CommaCategory_Object_Member :> { αβ : A * objB & C.(Morphism) (S (fst αβ)) (T (snd αβ)) } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition CommaCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaCategory_Object.
  Global Identity Coercion CommaCategory_Object_Id : CommaCategory_ObjectT >-> sigT.
  Definition Build_CommaCategory_Object' (mem : CommaCategory_ObjectT) := Build_CommaCategory_Object mem.
  Global Coercion Build_CommaCategory_Object' : CommaCategory_ObjectT >-> CommaCategory_Object.

  Record CommaCategory_Morphism (αβf α'β'f' : CommaCategory_ObjectT) := { CommaCategory_Morphism_Member :>
    { gh : (A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f')))  |
      Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
    }
  }.

  Definition CommaCategory_MorphismT (αβf α'β'f' : CommaCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_CommaCategory_Morphism αβf α'β'f').
  Global Identity Coercion CommaCategory_Morphism_Id : CommaCategory_MorphismT >-> sig.
  Definition Build_CommaCategory_Morphism' αβf α'β'f' (mem : @CommaCategory_MorphismT αβf α'β'f') :=
    @Build_CommaCategory_Morphism _ _ mem.
  Global Coercion Build_CommaCategory_Morphism' : CommaCategory_MorphismT >-> CommaCategory_Morphism.

  Lemma CommaCategory_Morphism_eq αβf α'β'f' αβf2 α'β'f'2
        (M : CommaCategory_Morphism αβf α'β'f')
        (N : CommaCategory_Morphism αβf2 α'β'f'2) :
    αβf = αβf2
    -> α'β'f' = α'β'f'2
    -> proj1_sig M == proj1_sig N
    -> M == N.
admit.
Defined.

  Global Arguments CommaCategory_Object_Member _ : simpl nomatch.
  Global Arguments CommaCategory_Morphism_Member _ _ _ : simpl nomatch.

  Definition CommaCategory_Compose s d d'
    (gh : CommaCategory_MorphismT d d') (g'h' : CommaCategory_MorphismT s d) :
    CommaCategory_MorphismT s d'.
    exists (Compose (C := A * B) (proj1_sig gh) (proj1_sig g'h')).
    hnf in *; simpl in *.
    abstract (
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments CommaCategory_Compose _ _ _ _ _ /.

  Definition CommaCategory_Identity o : CommaCategory_MorphismT o o.
    exists (Identity (C := A * B) (projT1 o)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaCategory_Identity _ /.

  Local Ltac comma_t :=
    repeat (
      let H:= fresh in intro H; destruct H as [ [ ] ]
    );
    destruct_hypotheses;
    simpl in *;
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Lemma CommaCategory_Associativity : forall o1 o2 o3 o4 (m1 : CommaCategory_MorphismT o1 o2) (m2 : CommaCategory_MorphismT o2 o3) (m3 : CommaCategory_MorphismT o3 o4),
    CommaCategory_Compose (CommaCategory_Compose m3 m2) m1 =
    CommaCategory_Compose m3 (CommaCategory_Compose m2 m1).
admit.
Defined.

  Lemma CommaCategory_LeftIdentity : forall a b (f : CommaCategory_MorphismT a b),
    CommaCategory_Compose (CommaCategory_Identity b) f = f.
admit.
Defined.

  Lemma CommaCategory_RightIdentity : forall a b (f : CommaCategory_MorphismT a b),
    CommaCategory_Compose f (CommaCategory_Identity a) = f.
admit.
Defined.

  Definition CommaCategory : @Category CommaCategory_Object.
    match goal with
      | [ |- @Category ?obj ] =>
        refine (@Build_Category obj
          CommaCategory_Morphism
          CommaCategory_Identity
          CommaCategory_Compose
          _ _ _
        )
    end;
    abstract (
      intros;
        destruct_type' @CommaCategory_Morphism;
        unfold CommaCategory_Morphism_Member, Build_CommaCategory_Morphism';
          try apply f_equal;
            apply CommaCategory_Associativity ||
              apply CommaCategory_LeftIdentity ||
                apply CommaCategory_RightIdentity
    ).
  Defined.
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity : category.
Hint Constructors CommaCategory_Morphism CommaCategory_Object : category.

Local Notation "S ↓ T" := (CommaCategory S T).

Section SliceCategory.
  Variable A : Category.
  Variable C : Category.
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C.
    refine {| ObjectOf := (fun _ => a);
      MorphismOf := (fun _ _ _ => Identity a)
    |}; abstract (intros; auto with morphism).
  Defined.

  Definition SliceCategory := CommaCategory S SliceCategory_Functor.
  Definition CosliceCategory := CommaCategory SliceCategory_Functor S.

   
End SliceCategory.

Section SliceCategoryOver.
  Variable C : Category.
  Variable a : C.

  Definition SliceCategoryOver := SliceCategory a (IdentityFunctor C).
  Definition CosliceCategoryOver := CosliceCategory a (IdentityFunctor C).
End SliceCategoryOver.

Section ArrowCategory.
  Variable C : Category.

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.

End CommaCategory.

Module CommaCategory.
Import ProofIrrelevance.
Export Category Category Functor ProductCategory.
Import Common Notations InitialTerminalCategory CommaCategory DefinitionSimplification.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Local Ltac fold_functor :=
  change CObject with (fun C => @Object (CObject C) C) in *;
    change (@Functor) with (fun objC (C : @Category objC) objD (D : @Category objD) => @Functor C D) in *.

Section CommaCategory.
   
  Variable A : Category.
  Variable B : Category.
  Variable C : Category.
  Variable S : Functor A C.
  Variable T : Functor B C.

   

   
   
  Let CommaCategory_Object' := Eval hnf in CommaCategory_ObjectT S T.
  Let CommaCategory_Object'' : Type.
    simpl_definition_by_tac_and_exact CommaCategory_Object' ltac:(simpl in *; fold_functor).
  Defined.
  Definition CommaCategory_Object := Eval cbv beta delta [CommaCategory_Object''] in CommaCategory_Object''.

  Let CommaCategory_Morphism' (XG X'G' : CommaCategory_Object) := Eval hnf in CommaCategory_MorphismT (S := S) (T := T) XG X'G'.
  Let CommaCategory_Morphism'' (XG X'G' : CommaCategory_Object) : Type.
    simpl_definition_by_tac_and_exact (CommaCategory_Morphism' XG X'G') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in  *) .
  Defined.
  Definition CommaCategory_Morphism (XG X'G' : CommaCategory_Object) := Eval hnf in CommaCategory_Morphism'' XG X'G'.

  Let CommaCategory_Compose' s d d' Fα F'α'
    := Eval hnf in CommaCategory_Compose (S := S) (T := T) (s := s) (d := d) (d' := d') Fα F'α'.
  Let CommaCategory_Compose'' s d d' (Fα : CommaCategory_Morphism d d') (F'α' : CommaCategory_Morphism s d) :
    CommaCategory_Morphism s d'.
    simpl_definition_by_tac_and_exact (@CommaCategory_Compose' s d d' Fα F'α') ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in  *) .
  Defined.
  Definition CommaCategory_Compose s d d' (Fα : CommaCategory_Morphism d d') (F'α' : CommaCategory_Morphism s d) :
    CommaCategory_Morphism s d'
    := Eval hnf in @CommaCategory_Compose'' s d d' Fα F'α'.

  Let CommaCategory_Identity' o := Eval hnf in CommaCategory_Identity (S := S) (T := T) o.
  Let CommaCategory_Identity'' (o : CommaCategory_Object) : CommaCategory_Morphism o o.
    simpl_definition_by_tac_and_exact (@CommaCategory_Identity' o) ltac:(subst_body; cbv beta in *; fold_functor; cbv beta in  *) .
  Defined.
  Definition CommaCategory_Identity (o : CommaCategory_Object) : CommaCategory_Morphism o o
    := Eval hnf in @CommaCategory_Identity'' o.

  Global Arguments CommaCategory_Compose _ _ _ _ _ /.
  Global Arguments CommaCategory_Identity _ /.

  Lemma CommaCategory_Associativity o1 o2 o3 o4 (m1 : CommaCategory_Morphism o1 o2) (m2 : CommaCategory_Morphism o2 o3) (m3 : CommaCategory_Morphism o3 o4) :
    CommaCategory_Compose (CommaCategory_Compose m3 m2) m1 = CommaCategory_Compose m3 (CommaCategory_Compose m2 m1).
admit.
Defined.

  Lemma CommaCategory_LeftIdentity (a b : CommaCategory_Object) (f : CommaCategory_Morphism a b) :
    CommaCategory_Compose (CommaCategory_Identity b) f = f.
admit.
Defined.

  Lemma CommaCategory_RightIdentity (a b : CommaCategory_Object) (f : CommaCategory_Morphism a b) :
    CommaCategory_Compose f (CommaCategory_Identity a) = f.
admit.
Defined.

  Definition CommaCategory : Category.
    refine (@Build_Category CommaCategory_Object CommaCategory_Morphism
      CommaCategory_Identity
      CommaCategory_Compose
      _ _ _
    );
    subst_body;
    abstract (apply CommaCategory_Associativity || apply CommaCategory_LeftIdentity || apply CommaCategory_RightIdentity).
  Defined.
End CommaCategory.

Hint Unfold CommaCategory_Compose CommaCategory_Identity CommaCategory_Morphism CommaCategory_Object : category.

Arguments CommaCategory [A B C] S T.

Local Notation "S ↓ T" := (CommaCategory S T).

Section SliceCategory.
  Variable A : Category.
  Variable C : Category.
  Variable a : C.
  Variable S : Functor A C.
  Let B := TerminalCategory.

  Definition SliceCategory_Functor : Functor B C.
    refine {| ObjectOf := (fun _ => a);
      MorphismOf := (fun _ _ _ => Identity a)
    |}; abstract (intros; auto with morphism).
  Defined.

  Definition SliceCategory := CommaCategory S SliceCategory_Functor.
  Definition CosliceCategory := CommaCategory SliceCategory_Functor S.
End SliceCategory.

Section SliceCategoryOver.
  Variable C : Category.
  Variable a : C.

  Definition SliceCategoryOver := SliceCategory a (IdentityFunctor C).
  Definition CosliceCategoryOver := CosliceCategory a (IdentityFunctor C).
End SliceCategoryOver.

Section ArrowCategory.
  Variable C : Category.

  Definition ArrowCategory := CommaCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowCategory.

End CommaCategory.

Module UniversalProperties.
Export CommaCategory CategoryIsomorphisms.
Import Common Notations DefinitionSimplification Eqdep.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section UniversalMorphism.
   
  Variable C : Category.
  Variable D : Category.

  Local Ltac intro_t :=
    simpl in *;
    repeat intro;
    simpl_eq;
    destruct_sig;
    destruct_head_hnf prod;
    destruct_head_hnf unit;
    destruct_head_hnf and;
    autorewrite with morphism in *;
    subst;
    intuition.

  Section InitialMorphism.
    Local Notation "A ↓ F" := (CosliceCategory A F).
    Variable X : C.
    Variable U : Functor D C.
     
    Definition IsInitialMorphism (Aφ : (X ↓ U)) := IsInitialObject Aφ.
    Definition InitialMorphism := InitialObject (X ↓ U).

    Section coercions.
      Definition InitialMorphism_IsInitialMorphism : forall o : InitialMorphism, IsInitialMorphism o
        := InitialObject_IsInitialObject (C := (X ↓ U)).
      Definition IsInitialMorphism_InitialMorphism : forall o, IsInitialMorphism o -> InitialMorphism
        := IsInitialObject_InitialObject (C := (X ↓ U)).

      Global Coercion InitialMorphism_IsInitialMorphism : InitialMorphism >-> IsInitialMorphism.
      Global Coercion IsInitialMorphism_InitialMorphism : IsInitialMorphism >-> InitialMorphism.
    End coercions.

    Section IntroductionAbstractionBarrier.
      Definition Build_InitialMorphism'
                 (UniversalProperty : { A : D & { φ : Morphism C X (U A) &
                                               
                                              forall (A' : D) (φ' : Morphism C X (U A')),
                                                { m : Morphism D A A' |
                                                  Compose (MorphismOf U m) φ = φ'
                                                  /\
                                                  forall m' : Morphism D A A',
                                                    Compose (MorphismOf U m') φ = φ'
                                                    -> m' = m } } })
      : InitialMorphism.
        pose proof (projT2 UniversalProperty) as φUniversalProperty;
        set (A := projT1 UniversalProperty) in *;
        clearbody A; clear UniversalProperty; simpl in *.
        pose proof (projT2 φUniversalProperty) as UniversalProperty;
        set (φ := projT1 φUniversalProperty) in *;
        clearbody φ; clear φUniversalProperty; simpl in *.
        refine (_ : IsInitialMorphism (existT _ (tt, A) φ)).
        intro o'.
        specialize (UniversalProperty (snd (projT1 o')) (projT2 o')).
        match goal with
          | [ |- { _ : ?T | _ } ] => match eval hnf in T with
                                       | sig ?P => cut (P (@unit_eq _ _, proj1_sig UniversalProperty));
                                                  [ let H := fresh in
                                                    intro H;
                                                      exists (exist _ (@unit_eq _ _, proj1_sig UniversalProperty) H)
                                                  | ]
                                     end
        end;
          abstract intro_t.
      Defined.

      Arguments Build_InitialMorphism' / .
      Local Arguments Object / .
      Local Arguments CommaCategory_Object / .
      Local Arguments CommaCategory_Morphism / .

      Definition Build_InitialMorphism A φ UniversalProperty : InitialMorphism
        := Eval simpl in @Build_InitialMorphism' (existT _ A (existT _ φ UniversalProperty)).
    End IntroductionAbstractionBarrier.

    Section EliminationAbstractionBarrier.
      Variable M : InitialMorphism.

      Definition InitialMorphism_Object : D := snd (projT1 (InitialObject_Object M)).
      Definition InitialMorphism_Morphism : C.(Morphism) X (U (InitialMorphism_Object)) := projT2 (InitialObject_Object M).
      Definition InitialProperty_Morphism (Y : D) (f : C.(Morphism) X (U Y)) : D.(Morphism) InitialMorphism_Object Y
        := snd (proj1_sig (InitialObject_Morphism M (existT (fun ttY => C.(Morphism) X (U (snd ttY))) (tt, Y) f))).
       
      Lemma InitialProperty (Y : D) (f : C.(Morphism) X (U Y)) :
        unique (fun g => Compose (U.(MorphismOf) g) InitialMorphism_Morphism = f) (InitialProperty_Morphism Y f).
admit.
Defined.
  End InitialMorphism.

  Section TerminalMorphism.
    Local Notation "F ↓ A" := (SliceCategory A F).
    Variable U : Functor D C.
    Variable X : C.
     
    Definition IsTerminalMorphism (Aφ : (U ↓ X)) := IsTerminalObject Aφ.
    Definition TerminalMorphism := TerminalObject (U ↓ X).

    Section coercions.
      Definition TerminalMorphism_IsTerminalMorphism : forall o : TerminalMorphism, IsTerminalMorphism o
        := TerminalObject_IsTerminalObject (C := (U ↓ X)).
      Definition IsTerminalMorphism_TerminalMorphism : forall o, IsTerminalMorphism o -> TerminalMorphism
        := IsTerminalObject_TerminalObject (C := (U ↓ X)).

      Global Coercion TerminalMorphism_IsTerminalMorphism : TerminalMorphism >-> IsTerminalMorphism.
      Global Coercion IsTerminalMorphism_TerminalMorphism : IsTerminalMorphism >-> TerminalMorphism.
    End coercions.

    Section IntroductionAbstractionBarrier.
      Definition Build_TerminalMorphism'
                 (UniversalProperty : { A : D & { φ : Morphism C (U A) X &
                                                                
                                                               forall (A' : D) (φ' : Morphism C (U A') X),
                                                                 { m : Morphism D A' A |
                                                                   Compose φ (MorphismOf U m) = φ'
                                                                   /\
                                                                   forall m' : Morphism D A' A,
                                                                     Compose φ (MorphismOf U m') = φ'
                                                                     -> m' = m } } })
      : TerminalMorphism.
        pose proof (projT2 UniversalProperty) as φUniversalProperty;
        set (A := projT1 UniversalProperty) in *;
        clearbody A; clear UniversalProperty; simpl in *.
        pose proof (projT2 φUniversalProperty) as UniversalProperty;
        set (φ := projT1 φUniversalProperty) in *;
        clearbody φ; clear φUniversalProperty; simpl in *.
        refine (_ : IsTerminalMorphism (existT _ (A, tt) φ)).