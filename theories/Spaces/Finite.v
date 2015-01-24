(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations Factorization EquivalenceVarieties UnivalenceImpliesFunext HSet DProp.
Require Import hit.Truncations hit.quotient.
Import TrM.
Require Import Spaces.Nat.
Require Import HoTT.Tactics.Nameless.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Local Open Scope nat_scope.

(** * Finite sets *)

(** ** Canonical finite sets *)

(** A *finite set* is a type that is merely equivalent to the canonical finite set determined by some natural number.  There are many equivalent ways to define the canonical finite sets, such as [{ k : nat & k < n}]; we instead choose a recursive one. *)

Fixpoint Fin (n : nat) : Type
  := match n with
       | 0 => Empty
       | 1 => Unit
       | 2 => Bool
       | n.+1 => Fin n + Unit
     end.

Delimit Scope fin_scope with fin.
Bind Scope fin_scope with Fin.
Local Open Scope fin_scope.

(** ** Classification of [Fin] as a sum *)
Definition equiv_fin_sum {n : nat} : Fin n.+1 <~> Fin n + Unit.
Proof.
  destruct n as [|[|n]].
  { refine equiv_contr_contr.
    exists (inr tt).
    intros [[]|[]]; reflexivity. }
  { exact (equiv_inverse equiv_bool_sum_unit). }
  { exact (equiv_idmap _). }
Defined.

Arguments equiv_fin_sum : simpl never.

(** ** Names for elements of [Fin n] *)
Definition fin_lift {n : nat} : Fin n -> Fin n.+1
  := match n as n return Fin n -> Fin n.+1 with
       | 0 => fun x => match x with end
       | 1 => fun x => true
       | n.+2 => fun x => inl x
     end.

Fixpoint fin_zero {n : nat} : Fin n.+1
  := match n as n return Fin n.+1 with
       | 0 => tt
       | n.+1 => fin_lift (@fin_zero n)
     end.

Declare Equivalent Keys fin_zero fin_lift.

Definition fin_minus_one {n : nat} : Fin n.+1
  := match n as n return Fin n.+1 with
       | 0 => tt
       | 1 => false
       | n.+1 => inr tt
     end.

Arguments fin_zero : simpl never.
Arguments fin_minus_one : simpl nomatch.

Notation "0" := fin_zero : fin_scope.
Notation "-1" := fin_minus_one : fin_scope.

Definition red_fin_zero {n : nat} : @fin_zero (n.+2) = inl fin_zero
  := idpath.

Definition red_equiv_fin_sum_fin_lift {n : nat} (k : Fin n) : equiv_fin_sum (fin_lift k) = inl k.
Proof.
  destruct n as [|[|[|n]]]; try reflexivity; destruct k; reflexivity.
Defined.

Definition red_equiv_fin_sum_fin_lift' {n : nat} : @equiv_fin_sum n.+2 = equiv_idmap _
  := idpath.

Definition red_equiv_fin_sum_last {n : nat} : (@equiv_fin_sum n)^-1 (inr tt) = -1.
Proof.
  destruct n as [|[|]]; try reflexivity.
Defined.

Definition red_equiv_fin_sum_rest {n : nat} (k : Fin n) : equiv_fin_sum^-1 (inl k) = fin_lift k.
Proof.
  destruct n as [|[|]]; try reflexivity; destruct k.
Defined.

(** We define a tactic to go from [Fin n.+1 <~> Fin m.+1] to [Fin n + Unit <~> Fin m + Unit]. *)
Ltac equiv_fin_to_sum_left :=
  idtac;
  match goal with
    | [ |- _ <~> Fin _.+1 ]
      => exact (equiv_inverse equiv_fin_sum)
    | [ |- _ <~> _ + Unit ]
      => refine (equiv_functor_sum' _ (equiv_idmap Unit)); shelve_unifiable;
        equiv_fin_to_sum_left
  end.
Ltac equiv_fin_to_sum_right :=
  idtac;
  match goal with
    | [ |- Fin _.+1 <~> _ ]
      => exact equiv_fin_sum
    | [ |- _ + Unit <~> _ ]
      => refine (equiv_functor_sum' _ (equiv_idmap Unit)); shelve_unifiable;
        equiv_fin_to_sum_right
  end.

Ltac equiv_fin_to_sum :=
  refine (equiv_compose'
            _
            (equiv_compose'
               _
               _)); shelve_unifiable;
  [ equiv_fin_to_sum_left | | equiv_fin_to_sum_right ].

(** ** Transpositions and rotations *)
(** We define some basic transpositions and rotations to build other terms. *)

(** *** Swap the last two elements. *)

Definition fin_transpose_last_two (n : nat)
: Fin n.+2 <~> Fin n.+2.
Proof.
  do 2 equiv_fin_to_sum.
  exact (equiv_compose'
           (equiv_inverse (equiv_sum_assoc _ _ _))
           (equiv_compose'
              (equiv_functor_sum' (equiv_idmap _)
                                  (equiv_sum_symm _ _))
              (equiv_sum_assoc _ _ _))).
Defined.

Arguments fin_transpose_last_two : simpl nomatch.

Goal forall n m : nat, n = m -> n = m.
intros ? ? p.
induction p.


Class RespectsEquivalence {A : Type} (P : forall B, A <~> B -> Type)
  := respects_equivalence : forall B e, (P A (equiv_idmap _) <~> P B e).

Global Instance respects_equivalence_forall `{Funext} {A X Y} `{HX : @RespectsEquivalence A (fun B e => X B)}
: RespectsEquivalence (fun B (e : A <~> B) => forall x : X B, Y B x).
Proof.
  intros B e.
  refine (equiv_functor_forall' (equiv_inverse (HX B e)) _).
  intro x.
  (forall B (e : A <~> B) (x : X B), @RespectsEquivalence B (fun A' (e' : B <~> A') =>
  eapply equiv_functor_forall'.
  Unshelve.
  Focus 2.
  hnf in HX.
  exact (equiv_inverse (HX B e)).
  Show Proof.
  instantiate (1 := HX B).
  pose (equiv_functor_forall' (P := Y) (@HX B e)).
  Unshelve.
  Focus 2.
  hnf in HX.
  SearchAbout Equiv.
  `{HY : forall B (e : A <~> B) (x : X B), @RespectsEquivalence B (fun B' e' => X}
  hnf in HX.
  pose (fun k => HX

Goal forall A B P Q (e : A <~> B), @sigT A P <~> @sigT B Q.
Proof.
  intros.
  Ltac equiv_induction e :=
    let y := match type of e with ?x <~> ?y => constr:y end in
    generalize dependent e;
      let H := fresh "e" in
      intro H;
        move H at top;
        generalize dependent y;
        refine (respects_equivalence _); cycle 1;
        [
        | ].
  equiv_induction e.



(** This one is harder to reason about in general, but gives better judgmental behavior for, say, [fin_succ^-1 -1] *)
Fixpoint fin_succ_pair {n : nat} : { e : Fin n <~> Fin n | Unit }.
Proof.
  destruct n as [|n].
  { exact (equiv_idmap Empty; tt). }
  { specialize (fin_succ_pair n).
    destruct n as [|[|n]].
    { exact (equiv_idmap Unit; tt). }
    { exact (equiv_negb; tt). }
    { refine (equiv_adjointify
                (fun x : Fin n.+3 => match x with
                                       | inl x' => _
                                       | inr tt => 0
                                     end)
                (fun x : Fin n.+3 => match x with
                                       | inl x' => let x'' := fin_succ_pair.1^-1 x' in
                                                   _
                                       | inr tt => inl (fin_succ_pair.1^-1 -1)
                                     end)
                _ _; _).
      { destruct n.
        exact match x' with
                | false => -1
                | x'' => fin_lift (fin_succ_pair.1 x'')
              end.
        exact match x' with
                | inr tt => -1
                | x'' => fin_lift (fin_succ_pair.1 x'')
              end. }
      { destruct n.
        exact match fin_succ_pair.1^-1 x' with
                | false => -1
                | x'' => fin_lift x''
              end.
        exact match fin_succ_pair.1^-1 x' with
                | inr tt => -1
                | x'' => fin_lift x''
              end. }
      { destruct n; repeat intros []; cbn.
destruct n; repeat intros []; reflexivity. }
    { refine (equiv_compose'
                _
                (fin_transpose_last_two _)).
      equiv_fin_to_sum.
      exact (equiv_functor_sum' fin_succ (equiv_idmap _)). } }
Defined.

Arguments fin_succ : simpl nomatch.

Fixpoint fin_succ' {n : nat} : Fin n <~> Fin n.
Proof.
  destruct n as [|n].
  { exact (equiv_idmap Empty). }
  { specialize (fin_succ' n).
    destruct n as [|[|n]].
    { exact (equiv_idmap Unit). }
    { exact equiv_negb. }
    { refine (equiv_compose'
                _
                (fin_transpose_last_two _)).
      equiv_fin_to_sum.
      exact (equiv_functor_sum' fin_succ (equiv_idmap _)). } }
Defined.

Lemma fin_succ__fin_succ' {n} k : @fin_succ n k = @fin_succ'

Notation fin_pred := fin_succ^-1.
Notation "@ 'fin_pred' n" := (@fin_succ n)^-1 (at level 10, n at level 8, only parsing).

(** Note that putting the negative numbers at level 0 allows us to override the [- _] notation for negative numbers. *)
Notation "n .+1" := (fin_succ n) (at level 2, left associativity, format "n .+1") : fin_scope.
Notation "n .+2" := (n.+1.+1)%fin (at level 2, left associativity, format "n .+2") : fin_scope.
Notation "n .+3" := (n.+1.+2)%fin (at level 2, left associativity, format "n .+3") : fin_scope.
Notation "n .+4" := (n.+1.+3)%fin (at level 2, left associativity, format "n .+4") : fin_scope.
Notation "n .+5" := (n.+1.+4)%fin (at level 2, left associativity, format "n .+5") : fin_scope.
Notation "n .-1" := (fin_pred n) (at level 2, left associativity, format "n .-1") : fin_scope.
Notation "n .-2" := (n.-1.-1)%fin (at level 2, left associativity, format "n .-2") : fin_scope.
Notation "n .-3" := (n.-1.-2)%fin (at level 2, left associativity, format "n .-3") : fin_scope.
Notation "n .-4" := (n.-1.-3)%fin (at level 2, left associativity, format "n .-4") : fin_scope.
Notation "n .-5" := (n.-1.-4)%fin (at level 2, left associativity, format "n .-5") : fin_scope.
Notation "1" := (0.+1)%fin : fin_scope.
Notation "2" := (1.+1)%fin : fin_scope.
Notation "-2" := (-1.-1)%fin : fin_scope.

Global Instance decidable_fin (n : nat)
: Decidable (Fin n).
Proof.
  destruct n; try exact _.
  exact (inl 0%fin).
Defined.

Global Instance decidablepaths_fin (n : nat)
: DecidablePaths (Fin n).
Proof.
  destruct n as [|[|n]]; try exact _.
  induction n as [|n IHn]; simpl; exact _.
Defined.

Definition contr_fin1 : Contr (Fin 1).
Proof.
  exact _.
Defined.

Definition fin_empty (n : nat) (f : Fin n -> Empty) : n = 0%nat.
Proof.
  destruct n;
  solve [ reflexivity
        | elim (f 0%fin) ].
Defined.

(** ** Transposition equivalences *)

(** To prove some basic facts about canonical finite sets, we need some standard automorphisms of them.  Here we define some transpositions and prove that they in fact do the desired things. *)

(** *** Swap the last two elements. *)

Definition fin_transpose_last_two_last (n : nat)
: fin_transpose_last_two n -1 = -2.
Proof.
  destruct n; reflexivity.
Defined.

Definition fin_transpose_last_two_nextlast (n : nat)
: fin_transpose_last_two n -2 = -1.
Proof.
  destruct n; try reflexivity.
  destruct n; reflexivity.
Defined.

Definition fin_transpose_last_two_rest (n : nat) (k : Fin n)
: fin_transpose_last_two n (fin_lift (fin_lift k)) = fin_lift (fin_lift k).
Proof.
  destruct n; try solve [ destruct k ].
  destruct n; reflexivity.
Defined.

Definition fin_transpose_last_two_last' (n : nat)
: (fin_transpose_last_two n)^-1 -2 = -1.
Proof.
  apply (ap (fin_transpose_last_two n))^-1.
  exact (eisretr _ _ @ (fin_transpose_last_two_last _)^).
Defined.

Definition fin_transpose_last_two_nextlast' (n : nat)
: (fin_transpose_last_two n)^-1 -1 = -2.
Proof.
  apply (ap (fin_transpose_last_two n))^-1.
  exact (eisretr _ _ @ (fin_transpose_last_two_nextlast _)^).
Defined.

Definition fin_transpose_last_two_rest' (n : nat) (k : Fin n)
: (fin_transpose_last_two n)^-1 (fin_lift (fin_lift k)) = fin_lift (fin_lift k).
Proof.
  apply (ap (fin_transpose_last_two n))^-1.
  exact (eisretr _ _ @ (fin_transpose_last_two_rest _ _)^).
Defined.

Definition fin_transpose_last_two_last'' (n : nat)
: fin_transpose_last_two n.+1 (inr tt) = inl -1.
Proof.
  rewrite fin_transpose_last_two_last.
  cbn.
  unfold equiv_fin_sum.
  cbn.
  unfold fin_transpose_last_two.
  cbn.
  unfold equiv_fin_sum; cbn.

  rewrite unfold_fin_transpose_last_two.
  unfold fin_transpose_last_two.
  cbn.
  cbn.
  destruct n; reflexivity.
Defined.


(** *** Swap the last element with [k]. *)

Definition fin_transpose_last_with'
           {fin_transpose_last_with : forall n (k : Fin n.+1), Fin n.+1 <~> Fin n.+1}
           (n : nat) (k : Fin n.+1)
: Fin n.+1 <~> Fin n.+1.
Proof.
  destruct n as [|n].
  - exact (@equiv_idmap Unit).
  - specialize (fin_transpose_last_with n).
    destruct (equiv_fin_sum k) as [k'|].
    + destruct (equiv_fin_sum k') as [k''|].
      * refine (equiv_compose'
                  (fin_transpose_last_two n)
                  (equiv_compose' _ (fin_transpose_last_two n))).
        equiv_fin_to_sum.
        refine (equiv_functor_sum'
                  (fin_transpose_last_with (fin_lift k''))
                  (equiv_idmap Unit)).
      * apply fin_transpose_last_two.
    + exact (equiv_idmap _).
Defined.

Fixpoint fin_transpose_last_with (n : nat) (k : Fin n.+1) {struct n}
: Fin n.+1 <~> Fin n.+1
  := @fin_transpose_last_with' fin_transpose_last_with n k.

Definition unfold_fin_transpose_last_with {n}
: fin_transpose_last_with n.+1 = @fin_transpose_last_with' fin_transpose_last_with n.+1
  := idpath.

Arguments fin_transpose_last_with : simpl nomatch.

Local Ltac fin_transpose_last_with_t :=
  repeat first [ reflexivity
               | let IHn := hyp in rewrite IHn
               | let IHn := hyp in let k := hyp in rewrite (IHn k)
               | let IHn := hyp in let l := hyp in rewrite (IHn _ l)
               | progress cbn
               | intro
               | rewrite red_equiv_fin_sum_fin_lift'
               | let H := hyp in destruct (H idpath : False)
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].

Definition fin_transpose_last_with_last (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k -1 = k.
Proof.
  revert k; induction n.
  { intros []; reflexivity. }
  { do 2 try destruct n; fin_transpose_last_with_t.
    rewrite unfold_fin_transpose_last_with; cbn.
    fin_transpose_last_with_t.
    rewrite fin_transpos
    repeat first [ fail
          | rewrite fin_transpose_last_two_last
               | rewrite fin_transpose_last_two_last'
               | rewrite fin_transpose_last_two_rest
               | rewrite fin_transpose_last_two_rest'
               | rewrite fin_transpose_last_two_nextlast
               | rewrite fin_transpose_last_two_nextlast' ].
    fin_transpose_last_with_t.
    repeat first [ fail
          | rewrite fin_transpose_last_two_last
               | rewrite fin_transpose_last_two_last'
               | rewrite fin_transpose_last_two_rest
               | rewrite fin_transpose_last_two_rest'
               | rewrite fin_transpose_last_two_nextlast
               | rewrite fin_transpose_last_two_nextlast' ].
    Opaque fin_transpose_last_with.
    cbn.    first [ reflexivity
               | let IHn := hyp in rewrite IHn
               | let IHn := hyp in let k := hyp in rewrite (IHn k)
               | let IHn := hyp in let l := hyp in rewrite (IHn _ l)
               | progress cbn
               | intro
               | rewrite red_equiv_fin_sum_fin_lift'
               | let H := hyp in destruct (H idpath : False)
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].
    first [ reflexivity
               | let IHn := hyp in rewrite IHn
               | let IHn := hyp in let k := hyp in rewrite (IHn k)
               | let IHn := hyp in let l := hyp in rewrite (IHn _ l)
               | progress cbn
               | intro
               | rewrite red_equiv_fin_sum_fin_lift'
               | let H := hyp in destruct (H idpath : False)
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].
    first [ reflexivity
               | let IHn := hyp in rewrite IHn
               | let IHn := hyp in let k := hyp in rewrite (IHn k)
               | let IHn := hyp in let l := hyp in rewrite (IHn _ l)
               | progress cbn
               | intro
               | rewrite red_equiv_fin_sum_fin_lift'
               | let H := hyp in destruct (H idpath : False)
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].
    first [ reflexivity
               | let IHn := hyp in rewrite IHn
               | let IHn := hyp in let k := hyp in rewrite (IHn k)
               | let IHn := hyp in let l := hyp in rewrite (IHn _ l)
               | progress cbn
               | intro
               | rewrite red_equiv_fin_sum_fin_lift'
               | let H := hyp in destruct (H idpath : False)
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].
    fin_transpose_last_with_t.

    repeat change (@inr (Fin ?n) Unit tt) with (@fin_minus_one n).
    rewrite fin_transpose_last_two_nextlast'.
    unfold fin_transpose_last_two.
    cbn.

    cbn.
    unfold functor_sum at 2.

    rewrite red_equiv_fin_sum_fin_lift'.
    unfold fin_transpose_last_with.
    cbn.
do 2 try destruct n; fin_transpose_last_with_t. }
Qed.

Definition fin_transpose_last_with_with (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k k = -1.
Proof.
  revert k; induction n.
  { intros []; reflexivity. }
  { do 2 try destruct n; fin_transpose_last_with_t. }
Qed.

Definition fin_transpose_last_with_rest (n : nat)
           (k : Fin n.+1) (l : Fin n)
           (notk : k <> fin_lift l)
: fin_transpose_last_with n k (fin_lift l) = (fin_lift l).
Proof.
  induction n as [|n IH]; cbn.
  { elim l. }
  { do 2 try destruct n;
    fin_transpose_last_with_t.
    let H := hyp in
    destruct (notk (ap inl H)). }
Qed.

Definition fin_transpose_last_with_rest' (n : nat)
           (k : Fin n.+3) (l : Fin n.+2)
           (notk : k <> inl l)
: fin_transpose_last_with n.+2 k (inl l) = (inl l)
  := fin_transpose_last_with_rest _ k l notk.

Definition fin_transpose_last_with_rest'' (n : nat)
           (k : Fin n.+1) (l : Fin n)
           (notk : equiv_fin_sum k <> inl l)
: fin_transpose_last_with n k (equiv_fin_sum^-1 (inl l)) = equiv_fin_sum^-1 (inl l).
Proof.
  destruct n as [|[|]]; simpl;
  try solve [ reflexivity
            | destruct k; reflexivity
            | exact (fin_transpose_last_with_rest _ _ l notk)
            | (repeat let H := hyp in destruct H; try reflexivity); reflexivity ].
Defined.

Definition fin_transpose_last_with_last_other (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n -1 k = k.
Proof.
  do 2 try destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_invol (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k o fin_transpose_last_with n k == idmap.
Proof.
  intro l.
  destruct (dec_paths k l) as [p|p]; path_induction;
  do 3 try destruct n;
  repeat first [ reflexivity
               | assumption
               | rewrite fin_transpose_last_with_with
               | rewrite fin_transpose_last_with_last
               | rewrite fin_transpose_last_with_rest'
               | let H := hyp in enforce (H : Unit); destruct H
               | let H := hyp in enforce (H : Bool); destruct H
               | let H := hyp in enforce (H : _ + _); destruct H ].
Qed.

(** ** Equivalences between canonical finite sets *)

(** To give an equivalence [Fin n.+1 <~> Fin m.+1] is equivalent to giving an element of [Fin m.+1] (the image of the last element) together with an equivalence [Fin n <~> Fin m].  More specifically, any such equivalence can be decomposed uniquely as a last-element transposition followed by an equivalence fixing the last element.  *)

(** If two canonical finite sets are equivalent, then their cardinalities are equal. *)
Definition nat_eq_fin_equiv (n m : nat)
: (Fin n <~> Fin m) -> (n = m).
Proof.
  revert m; induction n as [|n IHn]; destruct m as [|m]; intros e.
  - exact idpath.
  - elim (e^-1 0).
  - elim (e 0).
  - refine (ap S (IHn m _)).
    pose proof (equiv_compose'
                  equiv_fin_sum
                  (equiv_compose'
                     e (equiv_inverse equiv_fin_sum))) as e'.
    apply equiv_unfunctor_sum_contr_ll in e'.
    exact e'.
Qed.

(** Here is the uncurried map that constructs an equivalence [Fin n.+1 <~> Fin m.+1]. *)
Definition fin_equiv (n m : nat)
           (k : Fin m.+1) (e : Fin n <~> Fin m)
: Fin n.+1 <~> Fin m.+1.
Proof.
  refine (equiv_compose'
            (fin_transpose_last_with m k)
            (equiv_compose'
               (equiv_inverse equiv_fin_sum)
               (equiv_compose'
                  (equiv_functor_sum' e (equiv_idmap Unit))
                  equiv_fin_sum))).
Defined.

(** Here is the curried version that we will prove to be an equivalence. *)
Definition fin_equiv' (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) -> (Fin n.+1 <~> Fin m.+1)
  := fun ke => fin_equiv n m (fst ke) (snd ke).

(** We construct its inverse and the two homotopies first as versions using homotopies without funext (similar to [ExtendableAlong]), then apply funext at the end. *)
Definition fin_equiv_hfiber (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: { kf : (Fin m.+1) * (Fin n <~> Fin m) & fin_equiv' n m kf == e }.
Proof.
  (*pose proof (ap pred (nat_eq_fin_equiv _ _ e)) as H.
  simpl in H.
  destruct H.*)
  refine (equiv_sigma_prod _ _).
  recall (e -1) as y eqn:p.
  assert (p' := (moveL_equiv_V _ _ p)^).
  exists y.
  generalize dependent y.
  intro y.
  destruct (eissect equiv_fin_sum y).
  generalize (equiv_fin_sum y); clear y; intro y; intros.
  destruct y as [y|[]].
  + refine (equiv_unfunctor_sum_contr_ll
              (equiv_compose'
                 equiv_fin_sum
                 (equiv_compose'
                    (equiv_compose'
                       (fin_transpose_last_with m (fin_lift y))
                       e)
                    (equiv_inverse equiv_fin_sum)))
            ; _).
    { intros a. ev_equiv.
      rewrite ?red_equiv_fin_sum_rest.
      Opaque equiv_fin_sum fin_lift.
      cbn.
      rewrite <- (eissect equiv_fin_sum) (e' (equiv_fin_sum^-1 (inl a)))).
      assert (q : fin_lift y <> e a)
        by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))).
      change (equiv_fin_sum (e' (equiv_fin_sum^-1 (inl a)))) with (e (inl a)).
      set (z := e (inl a)) in *.
      destruct z as [z|[]].
      - rewrite fin_transpose_last_with_rest'';
        rewrite ?eisretr, ?eissect, ?red_equiv_fin_sum_fin_lift;
        try exact tt; try assumption.
      - rewrite ?red_equiv_fin_sum_last, fin_transpose_last_with_last, ?red_equiv_fin_sum_fin_lift; exact tt. }
    { intros []. ev_equiv.
      subst e; cbn in *.
      apply (ap (equiv_fin_sum^-1)) in p.
      rewrite eissect in p.
      rewrite p.
      rewrite red_equiv_fin_sum_rest, fin_transpose_last_with_with, <- red_equiv_fin_sum_last, eisretr; exact tt. }
    intros x'. unfold fst, snd; ev_equiv. simpl.
    rewrite <- (eissect equiv_fin_sum x').
    destruct (equiv_fin_sum x') as [x|[]]; simpl.
    * repeat match goal with
               | _ => let H := hyp in enforce (H : Empty); destruct H
               | _ => let H := hyp in enforce (H : Unit); destruct H
               | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
             end.
     cbn.
     subst e.
     cbn in *.
 .rewrite unfunctor_sum_l_beta.
      apply fin_transpose_last_with_invol.
    * refine (fin_transpose_last_with_last _ _ @ p^).
  + refine (equiv_unfunctor_sum_l e _ _ ; _).
    { intros a.
      destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
      - exact l.
      - assert (q := inr_un_inr (e (inl a)) r).
        apply moveR_equiv_V in q.
        assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ p').
        elim (inl_ne_inr _ _ s). }
    { intros []; exact (p^ # tt). }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [a|[]].
    * rewrite fin_transpose_last_with_last_other.
      apply unfunctor_sum_l_beta.
    * simpl.
      rewrite fin_transpose_last_with_last.
      symmetry; apply p.
Qed.


  { destruct m as [|[|m]].
    { destruct n as [|[|n]].
      { exists (equiv_idmap Empty).
        intro; apply path_ishprop. }
      { solve [ assert (Contr Bool) by (let e := hyp in exact (contr_equiv' _ (equiv_inverse e)));
                refine (match _ : Empty with end); apply true_ne_false; apply path_ishprop ]. }
      {
        intros []; simpl.
        destruct (e tt); reflexivity. }

      { }

Definition fin_equiv_inv (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: (Fin m.+1) * (Fin n <~> Fin m)
  := (fin_equiv_hfiber n m e).1.

Definition fin_equiv_issect (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: fin_equiv' n m (fin_equiv_inv n m e) == e
  := (fin_equiv_hfiber n m e).2.

Definition fin_equiv_inj_fst (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (k = l).
Proof.
  intros p.
  refine (_ @ p (inr tt) @ _); simpl;
  rewrite fin_transpose_last_with_last; reflexivity.
Qed.

Definition fin_equiv_inj_snd (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (e == f).
Proof.
  intros p.
  intros x. assert (q := p (inr tt)); simpl in q.
  rewrite !fin_transpose_last_with_last in q.
  rewrite <- q in p; clear q l.
  exact (path_sum_inl _
           (equiv_inj (fin_transpose_last_with m k) (p (inl x)))).
Qed.

(** Now it's time for funext. *)
Global Instance isequiv_fin_equiv `{Funext} (n m : nat)
: IsEquiv (fin_equiv' n m).
Proof.
  refine (isequiv_pathsplit 0 _); split.
  - intros e; exists (fin_equiv_inv n m e).
    apply path_equiv, path_arrow, fin_equiv_issect.
  - intros [k e] [l f]; simpl.
    refine (_ , fun _ _ => tt).
    intros p; refine (_ ; path_ishprop _ _).
    apply (ap equiv_fun) in p.
    apply ap10 in p.
    apply path_prod'.
    + refine (fin_equiv_inj_fst n m k l e f p).
    + apply path_equiv, path_arrow.
      refine (fin_equiv_inj_snd n m k l e f p).
Qed.

Definition equiv_fin_equiv `{Funext} (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) <~> (Fin n.+1 <~> Fin m.+1)
  := BuildEquiv _ _ (fin_equiv' n m) _.

(** In particular, this implies that if two canonical finite sets are equivalent, then their cardinalities are equal. *)
Definition nat_eq_fin_equiv (n m : nat)
: (Fin n <~> Fin m) -> (n = m).
Proof.
  revert m; induction n as [|n IHn]; induction m as [|m IHm]; intros e.
  - exact idpath.
  - elim (e^-1 (inr tt)).
  - elim (e (inr tt)).
  - refine (ap S (IHn m _)).
    exact (snd (fin_equiv_inv n m e)).
Qed.

(** ** Definition of general finite sets *)

Class Finite (X : Type) :=
  { fcard : nat ;
    merely_equiv_fin : merely (X <~> Fin fcard) }.

Arguments fcard X {_}.
Arguments merely_equiv_fin X {_}.

Definition issig_finite X
: { n : nat & merely (X <~> Fin n) } <~> Finite X.
Proof.
  issig (@Build_Finite X) (@fcard X) (@merely_equiv_fin X).
Defined.

(** Note that the sigma over cardinalities is not truncated.  Nevertheless, because canonical finite sets of different cardinalities are not isomorphic, being finite is still an hprop.  (Thus, we could have truncated the sigma and gotten an equivalent definition, but it would be less convenient to reason about.) *)
Global Instance ishprop_finite X
: IsHProp (Finite X).
Proof.
  refine (trunc_equiv' _ (issig_finite X)).
  apply ishprop_sigma_disjoint; intros n m Hn Hm.
  strip_truncations.
  refine (nat_eq_fin_equiv n m (equiv_compose' Hm (equiv_inverse Hn))).
Defined.

(** ** Preservation of finiteness by equivalences *)

Definition finite_equiv X {Y} (e : X -> Y) `{IsEquiv X Y e}
: Finite X -> Finite Y.
Proof.
  intros ?.
  refine (Build_Finite Y (fcard X) _).
  assert (f := merely_equiv_fin X); strip_truncations.
  apply tr.
  exact (equiv_compose f e^-1).
Defined.

Definition finite_equiv' X {Y} (e : X <~> Y)
: Finite X -> Finite Y
  := finite_equiv X e.

Corollary finite_equiv_equiv X Y
: (X <~> Y) -> (Finite X <~> Finite Y).
Proof.
  intros ?; apply equiv_iff_hprop; apply finite_equiv';
    [ assumption | symmetry; assumption ].
Defined.

Definition fcard_equiv {X Y} (e : X -> Y) `{IsEquiv X Y e}
           `{Finite X} `{Finite Y}
: fcard X = fcard Y.
Proof.
  transitivity (@fcard Y (finite_equiv X e _)).
  - reflexivity.
  - exact (ap (@fcard Y) (path_ishprop _ _)).
Defined.

Definition fcard_equiv' {X Y} (e : X <~> Y)
           `{Finite X} `{Finite Y}
: fcard X = fcard Y
  := fcard_equiv e.

(** ** Simple examples of finite sets *)

(** Canonical finite sets are finite *)
Global Instance finite_fin n : Finite (Fin n)
  := Build_Finite _ n (tr (equiv_idmap _)).

(** This includes the empty set. *)
Global Instance finite_empty : Finite Empty
  := finite_fin 0.

(** The unit type is finite, since it's equivalent to [Fin 1]. *)
Global Instance finite_unit : Finite Unit.
Proof.
  refine (finite_equiv' (Fin 1) _ _); simpl.
  apply sum_empty_l.
Defined.

(** Thus, any contractible type is finite. *)
Global Instance finite_contr X `{Contr X} : Finite X
  := finite_equiv Unit equiv_contr_unit^-1 _.

(** Any decidable hprop is finite, since it must be equivalent to [Empty] or [Unit]. *)
Definition finite_decidable_hprop X `{IsHProp X} `{Decidable X}
: Finite X.
Proof.
  destruct (dec X) as [x|nx].
  - assert (Contr X) by exact (contr_inhabited_hprop X x).
    exact _.
  - refine (finite_equiv Empty nx^-1 _).
Defined.

Hint Immediate finite_decidable_hprop : typeclass_instances.

(** It follows that the propositional truncation of any finite set is finite. *)
Global Instance finite_merely X {fX : Finite X}
: Finite (merely X).
Proof.
  (** As in decidable_finite_hprop, we case on cardinality first to avoid needing funext. *)
  destruct fX as [[|n] e]; refine (finite_decidable_hprop _).
  - right.
    intros x; strip_truncations; exact (e x).
  - left.
    strip_truncations; exact (tr (e^-1 (inr tt))).
Defined.

(** Finite sets are closed under path-spaces. *)
Global Instance finite_paths {X} `{Finite X} (x y : X)
: Finite (x = y).
Proof.
  (** If we assume [Funext], then typeclass inference produces this automatically, since [X] has decidable equality and (hence) is a set, so [x=y] is a decidable hprop.  But we can also deduce it without funext, since [Finite] is an hprop even without funext. *)
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _ (ap e)^-1 _).
  apply finite_decidable_hprop; exact _.
Defined.

(** Finite sets are also closed under successors. *)

Global Instance finite_succ X `{Finite X} : Finite (X + Unit).
Proof.
  refine (Build_Finite _ (fcard X).+1 _).
  pose proof (merely_equiv_fin X).
  strip_truncations; apply tr.
  refine (equiv_functor_sum' _ (equiv_idmap _)); assumption.
Defined.

Definition fcard_succ X `{Finite X}
: fcard (X + Unit) = (fcard X).+1
  := 1.

(** ** Decidability *)

(** Like canonical finite sets, finite sets have decidable equality. *)
Global Instance decidablepaths_finite `{Funext} X `{Finite X}
: DecidablePaths X.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (decidablepaths_equiv _ e^-1 _).
Defined.

(** However, contrary to what you might expect, we cannot assert that "every finite set is decidable"!  That would be claiming a *uniform* way to select an element from every nonempty finite set, which contradicts univalence. *)

(** One thing we can prove is that any finite hprop is decidable. *)
Global Instance decidable_finite_hprop X `{IsHProp X} {fX : Finite X}
: Decidable X.
Proof.
  (** To avoid having to use [Funext], we case on the cardinality of [X] before stripping the truncation from its equivalence to [Fin n]; if we did things in the other order then we'd have to know that [Decidable X] is an hprop, which requires funext. *)
  destruct fX as [[|n] e].
  - right; intros x.
    strip_truncations; exact (e x).
  - left.
    strip_truncations; exact (e^-1 (inr tt)).
Defined.

(** It follows that if [X] is finite, then its propositional truncation is decidable. *)
Global Instance decidable_merely_finite X {fX : Finite X}
: Decidable (merely X).
Proof.
  exact _.
Defined.

(** From this, it follows that any finite set is *merely* decidable. *)
Definition merely_decidable_finite X `{Finite X}
: merely (Decidable X).
Proof.
  apply O_decidable; exact _.
Defined.

(** ** Induction over finite sets *)

(** Most concrete applications of this don't actually require univalence, but the general version does.  For this reason the general statement is less useful (and less used in the sequel) than it might be. *)
Definition finite_ind_hprop `{Univalence}
           (P : forall X, Finite X -> Type)
           `{forall X (fX:Finite X), IsHProp (P X _)}
           (f0 : P Empty _)
           (fs : forall X (fX:Finite X), P X _ -> P (X + Unit)%type _)
           (X : Type) `{Finite X}
: P X _.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  assert (p := transportD Finite P (path_universe e^-1) _).
  refine (transport (P X) (path_ishprop _ _) (p _)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact f0.
  - refine (transport (P (Fin n.+1)) (path_ishprop _ _) (fs _ _ IH)).
Defined.

(** ** The finite axiom of choice *)

Definition finite_choice {X} `{Finite X} (P : X -> Type)
: (forall x, merely (P x)) -> merely (forall x, P x).
Proof.
  intros f.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  set (P' := P o e^-1).
  assert (f' := (fun x => f (e^-1 x)) : forall x, merely (P' x)).
  refine (Trunc_functor (X := forall x:Fin (fcard X), P' x) -1 _ _).
  - intros g x; exact (eissect e x # g (e x)).
  - clearbody P'; clear f P e.
    generalize dependent (fcard X); intros n P f.
    induction n as [|n IH].
    + exact (tr (Empty_ind P)).
    + specialize (IH (P o inl) (f o inl)).
      assert (e := f (inr tt)).
      strip_truncations.
      exact (tr (sum_ind P IH (Unit_ind e))).
Defined.

(** ** Constructions on finite sets *)

(** Finite sets are closed under sums, products, function spaces, and equivalence spaces.  There are multiple choices we could make regarding how to prove these facts.  Since we know what the cardinalities ought to be in all cases (since we know how to add, multiply, exponentiate, and take factorials of natural numbers), we could specify those off the bat, and then reduce to the case of canonical finite sets.  However, it's more amusing to instead prove finiteness of these constructions by "finite-set induction", and then *deduce* that their cardinalities are given by the corresponding operations on natural numbers (because they satisfy the same recurrences). *)

(** *** Binary sums *)

Global Instance finite_sum X Y `{Finite X} `{Finite Y}
: Finite (X + Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_sum idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (sum_empty_r X)^-1 _).
  - refine (finite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

(** Note that the cardinality function [fcard] actually computes.  The same will be true of all the other proofs in this section, though we don't always verify it. *)
Goal fcard (Fin 3 + Fin 4) = 7.
  reflexivity.
Abort.

Definition fcard_sum X Y `{Finite X} `{Finite Y}
: fcard (X + Y) = (fcard X + fcard Y).
Proof.
  refine (_ @ nat_plus_comm _ _).
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (fcard_equiv' (equiv_functor_sum' (equiv_idmap X) e) @ _).
  refine (_ @ ap (fun y => (y + fcard X)) (fcard_equiv e^-1)).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (sum_empty_r X)^-1).
  - refine (fcard_equiv (equiv_sum_assoc _ _ _)^-1 @ _).
    exact (ap S IH).
Defined.

(** *** Binary products *)

Global Instance finite_prod X Y `{Finite X} `{Finite Y}
: Finite (X * Y).
Proof.
  assert (e := merely_equiv_fin Y).
  strip_truncations.
  refine (finite_equiv _ (functor_prod idmap e^-1) _).
  generalize (fcard Y); intros n.
  induction n as [|n IH].
  - refine (finite_equiv _ (prod_empty_r X)^-1 _).
  - refine (finite_equiv _ (sum_distrib_l X _ Unit)^-1 (finite_sum _ _)).
    refine (finite_equiv _ (prod_unit_r X)^-1 _).
Defined.

Definition fcard_prod X Y `{Finite X} `{Finite Y}
: fcard (X * Y) = fcard X * fcard Y.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv' (equiv_functor_prod' e (equiv_idmap Y)) @ _).
  refine (_ @ ap (fun x => x * fcard Y) (fcard_equiv e^-1)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - refine (fcard_equiv (prod_empty_l Y)).
  - refine (fcard_equiv (sum_distrib_r Y (Fin n) Unit) @ _).
    refine (fcard_sum _ _ @ _).
    simpl.
    refine (_ @ nat_plus_comm _ _).
    refine (ap011 plus _ _).
    + apply IH.
    + apply fcard_equiv', prod_unit_l.
  Defined.

(** *** Function types *)

(** Finite sets are closed under function types, and even dependent function types. *)

Global Instance finite_forall `{Funext} {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite (forall x:X, Y x).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv' _
            (equiv_functor_forall' (P := fun x => Y (e^-1 x)) e _) _); try exact _.
  { intros x; refine (equiv_transport _ _ _ (eissect e x)). }
  set (Y' := Y o e^-1); change (Finite (forall x, Y' x)).
  assert (forall x, Finite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_sum_ind Y') _).
    apply finite_prod.
    + apply IH; exact _.
    + refine (finite_equiv _ (@Unit_ind (fun u => Y' (inr u))) _).
      refine (isequiv_unit_ind (Y' o inr)).
Defined.

Definition fcard_arrow `{Funext} X Y `{Finite X} `{Finite Y}
: fcard (X -> Y) = nat_exp (fcard Y) (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv (functor_arrow e idmap)^-1 @ _).
  refine (_ @ ap (fun x => nat_exp (fcard Y) x) (fcard_equiv e)).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_sum_ind (fun (_:Fin n.+1) => Y))^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply (ap011 mult).
    + assumption.
    + refine (fcard_equiv (@Unit_ind (fun (_:Unit) => Y))^-1).
Defined.

(** [fcard] still computes, despite the funext: *)
Goal forall fs:Funext, fcard (Fin 3 -> Fin 4) = 64.
  reflexivity.
Abort.

(** *** Automorphism types (i.e. symmetric groups) *)

Global Instance finite_aut `{Funext} X `{Finite X}
: Finite (X <~> X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv _
            (equiv_functor_equiv (equiv_inverse e) (equiv_inverse e)) _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - exact _.
  - refine (finite_equiv _ (equiv_fin_equiv n n) _).
Defined.

Definition fcard_aut `{Funext} X `{Finite X}
: fcard (X <~> X) = factorial (fcard X).
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (fcard_equiv
            (equiv_functor_equiv (equiv_inverse e) (equiv_inverse e))^-1 @ _).
  generalize (fcard X); intros n.
  induction n as [|n IH].
  - reflexivity.
  - refine (fcard_equiv (equiv_fin_equiv n n)^-1 @ _).
    refine (fcard_prod _ _ @ _).
    apply ap011.
    + reflexivity.
    + assumption.
Defined.

(** [fcard] still computes: *)
Goal forall fs:Funext, fcard (Fin 4 <~> Fin 4) = 24.
  reflexivity.
Abort.

(** ** Finite sums of natural numbers *)

(** Perhaps slightly less obviously, finite sets are also closed under sigmas. *)

Global Instance finite_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: Finite { x:X & Y x }.
Proof.
  assert (e := merely_equiv_fin X).
  strip_truncations.
  refine (finite_equiv' _
            (equiv_functor_sigma (equiv_inverse e)
                                 (fun x (y:Y (e^-1 x)) => y)) _).
  (** Unfortunately, because [compose] is currently beta-expanded, [set (Y' := Y o e^-1)] doesn't change the goal. *)
  set (Y' := fun x => Y (e^-1 x)).
  assert (forall x, Finite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (fcard X); intros n Y' ?.
  induction n as [|n IH].
  - refine (finite_equiv Empty pr1^-1 _).
  - refine (finite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply finite_sum.
    + apply IH; exact _.
    + refine (finite_equiv _ (equiv_contr_sigma _)^-1 _).
Defined.

(** Amusingly, this automatically gives us a way to add up a family of natural numbers indexed by any finite set.  (We could of course also define such an operation directly, probably using [merely_ind_hset].) *)

Definition finplus {X} `{Finite X} (f : X -> nat) : nat
  := fcard { x:X & Fin (f x) }.

Definition fcard_sigma {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard { x:X & Y x } = finplus (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finplus.
  refine (fcard_equiv' (equiv_functor_sigma' (equiv_idmap X) g)).
Defined.

(** The sum of a finite constant family is the product by its cardinality. *)
Definition finplus_const X `{Finite X} n
: finplus (fun x:X => n) = fcard X * n.
Proof.
  transitivity (fcard (X * Fin n)).
  - exact (fcard_equiv' (equiv_sigma_prod0 X (Fin n))).
  - exact (fcard_prod X (Fin n)).
Defined.

(** Closure under sigmas and paths also implies closure under hfibers. *)
Definition finite_hfiber {X Y} (f : X -> Y) (y : Y)
       `{Finite X} `{Finite Y}
: Finite (hfiber f y).
Proof.
  exact _.
Defined.

(** Therefore, the cardinality of the domain of a map between finite sets is the sum of the cardinalities of its hfibers. *)
Definition fcard_domain {X Y} (f : X -> Y) `{Finite X} `{Finite Y}
: fcard X = finplus (fun y => fcard (hfiber f y)).
Proof.
  refine (_ @ fcard_sigma (hfiber f)).
  refine (fcard_equiv' (equiv_fibration_replacement f)).
Defined.

(** In particular, the image of a map between finite sets is finite. *)
Definition finite_image
       {X Y} `{Finite X} `{Finite Y} (f : X -> Y)
: Finite (himage f).
Proof.
  exact _.
Defined.

(** ** Finite products of natural numbers *)

(** Similarly, closure of finite sets under [forall] automatically gives us a way to multiply a family of natural numbers indexed by any finite set.  Of course, if we defined this explicitly, it wouldn't need funext. *)

Definition finmult `{Funext} {X} `{Finite X} (f : X -> nat) : nat
  := fcard (forall x:X, Fin (f x)).

Definition fcard_forall `{Funext} {X} (Y : X -> Type)
       `{Finite X} `{forall x, Finite (Y x)}
: fcard (forall x:X, Y x) = finmult (fun x => fcard (Y x)).
Proof.
  set (f := fun x => fcard (Y x)).
  set (g := fun x => merely_equiv_fin (Y x) : merely (Y x <~> Fin (f x))).
  apply finite_choice in g.
  strip_truncations.
  unfold finmult.
  refine (fcard_equiv' (equiv_functor_forall' (equiv_idmap X) g)).
Defined.

(** The product of a finite constant family is the exponential by its cardinality. *)
Definition finmult_const `{Funext} X `{Finite X} n
: finmult (fun x:X => n) = nat_exp n (fcard X).
Proof.
  refine (fcard_arrow X (Fin n)).
Defined.


(** ** Finite subsets *)

(** Closure under sigmas implies that a detachable subset of a finite set is finite. *)
Global Instance finite_detachable_subset {X} `{Finite X} (P : X -> Type)
       `{forall x, IsHProp (P x)} `{forall x, Decidable (P x)}
: Finite { x:X & P x }.
Proof.
  exact _.
Defined.

(** Conversely, if a subset of a finite set is finite, then it is detachable.  We show first that an embedding between finite subsets has detachable image. *)
Definition detachable_image_finite
           {X Y} `{Finite X} `{Finite Y} (f : X -> Y) `{IsEmbedding f}
: forall y, Decidable (hfiber f y).
Proof.
  intros y.
  assert (ff : Finite (hfiber f y)) by exact _.
  destruct ff as [[|n] e].
  - right; intros u; strip_truncations; exact (e u).
  - left; strip_truncations; exact (e^-1 (inr tt)).
Defined.

Definition detachable_finite_subset {X} `{Finite X}
           (P : X -> Type) `{forall x, IsHProp (P x)}
           {Pf : Finite ({ x:X & P x })}
: forall x, Decidable (P x).
Proof.
  intros x.
  refine (decidable_equiv _ (hfiber_fibration x P)^-1 _).
  refine (detachable_image_finite pr1 x).
  - assumption.                 (** Why doesn't Coq find this? *)
  - apply mapinO_pr1; exact _.  (** Why doesn't Coq find this? *)
Defined.

(** ** Quotients *)

(** The quotient of a finite set by a detachable equivalence relation is finite. *)

Section DecidableQuotients.
  Context `{Univalence} {X} `{Finite X}
          (R : relation X) `{is_mere_relation X R}
          `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R}
          {Rd : forall x y, Decidable (R x y)}.

  Global Instance finite_quotient : Finite (quotient R).
  Proof.
    assert (e := merely_equiv_fin X).
    strip_truncations.
    pose (R' x y := R (e^-1 x) (e^-1 y)).
    assert (is_mere_relation _ R') by exact _.
    assert (Reflexive R') by (intros ?; unfold R'; apply reflexivity).
    assert (Symmetric R') by (intros ? ?; unfold R'; apply symmetry).
    assert (Transitive R') by (intros ? ? ?; unfold R'; apply transitivity).
    assert (R'd : forall x y, Decidable (R' x y)) by (intros ? ?; unfold R'; apply Rd).
    refine (finite_equiv' (quotient R') (quotient_functor_equiv R' R e^-1 _) _); try exact _.
    { intros x y; split; apply idmap. }
    clearbody R'; clear e.
    generalize dependent (fcard X);
      intros n; induction n as [|n IH]; intros R' ? ? ? ? ?.
    - refine (finite_equiv Empty _^-1 _).
      refine (quotient_rec R' Empty_rec (fun x _ _ => match x with end)).
    - pose (R'' x y := R' (inl x) (inl y)).
      assert (is_mere_relation _ R'') by exact _.
      assert (Reflexive R'') by (intros ?; unfold R''; apply reflexivity).
      assert (Symmetric R'') by (intros ? ?; unfold R''; apply symmetry).
      assert (Transitive R'') by (intros ? ? ?; unfold R''; apply transitivity).
      assert (forall x y, Decidable (R'' x y)) by (intros ? ?; unfold R''; apply R'd).
      assert (inlresp := (fun x y => idmap)
                         : forall x y, R'' x y -> R' (inl x) (inl y)).
      destruct (dec (merely {x:Fin n & R' (inl x) (inr tt)})) as [p|np].
      { strip_truncations.
        destruct p as [x r].
        refine (finite_equiv' (quotient R'') _ _).
        refine (BuildEquiv _ _ (quotient_functor R'' R' inl inlresp) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (quotient_ind_prop R' _ _).
          intros [y|[]]; apply tr.
          + exists (class_of R'' y); reflexivity.
          + exists (class_of R'' x); simpl.
            apply related_classes_eq, r.
        - apply isembedding_isinj_hset; intros u.
          refine (quotient_ind_prop R'' _ _); intros v.
          revert u; refine (quotient_ind_prop R'' _ _); intros u.
          simpl; intros q.
          apply related_classes_eq; unfold R''.
          exact (classes_eq_related R' (inl u) (inl v) q). }
      { refine (finite_equiv' (quotient R'' + Unit) _ _).
        refine (BuildEquiv _ _ (sum_ind (fun _ => quotient R')
                                        (quotient_functor R'' R' inl inlresp)
                                        (fun _ => class_of R' (inr tt))) _).
        apply isequiv_surj_emb.
        - apply BuildIsSurjection.
          refine (quotient_ind_prop R' _ _).
          intros [y|[]]; apply tr.
          + exists (inl (class_of R'' y)); reflexivity.
          + exists (inr tt); reflexivity.
        - apply isembedding_isinj_hset; intros u.
          refine (sum_ind _ _ _).
          + refine (quotient_ind_prop R'' _ _); intros v.
            revert u; refine (sum_ind _ _ _).
            * refine (quotient_ind_prop R'' _ _); intros u.
              simpl; intros q.
              apply ap, related_classes_eq; unfold R''.
              exact (classes_eq_related R' (inl u) (inl v) q).
            * intros []; simpl.
              intros q.
              apply classes_eq_related in q; try exact _.
              apply symmetry in q.
              elim (np (tr (v ; q))).
          + intros []; simpl.
            destruct u as [u|[]]; simpl.
            * revert u; refine (quotient_ind_prop R'' _ _); intros u; simpl.
              intros q.
              apply classes_eq_related in q; try exact _.
              elim (np (tr (u;q))).
            * intros; reflexivity. }
  Defined.

  (** Therefore, the cardinality of [X] is the sum of the cardinalities of its equivalence classes. *)
  Definition fcard_quotient
  : fcard X = finplus (fun z:quotient R => fcard {x:X & in_class R z x}).
  Proof.
    refine (fcard_domain (class_of R) @ _).
    apply ap, path_arrow; intros z; revert z.
    refine (quotient_ind_prop _ _ _); intros x; simpl.
    apply fcard_equiv'; unfold hfiber.
    refine (equiv_functor_sigma' (equiv_idmap X) _); intros y; simpl.
    refine (equiv_compose' _ (sets_exact R y x)).
    apply equiv_iff_hprop; apply symmetry.
  Defined.

End DecidableQuotients.
