Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.
Require Import Category.Dual Functor.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import InitialTerminalCategory NatCategory.
Require Import FunctorCategory.Core.
Require Import Cat.Core.
Require Import Functor.Paths.
Require Import Comma.Core Comma.InducedFunctors Comma.Projection.
Require ProductLaws ExponentialLaws.Law1.Functors ExponentialLaws.Law4.Functors.
Require Import types.Prod types.Forall PathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Section comma.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Hypothesis PAB : P (A * B).
  Hypothesis P_comma : forall (S : Functor A C) (T : Functor B C),
                         P (S / T).

  Local Open Scope morphism_scope.

  Definition comma_category_projection_functor_object_of
             (ST : object ((A -> C)^op * (B -> C)))
  : Cat / !((A * B; PAB) : Cat).
  Proof.
    exists (Datatypes.fst ST / Datatypes.snd ST; P_comma _ _) (center _).
    exact (comma_category_projection (Datatypes.fst ST) (Datatypes.snd ST)).
  Defined.

  Definition comma_category_projection_functor_morphism_of
             s d (m : morphism ((A -> C)^op * (B -> C)) s d)
  : morphism (Cat / !((A * B; PAB) : Cat))
             (comma_category_projection_functor_object_of s)
             (comma_category_projection_functor_object_of d).
  Proof.
    exists (comma_category_induced_functor m) (center _).
    simpl.
    destruct_head_hnf Datatypes.prod.
    path_functor.
  Defined.

  Local Ltac comma_laws_t :=
    repeat (apply path_forall || intro);
    simpl;
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    simpl;
    destruct_head Datatypes.prod;
    simpl in *;
    apply CommaCategory.path_morphism;
    simpl;
    repeat match goal with
             | [ |- appcontext[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _ _ _ _)
                                   z)
             | [ |- appcontext[transport (fun y => ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _ _ _ _))
             | [ |- appcontext[transport (fun y => ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _ _ _ _))
           end;
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl;
    rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object';
    try reflexivity.

  Lemma comma_category_projection_functor_identity_of_helper
  : forall (X : Functor A C) (X0 : Functor B C)
           (X1 : Functor A C -> Functor B C -> Type) (X2 X3 : X1 X X0)
           (X4 : X1 X X0 -> X1 X X0) (X5 : forall x : X1 X X0, X4 x = x)
           (X6 : forall (S : Functor A C) (T : Functor B C),
                   X1 S T -> X1 S T -> Type) (X7 : X6 X X0 X2 X3)
           (X8 : forall s0 d0 : X1 X X0, X6 X X0 s0 d0 -> X6 X X0 (X4 s0) (X4 d0)),
      transport (fun y : X1 X X0 => X6 X X0 X2 y) (X5 X3)
                (transport (fun y : X1 X X0 => X6 X X0 y (X4 X3)) (X5 X2) (X8 X2 X3 X7)) =
      X7
      -> transport
           (fun GO : X1 X X0 -> X1 X X0 =>
              forall s d : X1 X X0, X6 X X0 s d -> X6 X X0 (GO s) (GO d))
           (path_forall X4 idmap X5) X8 X2 X3 X7 = X7.
  Proof.
    intros.
    rewrite !transport_forall_constant.
    transport_path_forall_hammer.
    assumption.
  Qed.

  Lemma comma_category_projection_functor_identity_of_helper_2
  : forall (X : Functor A C) (X0 : Functor B C)
           (X1 X2 : @CommaCategory.object A B C X X0)
           (X3 : forall (S : Functor A C) (T : Functor B C),
                   @CommaCategory.object A B C S T ->
                   @CommaCategory.object A B C S T -> Type)
           (X4 : X3 X X0 X1 X2)
           (X5 : forall (S : Functor A C) (T : Functor B C)
                        (abf a'b'f' : @CommaCategory.object A B C S T),
                   X3 S T abf a'b'f' ->
                   morphism B (@CommaCategory.b A B C S T abf)
                            (@CommaCategory.b A B C S T a'b'f'))
           (X6 : forall (S : Functor A C) (T : Functor B C)
                        (abf a'b'f' : @CommaCategory.object A B C S T),
                   X3 S T abf a'b'f' ->
                   morphism A (@CommaCategory.a A B C S T abf)
                            (@CommaCategory.a A B C S T a'b'f')),
      (forall (S : Functor A C) (T : Functor B C)
              (abf a'b'f' : @CommaCategory.object A B C S T)
              (gh g'h' : X3 S T abf a'b'f'),
         X6 S T abf a'b'f' gh = X6 S T abf a'b'f' g'h' ->
         X5 S T abf a'b'f' gh = X5 S T abf a'b'f' g'h' -> gh = g'h') ->
      forall (X8 : @Core.NaturalTransformation A C X X)
             (X9 : @Core.NaturalTransformation B C X0 X0)
             (X10 : @comma_category_induced_functor_object_of H A B C
                                                              (X, X0) (X, X0) (X8, X9) X1 = X1),
        @ap (@CommaCategory.object A B C X X0) B (@CommaCategory.b A B C X X0)
            (@comma_category_induced_functor_object_of H A B C
                                                       (X, X0) (X, X0) (X8, X9) X1) X1 X10 = 1%path ->
        @ap (@CommaCategory.object A B C X X0) A (@CommaCategory.a A B C X X0)
            (@comma_category_induced_functor_object_of H A B C
                                                       (X, X0) (X, X0) (X8, X9) X1) X1 X10 = 1%path ->
        forall
          X13 : @comma_category_induced_functor_object_of H A B C
                                                          (X, X0) (X, X0) (X8, X9) X2 = X2,
          @ap (@CommaCategory.object A B C X X0) B (@CommaCategory.b A B C X X0)
              (@comma_category_induced_functor_object_of H A B C
                                                         (X, X0) (X, X0) (X8, X9) X2) X2 X13 = 1%path ->
          @ap (@CommaCategory.object A B C X X0) A (@CommaCategory.a A B C X X0)
              (@comma_category_induced_functor_object_of H A B C
                                                         (X, X0) (X, X0) (X8, X9) X2) X2 X13 = 1%path ->
          forall
            X16 : X3 X X0
                     (@comma_category_induced_functor_object_of H A B C
                                                                (X, X0) (X, X0) (X8, X9) X1)
                     (@comma_category_induced_functor_object_of H A B C
                                                                (X, X0) (X, X0) (X8, X9) X2),
            (forall (S : Functor A C) (T : Functor B C)
                    (x : @CommaCategory.object A B C S T),
               morphism C (S (@CommaCategory.a A B C S T x))
                        (T (@CommaCategory.b A B C S T x))) ->
            X6 X X0
               (@comma_category_induced_functor_object_of H A B C
                                                          (X, X0) (X, X0) (X8, X9) X1)
               (@comma_category_induced_functor_object_of H A B C
                                                          (X, X0) (X, X0) (X8, X9) X2) X16 = X6 X X0 X1 X2 X4
            -> X5 X X0
                  (@comma_category_induced_functor_object_of H A B C
                                                             (X, X0) (X, X0) (X8, X9) X1)
                  (@comma_category_induced_functor_object_of H A B C
                                                             (X, X0) (X, X0) (X8, X9) X2) X16 = X5 X X0 X1 X2 X4
            -> @transport (@CommaCategory.object A B C X X0)
                          (fun y : @CommaCategory.object A B C X X0 => X3 X X0 X1 y)
                          (@comma_category_induced_functor_object_of H A B C
                                                                     (X, X0) (X, X0) (X8, X9) X2) X2 X13
                          (@transport (@CommaCategory.object A B C X X0)
                                      (fun y : @CommaCategory.object A B C X X0 =>
                                         X3 X X0 y
                                            (@comma_category_induced_functor_object_of H A B C
                                                                                       (X, X0) (X, X0) (X8, X9) X2))
                                      (@comma_category_induced_functor_object_of H A B C
                                                                                 (X, X0) (X, X0) (X8, X9) X1) X1 X10 X16) = X4.
  Proof.
    intros.
    apply_hyp;
    repeat match goal with
             | [ |- appcontext[?f _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _)
                                   z)
             | [ |- appcontext[transport (fun y => ?f (?fa _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _))
             | [ |- appcontext[transport (fun y => ?f ?x (?fa _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _))
           end;
    rewrite_hyp;
    simpl in *;
    reflexivity.
  Qed.

  Lemma comma_category_projection_functor_composition_of_helper
  : forall
      (T : Type) (f0 f2 : T) (T0 : Type) (f f1 : T0)
      (T1 : T0 -> T -> Type) (x x0 : T1 f f0)
      (fg x'' : T1 f f0 -> T1 f1 f2)
      (T2 : forall (S : T0) (T2 : T),
              T1 S T2 -> T1 S T2 -> Type)
      (x1 : T2 f f0 x x0) (m1 : T2 f1 f2 (fg x) (fg x0))
      (m0 : forall s0 d0 : T1 f f0,
              T2 f f0 s0 d0 -> T2 f1 f2 (x'' s0) (x'' d0))
      (x2 : forall x2 : T1 f f0, x'' x2 = fg x2),
      transport (fun y : T1 f1 f2 => T2 f1 f2 (fg x) y)
                (x2 x0)
                (transport (fun y : T1 f1 f2 => T2 f1 f2 y (x'' x0)) (x2 x) (m0 x x0 x1)) =
      m1
      -> transport
           (fun GO : T1 f f0 -> T1 f1 f2 =>
              forall s d : T1 f f0,
                T2 f f0 s d -> T2 f1 f2 (GO s) (GO d))
           (path_forall x'' fg x2) m0 x x0 x1 = m1.
  Proof.
    intros.
    rewrite !transport_forall_constant.
    transport_path_forall_hammer.
    assumption.
  Qed.

  Lemma comma_category_projection_functor_identity_of x
  : comma_category_projection_functor_morphism_of (Category.Core.identity x)
    = 1.
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_identity _)).
    Time (repeat (apply path_forall; intro)).
    Time refine (comma_category_projection_functor_identity_of_helper _ _ _ _ _ _ _ _ _ _).
    unfold comma_category_induced_functor_object_of_identity.
    Time (refine (comma_category_projection_functor_identity_of_helper_2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    exact (@CommaCategory.path_morphism A B C).
    exact (CommaCategory.ap_b_path_object' _ _ _ _ _).
    exact (CommaCategory.ap_a_path_object' _ _ _ _ _).
    exact (CommaCategory.ap_b_path_object' _ _ _ _ _).
    exact (CommaCategory.ap_a_path_object' _ _ _ _ _).
    Focus 2.
    reflexivity.
    Focus 2.
    reflexivity.
    simpl in *.

    match goal with
      | [ |- appcontext[transport ?a ?b ?c] ]
        => match c with
             | appcontext[transport] => fail 1
             | _ => generalize c; intro
           end
    end.
    intros.
    repeat match goal with
             | [ |- appcontext[CommaCategory.path_object' ?x ?y ?Ha ?Hb (?H ?f)] ]
               => generalize (CommaCategory.ap_a_path_object' x y Ha Hb (H f));
                 generalize (CommaCategory.ap_b_path_object' x y Ha Hb (H f));
                 generalize (CommaCategory.path_object' x y Ha Hb (H f))
           end.
    clear.
    intros; simpl in *.
    generalize (@CommaCategory.path_morphism A B C).
    generalize (@CommaCategory.g A B C).
    generalize (@CommaCategory.h A B C).
    generalize dependent (@CommaCategory.morphism A B C).
    intros.
    simpl in *.
    repeat match goal with
             | |- appcontext[comma_category_induced_functor_object_of (?a, ?b)] => generalize dependent (a, b)
           end.
    intros; simpl in *.
    generalize dependent (@CommaCategory.f A B C).
    destruct x.
    intros.

    simpl in *.
    destruct_head @Datatypes.prod.

    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros ? A B C.
    repeat (let X := fresh "X" in intro X).
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros ? A B C.

    Set Printing Implicit.


    unfold comma_category_induced_functor_object_of in *.
    repeat match goal with
             | [ |- appcontext[{| CommaCategory.f := (?f ?x) |}] ]
               => generalize dependent (f x)
           end.

    lazymatch goal with
      | [ |- appcontext[@comma_category_induced_functor_object_of H A B C ?x ?y ?z ?w] ]
        => generalize dependent (@comma_category_induced_functor_object_of H A B C x y z w)
    end.
    lazymatch goal with
      | [ |- appcontext[transport ?x ?y ?z] ] => generalize z
    end.
    intros.
    simpl in *.
    lazymatch goal with
      | [ |- appcontext[path_forall ?x ?y ?z] ] => generalize dependent x
    end.
    intros.
    clear.
    generalize dependent (@CommaCategory.morphism A B C).
    simpl in *.
    generalize dependent (@CommaCategory.object A B C).
    intros.
    simpl in *.
    destruct x.
    simpl in *.
    clear.
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros ? A B C.
    repeat (let X := fresh "X" in intro X).
    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.
    intros ? A B C.

    rewrite ?transport_forall_constant.
    transport_path_forall_hammer.
    unfold comma_category_induced_functor_object_of_identity.
    simpl in *.
    admit. (*abstract comma_laws_t.*)
  Qed.

  Lemma comma_category_projection_functor_composition_of s d d' m m'
  : comma_category_projection_functor_morphism_of
      (@Category.Core.compose _ s d d' m' m)
    = (comma_category_projection_functor_morphism_of m')
        o (comma_category_projection_functor_morphism_of m).
  Proof.
    apply CommaCategory.path_morphism; simpl; [ | reflexivity ].
    path_functor.
    exists (path_forall _ _ (comma_category_induced_functor_object_of_compose m' m)).
    Time (repeat (apply path_forall; intro)).
    Time destruct_head Datatypes.prod.
    Time simpl in *.
    Time refine (@comma_category_projection_functor_composition_of_helper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    Time apply CommaCategory.path_morphism.
    Time simpl.
    generalize (@CommaCategory.g A B C); intro.
    destruct s, d', m, m'; simpl in *.
    unfold comma_category_induced_functor_object_of_compose.
    match goal with
      | [ |- appcontext[transport ?a ?b ?c] ]
        => match c with
             | appcontext[transport] => fail 1
             | _ => generalize c; intro
           end
    end.
    intros.
    repeat match goal with
             | [ |- appcontext[CommaCategory.path_object' ?x ?y ?Ha ?Hb (?H ?f)] ]
               => generalize (CommaCategory.ap_a_path_object' x y Ha Hb (H f));
                 generalize (CommaCategory.ap_b_path_object' x y Ha Hb (H f));
                 generalize (CommaCategory.path_object' x y Ha Hb (H f))
           end.
    clear.
    intros; simpl in *.
    generalize dependent (@CommaCategory.morphism A B C).
    intros.
    simpl in *.
    repeat match goal with
             | |- appcontext[comma_category_induced_functor_object_of (?a, ?b)] => generalize dependent (a, b)
           end.
    intros; simpl in *.
    generalize dependent (@CommaCategory.f A B C).

    intros.
    simpl in *.

    repeat match goal with
             | [ H : _ |- _ ] => revert H
           end.

    simpl in *.

    intros ? A B C.

    Set Printing Implicit.


    Focus 2.
    assert (   forall (X : Functor A C) (X0 : Functor B C)
     (X1 : Functor A C * Functor B C) (X2 : Functor A C)
     (X3 : Functor B C),
   @Core.NaturalTransformation A C
     (@Datatypes.fst (Functor A C) (Functor B C) X1) X ->
   @Core.NaturalTransformation B C X0
     (@Datatypes.snd (Functor A C) (Functor B C) X1) ->
   @Core.NaturalTransformation A C X2
     (@Datatypes.fst (Functor A C) (Functor B C) X1) ->
   @Core.NaturalTransformation B C
     (@Datatypes.snd (Functor A C) (Functor B C) X1) X3 ->
   forall (X8 X9 : @CommaCategory.object A B C X X0)
     (X10 : forall (S : Functor A C) (T : Functor B C),
            @CommaCategory.object A B C S T ->
            @CommaCategory.object A B C S T -> Type)
     (X11 : X10 X X0 X8 X9)
     (X12 : forall (S : Functor A C) (T : Functor B C)
              (abf a'b'f' : @CommaCategory.object A B C S T),
            X10 S T abf a'b'f' ->
            morphism A (@CommaCategory.a A B C S T abf)
              (@CommaCategory.a A B C S T a'b'f'))
     (X13 : @Core.NaturalTransformation A C
              (@Datatypes.fst (Functor A C) (Functor B C) X1) X *
            @Core.NaturalTransformation B C X0
              (@Datatypes.snd (Functor A C) (Functor B C) X1))
     (X14 : @Core.NaturalTransformation A C X2 X *
            @Core.NaturalTransformation B C X0 X3)
     (X15 : X10 X2 X3
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) (X2, X3) X14 X8)
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) (X2, X3) X14 X9))
     (X16 : @Core.NaturalTransformation A C X2
              (@Datatypes.fst (Functor A C) (Functor B C) X1) *
            @Core.NaturalTransformation B C
              (@Datatypes.snd (Functor A C) (Functor B C) X1) X3)
     (X17 : @comma_category_induced_functor_object_of H A B C
              (X, X0) (X2, X3) X14 X8 =
            @comma_category_induced_functor_object_of H A B C X1
              (X2, X3) X16
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) X1 X13 X8)),
   @ap (@CommaCategory.object A B C X2 X3) B (@CommaCategory.b A B C X2 X3)
     (@comma_category_induced_functor_object_of H A B C
        (X, X0) (X2, X3) X14 X8)
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X8))
     X17 = 1%path ->
   @ap (@CommaCategory.object A B C X2 X3) A (@CommaCategory.a A B C X2 X3)
     (@comma_category_induced_functor_object_of H A B C
        (X, X0) (X2, X3) X14 X8)
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X8))
     X17 = 1%path ->
   forall
     X20 : @comma_category_induced_functor_object_of H A B C
             (X, X0) (X2, X3) X14 X9 =
           @comma_category_induced_functor_object_of H A B C X1
             (X2, X3) X16
             (@comma_category_induced_functor_object_of H A B C
                (X, X0) X1 X13 X9),
   @ap (@CommaCategory.object A B C X2 X3) B (@CommaCategory.b A B C X2 X3)
     (@comma_category_induced_functor_object_of H A B C
        (X, X0) (X2, X3) X14 X9)
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X9))
     X20 = 1%path ->
   @ap (@CommaCategory.object A B C X2 X3) A (@CommaCategory.a A B C X2 X3)
     (@comma_category_induced_functor_object_of H A B C
        (X, X0) (X2, X3) X14 X9)
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X9))
     X20 = 1%path ->
   (forall (S : Functor A C) (T : Functor B C)
      (x : @CommaCategory.object A B C S T),
    morphism C (S (@CommaCategory.a A B C S T x))
      (T (@CommaCategory.b A B C S T x))) ->
   X12 X2 X3
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X8))
     (@comma_category_induced_functor_object_of H A B C X1
        (X2, X3) X16
        (@comma_category_induced_functor_object_of H A B C (X, X0) X1 X13 X9))
     (@transport (@CommaCategory.object A B C X2 X3)
        (fun y : @CommaCategory.object A B C X2 X3 =>
         X10 X2 X3
           (@comma_category_induced_functor_object_of H A B C X1
              (X2, X3) X16
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) X1 X13 X8)) y)
        (@comma_category_induced_functor_object_of H A B C
           (X, X0) (X2, X3) X14 X9)
        (@comma_category_induced_functor_object_of H A B C X1
           (X2, X3) X16
           (@comma_category_induced_functor_object_of H A B C
              (X, X0) X1 X13 X9)) X20
        (@transport (@CommaCategory.object A B C X2 X3)
           (fun y : @CommaCategory.object A B C X2 X3 =>
            X10 X2 X3 y
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) (X2, X3) X14 X9))
           (@comma_category_induced_functor_object_of H A B C
              (X, X0) (X2, X3) X14 X8)
           (@comma_category_induced_functor_object_of H A B C X1
              (X2, X3) X16
              (@comma_category_induced_functor_object_of H A B C
                 (X, X0) X1 X13 X8)) X17 X15)) = X12 X X0 X8 X9 X11
).
    admit.
    Unset Printing Implicit.
    destruct s, d, d', m, m'.
    simpl in *.
    refine (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

    Time repeat match goal with
             | [ |- appcontext[?f _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _)
                                   z)
             | [ |- appcontext[transport (fun y => ?f (?fa _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _))
             | [ |- appcontext[transport (fun y => ?f ?x (?fa _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _))
           end.
    rewrite_hyp.
    simpl.


generalize dependent (@comma_category_induced_functor_object_of H A B C (f, f0) (f1, f2) p0 x).

generalize dependent (@comma_category_induced_functor_object_of H A B C (f, f0) d p x).


generalize dependent (@CommaCategory.a A B C).
    generalize dependent (@CommaCategory.b A B C).
    generalize dependent (@CommaCategory.object A B C).
    progress repeat match goal with
                      | [ |- appcontext[@comma_category_induced_functor_object_of ?H ?A ?B ?C ?x ?y] ]
                        => generalize dependent (@comma_category_induced_functor_object_of H A B C x y)
                    end.
    Set Printing Implicit.
    progress repeat match goal with
                      | [ |- appcontext[@comma_category_induced_functor_object_of ?H ?A ?B ?C ?x ?y] ]
                        => generalize dependent (@comma_category_induced_functor_object_of H A B C x y)
                    end.

    generalize dependent (comma_category_induced_functor_object_of p2
                                                                   (comma_category_induced_functor_object_of p0 x0)).
    generalize dependent (@CommaCategory.f A B C).
    generalize dependent (@CommaCategory.a A B C).
    generalize dependent (@CommaCategory.b A B C).
    generalize dependent (@CommaCategory.object A B C).



    lazymatch goal with
      | [ |- appcontext[@comma_category_induced_functor_object_of ?H ?A ?B ?C ?x ?y] ]
        => generalize dependent (@comma_category_induced_functor_object_of H A B C x y)
    end.

    lazymatch goal with
             | [ |- appcontext[CommaCategory.path_object' (?f ?x) (?g ?y)] ]
               => generalize dependent (f x); generalize dependent (g y)
           end.

    Set Printing Implicit.
    match goal with
      | [
    match goal with
        match goal with
      | |- appcontext[comma_category_induced_functor_morphism_of (?a, ?b)] => generalize dependent (a, b)
    end.
        intros.
        generalize (comma_category_induced_functor_morphism_of p0).
        intro.
        generalize (comma_category_induced_functor_morphism_of m'
     (comma_category_induced_functor_morphism_of m x1)).
        intro.
        revert p1.


    generalize dependent (@CommaCategory.morphism A B C).


    Time repeat match goal with
             | [ |- appcontext[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _ _ _ _)
                                   z)
             | [ |- appcontext[transport (fun y => ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _ _ _ _))
             | [ |- appcontext[transport (fun y => ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _ _ _ _))
           end.
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl.
    Time rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object'.
    Time reflexivity.




    pose @transport_forall_constant.
    let H := lazymatch goal with |- appcontext[path_forall ?x ?y ?z] => constr:(z) end in
        generalize H.
        simpl.
        match goal with
          | |- appcontext[comma_category_induced_functor_morphism_of (?a, ?b)] => generalize (a, b)
        end.
        intros.
        generalize (comma_category_induced_functor_morphism_of p0).
        intro.
        generalize (comma_category_induced_functor_morphism_of m'
     (comma_category_induced_functor_morphism_of m x1)).
        intro.
        revert p1.
        lazymatch goal with
          | |- forall x0 : forall x2, @?a x2 = ?f (?g x2), @?h x0
            => let fg := fresh "fg" in
               set (fg := fun x' => f (g x'));
                 change (forall x0 : forall x2, a x2 = fg x2, h x0);
                 repeat match goal with
                          | [ |- appcontext[f (g ?x)] ] =>
                            change (f (g x)) with (fg x)
                          | [ H : appcontext[f (g ?x)] |- _ ] =>
                            change (f (g x)) with (fg x) in H
                        end
        end.
        cbv beta.
        lazymatch goal with
          | [ |- appcontext[path_forall ?x ?y] ]
            => change y with fg
        end.
        generalize dependent fg.
        intros.
        generalize dependent (comma_category_induced_functor_object_of p0).
        intro x''.
        simpl in *.
        generalize dependent (@CommaCategory.morphism A B C).
        intros.
        simpl in *.
        generalize dependent (@CommaCategory.object A B C).
        intros.
        simpl in *.
        clear.
        destruct s, d'.
        simpl in *.
        generalize dependent (Functor A C).
        generalize dependent (Functor B C).
        clear.
        intros.
        simpl in *.
        repeat match goal with
                 | [ H : _ |- _ ] => revert H
               end.
        intro.
        rewrite transport_forall_constant.
        rewrite transport_forall_constant.
        rewrite transport_forall_constant.
        transport_path_forall_hammer.



        set (T' := fun xy => T (Datatypes.fst xy) (Datatypes.snd xy)).
        set (T0' := fun xy => T0 (Datatypes.fst xy) (Datatypes.snd xy) : T' xy -> T' xy -> Type).
        repeat match goal with
                 | [ |- appcontext[T (Datatypes.fst ?x) (Datatypes.snd ?y)] ]
                   => progress change (T (Datatypes.fst x) (Datatypes.snd y)) with (T' x)
                 | [ |- appcontext[T0 (Datatypes.fst ?x) (Datatypes.snd ?y)] ]
                   => progress change (T0 (Datatypes.fst x) (Datatypes.snd y)) with (T0' x)
                 | [ H : appcontext[T (Datatypes.fst ?x) (Datatypes.snd ?y)] |- _ ]
                   => progress change (T (Datatypes.fst x) (Datatypes.snd y)) with (T' x) in H
                 | [ H : appcontext[T0 (Datatypes.fst ?x) (Datatypes.snd ?y)] |- _ ]
                   => progress change (T0 (Datatypes.fst x) (Datatypes.snd y)) with (T0' x) in H
                 | _ => clearbody T0'
                 | _ => clearbody T'
               end.

        simpl in *.





        generalize dependent T0'.




        change (forall xy, T (Datatypes.fst xy) (Datatypes.snd xy) -> T (Datatypes.fst xy) (Datatypes.snd xy) -> Type) with (forall xy, T' xy -> T' xy -> Type).


        clearbody T'.
        cleargeneralize dependent (T f f0).




 generalize ((fun x2 : CommaCategory.object (Datatypes.fst s) (Datatypes.snd s) =>
         comma_category_induced_functor_object_of m'
           (comma_category_induced_functor_object_of m x2)))
        intro.
        match goal with
          |
        lazymatch goal with
          | |- appcontext[
    lazymatch goal with
    |- appcontext[path_forall ?x ?y] => generalize dependent y
        end.
        generalize H.
           (Core.compose (Datatypes.fst m) (Datatypes.fst m'),
           Core.compose (Datatypes.snd m') (Datatypes.snd m)))).

    Time rewrite !transport_forall_constant.
    Time transport_path_forall_hammer.
    Time simpl.
    Time destruct_head Datatypes.prod.
    Time simpl in *.
    Time apply CommaCategory.path_morphism.
    Time simpl.
    Time repeat match goal with
             | [ |- appcontext[?f _ _ _ _ _ _ _ (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport
                                   _ P _ _ _ p
                                   (fun _ => f _ _ _ _ _ _ _)
                                   z)
             | [ |- appcontext[transport (fun y => ?f (?fa _ _ _ _ _ y) ?x)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f y x) (fa _ _ _ _ _))
             | [ |- appcontext[transport (fun y => ?f ?x (?fa _ _ _ _ _ y))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x y) (fa _ _ _ _ _))
           end.
    unfold comma_category_induced_functor_object_of_identity;
    unfold comma_category_induced_functor_object_of_compose;
    simpl.
    Time rewrite ?CommaCategory.ap_a_path_object', ?CommaCategory.ap_b_path_object'.
    Time reflexivity.

    abstract comma_laws_t.
  Qed.

  Definition comma_category_projection_functor
  : Functor ((A -> C)^op * (B -> C))
            (Cat / !((A * B; PAB) : Cat))
    := Build_Functor ((A -> C)^op * (B -> C))
                     (Cat / !((A * B; PAB) : Cat))
                     comma_category_projection_functor_object_of
                     comma_category_projection_functor_morphism_of
                     comma_category_projection_functor_composition_of
                     comma_category_projection_functor_identity_of.
End comma.

Section slice_category_projection_functor.
  Context `{Funext}.

  Variable P : PreCategory -> Type.
  Context `{HF : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Variable D : PreCategory.

  Hypothesis P1C : P (1 * C).
  Hypothesis PC1 : P (C * 1).
  Hypothesis PC : P C.
  Hypothesis P_comma : forall (S : Functor C D) (T : Functor 1 D), P (S / T).
  Hypothesis P_comma' : forall (S : Functor 1 D) (T : Functor C D), P (S / T).

  Local Open Scope functor_scope.
  Local Open Scope category_scope.

  Definition slice_category_projection_functor
  : object (((C -> D)^op) -> (D -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 ExponentialLaws.Law1.Functors.inverse D)).
    refine (_ o @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  Definition coslice_category_projection_functor
  : object ((C -> D)^op -> (D -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D)^op,
                 ExponentialLaws.Law1.Functors.inverse D)).
    refine (_ o @comma_category_projection_functor _ P HF C 1 D PC1 P_comma).
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor _).
  Defined.

  Definition slice_category_projection_functor'
  : object ((C -> D) -> (D^op -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (ExponentialLaws.Law1.Functors.inverse D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.

  Definition coslice_category_projection_functor'
  : object ((C -> D) -> (D^op -> (Cat / ((C; PC) : Cat)))).
  Proof.
    refine ((ExponentialLaws.Law4.Functors.inverse _ _ _) _).
    refine (_ o (Functor.Identity.identity (C -> D),
                 (ExponentialLaws.Law1.Functors.inverse D)^op)).
    refine (_ o ProductLaws.Swap.functor _ _).
    refine (_ o @comma_category_projection_functor _ P HF 1 C D P1C P_comma').
    refine (cat_over_induced_functor _).
    hnf.
    exact (ProductLaws.Law1.functor' _).
  Defined.
End slice_category_projection_functor.
