Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import Functor.Composition.Functorial.
Require Import UniversalProperties KanExtensions.Core InitialTerminalCategory NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import Limits.Core.
Require Import Category.Morphisms.
Require Import Category.Dual Functor.Dual IndiscreteCategory.
Require Import Equivalences HoTT.Tactics types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

(** ** Introduction and elimination rules for limit and colimit *)
(** Internally, we represent (co)limits as Kan extensions.  This is
    very convenient for abstract reasoning about (co)limits, because
    all of the theorems about Kan extensions apply automatically to
    limits without any kind of correction needed.  Unfortunately, it's
    rather inconvenient for actually building or using (co)limits,
    because it results in lots of functors and identities and objects
    of terminal categories flying around, when we don't really need
    any of that.  So we write introduction rules (for constructing
    (co)limits) and elimination rules (for obtaining properties of
    (co)limits) which are nicely typed.  We opacify all of the
    constructions so that they don't get unfolded when they shouldn't
    be.  We should probably eventually add computation rules, about
    how when you apply an eliminator to a constructor, you get back
    what you started with.  But that's for another time.

    We do not provide (co)limit specific versions of the introduction
    rule that uses [Contr], and is nether completely curried nor
    completely uncurried, because if you actually want to be using
    [Contr], then you are probably proving a theorem about (co)limits
    in general, and that theorem probably generalizes to Kan
    extensions and possibly to adjoint functors in general. So we
    don't expect anyone to want to use a [Contr] property when talking
    only about (co)limits. *)

Section Colimit.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor D C.

  Local Open Scope morphism_scope.

  Section introduction_abstraction_barrier.
    Local Notation mk_nt :=
      (fun (A : C)
           (p' : forall d : D, morphism C (F d) A)
           (p'_commutes : forall s d (m : morphism D s d),
                            p' s = p' d o F _1 m)
       => Build_NaturalTransformation
            F ((pullback_along C (Functors.to_terminal D)) !A)
            p'
            (fun _ _ _ =>
               (left_identity _ _ _ _ @ p'_commutes _ _ _)^%path)).

    Definition Build_IsColimit_curried
    : forall
        (A : C)
        (p' : forall d : D, morphism C (F d) A)
        (p'_commutes : forall s d (m : morphism D s d),
                         p' s = p' d o F _1 m)
        (m : forall (A' : C)
                    (p'' : forall d : D, morphism C (F d) A'),
               (forall s d (m : morphism D s d),
                  p'' s = p'' d o F _1 m)
               -> morphism C A A')
        (H0 : forall (A' : C)
                     (p'' : forall d : D, morphism C (F d) A')
                     (p''_commutes : (forall s d (m : morphism D s d),
                                        p'' s = p'' d o F _1 m)),
              forall d : D, m A' p'' p''_commutes o p' d = p'' d)
        (H1 : forall (A' : C)
                     (p'' : forall d : D, morphism C (F d) A')
                     (p''_commutes : (forall s d (m : morphism D s d),
                                        p'' s = p'' d o F _1 m))
                     (m' : morphism C A A'),
                (forall d : D, m' o p' d = p'' d)
                -> m A' p'' p''_commutes = m'),
        @IsColimit
          _ C D F
          (CommaCategory.Build_object
             !(F : object (_ -> _)) (pullback_along C (Functors.to_terminal D))
             (center _) !A (mk_nt A p' p'_commutes)).
    Proof.
      intros.
      refine ((fun e0 =>
                 (fun e0 e1 =>
                    @Build_IsLeftKanExtensionAlong_curried
                      _ _ _ _ _ _
                      !A
                      (mk_nt A p' p'_commutes)
                      (fun A' p'' =>
                         Build_NaturalTransformation
                           !A A'
                           (fun c =>
                              m (A' c)
                                (fun c => A' _1 (idtoiso _ (contr _))%path o components_of p'' c)
                                (fun s d m => e0 A' p'' c s d m))
                           (fun s d m => e1 A' p'' s d m))
                      _
                      _)
                   e0 _)
                _);
        abstract (
            repeat
              match goal with
                | _ => reflexivity
                | _ => (let s := fresh "s" in
                        let H := fresh in
                        intro s;
                        assert (H := contr s);
                        case H; clear H; clear s)
                | [ |- appcontext[contr ?c] ] => destruct (contr c)
                | _ => intro
                | _ => progress path_natural_transformation
                | _ => progress autorewrite with functor morphism
                | _ => (instantiate; progress rewrite_hyp; autorewrite with functor morphism)
                | _ => ((progress apply_hyp); intros; rewrite_rev_hyp)
                | _ => (etransitivity; [ apply ap; apply identity_of | ])
                | [ |- appcontext[components_of ?p''] ]
                  => try_associativity_quick simpl rewrite (commutes p'')
              end
          ).
    Defined.

    (** See the note in [UniversalProperties] for why we want this helper function for building the uncurried version. *)
    Let make_uncurried AT p'T p'_comT mT H0T H1T
        (F' : forall (A : AT)
                     (p' : p'T A)
                     (p'_commutes : p'_comT A p'),
                Type)
        (f : forall A p' p'_commutes
                    (m : forall (A' : AT)
                                (p'' : p'T A')
                                (p''_commutes : p'_comT A' p''),
                           mT A A'),
               (forall (A' : AT)
                       (p'' : p'T A')
                       (p''_commutes : p'_comT A' p''),
                  H0T A p' A' p'' (m A' p'' p''_commutes))
               -> (forall (A' : AT)
                          (p'' : p'T A')
                          (p''_commutes : p'_comT A' p'')
                          (m' : mT A A'),
                     H1T A p' p'_commutes A' p'' (m A' p'' p''_commutes) m')
               -> F' A p' p'_commutes)
        (univ
         : { A : AT
           | { p' : p'T A
             | { p'_commutes : p'_comT A p'
               | forall A' p'' p''_commutes,
                   { m : mT A A'
                   | { H0 : H0T A p' A' p'' m
                     | forall m', H1T A p' p'_commutes A' p'' m m' }}}}})
    : F' univ.1 univ.2.1 univ.2.2.1
      := f (univ.1)
           (univ.2.1)
           (univ.2.2.1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).2.1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).2.2).

    Definition Build_IsColimit_uncurried
      := @make_uncurried
           C
           (fun A => forall d : D, morphism C (F d) A)
           (fun A p' => forall s d (m : morphism D s d),
                          p' s = p' d o F _1 m)
           (morphism C)
           (fun A p' A' p'' m =>
              forall d : D, m o p' d = p'' d)
           (fun A p' p'_commutes A' p'' m m' =>
              forall (_ : forall d : D, m' o p' d = p'' d), m = m')
           (fun A p' p'_commutes =>
              @IsColimit
                _ C D F
                (CommaCategory.Build_object
                   !(F : object (_ -> _)) (pullback_along C (Functors.to_terminal D))
                   (center _) !A (mk_nt A p' p'_commutes)))
           Build_IsColimit_curried.
  End introduction_abstraction_barrier.

  Section elimination_abstraction_barrier.
    Context `(is_colim : @IsColimit _ C D F colim).

    Definition IsColimit_object : C
      := IsInitialMorphism_object is_colim (center _).
    Local Notation IsColimit_natural_transformation
      := (IsInitialMorphism_morphism is_colim).
    Definition IsColimit_morphism
    : forall d : D, morphism C (F d) IsColimit_object
      := components_of IsColimit_natural_transformation.
    Definition IsColimit_morphism_commutes
               s d (m : morphism D s d)
    : IsColimit_morphism d o F _1 m = IsColimit_morphism s
      := ((commutes IsColimit_natural_transformation s d m)
            @ (ap10 (ap _ (identity_of _ _)) _)
            @ (left_identity _ _ _ _))%path.
    Local Notation IsColimit_property_natural_transformation
      := (IsInitialMorphism_property_morphism is_colim).
    Definition IsColimit_property_morphism
               (c : C)
               (ms : forall d, morphism C (F d) c)
               (ms_commutes : forall s d (m : morphism D s d),
                                ms s = ms d o F _1 m)
    : morphism C IsColimit_object c
      := @IsColimit_property_natural_transformation
           !c
           (Build_NaturalTransformation
              F ((pullback_along C (Functors.to_terminal D)) !c)
              ms
              (fun s d m => (left_identity _ _ _ _ @ ms_commutes s d m)^%path))
           (center _).
    Definition IsColimit_property_morphism_property c ms ms_commutes (d : D)
    : IsColimit_property_morphism c ms ms_commutes o IsColimit_morphism d
      = ms d
      := apD10
           (ap
              components_of
              (IsInitialMorphism_property_morphism_property is_colim !c _))
           d.
    (** TODO: Figure out how to refactor this next lemma to make things prettier. *)
    Lemma IsColimit_property_morphism_unique c ms ms_commutes
               (m' : morphism C IsColimit_object c)
               (H' : forall d, m' o IsColimit_morphism d = ms d)
    : IsColimit_property_morphism c ms ms_commutes = m'.
    Proof.
      refine ((fun H1 =>
                 (fun H2 =>
                    apD10
                      (ap
                         components_of
                         (IsInitialMorphism_property_morphism_unique
                            is_colim
                            !c
                            (Build_NaturalTransformation
                               (IsInitialMorphism_object is_colim) !c
                               (fun x =>
                                  transport
                                    (fun x' => morphism C (IsInitialMorphism_object is_colim x') c)
                                    (contr x)
                                    m')
                               (fun s d m => H1 s d m)%path)
                            (f := (Build_NaturalTransformation
                                     F ((pullback_along C (Functors.to_terminal D)) !c)
                                     ms
                                     (fun s d m => (left_identity _ _ _ _ @ ms_commutes s d m)^%path)))
                            (path_natural_transformation _ _ H2)))
                      (center _))
                   H')
                _).
      repeat (let x := fresh in
              let H := fresh in
              intro x;
              try (assert (H := contr x); case H; clear H; clear x)
             ).
      simpl.
      autorewrite with functor morphism.
      reflexivity.
    Qed.
    Definition IsColimit_property
               (c : C)
               (ms : forall d, morphism C (F d) c)
               (ms_commutes : forall s d (m : morphism D s d),
                                ms s = ms d o F _1 m)
    : Contr { m : morphism C IsColimit_object c
            | forall d, m o IsColimit_morphism d = ms d }
      := {| center := (IsColimit_property_morphism c ms ms_commutes;
                       IsColimit_property_morphism_property c ms ms_commutes);
            contr m' := path_sigma
                          _
                          (IsColimit_property_morphism c ms ms_commutes;
                           IsColimit_property_morphism_property c ms ms_commutes)
                          m'
                          (@IsColimit_property_morphism_unique c ms ms_commutes m'.1 m'.2)
                          (center _) |}.
  End elimination_abstraction_barrier.
End Colimit.

Section Limit.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor D C.

  Local Open Scope morphism_scope.

  Local Transparent IsLeftKanExtensionAlong IsRightKanExtensionAlong.

  Section introduction_abstraction_barrier.
    Local Notation mk_nt :=
      (fun (A : C)
           (p' : forall d : D, morphism C A (F d))
           (p'_commutes : forall s d (m : morphism D s d),
                            p' d o F _1 m = p' s)
       => Build_NaturalTransformation
            F
            ((pullback_along C (Functors.to_terminal D)) !A)
            p'
            (fun _ _ _ =>
               p'_commutes _ _ _ @ (left_identity _ _ _ _)^)%path).


    Definition Build_IsLimit_curried
               (A : C)
               (p' : forall d : D, morphism C A (F d))
               (p'_commutes : forall d s (m : morphism D s d),
                                p' d = F _1 m o p' s)
               (m : forall (A' : C)
                           (p'' : forall d : D, morphism C A' (F d)),
                      (forall d s (m : morphism D s d),
                         p'' d = F _1 m o p'' s)
                      -> morphism C A' A)
               (H0 : forall (A' : C)
                            (p'' : forall d : D, morphism C A' (F d))
                            (p''_commutes : (forall d s (m : morphism D s d),
                                               p'' d = F _1 m o p'' s)),
                     forall d : D, p' d o m A' p'' p''_commutes = p'' d)
               (H1 : forall (A' : C)
                            (p'' : forall d : D, morphism C A' (F d))
                            (p''_commutes : (forall d s (m : morphism D s d),
                                               p'' d = F _1 m o p'' s))
                            (m' : morphism C A' A),
                       (forall d : D, p' d o m' = p'' d)
                       -> m A' p'' p''_commutes = m')
    : { x : _ | @IsLimit _ C D F x }.
      pose
        (@Build_IsColimit_curried
           _ (C^op) (D^op) (F^op)
           A). (* p' p'_commutes m H0 H1).*)
      simpl in *.
      eexists.
      unfold IsColimit, IsLimit, IsRightKanExtensionAlong, IsLeftKanExtensionAlong, IsTerminalMorphism in *; simpl in *.

      Set Printing Implicit.







      unfold Category.Dual.opposite at 1.
      Require Import FunctorCategory.Core.
      unfold functor_category in *.
      simpl in *.
      change (fun x y => ?f
      Print Implicit IsInitialMorphism.
      lazymatch type of i with
      | ?f ?a ?b ?c ?d ?e =>
        lazymatch goal with
      | |- ?f' ?a' ?b' ?c' ?d' ?e' =>
        change f' with f;
          try change a' with a;
          try change b' with b;
          try change c' with c;
          try change d' with d;
          try change e' with e
      end
      end.

      let T := match type of i with
                 | ?f ?x ?y ?z ?w
      repeat match goal with
      repeat match goal with
               | [

      exact i.


      unfold Category.Dual.opposite, Functor.Dual.opposite in *.
      simpl in *.
      exact i.
         (D^op)
           (F^op)
           A
           p'
           p'_commutes
           m
           H0).
             H1).
        simpl in *.
    Transparent IsLimit IsRightKanExtensionAlong.
      unfold IsLimit in *.
      unfold IsRightKanExtensionAlong in *.
      unfold IsInitialMorphism in *.
      simpl in *.
      unfold IsColimit.
      Transparent IsLeftKanExtensionAlong.
      unfold IsLeftKanExtensionAlong.
      unfold.

forall
          (A : D)
          (p : morphism C (U A) X)
          (Ap := CommaCategory.Build_object U !X A tt p)
          (m : forall (A' : D) (p' : morphism C (U A') X),
                 morphism D A' A)
          (H : forall (A' : D) (p' : morphism C (U A') X),
                 p o morphism_of U (m A' p') = p')
          (H' : forall (A' : D) (p' : morphism C (U A') X) m',
                  p o morphism_of U m' = p'
                  -> m A' p' = m'),
          IsTerminalMorphism Ap
        := @Build_IsInitialMorphism_curried
             (C^op)
             (D^op)
             X
             (U^op).

      Definition Build_IsTerminalMorphism_uncurried
      : forall
          (univ : { A : D
                  | { p : morphism C (U A) X
                    | let Ap := CommaCategory.Build_object U !X A tt p in
                      forall (A' : D) (p' : morphism C (U A') X),
                        { m : morphism D A' A
                        | { H : p o morphism_of U m = p'
                          | forall m',
                              p o morphism_of U m' = p'
                              -> m = m' }}}}),
          IsTerminalMorphism (CommaCategory.Build_object U !X univ.1 tt univ.2.1)

    Local Notation mk_nt :=
      (fun (A : C)
           (p' : forall d : D, morphism C (F d) A)
           (p'_commutes : forall s d (m : morphism D s d),
                            p' d = F _1 m o p' s)
       => Build_NaturalTransformation
            ((pullback_along C (Functors.to_terminal D)) !A)
            F
            p'
            (fun _ _ _ =>
               right_identity _ _ _ _ @ p'_commutes _ _ _)%path).

    Definition Build_IsLimit_curried
    : forall
        (A : C)
        (p' : forall d : D, morphism C A (F d))
        (p'_commutes : forall s d (m : morphism D s d),
                         p' d = F _1 m o p' s)
        (m : forall (A' : C)
                    (p'' : forall d : D, morphism C A' (F d)),
               (forall s d (m : morphism D s d),
                  p'' d = F _1 m o p'' s)
               -> morphism C A' A)
        (H0 : forall (A' : C)
                     (p'' : forall d : D, morphism C A' (F d))
                     (p''_commutes : (forall s d (m : morphism D s d),
                                        p'' d = F _1 m o p'' s)),
              forall d : D, p' d o m A' p'' p''_commutes = p'' d)
        (H1 : forall (A' : C)
                     (p'' : forall d : D, morphism C A' (F d))
                     (p''_commutes : (forall s d (m : morphism D s d),
                                        p'' d = F _1 m o p'' s))
                     (m' : morphism C A' A),
                (forall d : D, p' d o m' = p'' d)
                -> m A' p'' p''_commutes = m'),
        @IsLimit
          _ C D F
          (CommaCategory.Build_object
             (pullback_along C (Functors.to_terminal D)) !(F : object (_ -> _))
             !A (center _) (mk_nt A p' p'_commutes)).
    Proof.
      intros.
      refine ((fun e0 =>
                 (fun e0 e1 =>
                    @Build_IsRightKanExtensionAlong_curried
                      _ _ _ _ _ _
                      !A
                      (mk_nt A p' p'_commutes)
                      (fun A' p'' =>
                         Build_NaturalTransformation
                           A' !A
                           (fun c =>
                              m (A' c)
                                (fun c => components_of p'' c o A' _1 (idtoiso _ (contr _)^)%path)
                                (fun s d m => e0 A' p'' c s d m))
                           (fun s d m => e1 A' p'' s d m))
                      _
                      _)
                   e0 _)
                _);
        abstract (
            repeat
              match goal with
                | _ => reflexivity
                | _ => (let s := fresh "s" in
                        let H := fresh in
                        intro s;
                        assert (H := contr s);
                        case H; clear H; clear s)
                | [ |- appcontext[contr ?c] ] => destruct (contr c)
                | _ => intro
                | _ => progress path_natural_transformation
                | _ => progress autorewrite with functor morphism
                | _ => (instantiate; progress rewrite_hyp; autorewrite with functor morphism)
                | _ => ((progress apply_hyp); intros; rewrite_rev_hyp)
                | _ => (etransitivity; [ apply ap; apply identity_of | ])
                | [ |- appcontext[components_of ?p''] ]
                  => try_associativity_quick simpl rewrite <- (commutes p'')
              end
          ).
    Defined.

    (** See the note in [UniversalProperties] for why we want this helper function for building the uncurried version. *)
    Let make_uncurried AT p'T p'_comT mT H0T H1T
        (F' : forall (A : AT)
                     (p' : p'T A)
                     (p'_commutes : p'_comT A p'),
                Type)
        (f : forall A p' p'_commutes
                    (m : forall (A' : AT)
                                (p'' : p'T A')
                                (p''_commutes : p'_comT A' p''),
                           mT A' A),
               (forall (A' : AT)
                       (p'' : p'T A')
                       (p''_commutes : p'_comT A' p''),
                  H0T A p' A' p'' (m A' p'' p''_commutes))
               -> (forall (A' : AT)
                          (p'' : p'T A')
                          (p''_commutes : p'_comT A' p'')
                          (m' : mT A' A),
                     H1T A p' p'_commutes A' p'' (m A' p'' p''_commutes) m')
               -> F' A p' p'_commutes)
        (univ
         : { A : AT
           | { p' : p'T A
             | { p'_commutes : p'_comT A p'
               | forall A' p'' p''_commutes,
                   { m : mT A' A
                   | { H0 : H0T A p' A' p'' m
                     | forall m', H1T A p' p'_commutes A' p'' m m' }}}}})
    : F' univ.1 univ.2.1 univ.2.2.1
      := f (univ.1)
           (univ.2.1)
           (univ.2.2.1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).2.1)
           (fun A' p'' p''_commutes => (univ.2.2.2 A' p'' p''_commutes).2.2).

    Definition Build_IsLimit_uncurried
      := @make_uncurried
           C
           (fun A => forall d : D, morphism C A (F d))
           (fun A p' => forall s d (m : morphism D s d),
                          p' d = F _1 m o p' s)
           (morphism C)
           (fun A p' A' p'' m =>
              forall d : D, p' d o m = p'' d)
           (fun A p' p'_commutes A' p'' m m' =>
              forall (_ : forall d : D, p' d o m' = p'' d), m = m')
           (fun A p' p'_commutes =>
              @IsLimit
                _ C D F
                (CommaCategory.Build_object
                   (pullback_along C (Functors.to_terminal D)) !(F : object (_ -> _))
                   !A (center _) (mk_nt A p' p'_commutes)))
           Build_IsLimit_curried.
  End introduction_abstraction_barrier.

  Section elimination_abstraction_barrier.
    Context `(is_lim : @IsLimit _ C D F lim).

    Definition IsLimit_object : C
      := IsTerminalMorphism_object is_lim (center _).
    Definition IsLimit_natural_transformation
      := IsTerminalMorphism_morphism is_lim.
    Definition IsLimit_morphism
    : forall d : D, morphism C IsLimit_object (F d)
      := components_of IsLimit_natural_transformation.
    Definition IsLimit_morphism_commutes
               s d (m : morphism D s d)
    : IsLimit_morphism d = F _1 m o IsLimit_morphism s
      := ((right_identity _ _ _ _)^
          @ ap _ (identity_of _ _)^
          @ commutes IsLimit_natural_transformation s d m)%path.
    Definition IsLimit_property_natural_transformation
      := IsTerminalMorphism_property_morphism is_lim.
    Definition IsLimit_property_natural_transformation'
               (c : C)
               (ms : forall d, morphism C c (F d))
               (ms_commutes : forall s d (m : morphism D s d),
                                ms d = F _1 m o ms s)
      := @IsLimit_property_natural_transformation
           !c
           (Build_NaturalTransformation
              ((pullback_along C (Functors.to_terminal D)) !c) F
              ms
              (fun s d m => right_identity _ _ _ _ @ ms_commutes s d m)%path).
    Definition IsLimit_property_morphism c ms ms_commutes
    : morphism C c IsLimit_object
      := (@IsLimit_property_natural_transformation' c ms ms_commutes) (center _).
    Definition IsLimit_property_morphism_property c ms ms_commutes (d : D)
    : IsLimit_morphism d o IsLimit_property_morphism c ms ms_commutes
      = ms d
      := apD10
           (ap
              components_of
              (IsTerminalMorphism_property_morphism_property is_lim !c _))
           d.
    Lemma IsLimit_property_morphism_unique c ms ms_commutes
               (m' : morphism C c IsLimit_object)
               (H' : forall d, IsLimit_morphism d o m' = ms d)
    : IsLimit_property_morphism c ms ms_commutes = m'.
    Proof.
      refine ((fun H1 =>
                 (fun H2 =>
                    apD10
                      (ap
                         components_of
                         (IsTerminalMorphism_property_morphism_unique
                            is_lim
                            !c
                            (Build_NaturalTransformation
                               !c (IsTerminalMorphism_object is_lim)
                               (fun x =>
                                  transport
                                    (fun x' => morphism C c (IsTerminalMorphism_object is_lim x'))
                                    (contr x)
                                    m')
                               (fun s d m =>
                                  (right_identity _ _ _ _) @ H1 s d m)%path)
                            (f := (Build_NaturalTransformation
                                     ((pullback_along C (Functors.to_terminal D)) !c) F
                                     ms
                                     (fun s d m => right_identity _ _ _ _ @ ms_commutes s d m)%path))
                            (path_natural_transformation _ _ H2)))
                      (center _))
                   H')
                _).
      repeat (let x := fresh in
              let H := fresh in
              intro x;
              try (assert (H := contr x); case H; clear H; clear x)
             ).
      simpl.
      autorewrite with functor morphism.
      reflexivity.
    Qed.
    Definition IsLimit_property
               (c : C)
               (ms : forall d, morphism C c (F d))
               (ms_commutes : forall s d (m : morphism D s d),
                                ms d = F _1 m o ms s)
    : Contr { m : morphism C c IsLimit_object
            | forall d, IsLimit_morphism d o m = ms d }
      := {| center := (IsLimit_property_morphism c ms ms_commutes;
                       IsLimit_property_morphism_property c ms ms_commutes);
            contr m' := path_sigma
                          _
                          (IsLimit_property_morphism c ms ms_commutes;
                           IsLimit_property_morphism_property c ms ms_commutes)
                          m'
                          (@IsLimit_property_morphism_unique c ms ms_commutes m'.1 m'.2)
                          (center _) |}.
  End elimination_abstraction_barrier.
End Limit.

Global Opaque
       IsLimit
       Build_IsLimit_curried
       Build_IsLimit_uncurried
       IsLimit_object
       IsLimit_morphism
       IsLimit_morphism_commutes
       IsLimit_property_morphism
       IsLimit_property_morphism_property
       IsLimit_property_morphism_unique
       IsLimit_property.
