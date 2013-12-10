Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import Functor.Composition.Functorial.
Require Import UniversalProperties KanExtensions.Core InitialTerminalCategory NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import Limits.Core.
Require Import Category.Morphisms.
Require Import Equivalences HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

Section Limit.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor D C.

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural
     transformation [t : Δ L -> F] such that for every object [X] of
     [C] and every natural transformation [s : Δ X -> F], there exists
     a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].  **)

  Local Open Scope morphism_scope.

  (*Definition Build_IsLimit_curried
    : forall A p' m H H', @IsLimit _
      := @Build_IsRightKanExtensionAlong_curried _ _ _ _ _ _.
  Definition typeof {T} (_ : T) := T.
  Arguments typeof / .
  Require Import NaturalTransformation.Composition.Core.
  Arguments compose / .
  Arguments whisker_l / .
  Unset Printing Records.
  Eval simpl in typeof Build_IsLimit_curried.*)

  Local Notation mk_nt :=
    (fun (A : C)
         (p' : forall d : D, morphism C A (F d))
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

  Section EliminationAbstractionBarrier.
    Context `(is_lim : @IsLimit _ C F G lim).,.

      Definition IsInitialMorphism_object (M : IsInitialMorphism Ap) : D
        := CommaCategory.b Ap.
      Definition IsInitialMorphism_morphism (M : IsInitialMorphism Ap)
      : morphism C X (U (IsInitialMorphism_object M))
        := CommaCategory.f Ap.
      Definition IsInitialMorphism_property_morphism (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : morphism D (IsInitialMorphism_object M) Y
        := CommaCategory.h
             (@center _ (M (CommaCategory.Build_object !X U tt Y f))).
      Definition IsInitialMorphism_property_morphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : (morphism_of U (IsInitialMorphism_property_morphism M Y f))
          o IsInitialMorphism_morphism M = f
        := concat
             (CommaCategory.p
                (@center _ (M (CommaCategory.Build_object !X U tt Y f))))
             (right_identity _ _ _ _).
      Definition IsInitialMorphism_property_morphism_unique
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
                 m'
                 (H : morphism_of U m' o IsInitialMorphism_morphism M = f)
      : IsInitialMorphism_property_morphism M Y f = m'
        := ap
             (@CommaCategory.h _ _ _ _ _ _ _)
             (@contr _
                     (M (CommaCategory.Build_object !X U tt Y f))
                     (CommaCategory.Build_morphism
                        Ap (CommaCategory.Build_object !X U tt Y f)
                        tt m' (H @ (right_identity _ _ _ _)^)%path)).
      Definition IsInitialMorphism_property
                 (M : IsInitialMorphism Ap)
                 (Y : D) (f : morphism C X (U Y))
      : Contr { m : morphism D (IsInitialMorphism_object M) Y
              | morphism_of U m o IsInitialMorphism_morphism M = f }
        := {| center := (IsInitialMorphism_property_morphism M Y f;
                         IsInitialMorphism_property_morphism_property M Y f);
              contr m' := path_sigma
                            _
                            (IsInitialMorphism_property_morphism M Y f;
                             IsInitialMorphism_property_morphism_property M Y f)
                            m'
                            (@IsInitialMorphism_property_morphism_unique M Y f m'.1 m'.2)
                            (center _) |}.


  Definition IsLimit
End Limit.

(** TODO(JasonGross): Port MorphismsBetweenLimits from catdb *)
