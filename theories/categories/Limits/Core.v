(** * Limits and Colimits *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import UniversalProperties KanExtensions.Core InitialTerminalCategory.Core NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import Category.Morphisms.
Require Import Equivalences HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.
Local Open Scope category_scope.

(** ** The diagonal or "constant diagram" functor Δ *)
Section diagonal_functor.
  Context `{Funext}.
  Variables C D : PreCategory.

  (**
     Quoting Dwyer and Spalinski:

     There is a diagonal or ``constant diagram'' functor

<<
     Δ : C → Cᴰ,
>>

     which carries an object [X : C] to the constant functor [Δ X : D
     -> C] (by definition, this ``constant functor'' sends each object
     of [D] to [X] and each morphism of [D] to [Identity X]). The
     functor Δ assigns to each morphism [f : X -> X'] of [C] the
     constant natural transformation [t(f) : Δ X -> Δ X'] determined
     by the formula [t(f) d = f] for each object [d] of [D].  **)

  (** We use [C¹] rather than [C] for judgemental compatibility with
      Kan extensions. *)

  Definition diagonal_functor : Functor (1 -> C) (D -> C)
    := @pullback_along _ D 1 C (Functors.to_terminal _).

  Definition diagonal_functor' : Functor C (D -> C)
    := diagonal_functor o ExponentialLaws.Law1.Functors.inverse _.

  Section convert.
    Lemma diagonal_functor_diagonal_functor' X
    : diagonal_functor X = diagonal_functor' (X (center _)).
    Proof.
      path_functor.
      simpl.
      repeat (apply path_forall || intro).
      apply identity_of.
    Qed.
  End convert.
End diagonal_functor.

Arguments diagonal_functor : simpl never.

Section diagonal_functor_lemmas.
  Context `{Funext}.
  Variables C D D' : PreCategory.

  Lemma compose_diagonal_functor x (F : Functor D' D)
  : diagonal_functor C D x o F = diagonal_functor _ _ x.
  Proof.
    path_functor.
  Qed.

  Definition compose_diagonal_functor_natural_transformation
             x (F : Functor D' D)
  : NaturalTransformation (diagonal_functor C D x o F) (diagonal_functor _ _ x)
    := Build_NaturalTransformation
         (diagonal_functor C D x o F)
         (diagonal_functor _ _ x)
         (fun z => identity _)
         (fun _ _ _ => transitivity
                         (left_identity _ _ _ _)
                         (symmetry
                            _ _
                            (right_identity _ _ _ _))).
End diagonal_functor_lemmas.

Hint Rewrite @compose_diagonal_functor : category.

Section Limit.
  Context `{Funext}.
  Variables C D : PreCategory.
  Variable F : Functor D C.

  (** ** Definition of Limit *)
  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A limit
     for [F] is an object [L] of [C] together with a natural
     transformation [t : Δ L -> F] such that for every object [X] of
     [C] and every natural transformation [s : Δ X -> F], there exists
     a unique map [s' : X -> L] in [C] such that [t (Δ s') = s].  **)

  Local Open Scope morphism_scope.

  Definition IsLimit
    := @IsRightKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.

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
  Definition Build_IsLimit_curried
  : forall (mk_nt := (fun (A : C)
                          (p' : forall d : D, morphism C A (F d))
                          (p'_commutes : forall s d (m : morphism D s d),
                                           p' d = F _1 m o p' s)
                      => Build_NaturalTransformation
                           ((pullback_along C (Functors.to_terminal D)) !A)
                           F
                           p'
                           (fun _ _ _ =>
                              right_identity _ _ _ _ @ p'_commutes _ _ _)%path))
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
        (CommaCategory.Build_object
           (pullback_along C (Functors.to_terminal D)) !(F : object (_ -> _))
           !A (center _) (mk_nt A p' p'_commutes)).
  Proof.
    intros.
    eapply (@Build_IsRightKanExtensionAlong_curried
              _ _ _ _ _ _
              !A
              (mk_nt A p' p'_commutes)
              (fun A' p'' =>
                 Build_NaturalTransformation
                   A' !A
                   (fun c =>
                      m (A' c)
                        (fun c => components_of p'' c o A' _1 (idtoiso _ (contr _)^)%path)
                        (fun s d m => _))
                   _));
      simpl;
      intros;
      path_natural_transformation; simpl;
      [ rewrite_hyp
      | apply_hyp; intros; rewrite_rev_hyp ];
      simpl;
      rewrite !identity_of, ?right_identity, ?left_identity;
      reflexivity.
    Grab Existential Variables.
    - intros [] [] []; simpl.
      rewrite left_identity.
      etransitivity;
        [ apply ap | ].
      apply identity_of.
      rewrite right_identity.
      simpl.
      apply ap.
      repeat (apply path_forall; intro).
      reflexivity.
    match goal with |- appcontext[contr ?c] => destruct (contr c) end.
    simpl in *.
    try_associativity_quick simpl rewrite <- (commutes p'').
    rewrite ?identity_of, ?left_identity, ?right_identity.
    reflexivity.
  Defined.


    rewrite right_identity.

    reflexivity
    rewrite <- commutes.
    simpl.
    intros [] [] []; simpl.
      first [ reflexivity
            | apply right_identity
            | apply left_identity ].
    simpl.
    intros.
    intros.
    rewrite <- X.
    simpl.
    destruct x.
    simpl.
    rewrite
    subst mk_nt; simpl in *.
    pose (H1 (A' x)).
    apply p.
    erewrite H1.

 rewrite left_identity.

    pose (fun A' p'' =>
                              idpath)).
/
        := @Build_IsRightKanExtensionAlong_curried _ _ _ _ _ _.

    Definition Build_IsRightKanExtensionAlong_uncurried
    : forall univ, @IsRightKanExtensionAlong _
      := @Build_IsTerminalMorphism_uncurried _ (_ -> _) _ _.


  (*Definition IsLimit' := @IsTerminalMorphism (_ -> _) (_ -> _) (diagonal_functor C D) F.*)
  (*  Definition Limit (L : C) :=
    { t : SmallNaturalTransformation ((diagonal_functor C D) L) F &
      forall X : C, forall s : SmallNaturalTransformation ((diagonal_functor C D) X) F,
        { s' : C.(Morphism) X L |
          unique
          (fun s' => SNTComposeT t ((diagonal_functor C D).(MorphismOf) s') = s)
          s'
        }
    }.*)

  (**
     Quoting Dwyer and Spalinski:

     Let [D] be a small category and [F : D -> C] a functor. A colimit
     for [F] is an object [c] of [C] together with a natural
     transformation [t : F -> Δ c] such that for every object [X] of
     [C] and every natural transformation [s : F -> Δ X], there exists
     a unique map [s' : c -> X] in [C] such that [(Δ s') t = s].  **)

  (** ** Definition of Colimit *)
  Definition IsColimit
    := @IsLeftKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  (*Definition IsColimit' := @IsInitialMorphism (_ -> _) (_ -> _) F (diagonal_functor C D).*)
  (*  Definition Colimit (c : C) :=
    { t : SmallNaturalTransformation F ((diagonal_functor C D) c) &
      forall X : C, forall s : SmallNaturalTransformation F ((diagonal_functor C D) X),
        { s' : C.(Morphism) c X | is_unique s' /\
          SNTComposeT ((diagonal_functor C D).(MorphismOf) s') t = s
        }
    }.*)
  (** TODO(JasonGross): Figure out how to get good introduction and elimination rules working, which don't mention spurious identities. *)
  (*Section AbstractionBarrier.
    Section Limit.
      Set Printing  Implicit.
      Section IntroductionAbstractionBarrier.
        Local Open Scope morphism_scope.

        Definition Build_IsLimit
                 (lim_obj : C)
                 (lim_mor : morphism (D -> C)
                                     (diagonal_functor' C D lim_obj)
                                     F)
                 (lim := CommaCategory.Build_object
                           (diagonal_functor C D)
                           !(F : object (_ -> _))
                           !lim_obj
                           (center _)
                           lim_mor)
                 (UniversalProperty
                  : forall (lim_obj' : C)
                           (lim_mor' : morphism (D -> C)
                                                (diagonal_functor' C D lim_obj')
                                                F),
                      Contr { m : morphism C lim_obj' lim_obj
                            | lim_mor o morphism_of (diagonal_functor' C D) m = lim_mor' })
        : IsTerminalMorphism lim.
        Proof.
          apply Build_IsTerminalMorphism.
          intros A' p'.
          specialize (UniversalProperty (A' (center _))).*)
End Limit.

(** TODO(JasonGross): Port MorphismsBetweenLimits from catdb *)
