(** * Limits and Colimits *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import ExponentialLaws.Law1.Functors FunctorCategory.Core.
Require Import ExponentialLaws.Law1.Law.
Require Import Functor.Composition.Functorial.
Require Import UniversalProperties KanExtensions.Core.
Require Import InitialTerminalCategory.Core.
Require InitialTerminalCategory.Functors.
Import InitialTerminalCategory.Functors.InitialTerminalCategoryFunctorsNotations.
Require Import NatCategory.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Comma.Core.
Require Import HoTT.Basics.Equivalences HoTT.Types.Unit HoTT.Tactics HoTT.Types.Forall HoTT.Basics.PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

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

  (** We construct two versions.  In the first, we use [C¹] rather
      than [C] for judgemental compatibility with Kan extensions.  In
      the latter, we use [C] so that limits are judgmentally opposite
      colimits. *)

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

    Lemma diagonal_functor'_diagonal_functor X
    : diagonal_functor' X = diagonal_functor (!X).
    Proof.
      exact idpath.
    Qed.
  End convert.
End diagonal_functor.

Arguments diagonal_functor : simpl never.
Arguments diagonal_functor' : simpl never.

Section diagonal_functor_lemmas.
  Context `{Funext}.
  Variables C D D' : PreCategory.

  Lemma compose_diagonal_functor x (F : Functor D' D)
  : diagonal_functor C D x o F = diagonal_functor _ _ x.
  Proof.
    path_functor.
  Qed.

  Definition compose_diagonal_functor' x (F : Functor D' D)
  : diagonal_functor' C D x o F = diagonal_functor' _ _ x
    := compose_diagonal_functor (!x) F.

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

  Definition compose_diagonal_functor'_natural_transformation
             x (F : Functor D' D)
  : NaturalTransformation (diagonal_functor' C D x o F) (diagonal_functor' _ _ x)
    := compose_diagonal_functor_natural_transformation (!x) F.
End diagonal_functor_lemmas.

Hint Rewrite @compose_diagonal_functor : category.
Hint Rewrite @compose_diagonal_functor' : category.

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

  Definition IsLimit
    := @IsRightKanExtensionAlong _ D 1 C (Functors.to_terminal _) F.
  Definition IsLimit' := @IsTerminalMorphism (_ -> _) _ (diagonal_functor' C D) F.
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
  Definition IsColimit' := @IsInitialMorphism (_ -> _) _ F (diagonal_functor' C D).
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

Section equiv.
  (** We prove that the [C¹]-based and [C]-based definitions are
  equivalent. *)
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : object (D -> C).

  Local Transparent IsRightKanExtensionAlong IsLeftKanExtensionAlong.

  Definition colim'_of_colim (Ap : object (!F / pullback_along C (Functors.to_terminal D)))
  : object (!F / diagonal_functor' C D)
    := CommaCategory.Build_object
         !F (diagonal_functor' C D)
         (CommaCategory.a Ap)
         (CommaCategory.b Ap (center _))
         (Build_NaturalTransformation
            F
            ((diagonal_functor' C D) ((CommaCategory.b Ap) (center _)))
            (fun x => CommaCategory.f Ap x)
            (fun s d m =>
               ((commutes (CommaCategory.f Ap) s d m)
                  @ (ap (fun x => x o _)%morphism (identity_of _ _)))%path)).

  Definition colim_of_colim' (Ap : object (!F / diagonal_functor' C D))
  : object (!F / pullback_along C (Functors.to_terminal D))
    := CommaCategory.Build_object
         !F (pullback_along C (Functors.to_terminal D))
         (CommaCategory.a Ap)
         (!(CommaCategory.b Ap))
         (Build_NaturalTransformation
            F
            (pullback_along C (Functors.to_terminal D) !(CommaCategory.b Ap))
            (fun x => CommaCategory.f Ap x)
            (fun s d m =>
               ((commutes (CommaCategory.f Ap) s d m)
                  @ (ap (fun x => x o _)%morphism (identity_of _ _)))%path)).

  Lemma colim_of_colim'_of_colim_b_helper Ap
  : CommaCategory.b (colim_of_colim' (colim'_of_colim Ap)) = CommaCategory.b Ap.
  Proof.
    destruct Ap as [[] b ?]; simpl in *.
    path_functor; simpl.
    exists (path_forall _ _ (fun z => ap b (eta_unit z))).
    abstract (
        repeat (apply path_forall || intros []);
        rewrite !transport_forall_constant;
        transport_path_forall_hammer;
        simpl;
        symmetry; apply identity_of
      ).
  Defined.

  Global Instance isequiv_colim_of_colim' : IsEquiv colim_of_colim'.
  Proof.
    refine (isequiv_adjointify
              colim_of_colim' colim'_of_colim
              _
              _);
    abstract (
        intro Ap;
        pose Ap as Ap';
        destruct Ap as [[] ? ?];
        first [ apply CommaCategory.path_object' with (Ha := idpath : CommaCategory.a (colim_of_colim' (colim'_of_colim Ap')) = CommaCategory.a Ap')
                                                        (Hb := colim_of_colim'_of_colim_b_helper Ap')
              | apply CommaCategory.path_object' with (Ha := idpath : CommaCategory.a (colim'_of_colim (colim_of_colim' Ap')) = CommaCategory.a Ap')
                                                        (Hb := idpath) ];
        path_natural_transformation;
        try reflexivity;
        subst Ap';
        repeat match goal with
                 | _ => reflexivity
                 | _ => progress simpl in *
                 | _ => rewrite !transport_forall_constant
                 | _ => rewrite path_functor'_sig_fst
                 | [ |- appcontext[@components_of ?C ?D ?F ?G (transport ?P ?p ?x)] ]
                   => let x' := fresh in
                      set (x' := x);
                 simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @components_of _ _ _ _) x');
                 subst x'
                 | [ |- appcontext[transport (fun y => ?f (?g y ?z) ?x)] ]
                   => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y z) x) g)
                 | [ |- appcontext[transport (fun y => ?f ?x (?g y ?z))] ]
                   => rewrite (fun a b => @transport_compose _ _ a b (fun y => f x (y z)) g)
                 | _ => transport_path_forall_hammer
               end
      ).
  Defined.

  Definition iscolimit'_iscolimit Ap : @IsColimit _ _ _ F (colim_of_colim' Ap)  -> @IsColimit' _ _ _ F Ap.
  Proof.
    intro H'.
    unfold IsColimit, IsColimit', IsRightKanExtensionAlong in *.
    destruct Ap as [[] ? ?].
    unfold colim_of_colim' in H'; simpl in *.
    apply Build_IsInitialMorphism.
    intros A' p'.
    pose proof (IsInitialMorphism_property H' !A' p') as H''.
    simpl in *.
    Require Import Trunc.
    eapply (trunc_equiv'); [ | exact H'' ].
    SearchAbout Equiv sigT.




  Definition lim'_of_lim (Ap : object (pullback_along C (Functors.to_terminal D) / !F))
  : object (diagonal_functor' C D / !F)
    := CommaCategory.Build_object
              (diagonal_functor' C D) !F
              (CommaCategory.a Ap (center _))
              (CommaCategory.b Ap)
              (Build_NaturalTransformation
                 ((diagonal_functor' C D) ((CommaCategory.a Ap) (center _)))
                 F
                 (fun x => CommaCategory.f Ap x)
                 (fun s d m =>
                    ((ap (fun x => _ o x)%morphism (identity_of _ _)^)
                       @ (commutes (CommaCategory.f Ap) s d m))%path)).

  Definition lim_of_lim' (Ap : object (diagonal_functor' C D / !F))
  : object (pullback_along C (Functors.to_terminal D) / !F)
    := CommaCategory.Build_object
         (pullback_along C (Functors.to_terminal D)) !F
         (!(CommaCategory.a Ap))
         (CommaCategory.b Ap)
         (Build_NaturalTransformation
            (pullback_along C (Functors.to_terminal D) !(CommaCategory.a Ap))
            F
            (fun x => CommaCategory.f Ap x)
            (fun s d m =>
               ((ap (fun x => _ o x)%morphism (identity_of _ _))
                  @ (commutes (CommaCategory.f Ap) s d m))%path)).

  Lemma lim_of_lim'_of_lim_a_helper Ap
  : CommaCategory.a (lim_of_lim' (lim'_of_lim Ap)) = CommaCategory.a Ap.
  Proof.
    destruct Ap as [a [] ?]; simpl in *.
    path_functor; simpl.
    exists (path_forall _ _ (fun z => ap a (eta_unit z))).
    abstract (
        repeat (apply path_forall || intros []);
        rewrite !transport_forall_constant;
        transport_path_forall_hammer;
        simpl;
        symmetry; apply identity_of
      ).
  Defined.

  Global Instance isequiv_lim_of_lim' : IsEquiv lim_of_lim'.
  Proof.
    refine (isequiv_adjointify
              lim_of_lim' lim'_of_lim
              _
              _);
    abstract (
        intro Ap;
        pose Ap as Ap';
        destruct Ap as [? [] ?];
        first [ apply CommaCategory.path_object' with (Ha := lim_of_lim'_of_lim_a_helper Ap')
                                                        (Hb := idpath)
              | apply CommaCategory.path_object' with (Ha := idpath : CommaCategory.a (lim'_of_lim (lim_of_lim' Ap')) = CommaCategory.a Ap')
                                                        (Hb := idpath) ];
        path_natural_transformation;
        try reflexivity;
        subst Ap';
        repeat match goal with
                 | _ => reflexivity
                 | _ => progress simpl in *
                 | _ => rewrite !transport_forall_constant
                 | _ => rewrite path_functor'_sig_fst
                 | [ |- appcontext[@components_of ?C ?D ?F ?G (transport ?P ?p ?x)] ]
                   => let x' := fresh in
                      set (x' := x);
                 simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @components_of _ _ _ _) x');
                 subst x'
                 | [ |- appcontext[transport (fun y => ?f (?g y ?z) ?x)] ]
                   => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y z) x) g)
                 | _ => transport_path_forall_hammer
               end
      ).
  Defined.

  Definition islimit'_islimit Ap : @IsLimit _ _ _ F (lim_of_lim' Ap)  -> @IsLimit' _ _ _ F Ap.
  Proof.
    intro H'.
    unfold IsLimit, IsLimit', IsRightKanExtensionAlong in *.
    destruct Ap as [? [] ?].
    unfold lim_of_lim' in H'; simpl in *.

    hnf in *; simpl in *.
    intro x.
    exact H'.
    pose proof (fun q => @Build_IsTerminalMorphism_uncurried _ _ (diagonal_functor C D) F (a; (f; q))) as H''.
    simpl in *.
    apply H''.
    intros A' p'.

    Set Printing Implicit.


(** TODO(JasonGross): Port MorphismsBetweenLimits from catdb *)
