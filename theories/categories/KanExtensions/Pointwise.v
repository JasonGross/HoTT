Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import ExponentialLaws.Law4.Functors FunctorCategory.Core.
Require Import Functor.Composition.Functorial Functor.Composition.Core.
Require Import UniversalProperties.
Require Import Limits.Core.
Require Import Limits.Functors.
Require Import KanExtensions.Core.
Require Import Comma.ProjectionFunctors Comma.Projection Comma.InducedFunctors Comma.Core.
Require Import InitialTerminalCategory NatCategory.
Require ExponentialLaws.Law1.Functors.
Require Import Cat.Core.
Require Import types.Unit.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

(** Quoting nCatLab on Kan Extensions:

    ** in terms of conical (co)limits

    In the case of functors between ordinary locally small categories,
    hence in the special case of [V]-enriched category theory for [V =
    Set], there is an expression of a weighted (co)limit and hence a
    pointwise Kan extension as an ordinary (“conical”, meaning: in
    terms of cones) (co)limit over a comma category:

    Proposition. Let

      - [C] be a small category;

      - [D] have all small limits.

      Then the right Kan extension of a functor [F : C → D] of locally
      small categories along a functor [p : C → C'] exists and its
      value on an object [c' ∈ C'] is given by the limit

      [(Ran_p F)(c') ≃ lim((Δ_{c'} / p) → C ─{F}─→ D)],

      where

      - [Δ_{c'} / p] is the comma category;

      - [Δ_{c'} / p → C] is the canonical forgetful functor.

      Likewise, if [D] admits small colimits, the left Kan extension
      of a functor exists and is pointwise given by the colimit

      [(Lan_p F)(c') ≃ colim((p / Δ_{c'}) → C ─{F}─→ D)].

      This appears for instance as (Borceux, I, thm 3.7.2). Discussion
      in the context of enriched category theory is in (Kelly, section
      3.4).

      A cartoon picture of the forgetful functor out of the comma
      category [p / Δ_{c'} → C], useful to keep in mind, is

<<
      ⎛          p(ϕ)           ⎞
      ⎜ p(c₁) ----------> p(c₂) ⎟
      ⎜    \                /   ⎟        ⎛    ϕ     ⎞
      ⎜       \          /      ⎟ |----> ⎜c₁ ---> c₂⎟
      ⎜          ↘    ↙         ⎟        ⎝          ⎠
      ⎜            c'           ⎟
      ⎝                         ⎠
>>

      The comma category here is equivalently the category of elements
      of the functor [C'(p(−), c') : Cᵒᵖ → Set]

      [(p / Δ_{c'}) ≃ el(C'(p(−), c'))].
*)
(*
      Proof. Consider the case of the left Kan extension, the other
      case works analogously, but dually.

      First notice that the above pointwise definition of values of a
      functor canonically extends to an actual functor:

      for [ϕ : c'1→c'2 any morphism in C' we get a functor

ϕ∗:p/Δc'1→p/Δc'2
of comma categories, by postcomposition. This morphism of diagrams induces canonically a corresponding morphism of colimits

(LanpF)(c'1)→(LanpF)(c'2).
Now for the universal property of the functor LanpF defined this way. For c'∈C' denote the components of the colimiting cocone (LanpF)(c'):=lim→(p/Δc'→C−→FD) by s(−), as in

(p(c1)−→ϕc')F(c1)sϕ↘−→−−−−−−−p(h)−→−−−−−−−F(h)(LanpF)(c')↙sλ(p(c2)−→λc')F(c2).
We now construct in components a natural transformation

ηF:F→p∗LanpF
for LanpF defined as above, and show that it satisfies the required universal property. The components of ηF over c∈C are morphisms

ηF(c):F(c)→(LanpF)(p(c)).
Take these to be given by

ηF(c):=sIdp(c)
(this is similar to what happens in the proof of the Yoneda lemma, all of these arguments are variants of the argument for the Yoneda lemma, and vice versa). It is straightforward, if somewhat tedious, to check that these are natural, and that the natural transformation defined this way has the required universal property.  ▮ *)

Section pointwise.
  Context `{Funext}.
  Variable C  : PreCategory.
  Variable C' : PreCategory.
  Variable D  : PreCategory.

  Variable p : object (C -> C'). (* C -> D *)
  Variable F : object (C -> D). (* C -> Set *)

  (** From http://arxiv.org/pdf/1009.1166v1.pdf, David Spivak's
      "Functorial Data Migration", Definitions 2.1.1 and 2.1.2, we are
      actually interested in [c' / p]. *)

  Local Notation forgetful_functor c' :=
    (coslice_category_projection (c' : C') p
     : Functor (!c' / p) C).

  Require Import Category.Dual Category.Prod.

  Variable P : PreCategory -> Type.
  Hypothesis HF : forall C D, P C -> P D -> IsHSet (Functor C D).
  Hypothesis PC1 : P (C * 1).
  Hypothesis PC : P C.
  Hypothesis PD : P D.
  Hypothesis P_comma : forall (S : Functor C C') (T : Functor 1 C'), P (S / T).

  Local Notation Cat := (@sub_pre_cat _ P HF).

  Let forgetful_functor_composed_F
    := (((@cat_over_induced_functor _ P HF (C; PC) (D; PD) F)
           o (@coslice_category_projection_functor _ P HF C C' PC1 PC P_comma p))
        : Functor C' (Cat / ((D; PD) : Cat))).

  (*Context `(has_limits : forall c', @IsLimit _ _ _
                                             (F o forgetful_functor c')
                                             (limit_objects c')).*)

  (* TODO: We want Cat / D, not (!c' / p -> D), and we want to take coslice_category_projection to be a functor from C' to Cat / C, and then compose with composition with F, to get to Cat / D *)
  Context `(has_limits : forall c' (F : Functor (!c' / p) D), @IsLimit _ _ _
                                                                       F
                                                                       (limit_objects c' F)).

  Definition right_kan_extension_object
  : object (pullback_along D p / !F).
    simpl in *.
    let build := match goal with
                   | [ |- @CommaCategory.object ?A ?B ?C ?S ?T ]
                     => constr:(@CommaCategory.Build_object A B C S T)
                 end in
    refine ((fun G : Functor C' D => build G tt _) _);
    simpl.
    Focus 2.
    refine (_ o forgetful_functor_composed_F).


    pose proof (fun c' => Law1.Functors.functor _ o limit_functor (@has_limits c'))%functor.
    pose .
    pose proof (fun c' => CommaCategory.a (limit_objects c')).
    pose proof (fun c' => CommaCategory.b (limit_objects c')).
    pose proof (fun c' => components_of (CommaCategory.f (limit_objects c'))).
    simpl in *.

    pose (limit_functor (@has_limits c')).
4                        (fun c' : Functor 1 C' => @limit_objects (c' tt))
                         (fun c' : Functor 1 C' => @has_limits (c' tt))).
      Check limit_functor has_limits.


    match goal with |- NaturalTransformation ?F ?G => assert (forall x, morphism _ (F x) (G x)) end.
    simpl.



    Print CommaCategory.object.
    assert (object (pullback_along D p)).

  simpl.
Co.CommaCategory.object (pullback_along D p)
        (InitialTerminalCategory.Functors.from_terminal (C -> D) F).
  pose (@IsRightKanExtensionAlong _ _ _ _ p F).
  simpl in *.



  Variable limit (d / p)

  Hypothesis Haforall (F : Functor C D) d (F' : Functor (d ↓ F) S), Limit F'.

  Goal True.
  Section pullback_along.
    Definition pullback_along_functor
    : object ((C -> C') -> (C' -> D) -> (C -> D))
      := Functor.Composition.Functorial.compose_functor _ _ _.

    Definition pullback_along (p : Functor C C')
    : object ((C' -> D) -> (C -> D))
      := Eval hnf in pullback_along_functor p.
  End pullback_along.

  (** Definition. If [p*] has a left adjoint, typically denoted [p_! :
      (C → D) → (C' → D)] or [Lan_p : (C → D) → (C' → D)] then this
      left adjoint is called the (ordinary or weak) left Kan extension
      operation along [p]. For [h ∈ (C -> D)] we call [p_! h] the left
      Kan extension of [h] along [p].

      Similarly, if [p*] has a right adjoint, this right adjoint is
      called the right Kan extension operation along [p]. It is
      typically denoted [p_* : (C → D) → (C' → D)] or [Ran = Ran_p :
      (C → D) → (C' → D)].

      The analogous definition clearly makes sense as stated in other
      contexts, such as in enriched category theory.

      Observation. If [C' = 1] is the terminal category, then

      - the left Kan extension operation forms the colimit of a functor;

      - the right Kan extension operation forms the limit of a functor. *)

  (** Colimits are initial morphisms. *)
  Definition IsLeftKanExtensionAlong (p : Functor C C') (h : Functor C D)
    := @IsInitialMorphism (_ -> _) _ h (pullback_along p).

  (** Limits are terminal morphisms *)
  Definition IsRightKanExtensionAlong (p : Functor C C') (h : Functor C D)
    := @IsTerminalMorphism _ (_ -> _) (pullback_along p) h.
End kan_extensions.
