(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "HoTT" "-top" "Univalent") -*- *)
(* File reduced by coq-bug-finder from original input, then from 415 lines to 290 lines *)
(* coqc version 8.5 (January 2016) compiled on Jan 23 2016 16:15:22 with OCaml 4.01.0
   coqtop version 8.5 (January 2016) *)
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
End AdmitTactic.
Require HoTT.Basics.Overture.
Require HoTT.Basics.PathGroupoids.
Require HoTT.Basics.Equivalences.
Require HoTT.Basics.Contractible.
Require HoTT.Basics.Trunc.
Require HoTT.Basics.Notations.
Require HoTT.Basics.UniverseLevel.
Require HoTT.Basics.FunextVarieties.
Require HoTT.Basics.Decidable.
Require HoTT.Basics.
Require HoTT.Types.Unit.
Require HoTT.categories.Category.Core.
Require HoTT.Types.Empty.
Require HoTT.Types.Prod.
Require HoTT.Types.Paths.
Require HoTT.Types.Forall.
Require HoTT.Types.Arrow.
Require HoTT.Types.Sigma.
Require HoTT.categories.Functor.Core.
Require HoTT.categories.Category.Sigma.Core.
Require HoTT.Types.Record.
Require HoTT.Types.Equiv.
Require HoTT.Types.Universe.
Require HoTT.Types.Bool.
Require HoTT.Types.Wtype.
Require HoTT.Types.Sum.
Require HoTT.Types.
Require HoTT.HProp.
Require HoTT.Tactics.EvalIn.
Require HoTT.Tactics.BinderApply.
Require HoTT.Tactics.
Require HoTT.categories.Functor.Paths.
Require HoTT.categories.Functor.Composition.Core.
Require HoTT.categories.Functor.Identity.
Require HoTT.HSet.
Require HoTT.categories.Category.Sigma.OnMorphisms.
Require HoTT.categories.Category.Morphisms.
Require HoTT.categories.Category.Univalent.
Require HoTT.categories.Category.Sigma.OnObjects.
Import HoTT.categories.Category.Core.
Import HoTT.categories.Category.Morphisms.
Import HoTT.categories.Category.Univalent.
Import HoTT.categories.Category.Sigma.Core.
Import HoTT.categories.Category.Sigma.OnObjects.
Import HoTT.categories.Category.Sigma.OnMorphisms.
Import HoTT.Types.Sigma.
Import HoTT.Basics.Equivalences.
Import HoTT.Basics.Trunc.
Import HoTT.Basics.PathGroupoids.
Import HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation pr1_type := Overture.pr1 (only parsing).

Local Open Scope path_scope.
Local Open Scope morphism_scope.

Local Open Scope function_scope.




Section onobjects.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Global Instance iscategory_sigT_obj `{forall a, IsHProp (Pobj a), A_cat : IsCategory A}
  : IsCategory (sigT_obj A Pobj).
admit.
Defined.


End onobjects.


Section onmorphisms.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := { m : _ | Pmor s d m }%type.
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Local Notation A' := (@sigT_mor A Pmor HPmor Pidentity Pcompose P_associativity P_left_identity P_right_identity).


  Context `{forall s d m, IsIsomorphism m -> Contr (Pmor s d m)}.

  Definition iscategory_sigT_mor_helper {s d}
  : @Isomorphic A' s d -> @Isomorphic A s d.
admit.
Defined.

  Local Instance isequiv_iscategory_sigT_mor_helper s d
  : IsEquiv (@iscategory_sigT_mor_helper s d).
admit.
Defined.

  Global Instance iscategory_sigT_mor `{A_cat : IsCategory A}
  : IsCategory A'.
admit.
Defined.

  Definition iscategory_from_sigT_mor `{A'_cat : IsCategory A'}
  : IsCategory A.
admit.
Defined.

  Global Instance isequiv_iscategory_sigT_mor `{Funext}
  : IsEquiv (@iscategory_sigT_mor).
admit.
Defined.
End onmorphisms.


Section on_both.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := { x : _ | Pobj x }%type (only parsing).

  Variable Pmor : forall s d : obj, morphism A s.1 d.1 -> Type.

  Local Notation mor s d := { m : _ | Pmor s d m }%type (only parsing).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x.1; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Local Notation A' := (@sigT A Pobj Pmor HPmor Pidentity Pcompose P_associativity P_left_identity P_right_identity).


  Local Definition Pmor_iso_T s d m m' left right :=
    ({ e : Pmor s d m
     | { e' : Pmor d s m'
       | { _ : transport (Pmor _ _) ((left : m' o m = 1)%morphism) (Pcompose e' e) = Pidentity _
         | transport (Pmor _ _) ((right : m o m' = 1)%morphism) (Pcompose e e') = Pidentity _ } } }).

  Global Arguments Pmor_iso_T / .

  Local Definition Pmor_iso_T' x (xp xp' : Pobj x)
    := { e : Pmor (x; xp) (x; xp') 1
       | { e' : Pmor (x; xp') (x; xp) 1
         | { _ : Pcompose e' e = Pcompose (Pidentity _) (Pidentity _)
           | Pcompose e e' = Pcompose (Pidentity _) (Pidentity _) } } }.

  Global Arguments Pmor_iso_T' / .

  Local Definition Pidtoiso x (xp xp' : Pobj x) (H : xp = xp')
  : Pmor_iso_T' xp xp'.
admit.
Defined.

  Global Arguments Pidtoiso / .


  Local Instance ishset_pmor {s d m} : IsHSet (Pmor s d m).
admit.
Defined.

  Local Definition Pmor_iso_adjust x xp xp'
  : (Pmor_iso_T (x; xp) (x; xp') 1 1 (left_identity _ _ _ _) (right_identity _ _ _ _))
      <~> Pmor_iso_T' xp xp'.
admit.
Defined.

  Global Arguments Pmor_iso_adjust / .

  Local Definition iso_A'_code {s d}
  : (@Isomorphic A' s d)
    -> { e : @Isomorphic A s.1 d.1
       | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }.
  Proof.
    intro e.
    refine (_; _).
    Unshelve.
    all: try solve [ exists (e : morphism _ _ _).1;
                            exists (e^-1%morphism).1;
                            [ exact (@left_inverse _ _ _ e e)..1
                            | exact (@right_inverse _ _ _ e e)..1 ] ].
    {
 exists (e : morphism _ _ _).2.
      exists (e^-1%morphism).2; cbn.
      exists (((@left_inverse _ _ _ e e))..2).
      exact (@right_inverse _ _ _ e e)..2.
}
  Defined.

  Local Definition iso_A'_decode_helper {s d}
        (e : { e : @Isomorphic A s.1 d.1
             | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse })
  : @IsIsomorphism A' _ _ (e.1:morphism A s.1 d.1; (e.2).1).
admit.
Defined.

  Local Definition iso_A'_decode {s d}
  : { e : @Isomorphic A s.1 d.1
    | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }
    -> (@Isomorphic A' s d).
  Proof.
    intro e.
    eexists.
Unshelve.
    2:exact (e.1 : morphism _ _ _; e.2.1).
    apply iso_A'_decode_helper.
  Defined.

  Local Definition equiv_iso_A'_eisretr_helper {s d}
        (x : {e : @Isomorphic A s.1 d.1
             | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }%type)
  : transport
      (fun e : @Isomorphic A s.1 d.1 =>
         Pmor_iso_T s d e e^-1 left_inverse right_inverse)
      (path_isomorphic (iso_A'_code (iso_A'_decode x)).1 x.1 1)
      (iso_A'_code (iso_A'_decode x)).2 = x.2.
admit.
Defined.

  Local Definition equiv_iso_A' {s d}
  : (@Isomorphic A' s d)
      <~> { e : @Isomorphic A s.1 d.1
          | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }.
admit.
Defined.

  Local Arguments Pmor_iso_T : simpl never.

  Global Instance iscategory_sigT `{A_cat : IsCategory A}
  : IsCategory A'.
  Proof.
    intros s d.
    Time simple refine (isequiv_homotopic
              ((equiv_iso_A'^-1)
                 o (functor_sigma _ _)
                 o (path_sigma_uncurried _ _ _)^-1)
              _); [ | | | | | ].
    all: cbv beta.
    Time all: try exact _.
    Undo.
    Time 5: try exact _.
    Undo.
    Focus 5.
    Timeout 4 try exact _.
