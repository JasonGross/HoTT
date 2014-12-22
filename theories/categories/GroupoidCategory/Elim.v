(** * Functors out of groupoids (the elimination rule for groupoids) *)
Require Import Category.Core Functor.Core.
Require Import Category.Morphisms.
Require Import Functor.Paths.
Require Import GroupoidCategory.Core.
Require Import HoTT.Basics.PathGroupoids HoTT.Basics.Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.

Section elim.
  (** A functor out of a groupoid is uniquely determined by its action
      on objects.  We use [rec] to mirror the HoTT naming conventions
      for the eliminator. *)
  Variable X : Type.
  Context `{IsTrunc 1 X}.
  Variable D : PreCategory.
  Variable object_of : X -> D.

  Definition groupoid_rec : Functor (groupoid_category X) D
    := Build_Functor
         (groupoid_category X) D
         object_of
         (fun s d m => idtoiso _ (ap object_of m))
         (fun _ _ _ _ _ =>
            (ap (@idtoiso _ _ _ : _ -> morphism _ _ _) (ap_pp object_of _ _))
              @ (idtoiso_comp _ _ _)^)
         (fun x => idpath).
End elim.

(** ** [groupoid_rec] is unique *)
Section uniqueness.
  Context `{Funext}.

  Variable X : Type.
  Context `{IsTrunc 1 X}.
  Variable D : PreCategory.

  Global Instance isequiv_object_of_groupoid : IsEquiv (@object_of (groupoid_category X) D).
  Proof.
    refine (isequiv_adjointify
                (@Functor.Core.object_of (groupoid_category X) D)
                (@groupoid_rec X _ D)
                (fun _ => 1%path)
                _).
    abstract (
        intro;
        path_functor;
        repeat (apply path_forall; intro);
        path_induction;
          by rewrite identity_of
      ).
  Defined.

  Global Instance isequiv_groupoid_rec : IsEquiv (@groupoid_rec X _ D)
    := isequiv_inverse (@object_of (groupoid_category X) D).
End uniqueness.
