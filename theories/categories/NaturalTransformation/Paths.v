Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Equivalences types.Sigma Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section path_natural_transformation.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Local Open Scope equiv_scope.

  Lemma equiv_sig_natural_transformation
  : { CO : forall x, morphism D (F x) (G x)
    | forall s d (m : morphism C s d),
        CO d o F _1 m = G _1 m o CO s }
      <~> NaturalTransformation F G.
  Proof.
    let build := constr:(@Build_NaturalTransformation _ _ F G) in
    let pr1 := constr:(@components_of _ _ F G) in
    let pr2 := constr:(@commutes _ _ F G) in
    apply (equiv_adjointify (fun u => build u.1 u.2)
                            (fun v => (pr1 v; pr2 v)));
      hnf;
      [ intros []; intros; simpl; expand; f_ap; exact (center _)
      | intros; apply eta_sigma ].
  Defined.

  Global Instance trunc_natural_transformation n `{forall x y, IsTrunc n (morphism D x y)}
  : IsTrunc n (NaturalTransformation F G).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_natural_transformation | ].
    typeclasses eauto.
  Qed.

  Section path.
    Context `{forall s d, IsHSet (morphism D s d)}.
    Variables T U : NaturalTransformation F G.

    Lemma path'_natural_transformation
    : components_of T = components_of U
      -> T = U.
    Proof.
      intros.
      destruct T, U; simpl in *.
      path_induction.
      f_ap;
        refine (center _).
    Qed.

    Lemma path_natural_transformation
    : components_of T == components_of U
      -> T = U.
    Proof.
      intros.
      apply path'_natural_transformation.
      apply path_forall; assumption.
    Qed.

    Let path_inv
    : T = U -> components_of T == components_of U
      := (fun H _ => match H with idpath => idpath end).

    Lemma eisretr_path_natural_transformation
    : Sect path_natural_transformation path_inv.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eissect_path_natural_transformation
    : Sect path_inv path_natural_transformation.
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma eisadj_path_natural_transformation
    : forall x,
        @eisretr_path_natural_transformation (path_inv x)
        = ap path_inv (eissect_path_natural_transformation x).
    Proof.
      repeat intro.
      refine (center _).
    Qed.

    Lemma equiv_path_natural_transformation
    : T = U <~> (components_of T == components_of U).
    Proof.
      econstructor. econstructor. exact eisadj_path_natural_transformation.
    Defined.
  End path.
End path_natural_transformation.

Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
           | _ => typeclasses eauto
         end.
