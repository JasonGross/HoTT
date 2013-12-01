Require Import ProofIrrelevance.
Require Export Category Functor ProductCategory NaturalTransformation.
Require Import Common DecidableDiscreteCategory ComputableCategory DefinitionSimplification FEqualDep.

Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section LaxSliceCategory.
  (* [Definition]s are not sort-polymorphic. *)

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @Category (@Index2Object i).

  Local Coercion Index2Cat : I >-> Category.

  Let Cat := ComputableCategory Index2Object Index2Cat.

  Variable C : Category.

  (** Quoting David Spivak:
     David: ok
       so an object of [FC ⇓ D] is a pair [(X, G)], where [X] is a
       finite category (or a small category or whatever you wanted)
       and [G : X --> D] is a functor.
       a morphism in [FC ⇓ D] is a ``natural transformation diagram''
       (as opposed to a commutative diagram, in which the natural
       transformation would be ``identity'')
       so a map in [FC ⇓ D] from [(X, G)] to [(X', G')] is a pair
       [(F, α)] where [F : X --> X'] is a functor and
       [α : G --> G' ○ F] is a natural transformation
       and the punchline is that there is a functor
       [colim : FC ⇓ D --> D]
     David: consider for yourself the case where [F : X --> X'] is
       identity ([X = X']) and (separately) the case where
       [α : G --> G ○ F] is identity.
       the point is, you've already done the work to get this colim
       functor.
       because every map in [FC ⇓ D] can be written as a composition
       of two maps, one where the [F]-part is identity and one where
       the [α]-part is identity.
       and you've worked both of those cases out already.
       *)
  (* use a pair, so that it's easily interchangable with [SliceCategory] *)
  Record LaxSliceCategory_Object := { LaxSliceCategory_Object_Member :> { X : I * unit & Functor (fst X) C } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition LaxSliceCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_LaxSliceCategory_Object.
  Global Identity Coercion LaxSliceCategory_Object_Id : LaxSliceCategory_ObjectT >-> sigT.
  Definition Build_LaxSliceCategory_Object' (mem : LaxSliceCategory_ObjectT) := Build_LaxSliceCategory_Object mem.
  Global Coercion Build_LaxSliceCategory_Object' : LaxSliceCategory_ObjectT >-> LaxSliceCategory_Object.

  Record LaxSliceCategory_Morphism (XG X'G' : LaxSliceCategory_ObjectT) := { LaxSliceCategory_Morphism_Member :>
    { F : Functor (fst (projT1 XG)) (fst (projT1 X'G')) * unit &
      NaturalTransformation (projT2 XG) (ComposeFunctors (projT2 X'G') (fst F))
    }
  }.

  Definition LaxSliceCategory_MorphismT (XG X'G' : LaxSliceCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_LaxSliceCategory_Morphism XG X'G').
  Global Identity Coercion LaxSliceCategory_Morphism_Id : LaxSliceCategory_MorphismT >-> sigT.
  Definition Build_LaxSliceCategory_Morphism' XG X'G' (mem : @LaxSliceCategory_MorphismT XG X'G') :=
    @Build_LaxSliceCategory_Morphism _ _ mem.
  Global Coercion Build_LaxSliceCategory_Morphism' : LaxSliceCategory_MorphismT >-> LaxSliceCategory_Morphism.

  Global Arguments LaxSliceCategory_Object_Member _ : simpl nomatch.
  Global Arguments LaxSliceCategory_Morphism_Member _ _ _ : simpl nomatch.
  Global Arguments LaxSliceCategory_ObjectT /.
  Global Arguments LaxSliceCategory_MorphismT _ _ /.

  Definition LaxSliceCategory_Compose' s d d' (Fα : LaxSliceCategory_MorphismT d d') (F'α' : LaxSliceCategory_MorphismT s d) :
    LaxSliceCategory_MorphismT s d'.
    exists (ComposeFunctors (fst (projT1 Fα)) (fst (projT1 F'α')), tt).
    repeat match goal with
             | [ H : _ |- _ ] => unique_pose_with_body (fst (projT1 H))
             | [ H : _ |- _ ] => unique_pose_with_body (projT2 H)
           end; simpl in *.
    repeat match goal with
             | [ x : _, T : _ |- _ ] => unique_pose (NTComposeF T (IdentityNaturalTransformation x))
           end.
    match goal with
      | [ T0 : _, T1 : _ |- _ ] => eapply (NTComposeT _ (NTComposeT T0 T1))
    end.
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
      subst_body;
      intros; simpl;
      autorewrite with morphism;
      reflexivity
    ).
  Defined.

  Definition LaxSliceCategory_Compose'' s d d' (Fα : LaxSliceCategory_MorphismT d d') (F'α' : LaxSliceCategory_MorphismT s d) :
    LaxSliceCategory_MorphismT s d'.
    simpl_definition_by_tac_and_exact (@LaxSliceCategory_Compose' s d d' Fα F'α') ltac:(unfold LaxSliceCategory_Compose' in *).
  Defined.

  (* Then we clean up a bit with reduction. *)
  Definition LaxSliceCategory_Compose s d d' (Fα : LaxSliceCategory_MorphismT d d') (F'α' : LaxSliceCategory_MorphismT s d) :
    LaxSliceCategory_MorphismT s d'
    := Eval cbv beta iota zeta delta [LaxSliceCategory_Compose''] in (@LaxSliceCategory_Compose'' s d d' Fα F'α').

  Global Arguments LaxSliceCategory_Compose _ _ _ _ _ /.

  Definition LaxSliceCategory_Identity o : LaxSliceCategory_MorphismT o o.
    exists (IdentityFunctor _, tt).
    eapply (NTComposeT _ (IdentityNaturalTransformation _)).
    Grab Existential Variables.
    match goal with
      | [ C : _ |- NaturalTransformation ?F ?G ] =>
        refine (Build_NaturalTransformation F G
          (fun x => Identity (C := C) _)
          _
        )
    end.
    abstract (
        intros; simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Global Arguments LaxSliceCategory_Identity _ /.

  Local Ltac lax_slice_t :=
    repeat (
      let H := fresh in intro H; destruct H; simpl in * |-
    );
    unfold projT1, projT2;
      try unfold LaxSliceCategory_Compose at 1; try (symmetry; unfold LaxSliceCategory_Compose at 1);
        try apply f_equal (* slow; ~ 3s / goal *);
          simpl_eq (* slow; ~ 4s / goal *);
          nt_eq (* slow; ~ 2s / goal *); clear_refl_eq;
          repeat rewrite ComposeFunctorsAssociativity;
            repeat rewrite LeftIdentityFunctor; repeat rewrite RightIdentityFunctor;
              repeat rewrite FIdentityOf;
                repeat rewrite LeftIdentity; repeat rewrite RightIdentity;
                  repeat rewrite Associativity;
                    try reflexivity;
                    subst;
                    trivial.

  Lemma LaxSliceCategory_Associativity : forall (o1 o2 o3 o4 : LaxSliceCategory_ObjectT)
    (m1 : LaxSliceCategory_MorphismT o1 o2)
    (m2 : LaxSliceCategory_MorphismT o2 o3)
    (m3 : LaxSliceCategory_MorphismT o3 o4),
    LaxSliceCategory_Compose
    (LaxSliceCategory_Compose m3 m2) m1 =
    LaxSliceCategory_Compose m3
    (LaxSliceCategory_Compose m2 m1).
  Proof.
    repeat (let H := fresh in intro H; destruct H).
    simpl in * |- .
    unfold projT2, projT1.
    unfold LaxSliceCategory_Compose at 1.
    symmetry; unfold LaxSliceCategory_Compose at 1; symmetry.
    Set Printing All.
    apply id.
