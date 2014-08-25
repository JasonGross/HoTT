Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Prod Functor.Prod.
Require Import FunctorCategory.Morphisms.
Require Import Functor.Composition.Core.
Require Import Functor.Identity.
Require Import ProductLaws.
Require Import InitialTerminalCategory.
Require ExponentialLaws.Law1.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation fst_type := Datatypes.fst.
Local Notation snd_type := Datatypes.snd.

Local Open Scope functor_scope.
Local Open Scope morphism_scope.

Section PreMonoidalPreCategory.
  (** TODO: Redefine [NaturalIsomorphism] so it doesn't need [Funext]. *)
  Context `{Funext}.
  (* It's too hard to implement it all inside a record, so first we
     define everything, then we put it in a record *)

  (** Quoting Wikipedia:
     A  monoidal category is a category [C] equipped with
     *)
  Variable C : PreCategory.
  (**
     - a bifunctor [ ⊗ : C × C -> C] called the tensor product or
         monoidal product,
    *)
  Variable tensor_product : Functor (C * C) C.

  Let src {s d} (_ : morphism C s d) := s.
  Let dst {s d} (_ : morphism C s d) := d.

  Local Notation "A ⊗ B" := (tensor_product (A%object, B%object)%core) (at level 40, left associativity).
  Local Notation "A ⊗m B" := (morphism_of tensor_product
                                          (s := (@src _ _ A, @src _ _ B))
                                          (d := (@dst _ _ A, @dst _ _ B))
                                          (A%morphism, B%morphism)) (at level 40, left associativity).

  Local Open Scope functor_scope.

  Definition tri_monoidal_product_L : Functor (C * C * C) C
    := tensor_product o (tensor_product, 1).
  Definition tri_monoidal_product_R : Functor (C * C * C) C
    :=  tensor_product o (1, tensor_product) o Associativity.inverse _ _ _.

  (**
     - an object [I] called the unit object or identity object,
   *)
  Variable unit_object : C.
  Let I := unit_object.
  (**
     - three natural isomorphisms subject to certain coherence
         conditions expressing the fact that the tensor operation
       + is associative: there is a natural isomorphism [α], called
           associator, with components [α_{A,B,C} : (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)],
    *)
  Variable associator : NaturalIsomorphism tri_monoidal_product_L tri_monoidal_product_R.
  Local Notation α := associator.
  (**
       + has [I] as left and right identity: there are two natural
           isomorphisms [λ] and [ρ], respectively called left and
           right unitor, with components
           [λ A : I ⊗ A ≅ A] and [ρ A : A ⊗ I ≅ A].
     *)
  Definition LeftUnitorFunctor : Functor C C.
  Proof.
    pose ((tensor_product o (!I, 1) o @ProductLaws.Law1.functor $(admit)$ _)).
    pose .
    refine {| object_of := (fun A => I ⊗ A);
      morphism_of := (fun s d (m : morphism C s d) => Identity (C := C) I ⊗m m)
    |}; subst_body;
    abstract (
      intros; simpl;
        etransitivity; try (apply FCompositionOf || apply FIdentityOf);
          f_equal;
          unfold ProductCategory; simpl;
            try rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Definition RightUnitorFunctor : Functor C C.
    clear tri_monoidal_product_L_morphism_of tri_monoidal_product_R_morphism_of
      tri_monoidal_product_L_morphism_of' tri_monoidal_product_R_morphism_of'
      tri_monoidal_product_L_morphism_of'' tri_monoidal_product_R_morphism_of''
      tri_monoidal_product_L_object_of tri_monoidal_product_R_object_of.
    refine {| object_of := (fun A => A ⊗ I);
      morphism_of := (fun s d (m : morphism C s d) => m ⊗m Identity (C := C) I)
    |}; subst_body;
    abstract (
      intros; simpl;
        etransitivity; try (apply FCompositionOf || apply FIdentityOf);
          f_equal;
          unfold ProductCategory; simpl;
            try rewrite RightIdentity;
              reflexivity
    ).
  Defined.

  Variable LeftUnitor : NaturalIsomorphism LeftUnitorFunctor (IdentityFunctor _).
  Variable RightUnitor : NaturalIsomorphism RightUnitorFunctor (IdentityFunctor _).
  Let λ := LeftUnitor.
  Let ρ := RightUnitor.

  (**
     The coherence conditions for these natural transformations are:
     - for all [A], [B], [C] and [D] in [C], the pentagon diagram
     [[
                           α_{A,B,C} ⊗ D                          α_{A,B⊗C,D}
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     commutes
     *)

  Section associatorCoherenceCondition.
    Variables a b c d : C.

    (* going from top-left *)
    Let associatorCoherenceConditionT0 : morphism C (((a ⊗ b) ⊗ c) ⊗ d) ((a ⊗ (b ⊗ c)) ⊗ d)
      := α (a, b, c) ⊗m Identity (C := C) d.
    Let associatorCoherenceConditionT1 : morphism C ((a ⊗ (b ⊗ c)) ⊗ d) (a ⊗ ((b ⊗ c) ⊗ d))
      := α (a, b ⊗ c, d).
    Let associatorCoherenceConditionT2 : morphism C (a ⊗ ((b ⊗ c) ⊗ d)) (a ⊗ (b ⊗ (c ⊗ d)))
      := Identity (C := C) a ⊗m α (b, c, d).
    Let associatorCoherenceConditionB0 : morphism C (((a ⊗ b) ⊗ c) ⊗ d) ((a ⊗ b) ⊗ (c ⊗ d))
      := α (a ⊗ b, c, d).
    Let associatorCoherenceConditionB1 : morphism C ((a ⊗ b) ⊗ (c ⊗ d)) (a ⊗ (b ⊗ (c ⊗ d)))
      := α (a, b, c ⊗ d).

    Definition associatorCoherenceCondition' :=
      Compose associatorCoherenceConditionT2 (Compose associatorCoherenceConditionT1 associatorCoherenceConditionT0)
      = Compose associatorCoherenceConditionB1 associatorCoherenceConditionB0.
  End associatorCoherenceCondition.

  Definition associatorCoherenceCondition := Eval unfold associatorCoherenceCondition' in
    forall a b c d : C, associatorCoherenceCondition' a b c d.

  (**
     - for all [A] and [B] in [C], the triangle diagram
     [[
                   α_{A,I,B}
     (A ⊗ I) ⊗ B -------------> A ⊗ (I ⊗ B)
         \                         /
           \                     /
             \                 /
       ρ_A ⊗ B \             / A ⊗ λ_B
                 \         /
                   \     /
                     ↘ ↙
                    A ⊗ B
     ]]
     commutes;
     *)
  Definition UnitorCoherenceCondition := forall A B : C,
    Compose ((Identity (C := C) A) ⊗m (λ B)) (α (A, I, B))
    = (ρ A) ⊗m (Identity (C := C) B).
End PreMonoidalCategory.

Section MonoidalCategory.
  (** Quoting Wikipedia:
     A  monoidal category is a category [C] equipped with
     - a bifunctor [ ⊗ : C × C -> C] called the tensor product or
         monoidal product,
     - an object [I] called the unit object or identity object,
     - three natural isomorphisms subject to certain coherence
         conditions expressing the fact that the tensor operation
       + is associative: there is a natural isomorphism [α], called
           associator, with components [α_{A,B,C} : (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)],
       + has [I] as left and right identity: there are two natural
           isomorphisms [λ] and [ρ], respectively called left and
           right unitor, with components
           [λ A : I ⊗ A ≅ A] and [ρ A : A ⊗ I ≅ A].
     The coherence conditions for these natural transformations are:
     - for all [A], [B], [C] and [D] in [C], the pentagon diagram
     [[
                           α_{A,B,C} ⊗ D                          α_{A,B⊗C,D}
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     commutes
     - for all [A] and [B] in [C], the triangle diagram
     [[
                   α_{A,I,B}
     (A ⊗ I) ⊗ B -------------> A ⊗ (I ⊗ B)
         \                         /
           \                     /
             \                 /
       ρ_A ⊗ B \             / A ⊗ λ_B
                 \         /
                   \     /
                     ↘ ↙
                    A ⊗ B
     ]]
     commutes;

     It follows from these three conditions that any such diagram
     (i.e. a diagram whose morphisms are built using [α], [λ], [ρ],
     identities and tensor product) commutes: this is Mac Lane's
     "coherence theorem".

     A strict monoidal category is one for which the natural
     isomorphisms α, λ and ρ are identities. Every monoidal category
     is monoidally equivalent to a strict monoidal category.
     *)
  Local Reserved Notation "'I'".
  Local Reserved Notation "'α'".
  Local Reserved Notation "'λ'".
  Local Reserved Notation "'ρ'".

  Let src (C : Category) {s d} (_ : morphism C s d) := s.
  Let dst (C : Category) s d (_ : morphism C s d) := d.

  Let associatorCoherenceCondition' := Eval unfold associatorCoherenceCondition in @associatorCoherenceCondition.
  Let UnitorCoherenceCondition' := Eval unfold UnitorCoherenceCondition in @UnitorCoherenceCondition.

  Record MonoidalCategory := {
    MonoidalUnderlyingCategory :> Category;
    tensor_product : Functor (MonoidalUnderlyingCategory * MonoidalUnderlyingCategory) MonoidalUnderlyingCategory
      where "A ⊗ B" := (tensor_product (A, B)) and "A ⊗m B" := (tensor_product _1 (s := (@src _ _ _ A, @src _ _ _ B)) (d := (@dst _ _ _ A, @dst _ _ _ B)) (A, B)%morphism);

    IdentityObject : MonoidalUnderlyingCategory where "'I'" := IdentityObject;

    associator : NaturalIsomorphism (tri_monoidal_product_L tensor_product) (tri_monoidal_product_R tensor_product) where "'α'" := associator;
    LeftUnitor : NaturalIsomorphism (LeftUnitorFunctor tensor_product I)  (IdentityFunctor _) where "'λ'" := LeftUnitor;
    RightUnitor : NaturalIsomorphism (RightUnitorFunctor tensor_product I) (IdentityFunctor _) where "'ρ'" := RightUnitor;

    (*
     [[
                           α_{A,B,C} ⊗ D                        α_{A,B,C} ⊗ D
       ((A ⊗ B) ⊗ C) ⊗ D -----------------> (A ⊗ (B ⊗ C)) ⊗ D -----------------> A ⊗ ((B ⊗ C) ⊗ D)
               |                                                                         |
               |                                                                         |
               | α_{A⊗B,C,D}                                                             | A ⊗ α_{B,C,D}
               |                                                                         |
               |                                                                         |
               V                                                                         V
       (A ⊗ B) ⊗ (C ⊗ D) ------------------------------------------------------> A ⊗ (B ⊗ (C ⊗ D))
                                           α_{A,B,C⊗D}
     ]]
     *)
    associatorCoherent : associatorCoherenceCondition' α;
    UnitorCoherent : UnitorCoherenceCondition' α λ ρ
  }.
End MonoidalCategory.
