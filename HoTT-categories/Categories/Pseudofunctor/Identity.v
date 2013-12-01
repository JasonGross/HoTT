Require Export Pseudofunctor.Core Cat.
Require Import Common.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section IdentityPseudofunctor.
  Print SubPreCat.
  (** There is an identity pseudo functor.  It does the obvious thing. *)
  Definition IdentityPseudofunctor `{Funext} P PH : Pseudofunctor (@SubPreCat _ P PH).
    refine (Build_Pseudofunctor (SubPreCat P)
                                (fun x => projT1 x)
                                (fun _ _ f => f)
                                (fun _ _ _ _ _ => idtoiso [_, _] idpath)
                                (fun _ => idtoiso [_, _] idpath)
                                _
                                _
                                _);
    nt_eq; simpl.
    rewrite ?FIdentityOf, ?LeftIdentity, ?RightIdentity, ?ap_idmap.

    Opaque Identity.
    expand.
    unfold idtoiso.
    unfold reflexivity.
    unfold isomorphic_refl.
    unfold ComposeFunctorsAssociativity.

    simpl.
    unfold ap; simpl.
    Focus 2.
    intros; expand.
    Local Transparent NTComposeT_Commutes GeneralizedIdentityNaturalTransformation_Commutes NTWhiskerR_Commutes NTWhiskerL_Commutes.
    unfold NTComposeT_Commutes, GeneralizedIdentityNaturalTransformation_Commutes, NTWhiskerR_Commutes, NTWhiskerL_Commutes.
    simpl.
    Local Transparent
    simpl.

  := Build_Pseudofunctor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End IdentityPseudofunctor.

(* I'm not sure how much I like this notation... *)
Notation "─" := (IdentityPseudofunctor _) : functor_scope.
