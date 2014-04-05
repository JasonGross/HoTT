(** * PreCategories [set_cat] and [prop_cat] *)
Require Import Category.Core Category.Strict.
Require Import HProp HSet types.Universe UnivalenceImpliesFunext.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Notation cat_of obj :=
  (@Build_PreCategory obj
                      (fun x y => x -> y)
                      (fun _ x => x)
                      (fun _ _ _ f g => f o g)%core
                      (fun _ _ _ _ _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      (*(fun s d => @Arrow.trunc_arrow Funext_downward_closed _ _ _ _)*)).

(** There is a category [Set], where the objects are sets and the
    morphisms are set morphisms *)

Definition prop_cat `{Funext} : PreCategory := cat_of hProp.
Definition set_cat `{Funext} : PreCategory := cat_of Type (*hSet*).

(** ** [Prop] is a strict category *)
Instance isstrict_prop_cat `{Univalence}
: IsStrictCategory prop_cat
  := _.
