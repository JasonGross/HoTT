Require Import Category.Core Functor.Core Category.Univalent Category.Morphisms.

Goal forall C D (F : Functor C D) `{IsCategory C, IsCategory D}
            (s d : C) (e : Isomorphic s d),
       ap (object_of F) (isotoid C s d e)
       = isotoid D (F s) (F d) {| morphism_isomorphic := F _1 e |}.
  intros.
  rewrite <- (eisretr (idtoiso C (x := s) (y := d)) e).
  generalize ((isotoid C s d) e).
  intro p; clear e.
  destruct p.
  simpl.
Admitted.

Lemma isotoid_1 {C} `{IsCategory C} {x : C} (H : IsIsomorphism (identity x))
: isotoid C x x {| morphism_isomorphic := (identity x) |}
  = idpath.
Proof.
  refine (ap _ _ @ eissect (idtoiso C (x := x) (y := x)) idpath).
  apply path_isomorphic; reflexivity.
Defined.

Lemma ap_functor_isotoid {C D} `{IsCategory C, IsCategory D} (F : Functor C D) {s d : C} (e : Isomorphic s d)
: ap F (isotoid C s d e) = isotoid D _ _ {| morphism_isomorphic := F _1 e |}.
Proof.
  pattern e.
  refine (transport _ (eisretr (idtoiso C (x := s) (y := d)) e) _).
  generalize (isotoid C s d e); clear e; intro e.
  refine (ap (ap F) (eissect (idtoiso C (x := s) (y := d)) e) @ _).
  destruct e; simpl.
  refine ((isotoid_1 _)^ @ ap (isotoid D (F s) (F s)) _).
  apply path_isomorphic.
  exact (identity_of F _)^.
Defined.

(** * Grothendieck Construction of a functor to Set *)
Require Import Category.Core Functor.Core.
Require Import Category.Univalent.
Require Import Category.Morphisms.
Require Import SetCategory.Core.
Require Import Grothendieck.ToSet.
Require Import SetCategory.Morphisms.
Require Import Basics.Trunc HSet Types.Sigma TruncType UnivalenceImpliesFunext Types.Universe Basics.Equivalences Basics.PathGroupoids HoTT.Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.




Section Grothendieck.
  Context `{Univalence}.

  Variable C : PreCategory.
  Context `{IsCategory C}.
  Variable F : Functor C set_cat.

  Instance iscategory_grothendieck_toset : IsCategory (Grothendieck.ToSet.category F).
  Proof.
    intros s d.
    refine (isequiv_adjointify _ _ _ _).
    { intros [m [m' ? ?]].
      destruct s as [s s'], d as [d d']; simpl in *.
      transparent assert (H' : (s = d)).
      { apply (Morphisms.idtoiso C (x := s) (y := d))^-1%function.
        exists m.1.
        exists m'.1.
        { exact (ap projT1 left_inverse). }
        { exact (ap projT1 right_inverse). } }
      { transitivity {| x := transport (fun x => F x) H' s' |}.
        { apply (@transportD _ (fun s => F s) (fun d d' => {| c := s; x := s' |} = {| c := d; x := d' |}) _ _ H' s').
          exact 1. }
        { apply ap.
          subst H'.
          simpl.
          refine (transport_idmap_ap _ (fun x => F x : Type) _ _ _ _ @ _).
          change (fun x => F x : Type) with (trunctype_type o object_of F)%function.
          match goal with
            | [ |- transport ?P (ap (?f o ?g)%function ?H) ?x = ?y ]
              => refine (ap (fun H' => transport P H' x) (ap_compose g f H) @ _)
          end.
          rewrite ap_functor_isotoid.
          simpl.
          rewrite concat_1p, concat_p1.

          destruct H.
          pose (fun H => transport idmap H s').
          admit. } } }
    { intro x.
      simpl in *.
      apply path_isomorphic; simpl.
      rewrite <- idtoiso_comp.
      admit. }
    { intro.
      hnf in s, d.
      destruct x.
      simpl.
      destruct s; simpl.
      rewrite isotoid_1.
      simpl.
      rewrite !concat_1p.
      admit. }
      SearchAbout idtoiso.
      rewrite transportD_is_transport.
      SearchAbout transportD.
      SearchAbout (transportD _ _ _ _).

          apply idtoiso_of_transport.
          Check transport_forall_constant.
          SearchAbout transport idtoiso.
          SearchAbout
          Unset Printing Notations.
          Set Printing Implicit.
          SearchAbout isotoid.
          simpl in *.
        Require Import HoTT. Locate transportD.
      simpl.

End Grothendieck.
