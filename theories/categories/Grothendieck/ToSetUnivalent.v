Require Import Category.Core Functor.Core Category.Univalent Category.Morphisms.
Require Import HoTT.Basics.PathGroupoids HoTT.Types.Sigma HoTT.Tactics.EquivalenceInduction.

(*Lemma isotoid_1 {C} `{IsCategory C} {x : C} {H : IsIsomorphism (identity x)}
: isotoid C x x {| morphism_isomorphic := (identity x) ; isisomorphism_isomorphic := H |}
  = idpath.
Proof.
  refine (ap _ _ @ eissect (idtoiso C (x := x) (y := x)) idpath).
  apply path_isomorphic; reflexivity.
Defined.

Lemma isotoid_1' {C} `{IsCategory C} {x : C}
: isotoid C x x (isomorphic_refl _ _)
  = idpath.
Proof.
  exact isotoid_1.
Defined.

Lemma ap_transportD_commute {A} B (CT : Type) (C1 C2 : forall a : A, B a -> CT) {x1 x2}
      (p : x1 = x2) y {D} (f : CT -> D) (H : C1 x1 y = C2 x1 y)
: ap f (transportD B (fun a b => C1 a b = C2 a b) p y H)
  = transportD B (fun a b => f (C1 a b) = f (C2 a b)) p y (ap f H).
Proof.
  destruct p; simpl; reflexivity.
Defined.

Lemma ap_functor_isotoid {C D} `{IsCategory C, IsCategory D} (F : Functor C D) {s d : C} (e : Isomorphic s d)
: ap F (isotoid C s d e) = isotoid D _ _ {| morphism_isomorphic := F _1 e |}.
Proof.
  pattern e.
  refine (transport _ (eisretr (idtoiso C (x := s) (y := d)) e) _).
  generalize (isotoid C s d e); clear e; intro e.
  refine (ap (ap F) (eissect (idtoiso C (x := s) (y := d)) e) @ _).
  destruct e; simpl.
  refine (isotoid_1^ @ ap (isotoid D (F s) (F s)) _).
  apply path_isomorphic.
  exact (identity_of F _)^.
Defined.

Lemma path_sigma_hprop_1 {A P} `{forall x : A, IsHProp (P x)} {x : A} (y : P x)
: path_sigma_hprop (x; y) (x; y) 1 = 1%path.
Proof.
  change (path_sigma_hprop (x; y) (x; y) 1 = path_sigma_uncurried P (x; y) (x; y) (1%path; 1%path)).
  unfold path_sigma_hprop.
  apply ap.
  simpl.
  apply ap.
  apply contr.
Defined.*)

(** * Saturation of the Grothendieck Construction of a functor to Set *)
Require Import Category.Core Functor.Core.
Require Import Category.Univalent.
Require Import Category.Morphisms.
Require Import SetCategory.Core.
Require Import Grothendieck.ToSet.
Require Import SetCategory.Morphisms.
Require Import Basics.Trunc HSet Types.Sigma TruncType UnivalenceImpliesFunext Types.Universe Basics.Equivalences Basics.PathGroupoids HoTT.Types.Forall HoTT.Types.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.


(*Section idtoiso.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable F : Functor C set_cat.

  Lemma idtoiso_setcat {s d : set_cat} (H0 : s = d)
  : idtoiso set_cat H0 = transport idmap (ap trunctype_type H0) :> morphism _ _ _.
  Proof.
    destruct H0; reflexivity.
  Defined.

  Lemma idtoiso_category {s d : Grothendieck.ToSet.category F} (H0 : s = d)
  : idtoiso (category F) H0
    = (idtoiso C (ap (fun s => s.(c)) H0) : morphism _ _ _;
       (ap10 ((idtoiso_functor (ap (fun s => s.(c)) H0) F)
                @ ((ap (fun H' => idtoiso set_cat (x := _) (y := _) H' : morphism _ _ _)
                       (ap_compose (fun s => s.(c)) F H0))^)
                @ (idtoiso_setcat _))
             _)
         @ ((transport_compose idmap _ _ _)^)
         @ ((transport_compose (fun x : hSet => x : Type) (fun x => F (c x)) H0 (s.(x)))^)
         @ apD (fun s => s.(x)) H0) :> morphism _ _ _.
  Proof.
    destruct H0; simpl.
    apply path_sigma_uncurried; exists idpath; simpl.
    unfold identity_H, ap10; simpl.
    refine (_ @ (concat_p1 _)^ @ (concat_p1 _)^ @ (concat_p1 _)^); shelve_unifiable.
    match goal with
      | [ |- ?f ?H ?x = ?f' ?H' ?x ]
        => refine (@apD10 _ _ (f H) (f H') _ x)
    end.
    apply ap.
    refine ((concat_p1 _)^ @ (concat_p1 _)^).
  Defined.

  Lemma idtoiso_category_pr1 {s d : Grothendieck.ToSet.category F} (H0 : s = d)
  : (idtoiso (category F) H0 : morphism _ _ _).1
    = (idtoiso C (ap (fun s => s.(c)) H0) : morphism _ _ _).
  Proof.
    exact (ap projT1 (idtoiso_category H0)).
  Defined.

  Lemma idtoiso_ap_pair c0 {x0 x1} (H0 : x0 = x1)
  : idtoiso (category F) (ap (Build_Pair F c0) H0)
    = (1; ap10 (identity_of F c0) x0 @ H0) :> morphism _ _ _.
  Proof.
    refine (idtoiso_category _ @ _); simpl.
    apply path_sigma_uncurried; simpl.
    destruct H0; simpl; exists idpath; simpl.
    apply ap10, ap.
    refine (concat_p1 _ @ concat_p1 _ @ _).
    refine (apD10 _ x0).
    apply ap.
    refine (concat_p1 _ @ concat_p1 _).
  Defined.
End idtoiso.*)

Definition isequiv_sigma_category_isomorphism `{Funext} {C} (F : Functor C set_cat)
           {s d : Grothendieck.ToSet.category F}
: (s <~=~> d)%category <~> { e : (s.(c) <~=~> d.(c))%category | (F _1 e s.(x) = d.(x))%category }.
Proof.
  refine (equiv_adjointify _ _ _ _).
  { intro m.
    refine (_; _).
    { exists (m : morphism _ _ _).1.
      exists (m^-1).1.
      { exact (ap projT1 (@left_inverse _ _ _ m _)). }
      { exact (ap projT1 (@right_inverse _ _ _ m _)). } }
    { exact (m : morphism _ _ _).2. } }
  { intro m.
    exists (m.1 : morphism _ _ _ ; m.2).
    eexists (m.1^-1;
             ((ap (F _1 (m.1)^-1) m.2)^)
               @ (ap10 ((((composition_of F _ _ _ _ _)^)
                           @ (ap (fun m => F _1 m) (@left_inverse _ _ _ m.1 _))
                           @ (identity_of F _))
                        : (F _1 (m.1 : morphism _ _ _)^-1) o F _1 m.1 = idmap) s.(x)));
    apply path_sigma_hprop.
    exact left_inverse.
    exact right_inverse. }
  { intro x; apply path_sigma_hprop; apply path_isomorphic.
    reflexivity. }
  { intro x; apply path_isomorphic; reflexivity. }
Defined.

Section Grothendieck.
  Context `{Univalence}.

  Variable C : PreCategory.
  Context `{IsCategory C}.
  Variable F : Functor C set_cat.

  Definition category_isotoid_helper {s d} (a : c s = c d)
  : (transport (fun c : C => F c) a (x s) = x d)
      <~> (F _1 (idtoiso C a)) (x s) = x d.
  Proof.
    apply equiv_path.
    apply ap10, ap.
    destruct a; simpl.
    exact (ap10 (identity_of F _)^ _).
  Defined.

  Arguments category_isotoid_helper : simpl never.

  Definition category_isotoid {s d : Grothendieck.ToSet.category F}
  : s = d <~> (s <~=~> d)%category.
  Proof.
    refine (isequiv_sigma_category_isomorphism^-1 oE _ oE (equiv_ap' (issig_pair F)^-1 s d)).
    refine (_ oE (equiv_path_sigma _ _ _)^-1).
    simpl.
    refine (equiv_functor_sigma' _ _).
    { exists (@idtoiso C _ _).
      exact _. }
    { exact category_isotoid_helper. }
  Defined.

  Instance iscategory_grothendieck_toset : IsCategory (Grothendieck.ToSet.category F).
  Proof.
    intros s d.
    refine (@isequiv_homotopic _ _ category_isotoid (idtoiso (category F) (x:=s) (y:=d)) _ _).
    intro x.
    destruct x; apply path_isomorphic, path_sigma_hprop.
    reflexivity.
  Defined.
End Grothendieck.
