Require Import Overture types.Universe PathGroupoids Equivalences EquivalenceVarieties types.Paths.

Set Implicit Arguments.

(** * Universe Levels *)

(** We provide casting definitions for raising universe levels. *)

(** Because we have cumulativity (that [T : Uᵢ] gives us [T : Uᵢ₊₁]), we may define [Lift : U₀ → U₁] as the identity function with a fancy type; the type says that [U₀ ⊊ U₁]. *)
Definition Lift : Type@{i} -> Type@{j}
  := Eval hnf in let lt := Type@{i} : Type@{j} in fun T => T.

Definition lift {T} : T -> Lift T := fun x => x.
Global Instance isequiv_lift T : IsEquiv (@lift T)
  := @BuildIsEquiv
       _ _
       (fun x => x)
       (fun x => x)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath).
Definition lower {A} := (@equiv_inv _ _ (@lift A) _).

(** We make [lift] and [lower] opaque so that typeclass resolution doesn't pick up [isequiv_lift] as an instance of [IsEquiv idmap] and wreck havok. *)
Typeclasses Opaque lift lower.

Instance isembedding_Lift `{Univalence} x y : IsEquiv (@ap _ _ Lift x y).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  { intro H'.
    pose proof ((fun H0 => (@path_universe _ _ _ (@lift x) (H0 x) @ H' @ (@path_universe _ _ _ (@lift y) (H0 y))^)))%path as H''.
    set (id := fun T (x : T) => x).
    change @IsEquiv with (id _ (@IsEquiv)) in *.
    refine (match H'' _ with idpath => idpath end).
    subst id; simpl.
    intro.
    exact (@BuildIsEquiv
             _ _
             (fun x => x)
             (fun x => x)
             (fun _ => idpath)
             (fun _ => idpath)
             (fun _ => idpath)). }
  { hnf; simpl.
    intro x0.
    revert x0.
    intro x0.
    pattern x0.
    rewrite <- !(eta_path_universe x0).
    SearchAbout path_universe.
    Set Printing Implicit.

    match goal with
    unfold Lift, lower, lift in H''; simpl in H''.
    apply H''.



intro H'; apply path_universe_uncurried; apply equiv_path in H'.
    refine (BuildEquiv _ _ _ (BuildIsEquiv _ _ _ _ _ _ _)).
    { exact (lower o equiv_fun H' o lift). }
    { exact (lower o @equiv_inv _ _ _ H' o lift). }
    { intro H''.
      change ((lower o H' o H'^-1%equiv o lift) H'' = H'').
      exact (ap lower (eisretr H' (lift H''))). }
    { intro H''.
      change ((lower o H'^-1%equiv o H' o lift) H'' = H'').
      exact (ap lower (eissect H' (lift H''))). }
    { intro x0; cbv beta.

      lazymatch goal with
      | [ |- ?a = ?b :> ?T ]
        => pose (a:T)
      end.

      refine (_ @ (ap_compose (H' o lift) lower (ap lower (eissect H' (lift x0))))^)%path.
      refine (_ @ (ap_compose lower (lower o H' o lift) (eissect H' (lift x0))))%path.
      refine (
      apply (@equiv_inv _ _ (ap (ap lift)) (isequiv_ap _ _)).
      refine ((ap_compose lower lift _)^ @ _)%path.
      change (@lift ?T o lower) with (fun x : T => x).
      refine (ap_idmap _ @ _)%path.
      refine (eisadj H' x0 @ _)%path.
      apply (@equiv_inv _ _ (ap (ap lower)) (@isequiv_ap _ _ _ (@isequiv_ap _ _ _ (isequiv_inverse) _ _) _ _)).
      refine (_ @ (ap_compose lift lower _))%path.
      change (@lower ?T o lift) with (fun x : T => x).
      refine (_ @ (ap_idmap _)^)%path.
      apply (@equiv_inv _ _ (ap (ap H'%equiv)) (@isequiv_ap _ _ _ (@isequiv_ap _ _ _ (isequiv_inverse) _ _) _ _)).
      refine (_ @ (ap_compose lower H' _))%path.

      SearchAbout ap.
      apply (ap lift)^-1%equiv.

      exact idpath.
      Set Printing All.
      Set Printing Universes.
      apply H''''.
      apply H''''.
      simpl in *.
      pose (fun X => (H'''' X)) as H'''''.


      SearchAbout Equiv paths.
      speci

    { intro.
      let p := constr:((transport_pp idmap H'^ H' x0)^)%path in
      lazymatch type of p with
      | ?a = ?b :> ?T
        => refine (match p in (_ = y) return (a = y) with 1 => 1 end @ _)%path
      end.
      pattern (H'^ @ H')%path.
      refine (transport _ (@concat_Vp _ _ _ H')^%path idpath). }
    { intro.
      let p := constr:((transport_pp idmap H' H'^ x0)^)%path in
      lazymatch type of p with
      | ?a = ?b :> ?T
        => refine (match p in (_ = y) return (a = y) with 1 => 1 end @ _)%path
      end.
      pattern (H' @ H'^)%path.
      refine (transport _ (@concat_pV _ _ _ H')^%path idpath). } }
  { intro H'; simpl.

    SearchAbout path_universe.
    refine (ap_idmap _ @ _)%path.
    SearchAbout (ap idmap _).

    rewrite transport_idmap_ap.


      { exact idpath. }
      { pose .
      { by destruct H'. }
      rewrite <- transport_pp
      rewrite concat_Vp.
      simpl.
      reflexivity.
      SearchAbout transport.

      Set Printing All.
      Set Printing Universes.


SearchAbout transport inverse.
    refine (match H' in (_ = y') return (x <~> y)%equiv ->  with
              | idpath => _
            end).
induction H'.

  Set Printing All. Set Printing Universes.



Set Printing Universes.





(*Fail Check Lift nat : Type0.
Check 1 : Lift nat.*)
