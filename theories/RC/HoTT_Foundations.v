
Require Import HoTT.

Notation total2 := sigT.
Notation UU := Type.
Notation tpair := exist.
Definition dirprod (A B : UU) := sigT (fun _ : A => B).
Definition dirprodpair {A B : UU} := exist (fun _ : A => B).
Notation isaprop := IsHProp.
Notation isofhleveltotal2 := trunc_sigma.
Definition total2_paths_hProp {A : Type} (P : A -> Type) 
   (H : forall x, isaprop (P x)) (u v : sigT P)
   (p : u.1 = v.1) : u = v.
apply path_sigma_uncurried.
exists p.
apply H.
Defined.
Notation isaset := IsHSet.
Definition hSet := sigT (fun x => isaset x).
Definition hSetpr1 (X : hSet) : UU := pr1 X.
Coercion hSetpr1 : hSet >-> Sortclass.
Notation hSetpair := (exist (fun x => isaset x)).
Definition pr1hSet:= @pr1 UU (fun X : UU => isaset X) : hSet -> Type.
Coercion pr1hSet: hSet >-> Sortclass.

Definition uip : forall (X : UU) (hX : isaset X) 
         (x x' : X) (e e' : x = x'), e = e'.
intros X hx x x' e e'.
apply hx.
Qed.
Notation maponpaths := ap.
Notation isapropdirprod := isofhleveltotal2.
Notation pathscomp0 := concat.
Search ( _ -> isaprop _).
Notation invproofirrelevance := hprop_allpath.
About path_sigma.
Definition total2_paths {A P u v} H := @path_sigma A P u v H.
Search (isaprop _ -> forall _ _ , _ = _ ).
Notation proofirrelevance := allpath_hprop.
Notation pathsinv0 := inverse.
Notation isweq := IsEquiv.