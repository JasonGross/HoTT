
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