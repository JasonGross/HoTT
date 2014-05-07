
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
   (p : u.1 = v.1) : u = v
  := path_sigma_hprop u v p.
Notation isaset := IsHSet.
(*Definition hSet := sigT (fun x => isaset x).*)
Notation hSetpr1 := (setT : hSet -> UU).
(*Definition hSetpr1 (X : hSet) : UU := X.*)
(*Coercion hSetpr1 : hSet >-> Sortclass.*)
Notation hSetpair := BuildhSet.
Notation pr1hSet:= setT.
(*Coercion pr1hSet: hSet >-> Sortclass.*)

Definition uip (X : UU) (hX : isaset X)
           (x x' : X) (e e' : x = x')
: e = e'
  := allpath_hprop _ _.
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
