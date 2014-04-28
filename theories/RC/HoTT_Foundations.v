
Require Import HoTT.

Notation total2 := sigT.
Notation UU := Type.
Notation tpair := exist.
Definition dirprod (A B : UU) := sigT (fun _ : A => B).
Definition dirprodpair {A B : UU} := exist (fun _ : A => B).
Notation isaprop := IsHProp.