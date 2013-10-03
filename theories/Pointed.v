(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import Overture.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Allow ourselves to implicitly generalize over types [A] and [B], a function [f], and a hypothesis [H]. *)
Generalizable Variables A B f H.

(** Any contratible type is pointed. *)
Canonical Structure ispointed_contr `{Contr A} : IsPointed A
  := Build_IsPointed (center A).

(** A pi type with a pointed target is pointed. *)
(** I'm not sure why I need to explicitly pass the instance to [point] here. -Jason Gross *)
Canonical Structure ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := Build_IsPointed (fun a => @point (B a) (H a)).

(** A sigma type of pointed components is pointed. *)
Canonical Structure ispointed_sigma A (B : A -> Type)
          `{H : IsPointed A} `{H' : IsPointed (B (@point A H))}
: IsPointed (sigT B)
  := Build_IsPointed (point A; @point (B (@point A H)) H').

(** A cartesian product of pointed types is pointed. *)
Canonical Structure ispointed_pord `{HA : IsPointed A, HB : IsPointed B}
: IsPointed (A * B)
  := Build_IsPointed (@point A HA, @point B HB).

(** The type [x = x] is pointed. *)
Canonical Structure ispointed_loop_space A (a : A) : IsPointed (a = a)
  := Build_IsPointed idpath.

(** We can build an iterated loop space *)
Definition loopSpace (A : pointedType) : pointedType
  := (A.1 = A.1; Build_IsPointed idpath).

Fixpoint iteratedLoopSpace (n : nat) (A : Type) `{H : IsPointed A} {struct n} : pointedType
  := match n with
       | O => existT IsPointed A H
       | S p => @iteratedLoopSpace p (point = point) (ispointed_loop_space _ _)
     end.
