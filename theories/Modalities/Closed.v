(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions.
Require Import Modality Accessible Nullification Lex Topological.
Require Import Colimits.Pushout Homotopy.Join.

Local Open Scope nat_scope.
Local Open Scope path_scope.


(** * Closed modalities *)

(** We begin by characterizing the modal types. *)
Section ClosedModalTypes.
  Context (U : hProp).

  Definition equiv_inO_closed (A : Type)
  : (U -> Contr A) <-> IsEquiv (fun a:A => push (inr a) : Join U A).
  Proof.
    split.
    - intros uac.
      simple refine (isequiv_adjointify _ _ _ _).
      * simple refine (Pushout_rec A _ _ _).
        + intros u; pose (uac u); exact (center A).
        + intros a; assumption.
        + intros [u a]. simpl.
          pose (uac u). apply contr.
      * intros z. pattern z.
        simple refine (Pushout_ind _ _ _ _ z).
        + intros u.
          pose (contr_inhabited_hprop U u).
          apply path_contr.
        + intros a; reflexivity.
        + intros [u a]; pose (contr_inhabited_hprop U u).
          apply path_contr.
      * intros a. reflexivity.
    - intros ? u.
      refine (contr_equiv (Join U A) (fun a:A => push (inr a))^-1).
      pose (contr_inhabited_hprop U u).
      exact _.
  Defined.

End ClosedModalTypes.

Record Closed_Modality := Cl { unCl : hProp }.

(** Exercise 7.13(ii): Closed modalities *)
Module ClosedModalities <: Modalities.

  Definition Modality : Type@{u} := Closed_Modality@{a}.

  Definition O_reflector : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun O X => Join@{a i i} (unCl O) X.

  Definition In : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun O X => unCl O -> Contr X.

  Definition O_inO (O : Modality@{u a}) (T : Type@{i})
  : In@{u a i} O (O_reflector@{u a i} O T).
  Proof.
    intros u.
    pose (contr_inhabited_hprop _ u).
    exact _.
  Defined.

  Definition to (O : Modality@{u a}) (T : Type@{i})
  : T -> O_reflector@{u a i} O T
    := fun x => push (inr x).

  Definition inO_equiv_inO (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
     (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f)
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    In@{u a j} O U.
  Proof.
    cbn; intros u; pose (T_inO u).
    refine (contr_equiv _ f); exact _.
  Defined.

  Definition hprop_inO `{Funext}
             (O : Modality@{u a}) (T : Type@{i})
  : IsHProp (In@{u a i} O T).
  Proof.
    exact _.
  Defined.

  Definition O_ind_internal (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    (forall a, B (to@{u a i} O A a)) -> forall a, B a.
  Proof.
    simpl; intros f z.
    simple refine (Pushout_ind@{i a i j i} B _ _ _ z).
    - intros u; apply center, B_inO, u.
    - intros a; apply f.
    - intros [u a].
      pose (B_inO (push (inr a)) u).
      apply path_contr.
  Defined.

  Definition O_ind_beta_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a : A)
  : O_ind_internal O A B B_inO f (to O A a) = f a
  := 1.

  Definition minO_paths (O : Modality@{u a}) (A : Type@{i})
             (A_inO : In@{u a i} O A)
             (z z' : A)
  : In@{u a i} O (z = z').
  Proof.
    intros u; pose (A_inO u); apply contr_paths_contr.
  Defined.

  Definition IsSepFor@{u a} (O' O : Modality@{u a}) : Type@{u}
    := Empty.

  Definition inO_paths_from_inSepO@{u a i iplus}
            (O' O : Modality@{u a}) (sep : IsSepFor O' O)
            (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A)
    : In@{u a i} O (x = y)
    := Empty_rec sep.

  Definition inSepO_from_inO_paths@{u a i iplus}
             (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (op : forall (x y : A), In@{u a i} O (x = y))
    : In@{u a i} O' A
    := Empty_rec sep.

End ClosedModalities.

Module Import ClM := Modalities_Theory ClosedModalities.
Export ClM.Coercions.
Export ClM.RSU.Coercions.

Coercion Closed_Modality_to_Modality :=
  idmap : Closed_Modality -> ClosedModalities.Modality.

(** The closed modality is accessible. *)
Module Accessible_ClosedModalities
  <: Accessible_Modalities ClosedModalities.

  Module Os_Theory := Modalities_Theory ClosedModalities.

  Definition acc_gen
    := fun (O : ClosedModalities.Modality@{u a}) =>
         Build_NullGenerators@{a} (unCl O) (fun _ => Empty).

  Definition inO_iff_isnull@{u a i}
             (O : ClosedModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (ClosedModalities.In@{u a i} O X)
      (IsNull (acc_gen O) X).
  Proof.
    split.
    - intros X_inO u.
      pose (X_inO u).
      apply ooextendable_contr@{a a i i}; exact _.
    - intros ext u.
      exists ((fst (ext u 1%nat) Empty_rec).1 tt); intros x.
      unfold const in ext.
      exact ((fst (snd (ext u 2) (fst (ext u 1%nat) Empty_rec).1
                       (fun _ => x)) (Empty_ind _)).1 tt).
  Defined.

End Accessible_ClosedModalities.

(** In fact, it is topological, and therefore (assuming univalence) lex.  As for topological modalities generally, we don't need to declare these as global instances, but we prove them here as local instances for exposition. *)
Module Import ClT :=
  Topological_Modalities_Theory
    ClosedModalities
    Accessible_ClosedModalities.

Local Instance topological_closed (O : Modality)
: Topological O.
Proof.
  exact _.
Defined.

Local Instance lex_closed `{Univalence} (O : Modality)
: Lex O.
Proof.
  exact _.
Defined.

(** Thus, it also has the following alternative version. *)
Definition Cl' (U : hProp)
: Nullification_Modality
  := Nul (Build_NullGenerators U (fun _ => Empty)).
