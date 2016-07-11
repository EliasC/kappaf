Require Coq.Bool.Sumbool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.

Require Import Shared.

(* 
====
IDs
====
*)

Class ID (A : Type) :=
{
  id_eq_dec : forall (x y : A), {x = y} + {x <> y}
}.

Inductive svar : Type :=
  | SVar : nat -> svar.

Instance ID_svar : ID svar := {}.
  repeat decide equality.
Qed.

Definition this := SVar 0.

Inductive dvar : Type :=
  | DVar : nat -> dvar.

Instance ID_dvar : ID dvar := {}.
  repeat decide equality.
Qed.

Definition dthis := DVar 0.


Definition frame_id := nat.

Instance ID_frame_id : ID frame_id := {}.
  repeat decide equality.
Qed.

Instance ID_dvar_frame : ID (dvar * frame_id) := {}.
  repeat decide equality.
Qed. 

Inductive field_id : Type :=
  | Fid : nat -> field_id.

Definition field_id_eq (x y : field_id) : bool :=
  match x, y with
    | Fid n, Fid m => beq_nat n m
  end.

Instance ID_field : ID field_id := {}.
  repeat decide equality.
Qed.

Inductive region_id : Type :=
  | Rid : nat -> region_id.

Definition region_id_eq (x y : region_id) : bool :=
  match x, y with
    | Rid n, Rid m => beq_nat n m
  end.

Instance ID_region : ID region_id := {}.
  repeat decide equality.
Qed.


Inductive method_id : Type :=
  | Mid : nat -> method_id.

Definition method_id_eq (x y : method_id) : bool :=
  match x, y with
    | Mid n, Mid m => beq_nat n m
  end.

Instance ID_method : ID method_id := {}. 
  repeat decide equality.
Qed.


Inductive class_id : Type :=
  | Cid : nat -> class_id.

Definition class_id_eq (x y : class_id) : bool :=
  match x, y with
    | Cid n, Cid m => beq_nat n m
  end.

Instance ID_class : ID class_id := {}.
  repeat decide equality.
Qed.


Inductive interface_id : Type :=
  | Iid : nat -> interface_id.

Definition interface_id_eq (x y : interface_id) : bool :=
  match x, y with
    | Iid n, Iid m => beq_nat n m
  end.

Instance ID_interface : ID interface_id := {}.
  repeat decide equality.
Qed.

Definition loc := nat.

Instance ID_loc : ID loc := {id_eq_dec := eq_nat_dec}.

Definition lock := (loc * region_id)%type.

Definition lock_eq (x y : lock) : bool :=
  match x, y with
    | (l1, r1), (l2, r2) => andb (beq_nat l1 l2) (region_id_eq r1 r2)
  end.

Instance ID_lock : ID lock := {}.
  repeat decide equality.
Qed.

(* 
====
Map
====
*)

Definition partial_map (from:Type) {eqd : ID from} (to:Type) := from -> option to.

Definition empty {A B:Type} {eqd : ID A} : partial_map A B := (fun _ => None). 

Definition extend {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) (b:B) :=
  fun a' => if id_eq_dec a a' then 
              Some b 
            else 
              Gamma a'.

Hint Unfold extend.

Definition drop {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) :=
  fun a' => if id_eq_dec a a' then 
              None 
            else 
              Gamma a'.

Hint Unfold drop.

Definition fresh {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) := Gamma a = None.

Hint Unfold fresh.


