From sgdt Require Import category terminal.

(*  Definition of a category with an initial object *)
Class Initial (Y : Category) := mkInitial {
  initial_obj : Y; (* Initial object *)
  zero {A : Y} : initial_obj ~> A; (* Zero morphism *)
  zero_unique {A : Y} (f g : initial_obj ~> A) : f = g; (* Uniqueness of the zero morphism *)
}.
