From sgdt Require Import category.

(*  Definition of a category with a terminal object *)
Class Terminal (Y : Category) := mkTerminal {
  terminal_obj : Y; (* Terminal object *)
  one {A : Y} : A ~> terminal_obj; (* One morphism *)
  one_unique {A : Y} (f g : A ~> terminal_obj) : f = g; (* Uniqueness of the one morphism *)
}.

Declare Scope object_scope.
Notation "1" := terminal_obj : object_scope.
Opaque terminal_obj.
Notation "![ A ]" := (one (A:=A)) (at level 40) : object_scope.

Open Scope object_scope.
