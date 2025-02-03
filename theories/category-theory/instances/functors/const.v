From sgdt.category_theory Require Import category functor.
From Coq Require Import ssreflect.

(*  Constant functor satisfies the functor laws *)
Lemma const_funct_mixin {C D : Category} (d : D) : FunctMixin C D (fun _ => d) (fun _ _ _ => id{D}).
Proof.
  split ; intros ; by simplify_funct.
Qed.

(* Constant functor *)
Definition const_funct {C D : Category} (d : D) : Functor C D := {|
  fobj := fun _ => d ;
  fmap := fun _ _ _ => id{D} ;
  funct_mixin := const_funct_mixin d
|}.
  

