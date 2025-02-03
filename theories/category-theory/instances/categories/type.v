From sgdt.category_theory Require Import category.
From Coq Require Import FunctionalExtensionality ssreflect.

(*  Definition of the category of Types *)
Lemma type_mixin : CatMixin Type (fun A B => A -> B) (fun A x => x) (fun A B C f g x => f (g x)).
Proof.
  unshelve econstructor; intros; by extensionality t.
Qed.

(* Category of Types *)
Definition TYPE : Category := {|
  obj := Type;
  hom := fun A B => A -> B;
  id := fun A x => x;
  compose := fun A B C f g x => f (g x);
  cat_mixin := type_mixin;
|}.

