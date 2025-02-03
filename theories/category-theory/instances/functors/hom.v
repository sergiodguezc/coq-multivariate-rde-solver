From sgdt Require Import category_theory type.
From Coq Require Import ssreflect FunctionalExtensionality.

(*  Hom functor fmap *)
Definition hom_funct_fmap {C : Category} (A B : prod_cat C^op C) (f : A ~> B) : hom TYPE (hom C (fst A) (snd A)) (hom C (fst B) (snd B)).
Proof.
  intros g. destruct f as [f1 f2]. simpl in f1. exact (compose f2 (compose g f1)).
Defined.

(*  Hom functor satisfies the functor laws *)
Lemma hom_funct_mixin {C : Category} : FunctMixin (prod_cat C^op C) TYPE
  (fun x => hom C (fst x) (snd x)) (fun (A B : prod_cat C^op C) (f : A ~> B) => hom_funct_fmap A B f).
Proof.
  unshelve econstructor; intros; unfold compose, hom_funct_fmap; simpl.
  - extensionality g. by simplify_funct.
  - extensionality t. destruct f, g. simpl. rewrite <- !comp_assoc. reflexivity.
Qed.

(*  Hom functor *)
Definition hom_functor {C : Category} : mvFunctor C TYPE := {|
  fobj := fun x : prod_cat C^op C => hom C (fst x) (snd x) : TYPE ;
  fmap := fun (A B : prod_cat C^op C) (f : A ~> B) => hom_funct_fmap A B f;
  funct_mixin := hom_funct_mixin;
|}.

(*  Definition of the covariant and contravariant hom functors *)
Definition cov_hom_functor {C : Category} (c : C^op) : Functor C TYPE := second_funct hom_functor c.
Definition contrav_hom_functor {C : Category} (c : C) : Functor C^op TYPE := first_funct hom_functor c.

