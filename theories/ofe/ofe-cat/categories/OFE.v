From Coq Require Import ssreflect.
From sgdt Require Import category ofe.

(* CATEGORY OF OFE *)

(* Composition of morphisms *)
Program Definition ofe_comp {A B C : ofe} (f : B -n> C) (g : A -n> B) : A -n> C :=
  {| ne_mor := fun x => f (g x) |}.
Next Obligation.
  intros n x y H; by repeat apply hom_ne.
Qed.

(* Identity morphism *)
Program Definition ofe_id {A : ofe} : A -n> A := {| ne_mor := fun x => x |}.
Next Obligation.
  by intros n x y H.
Qed.

(* Satisfaction of the category laws *)
Lemma ofe_cat_mixin : CatMixin ofe (@NonExpansiveMaps) (@ofe_id) (@ofe_comp).
Proof. split; intros; by apply ne_eq. Qed.

(* Definition of the category of OFEs *)
Definition OFE : Category := {|
  obj := ofe;
  hom := NonExpansiveMaps;
  id := @ofe_id;
  compose := @ofe_comp;
  cat_mixin := ofe_cat_mixin
|}.

(* Coercion from non-expansive maps to morphisms in the OFE category *)
Coercion ne_map {A B : ofe} (f : A -n> B) : A ~{OFE}~> B := f.
Coercion ctr_map {A B : ofe} (f : A -c> B) : A ~{OFE}~> B := f.

(* In case we want to use the OFE category as a notation *)
Definition ofe_comp_cat {A B C : ofe} (f : B -n> C) (g : A -n> B)  :
  ofe_comp f g = f ∘ g := eq_refl.
