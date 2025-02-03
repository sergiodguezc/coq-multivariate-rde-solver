From Coq Require Import ssreflect FunctionalExtensionality PropExtensionality PeanoNat.

(* Definition of a category *)

(* 
   CatMixin is a structure that encapsulates the axioms of a category:
   - obj: the type of objects in the category.
   - hom: the type of morphisms between objects.
   - id: the identity morphism for each object.
   - compose: composition of morphisms.
   The structure also includes the category laws:
   - mixin_id_left: left identity law.
   - mixin_id_right: right identity law.
   - mixin_comp_assoc: associativity of composition.
*)
Structure CatMixin (obj : Type) (hom : obj -> obj -> Type) 
  (id : forall {x}, hom x x) (compose : forall {x y z}, hom y z -> hom x y -> hom x z) := {

  mixin_id_left : forall x y (f : hom x y), compose id f = f;
  mixin_id_right : forall x y (f : hom x y), compose f id = f;
  mixin_comp_assoc : forall x y z w (f : hom z w) (g : hom y z) (h : hom x y),
    compose f (compose g h) = compose (compose f g) h;
}.

(* 
   Category is a record that represents a category, including:
   - obj: the type of objects.
   - hom: the type of morphisms.
   - id: the identity morphism.
   - compose: composition of morphisms.
   - dom and cod: domain and codomain of a morphism.
   - cat_mixin: the category axioms encapsulated in CatMixin.
*)
Record Category : Type := mkCAT {
  obj : Type;

  hom : obj -> obj -> Type;

  id {x} : hom x x;
  compose {x y z} (f: hom y z) (g : hom x y) : hom x z;

  dom {x y} (f : hom x y) := x;
  cod {x y} (f : hom x y) := y;

  cat_mixin : CatMixin obj hom (@id) (@compose);
}.

(* Coercion to treat a category as a type of objects *)
Coercion obj : Category >-> Sortclass.

(* Declare scopes for category and morphism notations *)
Declare Scope category_scope.
Declare Scope morphism_scope.

(* Arguments directive to control simplification of compose *)
Arguments compose {_ _ _ _} _ _ : simpl never.

(* Notations for objects and morphisms in a category *)
Notation "obj[ C ]" := (@obj C)
  (at level 0, format "obj[ C ]") : category_scope.
Notation "hom[ C ]" := (@hom C)
 (at level 0, format "hom[ C ]") : category_scope.

Notation "x ~> y" := (@hom _ x y)
  (at level 90, right associativity) : category_scope.
Notation "x ~{ C }~> y" := (@hom C x y)
  (at level 90) : category_scope.

Notation "id[ x ]" := (@id _ x)
  (at level 9, format "id[ x ]") : morphism_scope.

Notation "id{ C }" := (@id C _)
  (at level 9, format "id{ C }") : morphism_scope.

Notation "f ∘ g" :=
  (@compose _ _ _ _  f g) (at level 40, only parsing) : morphism_scope.
Notation "f ∘[ C ] g" :=
  (@compose C _ _ _ f g)
  (at level 40, no associativity) : morphism_scope.

(* Open the scopes for category and morphism notations *)
Open Scope category_scope.
Open Scope morphism_scope.

(* Lifting properties of the mixin *)
Lemma id_left {C : Category} : forall x y (f : x ~> y), id[y] ∘[C] f = f.
Proof. intros; apply mixin_id_left; apply cat_mixin. Qed.

Lemma id_right {C : Category} : forall x y (f : x ~> y), f ∘[C] id[x] = f.
Proof. intros; apply mixin_id_right; apply cat_mixin. Qed.

Lemma comp_assoc {C : Category} : forall x y z w (f : z ~> w) (g : y ~> z) (h : x ~> y),
  f ∘[C] (g ∘[C] h) = (f ∘[C] g) ∘[C] h.
Proof. intros; eapply mixin_comp_assoc; apply cat_mixin. Qed.

(* Create a HintDB for the category laws *)
Create HintDb cat_db.
Hint Rewrite @comp_assoc : cat_db.
Hint Rewrite @id_left : cat_db.
Hint Rewrite @id_right : cat_db.

(* A tactic to simplify using the HintDB *)
Ltac simplify_cat := simpl ;autorewrite with cat_db.

(*  CONSTRUCTIONS OF CATEGORIES *)

(* Definition of the opposite category *)
Lemma Opposite_mixin (Z : Category) : CatMixin (obj Z) (fun A B => @hom Z B A) (@id Z) (fun _ _ _ f g => @compose Z _ _ _ g f).
Proof.
  unshelve econstructor ; intros ; by simplify_cat.
Qed.

Definition Opposite (Z : Category) : Category := 
  {|
    obj := obj Z;
    hom := fun A B => @hom Z B A;
    id := @id Z;
    compose := fun _ _ _ f g => @compose Z _ _ _ g f;
    cat_mixin := Opposite_mixin Z;
 |}.

Notation "C ^op" := (@Opposite C)
  (at level 7, format "C ^op", left associativity) : category_scope.

(* Definition of the trivial one-object category *)
Lemma one_mixin : CatMixin unit (fun _ _ => unit) (fun _ => tt) (fun _ _ _ _ _ => tt).
Proof.
  unshelve econstructor ; intros ; by destruct f.
Qed.

Definition one_cat : Category := 
  {|
    obj := unit;
    hom := fun _ _ => unit;
    id := fun _ => tt;
    compose := fun _ _ _ _ _ => tt;
    cat_mixin := one_mixin;
  |}.

(* Lemma showing that the opposite of the one-object category is itself *)
Lemma one_cat_op : one_cat^op = one_cat.
Proof.
  unfold Opposite; simpl ;
  unfold eq_ind_r, eq_ind, eq_sym, one_cat; simpl; f_equal ; apply proof_irrelevance.
Qed.

(*  Lemmas about the opposite category *)
Lemma op_id {C : Category} : @id (C^op) = @id C.
Proof. reflexivity. Qed.

Lemma op_obj_eq {C : Category} : obj[C^op] = obj[C].
Proof. reflexivity. Qed.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl. destruct C; simpl;
  f_equal; apply proof_irrelevance.
Qed.

(*  Product of two categories *)
Lemma prod_mixin (Y Z : Category) : CatMixin (prod (obj Y) (obj Z))
  (fun a b => prod (fst a ~> fst b) (snd a ~> snd b))
  (fun a => (id[fst a], id[snd a]))
  (fun _ _ _ f g => (@compose Y _ _ _ (fst f) (fst g), @compose Z _ _ _ (snd f) (snd g))).
Proof.
  unshelve econstructor ; intros  ; simplify_cat ; by destruct f.
Qed.

Definition prod_cat (Y Z : Category) : Category :=
  {|
    obj := prod (obj Y) (obj Z);
    hom := fun a b => prod (fst a ~> fst b) (snd a ~> snd b);
    id := fun a => (id[fst a], id[snd a]);
    compose := fun _ _ _ f g => (@compose Y _ _ _ (fst f) (fst g), @compose Z _ _ _ (snd f) (snd g));
    cat_mixin := prod_mixin Y Z;
  |}.

Notation "Y × Z" := (@prod_cat Y Z)
  (at level 40, left associativity) : category_scope.

(* Lemma showing that the opposite of a product category is the product of the opposites *)
Lemma op_prod {Y Z : Category} : (Y × Z)^op = Y^op × Z^op.
Proof.
  unfold Opposite, prod_cat; simpl. f_equal ;
  apply proof_irrelevance.
Qed.

(*  Product of n categories *)
Fixpoint n_prod_cat (n : nat) (C : Category) : Category :=
  match n with
  | O => one_cat
  | S n' => (n_prod_cat n' C) × C
  end.

Notation "C ** n" := (@n_prod_cat n C)
  (at level 30, right associativity) : category_scope.

(* Lemma showing the relationship between the product category and its successor *)
Lemma n_prod_cat_S {n : nat} {C : Category} :
  C ** (S n) = (C ** n) × C.
Proof. reflexivity. Qed.

(* Lemma showing that the opposite of an n-ary product category is the n-ary product of the opposites *)
Lemma n_prod_cat_op {n : nat} {C : Category} :
  (C ** n)^op = C^op ** n.
Proof.
  induction n; simpl.
  - unfold Opposite, one_cat ; simpl.
    f_equal ; apply proof_irrelevance.
  - rewrite op_prod. rewrite IHn. reflexivity.
Qed.

(* Lift two morphisms to the product category *)
Definition prod_mor {Y Z : Category} {A B : Y} {C D : Z}
  (f : A ~> B) (g : C ~> D) : (A, C) ~{Y × Z}~> (B, D) := (f, g).

Definition prod_mor_fst {Y Z : Category} {A B : Y} {C D : Z}
  (f : (A, C) ~{Y × Z}~> (B, D)) : A ~> B := fst f.

Definition prod_mor_snd {Y Z : Category} {A B : Y} {C D : Z}
  (f : (A, C) ~{Y × Z}~> (B, D)) : C ~> D := snd f.

(* Lemma showing that composition in the product category is component-wise *)
Lemma prod_mor_compose {Y Z : Category} {A B C : Y} {D E F : Z}
  (f : A ~> B) (h : B ~> C) (g : E ~> F) (k : D ~> E) 
  : prod_mor (h ∘ f) (g ∘ k) = prod_mor h g ∘ prod_mor f k.
Proof. reflexivity. Qed.

Lemma prod_mor_compose_2 {Y Z : Category} {A B C : prod_cat Y Z} 
  (f : A ~{prod_cat Y Z}~> B) (h : B ~{prod_cat Y Z}~> C)
  : (fst h ∘[Y] fst f, snd h ∘[Z] snd f) = h ∘ f.
Proof. reflexivity. Qed.

(* Lemma showing that composition in the opposite category reverses the order of morphisms *)
Lemma op_mor_eq {Y : Category} {A B C : Y} 
  (f : A ~{Y}~> B) (g : B ~{Y}~> C) : f ∘[Y^op] g = g ∘[Y] f.
Proof. reflexivity. Qed.
