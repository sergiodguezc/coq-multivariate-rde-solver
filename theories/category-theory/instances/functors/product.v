From sgdt Require Import category functor structure.

(* Definition of the object map of the product functor *)
Definition prod_funct_obj {C : Category} `{FiniteProducts C} (A : prod_cat C C) :=
  (fst A) × (snd A).

(* Definition of the morphism map of the product functor *)
Definition prod_funct_fmap {C : Category} `{FiniteProducts C} (A B : prod_cat C C)
  (f : A ~{prod_cat C C}~> B) : prod_funct_obj A ~{C}~> prod_funct_obj B.
Proof.
  destruct A as [A1 A2], B as [B1 B2], f as [f1 f2] ; simpl in *.
  exact (<| (f1 ∘ p_fst), (f2 ∘ p_snd) |>).
Defined.

(* Functor mixin for the product functor *)
Lemma prod_funct_mixin {C : Category} `{FiniteProducts C} : FunctMixin (prod_cat C C) C prod_funct_obj prod_funct_fmap.
Proof.
  split ; intros ; simpl ; intros.
  - destruct A as [A1 A2] ; simpl.
    unfold prod_funct_obj, prod_funct_fmap. unfork.
  - destruct A as [A1 A2], B as [B1 B2], C0 as [C1 C2], f as [f1 f2], g as [g1 g2].
    unfold prod_funct_obj, prod_funct_fmap. simpl.
    rewrite <- !comp_assoc. 
    rewrite fork_precompose.
    unfork ; rewrite <- !comp_assoc; unfork.
Qed.
    
(* Definition of the tensor product *)
Definition tensor_prod {C : Category} `{FiniteProducts C} : BiFunctor C C C := {|
  fobj := prod_funct_obj ;
  fmap := prod_funct_fmap ;
  funct_mixin := prod_funct_mixin 
 |}.
