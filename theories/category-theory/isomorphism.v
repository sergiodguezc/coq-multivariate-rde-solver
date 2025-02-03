From sgdt Require Import category.
From Coq Require Import ssreflect PropExtensionality.

(* Definition of isomorphism between objects in a category *)
Record iso {Y : Category} (A B : Y) : Type := mkISO
  { to : A ~> B;                    (* The forward morphism from A to B *)
    from : B ~> A;                  (* The inverse morphism from B to A *)
    from_to : from ∘ to = id[A];    (* Proof that the inverse composed with the forward is the identity on A *)
    to_from : to ∘ from = id[B];    (* Proof that the forward composed with the inverse is the identity on B *)
  }.

(* Arguments directives to control how the components of an isomorphism are referenced *)
Arguments to {Y A B} _.
Arguments from {Y A B} _.
Arguments from_to {Y A B} _.
Arguments to_from {Y A B} _.

(* Create a hint database for isomorphism proofs *)
Create HintDb iso_db.

(* Add the from_to and to_from proofs to the iso_db for automated rewriting *)
Hint Rewrite @from_to @to_from : iso_db.

(* Tactic to simplify proofs involving isomorphisms by rewriting with iso_db hints *)
Ltac simplify_iso := autorewrite with iso_db in *.

(* Definition of a morphism being an isomorphism (alternative representation) *)
Record is_iso {Y : Category} {A B : Y} (f : A ~> B) : Type := mkISISO
  { inv : B ~> A;                   (* The inverse morphism of f *)
    inv_left : inv ∘ f = id[A];     (* Proof that the inverse composes with f to the identity on A *)
    inv_right : f ∘ inv = id[B];    (* Proof that f composes with the inverse to the identity on B *)
  }.

(* Arguments directives for the components of is_iso *)
Arguments inv {Y A B f} _.
Arguments inv_left {Y A B f} _.
Arguments inv_right {Y A B f} _.

(* Lemma to convert an is_iso proof into an iso proof *)
Program Definition is_iso_to_iso {Y : Category} {A B : Y} (f : A ~> B) (H : is_iso f) : iso A B :=
  {| to := f; from := inv H; |}.
Solve All Obligations with (by destruct H).

(* Lemma to convert an iso proof into an is_iso proof *)
Program Definition iso_to_is_iso {Y : Category} {A B : Y} (H : iso A B) : is_iso (to H) :=
  {| inv := from H; |}.
Solve All Obligations with (by destruct H).

(* Notation for isomorphisms *)
Notation "A ≃ B" := (@iso _ A B)
  (at level 70) : category_scope.

(* Notation for isomorphisms in a specific category C *)
Notation "A ≃[ C ] B" := (@iso C A B)
  (at level 70, only parsing) : category_scope.

(* Lemma to decompose an isomorphism in a product category into component isomorphisms *)
Definition iso_prod_cat {Y Z : Category} {A B : prod_cat Y Z}  (H : A ≃ B) : 
  iso (fst A) (fst B) * iso (snd A) (snd B).
Proof.
  destruct A as [A1 A2], B as [B1 B2]. simpl in *.
  destruct H as [[to1 to2] [from1 from2] H1 H2]. simpl in *.
  split.
  - eapply mkISO with (to := to1) (from := from1).
    + by injection H1.  (* Extract the first component's from_to proof *)
    + by injection H2.  (* Extract the first component's to_from proof *)
  - eapply mkISO with (to := to2) (from := from2).
    + by injection H1.  (* Extract the second component's from_to proof *)
    + by injection H2.  (* Extract the second component's to_from proof *)
Defined.

(* Lemma to combine component isomorphisms into an isomorphism in a product category *)
Definition iso_to_prod_cat {Y Z : Category} {A B : prod_cat Y Z} (H : iso (fst A) (fst B) * iso (snd A) (snd B)) : A ≃ B.
Proof.
  destruct A as [A1 A2], B as [B1 B2]. simpl in *.
  destruct H as [[to1 from1] [to2 from2]]. simpl in *.
  eapply mkISO with (to := prod_mor to1 to2) (from := prod_mor from1 from2).
  - rewrite <- prod_mor_compose.  (* Show that the product morphism's composition equals the identity *)
    unfold prod_mor. simpl.
    by rewrite from_to0 from_to1.  (* Use component from_to proofs *)
  - rewrite <- prod_mor_compose.  (* Similarly for the other direction *)
    unfold prod_mor. simpl.
    by rewrite to_from0 to_from1.  (* Use component to_from proofs *)
Defined.

(* Lemma stating that an isomorphism in a category is also an isomorphism in its opposite category *)
Program Definition iso_op {Y : Category} {A B : Y} (H : A ≃ B) : A ≃[Y ^op] B :=
  {| to := from H; from := to H; |}. (*Use the same morphisms *)
Solve All Obligations with (by destruct H).

(* Lemma for proving equality of isomorphisms based on equality of their components *)
Lemma iso_eq {Y : Category} {A B : Y} (f g : A ≃ B) : to f = to g -> from f = from g -> f = g.
Proof. destruct f, g; simpl; intros -> ->; f_equal; apply proof_irrelevance. Qed.

(* Lemma stating that isomorphisms are symmetric *)
Program Definition iso_sym {Y : Category} {A B : Y} (H : A ≃ B) : B ≃ A :=
  {| to := from H; from := to H; |}. (* Swap the to and from morphisms *)
Solve All Obligations with (by destruct H).

(* Lemma stating that the inverse of an inverse isomorphism is the original *)
Lemma iso_sym_sym {Y : Category} {A B : Y} (H : A ≃[Y] B) : iso_sym (iso_sym H) = H.
Proof. by destruct H. Qed.  (* Directly follows from the definition of iso_sym *)

(* Lemma proving reflexivity of isomorphisms *)
Program Definition iso_refl {Y : Category} {A : Y} : A ≃ A :=
  {| to := id[A]; from := id[A]; |}. (* Use identity morphisms *)
Next Obligation. by simplify_cat. Qed.
Next Obligation. by simplify_cat. Qed.

(* Lemma proving transitivity of isomorphisms *)
Program Definition iso_trans {Y : Category} {A B C : Y} (f : B ≃ C) (g : A ≃ B) : A ≃ C :=
  {| to := to f ∘ to g; from := from g ∘ from f; |}.
Next Obligation. 
  rewrite <- comp_assoc.  (* Rearrange composition to apply from_to proofs *)
  assert (from f ∘ (to f ∘ to g) = (from f ∘ to f) ∘ to g) as -> by (by simplify_cat).
  by rewrite (from_to f) id_left (from_to g).  (* Simplify using associativity and identity laws *)
Qed.
Next Obligation. 
  rewrite <- comp_assoc.  (* Similarly for the other direction *)
  assert (to g ∘ (from g ∘ from f) = (to g ∘ from g) ∘ from f) as -> by (by simplify_cat).
  by rewrite (to_from g) id_left (to_from f).  (* Simplify using associativity and identity laws *)
Qed.

(* Lemma stating that composing an isomorphism with its inverse yields the identity isomorphism *)
Lemma iso_sym_trans_id {Y : Category} {A B : Y} (H : A ≃ B) : iso_trans (iso_sym H) H = iso_refl.
Proof.
  destruct H. unfold iso_trans. simpl.
  apply iso_eq; by simplify_cat.  (* Simplify using category laws to show equality *)
Qed.

(* Helper lemma to rewrite the domain of a morphism using an isomorphism *)
Definition rw_iso_dom {Y : Category} {A B C : Y} (f : A ≃ B) (g : A ~> C) : B ~> C.
Proof. destruct f. eapply compose; eauto. Defined.  (* Compose g with the inverse of f *)

(* Helper lemma to rewrite the codomain of a morphism using an isomorphism *)
Definition rw_iso_cod {Y : Category} {A B C : Y} (f : A ≃ B) (g : C ~> B) : C ~> A.
Proof. destruct f. eapply compose; eauto. Defined.  (* Compose g with the inverse of f *)

(* Lemma for proving equality of isomorphisms based on component equality *)
Lemma iso_inv' {Y : Category} {A B : Y} (f g : A ≃ B) : 
  to f = to g /\ from f = from g -> f = g.
Proof. destruct f, g; simpl; intros [-> ->]; f_equal; apply proof_irrelevance. Qed.

(* Tactic to simplify isomorphism proofs by applying iso_inv' *)
Ltac iso_inv := apply iso_inv'; split; simpl; try simplify_cat.

(* Tactic to rewrite morphisms using isomorphisms in the context *)
Ltac iso_rewrite := repeat match goal with
    | H : ?A ≃ ?B , h : ?A ~> ?C |- _ => apply (rw_iso_dom H)  (* Rewrite domain using H *)
    | H : ?A ≃ ?B , h : ?B ~> ?C |- _ => apply (rw_iso_dom (iso_sym H))  (* Rewrite domain using inverse of H *)
    | H : ?A ≃ ?B , h : ?C ~> ?B |- _ => apply (rw_iso_cod H)  (* Rewrite codomain using H *)
    | H : ?A ≃ ?B , h : ?C ~> ?A |- _ => apply (rw_iso_cod (iso_sym H))  (* Rewrite codomain using inverse of H *)
end.
