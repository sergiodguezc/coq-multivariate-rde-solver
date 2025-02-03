From sgdt Require Import category functor terminal isomorphism.
From Coq Require Import ssreflect.

(* Definition of a category with binary products *)
Class FiniteProducts (Y : Category) `(Terminal Y) := mkProducts
  { p_prod : Y -> Y -> Y  (* Binary product of objects *)
    where "A × B" := (p_prod A B) ;

    fork {A B C : Y} (f : C ~> A) (g : C ~> B) : C ~> A × B;  (* Fork morphism combining f and g *)

    p_fst {A B : Y} : A × B ~> A;  (* First projection morphism *)
    p_snd {A B : Y} : A × B ~> B;  (* Second projection morphism *)

    prod_univ {A B C : Y} (f : C ~> A) (g : C ~> B) (h : C ~> A × B) :
      h = fork f g <-> f = p_fst ∘ h /\ g = p_snd ∘ h;  (* Universal property of products *)
  }.

Notation "Y × Z" := (@p_prod _ _ _ Y Z)
  (at level 40, left associativity) : object_scope.

Notation "<| f , g |>" := (fork f g)
  (at level 40, no associativity) : morphism_scope.

(* Lemma stating that precomposing a fork with a morphism is equivalent to forking the compositions *)
Lemma fork_precompose {Y : Category} `{FiniteProducts Y} {A B C D : Y} (f : C ~> A) (g : C ~> B) (h : D ~> C)  :
  <| f, g |> ∘ h = <| f ∘ h, g ∘ h |>.
Proof.
  assert (f = p_fst ∘ (<| f, g |>) /\ g = p_snd ∘ <| f, g |>) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  apply prod_univ. split; simplify_cat.
  - by rewrite <- H1.  (* Rewrite using the first projection *)
  - by rewrite <- H2.  (* Rewrite using the second projection *)
Qed.

(* Lemma stating that the first projection of a fork is the first component *)
Lemma p_fst_fork {Y : Category} `{FiniteProducts Y} {A B C : Y} (f : C ~> A) (g : C ~> B) :
  p_fst ∘ (<| f, g |>) = f.
Proof.
  assert (f = p_fst ∘ (fork f g) /\ g = p_snd ∘ (fork f g)) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  symmetry. apply H1.  (* Apply the first projection property *)
Qed.

(* Lemma stating that the second projection of a fork is the second component *)
Lemma p_snd_fork {Y : Category} `{FiniteProducts Y} {A B C : Y} (f : C ~> A) (g : C ~> B) :
  p_snd ∘ (<| f, g |>) = g.
Proof.
  assert (f = p_fst ∘ (fork f g) /\ g = p_snd ∘ (fork f g)) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  symmetry. apply H2.  (* Apply the second projection property *)
Qed.

(* Lemma stating that two forks are equal if and only if their components are equal *)
Lemma fork_inv {Y : Category} `{FiniteProducts Y} {A B C : Y} (f : C ~> A) (g : C ~> A)  (h : C ~> B) (i : C ~> B)  :
  <| f, h |> = <| g, i |> <-> f = g /\ h = i.
Proof.
  split ; intros.
  - split.
    + assert (f = p_fst ∘ <| f, h |>) by (symmetry ; apply p_fst_fork).
      assert (g = p_fst ∘ <| g, i |>) by (symmetry ; apply p_fst_fork).
      rewrite H1 in H2. by rewrite H2.  (* Prove equality of the first components *)
    + assert (h = p_snd ∘ <| f, h |>) by (symmetry ; apply p_snd_fork).
      assert (i = p_snd ∘ <| g, i |>) by (symmetry ; apply p_snd_fork).
      rewrite H1 in H2. by rewrite H2.  (* Prove equality of the second components *)
  - destruct H1. by rewrite H1 H2.  (* Rewrite using the equalities *)
Qed.

(* Definition of a morphism in the product category *)
Definition times_mor {Y : Category} `{FiniteProducts Y} {A B C D : Y} (f : A ~> B) (g : C ~> D) :
  A × C ~> B × D := <| (f ∘ p_fst), (g ∘ p_snd) |>.

(* Lemma stating that times_mor is equivalent to forking the compositions *)
Lemma times_mor_eq {Y : Category} `{FiniteProducts Y} {A B C D : Y} (f : A ~> B) (g : C ~> D) :
  times_mor f g = <| (f ∘ p_fst), (g ∘ p_snd) |>.
Proof. reflexivity. Qed.

(* Lemma stating that the identity morphism in the product category is the identity *)
Lemma times_mor_id {Y : Category} `{FiniteProducts Y} {A B : Y} :
  times_mor id[A] id[B] = id[A × B].
Proof.
  unfold times_mor. simplify_cat.
  assert (id[A × B] = fork p_fst p_snd <-> p_fst = p_fst ∘ id[A × B] /\ p_snd = p_snd ∘ id[A × B]) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  symmetry. apply H2. split; by simplify_cat.  (* Simplify using category laws *)
Qed.

(* Lemma stating that forking the projections yields the identity *)
Lemma p_fst_p_snd_id {Y : Category} `{FiniteProducts Y} {A B : Y} :
  <| p_fst, p_snd |> = id[A × B].
Proof.
  assert (forall A B (f : hom Y A B), id{Y} ∘ f = f) as H1.
  { intros. by simplify_cat. }  (* Simplify using category laws *)
  set (H2 := H1 (A × B) A p_fst).
  set (H3 := H1 (A × B) B p_snd).
  rewrite -H2 -H3 -times_mor_eq.
  apply times_mor_id.  (* Apply the identity property of times_mor *)
Qed.

(* Definition of the first morphism in the product category *)
Definition first_mor {Y : Category} `{FiniteProducts Y} {A B C : Y} (f : A ~> B) :
  A × C ~> B × C := <| f ∘ p_fst, p_snd |>.

(* Definition of the second morphism in the product category *)
Definition second_mor {Y : Category} `{FiniteProducts Y} {A B C : Y} (f : A ~> B) :
  C × A ~> C × B := <| p_fst, f ∘ p_snd |>.

(* Lemma stating that first_mor preserves composition *)
Lemma first_mor_comp {Y : Category} `{FiniteProducts Y} {A B C D : Y} (f : B ~> C) (g : A ~> B) :
  first_mor (C:=D) (f ∘ g) = first_mor f ∘ first_mor g.
Proof.
  rewrite /first_mor fork_precompose.
  apply fork_inv; split.
  - by rewrite -!comp_assoc p_fst_fork.  (* Simplify using associativity and projections *)
  - by rewrite p_snd_fork.  (* Simplify using projections *)
Qed.

(* Lemma stating that second_mor preserves composition *)
Lemma second_mor_comp {Y : Category} `{FiniteProducts Y} {A B C D : Y} (f : B ~> C) (g : A ~> B) :
  second_mor (C:=D) (f ∘ g) = second_mor f ∘ second_mor g.
Proof.
  rewrite /second_mor fork_precompose.
  apply fork_inv; split.
  - by rewrite p_fst_fork.  (* Simplify using projections *)
  - by rewrite -!comp_assoc p_snd_fork.  (* Simplify using associativity and projections *)
Qed.

(* Create a HintDB for the category laws *)
Create HintDb fork_db.

Hint Rewrite @first_mor_comp @second_mor_comp : fork_db.
Hint Unfold first_mor second_mor : fork_db.
Hint Unfold times_mor : fork_db.
Hint Rewrite @fork_precompose @p_fst_fork @p_snd_fork @p_fst_p_snd_id : fork_db.
Hint Rewrite @times_mor_eq @times_mor_id : fork_db.

(* Tactic to simplify proofs involving forks and products *)
Ltac simplify_fork := autorewrite with fork_db cat_db ; try done.

(* Tactic to unfork and simplify proofs *)
Ltac unfork' := match goal with
    | |- <| _ , _ |> = <| _ , _ |> => apply fork_inv; split ; simplify_fork
    | |- <| _ , _ |> = id{_} => rewrite <- p_fst_p_snd_id 
    | |- id{_} = <| _ , _ |> => rewrite <- p_fst_p_snd_id
    | |- _ => try rewrite <- comp_assoc ; simplify_fork
  end.

Ltac unfork := repeat unfork'.

(* Lemma stating that times_mor preserves composition *)
Lemma times_mor_comp {Y : Category} `{FiniteProducts Y} {A B C D E F : Y} (f1 : A ~> B) (f2 : C ~> D) (g1 : B ~> E) (g2 : D ~> F) :
  (times_mor g1 g2) ∘[ Y] (times_mor f1 f2) = times_mor (g1 ∘ f1) (g2 ∘ f2).
Proof.
  rewrite !times_mor_eq.
  unfork.  (* Simplify using the unfork tactic *)
Qed.

(* CONSTRUCTIONS OF CATEGORIES *)

(* Isomorphism in the category with finite products *)

(* Lemma stating that the product is symmetric *)
Lemma prod_sym {Y : Category} `{FiniteProducts Y} {A B : Y} :
  A × B ≃ B × A.
Proof.
  eapply mkISO with (to := <| p_snd, p_fst |>) (from := <| p_snd, p_fst |>) ; simpl ;
  unfork.  (* Simplify using the unfork tactic *)
Defined.

(* Lemma stating that the product is associative *)
Lemma prod_assoc {Y : Category} `{FiniteProducts Y} {A B C : Y} :
  (A × B) × C ≃ A × (B × C).
Proof.
  eapply mkISO with (to := <| p_fst ∘ p_fst, <| p_snd ∘ p_fst, p_snd |> |>)
      (from := fork (fork p_fst (p_fst ∘ p_snd)) (p_snd ∘ p_snd)) ;
      simpl ; unfork ; symmetry ; apply prod_univ; unfork.  (* Simplify using the unfork tactic *)
Defined.

(* Lemma stating that the product of the terminal object and an object is isomorphic to the object *)
Lemma prod_1_l {Y : Category} `{FiniteProducts Y} (A : Y) : 1 × A ≃ A.
Proof.
  assert (one = p_fst ∘ fork one id[A] /\ id[A] = p_snd ∘ fork one id[A]) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  eapply mkISO with (to := p_snd) (from := <| one, id[A] |>) ; simpl .
  - unfork.
    assert (p_fst = ![ 1 × A ]) as -> by apply one_unique.  (* Use the uniqueness of the terminal morphism *)
    apply one_unique.
  - symmetry. apply H2. 
Defined.

(* Lemma stating that the product of an object and the terminal object is isomorphic to the object *)
Lemma prod_1_r {Y : Category} `{FiniteProducts Y} (A : Y) : A × 1 ≃ A.
Proof.
  assert (id[A] = p_fst ∘ fork id[A] one  /\ one = p_snd ∘ fork id[A] one) as [H1 H2].
  { by apply prod_univ. }  (* Use the universal property of products *)
  eapply mkISO with (to := p_fst) (from := <| id[A], one |>) ; simpl .
  - unfork.
    assert (p_snd = ![ A × 1 ]) as -> by apply one_unique.  (* Use the uniqueness of the terminal morphism *)
    apply one_unique.
  - symmetry. apply H1.
Defined.
