From sgdt Require Import category functor isomorphism.
From Coq Require Import ssreflect FunctionalExtensionality PropExtensionality.

(* Natural Transformation *)

(* Definition of natural transformation between functors *)
Record NatTrans {Y Z : Category} (F G : Functor Y Z) := mkNAT {
  nt (A : Y) : F A ~> G A ; (* The component of the natural transformation at A *)
  commutes {A B : Y} (f : A ~> B) : (* The naturality square commutes *)
    nt B ∘ fmap F f = fmap G f ∘ nt A 
}.

(* Coercion to treat a natural transformation as a function on objects *)
Coercion nt : NatTrans >-> Funclass.

(* Arguments directive to control simplification of nt *)
Arguments nt {Y Z F G} T _ : rename.

(* Create a hint database for natural transformation proofs *)
Create HintDb nt.

(* Add the commutation property to the nt hint database for automated rewriting *)
Hint Rewrite @commutes : nt.

(*
  Tactic to simplify proofs involving natural transformations by rewriting with
  nt, funct_db, and cat_db hints 
  - funct_db contains rewriting rules for functors, ensuring simplification of
   functorial mappings. 
  - cat_db contains general category-theoretic rewriting rules, such as
   associativity and identity properties.
*)
Ltac simplify_nt := simpl ; autorewrite with nt funct_db cat_db.

(* Lemma showing equality of natural transformations is given by pointwise equality *)
Lemma nat_eq  {Y Z : Category} {F G : Functor Y Z} (T S : NatTrans F G) :
    (forall A, nt T A = nt S A) <-> T = S.
Proof.
  split ; intros H.
  - destruct T, S; simpl in *.
    assert (nt0 = nt1) as -> by (apply functional_extensionality_dep; apply H).
    f_equal; apply proof_irrelevance.
  - subst. intros. reflexivity.
Qed.

(* Identity natural transformation *)
Program Definition id_transformation {Y Z : Category} (F : Functor Y Z) : NatTrans F F := {|
  nt A := @id Z (F A)
|}.
Next Obligation. by simplify_nt. Qed.

(* Composition of natural transformations *)
Program Definition compose_nat {Y Z : Category} {F G H : Functor Y Z}
 (T : NatTrans G H) (S : NatTrans F G) : NatTrans F H := {|
  nt A := nt T A ∘ nt S A
 |}.
Next Obligation. rewrite comp_assoc -comp_assoc; by simplify_nt. Qed.

Notation "F  ∘[NAT]  G" := (compose_nat F G) (at level 40) : category_scope.

(* Composition of natural transformations is associative *)
Lemma comp_nat_assoc {Y Z : Category} {F G H I : Functor Y Z} (T : NatTrans H I) (S : NatTrans G H) (R : NatTrans F G) :
  (T ∘[NAT] S) ∘[NAT] R = T ∘[NAT] (S ∘[NAT] R).
Proof. apply nat_eq; intros; by simplify_nt. Qed.

(* Identity natural transformation is a left and right identity for composition *)
Lemma id_left_nat {Y Z : Category} {F G : Functor Y Z} (T : NatTrans F G) : id_transformation G ∘[NAT] T = T.
Proof. apply nat_eq; intros; by simplify_nt. Qed.

Lemma id_right_nat {Y Z : Category} {F G : Functor Y Z} (T : NatTrans F G) : T ∘[NAT] id_transformation F = T.
Proof. apply nat_eq; intros; by simplify_nt. Qed.

(* Additional hints for natural transformations *)
Hint Rewrite @comp_nat_assoc : nt.
Hint Rewrite @id_left_nat @id_right_nat : nt.

(* NATURAL ISOMORPHISMS *)
Record NatIso {Y Z : Category} (F G : Functor Y Z) := mkNATISO {
    to_nt_iso : NatTrans F G ;    (* The forward natural transformation from F to G *)
    from_nt_iso : NatTrans G F ;  (* The inverse natural transformation from G to F *)
    to_from_nt : (* Proof that the forward composed with the inverse is the identity on G *)
      to_nt_iso ∘[NAT] from_nt_iso = id_transformation G ; 
    from_to_nt : (* Proof that the inverse composed with the forward is the identity on F *)
      from_nt_iso ∘[NAT] to_nt_iso = id_transformation F  
  }.
(* Arguments directive to control simplification of to_nt_iso and from_nt_iso *)
Arguments to_nt_iso {Y Z F G} T : rename.
Arguments from_nt_iso {Y Z F G} T : rename.
Arguments to_from_nt {Y Z F G} T : rename.
Arguments from_to_nt {Y Z F G} T : rename.

Notation "F ≅ G" := (NatIso F G) (at level 70) : category_scope.

(* Natural isomorphisms are reflexive *)
Program Definition nat_iso_refl {Y Z : Category} (F : Functor Y Z) : F ≅ F := {|
  to_nt_iso := id_transformation F ;
  from_nt_iso := id_transformation F
|}.
Next Obligation. by simplify_nt. Qed.
Next Obligation. by simplify_nt. Qed.

(* Natural isomorphisms are symmetric *)
Program Definition nat_iso_sym {Y Z : Category} {F G : Functor Y Z} (H : F ≅ G) : G ≅ F := {|
  to_nt_iso := from_nt_iso H ;
  from_nt_iso := to_nt_iso H
 |}.
Solve Obligations with by destruct H.

(* Natural isomorphisms are transitive *)
Program Definition nat_iso_trans {Y Z : Category} {F G H : Functor Y Z} (H1 : G ≅ H) (H2 : F ≅ G) : F ≅ H := {|
  to_nt_iso := to_nt_iso H1 ∘[NAT] to_nt_iso H2 ;
  from_nt_iso := from_nt_iso H2 ∘[NAT] from_nt_iso H1
 |}.
Next Obligation. 
  by rewrite comp_nat_assoc -(comp_nat_assoc (to_nt_iso H2) _ _) to_from_nt id_left_nat to_from_nt.
Qed.
Next Obligation. 
  by rewrite comp_nat_assoc -(comp_nat_assoc (from_nt_iso H1) _ _) from_to_nt id_left_nat from_to_nt.
Qed.

(* Natural ismorphisms define isomorphisms for every pair of objects *)
Lemma nat_iso_to_iso {Y Z : Category} {F G : Functor Y Z} (H : F ≅ G) : forall A : Y, F A ≃ G A.
Proof.
  intros. destruct H as [to from H1 H2].
  eapply mkISO with (to := to A) (from := from A).
  - eapply nat_eq in H2.
    apply H2.
  - eapply nat_eq in H1.
    apply H1.
Qed.
