From sgdt Require Import axioms ecategory ofe iCOFE icofe_ccc.
Require Import ssreflect.

(*  Definition of isomorphism between objects *)
Open Scope ofe_category_scope.
Open Scope ofe_morphism_scope.


Record eiso {Y : eCategory} (A B : Y) : Type := mkEISO
  { eto : A ~~> B;
    efrom : B ~~> A;
    efrom_to : efrom ∘e eto = eid[A] tt;
    eto_from : eto ∘e efrom = eid[B] tt;
  }.

Arguments eto {Y A B} _.
Arguments efrom {Y A B} _.
Arguments efrom_to {Y A B} _.
Arguments eto_from {Y A B} _.

Create HintDb eiso_db.

Hint Rewrite @efrom_to @eto_from : iso_db.

Ltac simplify_eiso := autorewrite with eiso_db in *.


(* Definition of a morphism being an isomorphism *)
Record is_eiso {Y : eCategory} {A B : Y} (f : A ~~> B) : Type := mkISEISO
  { einv : B ~~> A;
    einv_left : einv ∘e f = eid[A] tt;
    einv_right : f ∘e einv = eid[B]tt;
  }.

Arguments einv {Y A B f} _.
Arguments einv_left {Y A B f} _.
Arguments einv_right {Y A B f} _.

Lemma is_eiso_to_eiso {Y : eCategory} {A B : Y} (f : A ~~> B) (H : is_eiso f) : eiso A B.
Proof.
    eapply mkEISO with (eto := f) (efrom := einv H).
    - by apply einv_left.
    - by apply einv_right.
Defined.

Lemma eiso_to_is_eiso {Y : eCategory} {A B : Y} (H : eiso A B) : is_eiso (eto H).
Proof.
  eapply mkISEISO with (einv := efrom H).
  - by apply efrom_to.
  - by apply eto_from.
Defined.

Notation "A ≃ B" := (@eiso _ A B)
  (at level 70) : ofe_category_scope.

Notation "A ≃[ C ] B" := (@eiso C A B)
  (at level 70, only parsing) : ofe_category_scope.

Lemma eiso_eprod_cat {Y Z : eCategory} {A B : eprod_cat Y Z}  (H : A ≃ B) : 
  eiso (fst A) (fst B) * eiso (snd A) (snd B).
Proof.
  destruct A as [A1 A2], B as [B1 B2]. simpl in *.
  destruct H as [[to1 to2] [from1 from2] H1 H2]. simpl in *.
  split.
  - eapply mkEISO with (eto := to1) (efrom := from1).
    + by injection H1.
    + by injection H2.
  - eapply mkEISO with (eto := to2) (efrom := from2).
    + by injection H1.
    + by injection H2.
Defined.

Lemma eiso_to_eprod_cat {Y Z : eCategory} {A B : eprod_cat Y Z} (H : eiso (fst A) (fst B) * eiso (snd A) (snd B)) : A ≃ B.
Proof.
  destruct A as [A1 A2], B as [B1 B2]. simpl in *.
  destruct H as [[to1 from1] [to2 from2]]. simpl in *.
  unfold ecomp in *.
  eapply mkEISO with (eto := eprod_mor to1 to2) (efrom := eprod_mor from1 from2).
  - unfold ecomp in *. rewrite - eprod_mor_ecompose.
    unfold eprod_mor. 
    by rewrite efrom_to0 efrom_to1.
  - unfold ecomp in *.
    rewrite - eprod_mor_ecompose.
    unfold eprod_mor.
    by rewrite eto_from0 eto_from1.
Defined.

Lemma eiso_op {Y : eCategory} {A B : Y} (H : A ≃ B) : A ≃[Y ^op] B.
Proof.
  destruct H as [to from H1 H2].
  unshelve eapply mkEISO with (eto := _) (efrom := _).
  - exact from.
  - exact to.
  - apply H1.
  - apply H2.
Defined.

Lemma eiso_eq {Y : eCategory} {A B : Y} (f g : A ≃ B) : eto f = eto g -> efrom f = efrom g -> f = g.
Proof. destruct f, g. simpl. intros -> ->. f_equal; apply proof_irrelevance. Qed.

Lemma eiso_sym {Y : eCategory} {A B : Y} (H : A ≃ B) : B ≃ A.
Proof.
  exists (efrom H) (eto H).
  - by apply eto_from.
  - by apply efrom_to.
Defined.

Lemma eiso_sym_sym {Y : eCategory} {A B : Y} (H : A ≃[Y] B) : eiso_sym (eiso_sym H) = H.
Proof. by destruct H. Qed.

Lemma eiso_refl {Y : eCategory} {A : Y} : A ≃ A.
Proof.
  eapply mkEISO with (eto := eid[A] tt) (efrom := eid[A] tt); unfold ecomp ; by simplify_ecat.
Defined.

Lemma eiso_trans {Y : eCategory} {A B C : Y} (f : B ≃ C) (g : A ≃ B) : A ≃ C.
Proof.
  eapply mkEISO with (eto := eto f ∘e eto g) (efrom := efrom g ∘e efrom f) .
  - rewrite <- ecomp_assoc.
    assert (((efrom g ∘e efrom f) ∘e eto f) = (efrom g  ∘e (efrom f ∘e eto f))) as -> by (by simplify_ecat).
    by rewrite (efrom_to f) {2}/ecomp eid_right (efrom_to g).
  - rewrite <- ecomp_assoc.
    assert (((eto f ∘e eto g) ∘e efrom g) = (eto f ∘e (eto g ∘e efrom g))) as -> by (by simplify_ecat).
    by rewrite (eto_from g) {2}/ecomp eid_right (eto_from f).
Defined.

Lemma iso_sym_trans_id {Y : eCategory} {A B : Y} (H : A ≃ B) : eiso_trans (eiso_sym H) H = eiso_refl.
Proof.
  destruct H. unfold eiso_trans. simpl.
  apply eiso_eq; by simplify_ecat.
Qed.

Lemma rw_eiso_dom {Y : eCategory} {A B C : Y} (f : A ≃ B) (g : A ~~> C) : B ~~> C.
Proof.
  destruct f as [eto efrom H1 H2].
  exact (g ∘e efrom).
Defined.



Lemma rw_eiso_cod {Y : eCategory} {A B C : Y} (f : A ≃ B) (g : C ~~> B) : C ~~> A.
Proof.
  destruct f as [eto efrom H1 H2].
  exact (efrom ∘e g).
Defined.

Lemma eiso_inv' {Y : eCategory} {A B : Y} (f g : A ≃ B) : 
  eto f = eto g /\ efrom f = efrom g -> f = g.
Proof. destruct f, g. simpl. intros [-> ->]. f_equal; apply proof_irrelevance. Qed.

Ltac eiso_inv := apply eiso_inv'; split; simpl; try simplify_ecat.

Ltac eiso_rewrite := repeat match goal with
    | H : ?A ≃ ?B , h : ?A ~~> ?C |- _ => apply (rw_eiso_dom H)
    | H : ?A ≃ ?B , h : ?B ~~> ?C |- _ => apply (rw_eiso_dom (eiso_sym H))
    | H : ?A ≃ ?B , h : ?C ~~> ?B |- _ => apply (rw_eiso_cod H)
    | H : ?A ≃ ?B , h : ?C ~~> ?A |- _ => apply (rw_eiso_cod (eiso_sym H))
end.

