From sgdt Require Import functor ecategory efunctor eisomorphism product.
From sgdt Require Import ofe banach econtractive ectr_compl.
Require Import ssreflect.

Lemma dialgebra_unique {Y : eCategory} `{eCategoryCtrComplete Y} (F : eFunctorCtr (Y^op × Y) Y) 
  {A B : Y} (H1 : F (A, B) ≃ B) (H2 : F (B, A) ≃ A) :
  A ≃ B.
Proof.
  (* from *)
  unshelve epose (T1 := _ : B ~~> A -c> B ~~> A).
  { exists (fun h : B ~~> A => (eto H2 ∘e ebimap[F] h h ∘e efrom H1)).
    intros n x y Hxy.
    apply hom_ne ; split ; simpl.
    - apply hom_ne ; split ; simpl.
      + reflexivity.
      + apply efunct_ctr ; split ; simpl ; by apply Hxy.
    - reflexivity.
  }
  destruct (ibanach_fixed_point T1) as [from' Hfrom'].
  (* to *)
  unshelve epose (T2 := _ : A ~~> B -c> A ~~> B).
  { exists (fun h : A ~~> B => (eto H1 ∘e ebimap[F] h h ∘e efrom H2)).
    intros n x y Hxy.
    apply hom_ne ; split ; simpl. 
    - apply hom_ne ; split ; simpl ; first reflexivity.
      apply efunct_ctr ; split ; simpl ; by apply Hxy.
    - reflexivity.
  }
  destruct (ibanach_fixed_point T2) as [to' Hto'].

  unshelve epose (T3 := _ : tensor_prod (B ~~> B, A ~~> A) -c> tensor_prod ((B ~~> B), (A ~~> A))).
  {
    unshelve epose (T3' := _ : tensor_prod (B ~~> B, A ~~> A) -> tensor_prod ((B ~~> B), (A ~~> A))).
    {
      intros [h1 h2].
      split.
      -  exact (eto H1 ∘e ebimap[F] h2 h1 ∘e efrom H1).
      -  exact (eto H2 ∘e ebimap[F] h1 h2 ∘e efrom H2).
    }

    exists T3'.
    intros n [x1 x2] [y1 y2] Hxy.
    split; simpl.
    - apply hom_ne ; split ; simpl ; last reflexivity.
      apply hom_ne ; split ; simpl ; first reflexivity.
      apply efunct_ctr ; split ; simpl ; by apply Hxy.
    - apply hom_ne ; split ; simpl ; last reflexivity.
      apply hom_ne ; split ; simpl ; first reflexivity.
      apply efunct_ctr ; split ; simpl ; by apply Hxy.
  } 
  set idT := ibanach_fixed_point T3.

  unshelve epose (H3 := _ : {y : tensor_prod (B ~~> B, A ~~> A) & y = T3 y}).
  {
    exists (eprod_mor (eid{Y} tt) (eid{Y} tt)).
    by rewrite /eprod_mor /T3 /= !ebimap_id !ecomp_eid_right !eto_from.
  }

  assert (projT1 idT = projT1 H3) as H4.
  { apply fixpoint_unique. }

  unshelve epose (H5 := _ : {y :  tensor_prod (B ~~> B, A ~~> A) & y = T3 y}).
  {
    exists (eprod_mor (to' ∘e from') (from' ∘e to')).
    rewrite /eprod_mor {1}Hto' {1}Hfrom' {2}Hto' {2}Hfrom'.
    rewrite /T3 /T2 /T1 /= /T1.
    rewrite !ecomp_assoc.
    rewrite -(@ecomp_assoc _ _ _ _ _ (efrom H2) _ _) efrom_to ecomp_eid_left.
    rewrite -(@ecomp_assoc _ _ _ _ _ (efrom H1) _ _) efrom_to ecomp_eid_left.
    rewrite -(@ecomp_assoc _ _ _ _ _ _ _ (efrom H1)) -ebimap_ecompose.
    rewrite -(@ecomp_assoc _ _ _ _ _ _ _ (efrom H2)) -ebimap_ecompose.
    reflexivity.
  }

  assert (projT1 H5 = projT1 H3) as H6. 
  { apply fixpoint_unique. }

  rewrite /= /eprod_mor in H6.
  injection H6 as to_from from_to.
  refine {| eto := to' ; efrom := from' ; eto_from := to_from ; efrom_to := from_to |}.
Qed.
