From sgdt Require Import ecategory functor efunctor eisomorphism product.
From sgdt Require Import ofe iCOFE icofe_ccc econtractive partial_econtractive ectr_compl.
From sgdt Require Import muF ealgebra banach.

Require Import ssreflect.

(* Definition of ZF efunctor *)
Lemma to_op_ecomp {Y : eCategory} {A B C : Y} (f : A ~~{Y}~> B) (g : B ~~{Y}~> C) :
  to_op_mor (g ∘e f) = to_op_mor f ∘e to_op_mor g.
Proof. reflexivity. Qed.

Lemma to_op_muF {Y : eCategory}  
(F : eFunctorCtrSnd Y^op Y Y) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A B C : eobj[Y]) (f : B ~~{ Y }~> C) (g : A ~~{ Y }~> B) :
  efmap (muF F H) (to_op_mor (f ∘e g)) = efmap (muF F H) (to_op_mor g) ∘e efmap (muF F H) (to_op_mor f).
Proof. rewrite - efmap_ecomp //. Qed.

Lemma ZF_fmap_comp {Y : eCategory} (F : eFunctorCtrSnd Y^op Y Y)
  (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A)) 
  (A B C : Y) (f : B ~~{ Y }~> C) (g : A ~~{ Y }~> B) :
  @ebimap Y^op Y Y F (muF F H A) (muF F H C) A C (efmap (muF F H) (to_op_mor g ∘e to_op_mor f)) (f ∘e g) =
  @ebimap Y^op Y Y F (muF F H B) (muF F H C) B C (efmap (muF F H) (to_op_mor f)) f ∘e @ebimap Y^op Y Y F (muF F H A) (muF F H B) A B (efmap (muF F H) g) (to_op_mor g).
Proof.
  rewrite <- (@to_op_ecomp Y _ _ _ g f).
  rewrite -> (@to_op_muF Y F H _ _ _ f g).
  set (muF := muF F H).
  rewrite -> (@ebimap_ecompose Y^op Y Y F _ _ _ _ _ _ (efmap muF (to_op_mor f)) (efmap muF (to_op_mor g))).
  reflexivity.
Qed.

Lemma ZF_mixin {Y : eCategory} (F : eFunctorCtrSnd Y^op Y Y)
  (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A)): eFunctMixin Y Y (fun A => F (muF F H A, A))
  (fun A B f => ebimap[F] (muF_fmap F H f) f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. apply hom_ne; split ; simpl ; last assumption.
    apply muF_fmap_ne. apply Hfg.
  - intros A . simpl.
    rewrite <-!efmap_muF_eq.
    replace (eid_mor Y tt) with (eid[A] tt) by reflexivity.
    assert (eid{Y} tt = eid{Y^op} tt) as -> by reflexivity.
    rewrite (efmap_id (muF F H)) (@ebimap_id Y^op Y Y F) //.
  - intros A B C f g. 
    apply (@ZF_fmap_comp Y F H A B C f g).
Qed.

Definition ZF {Y : eCategory} (F : eFunctorCtrSnd Y^op Y Y)
  (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A)): eFunctor Y Y := {|
    efobj := fun A : Y => F (muF F H A, A);
    efmap_mor := fun A B f => ebimap[F] (muF_fmap F H f) f;
    efunct_mixin := ZF_mixin F H
  |}.

(* Definition of ZF contractive efunctor *)
Lemma ZF_efmap_ctr {Y : eCategory} `{eCategoryCtrComplete Y}
(F : eFunctorCtr (Y^op × Y) Y) (H2 : forall A : eobj[Y], eInitialAlg (second_efunctor_ctr (CtrToSnd F) A)) :
forall A B : eobj[Y], Contractive (@efmap _ _ (ZF (CtrToSnd F) H2) A B).
Proof.
  intros A B n x y Hxy. simpl.
  unfold CtrToSnd. simpl.
  apply efunct_ctr. split; simpl.
  - rewrite -!efmap_muF_eq. apply hom_ne.
    destruct n  ; first lia.
    eapply ofe_mono with n ; [| lia].
    + apply Hxy; lia.
  - destruct n  ; first lia.
    eapply ofe_mono with n ; [| lia].
    + apply Hxy; lia.
Qed.

Definition ZF_ctr {Y : eCategory} `{eCategoryCtrComplete Y} (F : eFunctorCtr (Y^op × Y) Y)
  (H2 : forall A : eobj[Y], eInitialAlg (second_efunctor_ctr (CtrToSnd F) A)) : eFunctorCtr Y Y :=
  {| efunct := ZF (CtrToSnd F) H2;
     efunct_ctr := ZF_efmap_ctr F H2
  |}.

(* Dialgebra for America-Rutten *)
Lemma america_rutten_dialgebra {Y : eCategory} `{eCategoryCtrComplete Y} 
 (F : eFunctorCtr (Y^op × Y) Y)  :
 { Z : Y & { W : Y & { HZ : F (W, Z) ≃ Z & F (Z, W) ≃ W } } }.
Proof.
  assert (H11 : forall A : Y, eInitialAlg (second_efunctor_ctr (CtrToSnd F) A)).
  { intros A; apply ctr_compl_iso_initial_alg. }

  set Z := fixpointF (ZF_ctr F H11).
  set HZ := fixpointF_iso (ZF_ctr F H11).
  set W := (muF (CtrToSnd F) H11) Z.
  assert (F (Z, W) ≃ W) as H2 .
  { eapply eiso_sym ; apply (muF_obj_iso (CtrToSnd F) H11 Z). }
  by exists Z, W, HZ.
Qed.

(**
   * Free Dialgebra unique
   In this file, we prove that if F : (Y^op × Y) →  Y is a contractive functor
   such that there exists A, B : Y with F (A, B) ≃ B and F (B, A) ≃ A, then
   (A, B) constitutes an initial F-dialgebra. Moreover, A ≃ B
   (which is the result we will need in the proof of the General America Rutten)
*)
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

Theorem general_america_rutten {Y : eCategory} `{eCategoryCtrComplete Y} 
 (F : eFunctorCtr (Y^op × Y) Y)  :
  { Z : Y & F (Z, Z) ≃ Z }.
Proof.
  destruct (america_rutten_dialgebra F) as [Z [W [HZ HZW]]].
  exists Z.
  eapply eiso_trans ; first exact HZ.
  apply efunctor_preserve_eiso, eiso_to_eprod_cat;
  split ; [apply eiso_op, (dialgebra_unique F HZW HZ) | apply eiso_refl].
Qed.

Theorem general_america_rutten_unique {Y : eCategory} `{eCategoryCtrComplete Y} 
 (F : eFunctorCtr (Y^op × Y) Y) (H1 H2 : { Z : Y & F (Z, Z) ≃ Z }) :
  projT1 H1 ≃  projT1 H2.
Proof.
  destruct H1 as [A HA], H2 as [B HB] ; simpl.
  unshelve epose (T1 := _ : tensor_prod (A ~~> B, B ~~> A) -c> tensor_prod (A ~~> B, B ~~> A)).
  { unshelve econstructor.
    - intros [h1 h2] ; split.
      +  exact (eto HB ∘e ebimap[F] h2 h1 ∘e efrom HA).
      +  exact (eto HA ∘e ebimap[F] h1 h2 ∘e efrom HB).
    - intros m [f1 f2] [g1 g2] Hfg. split.
      + unfold fst; apply hom_ne; split ; last reflexivity.
        unfold fst; apply hom_ne; split ; first reflexivity.
        apply efunct_ctr. intros k Hk. destruct (Hfg k Hk) as [Hf Hg].
        by split.
      + unfold snd; apply hom_ne; split ; last reflexivity.
        unfold fst; apply hom_ne; split ; first reflexivity.
        apply efunct_ctr. intros k Hk. destruct (Hfg k Hk) as [Hf Hg].
        by split.
  }
  destruct (ibanach_fixed_point T1) as [[to' from'] Hf].
  unfold T1 in Hf ; simpl in Hf.
  injection Hf as Hto' Hfrom'.

  unshelve epose (T2 := _ : tensor_prod (A ~~> A, B ~~> B) -c> tensor_prod (A ~~> A, B ~~> B)).
  {
    unshelve econstructor.
    - intros [h1 h2].
      split.
      +  exact (eto HA ∘e ebimap[F] h1 h1 ∘e efrom HA).
      +  exact (eto HB ∘e ebimap[F] h2 h2 ∘e efrom HB).
    - intros m [f1 f2] [g1 g2] Hfg. split.
      + unfold fst; apply hom_ne; split ; last reflexivity.
        unfold fst; apply hom_ne; split ; first reflexivity.
        apply efunct_ctr. intros k Hk. destruct (Hfg k Hk) as [Hf Hg].
        by split.
      + unfold snd; apply hom_ne; split ; last reflexivity.
        unfold fst; apply hom_ne; split ; first reflexivity.
        apply efunct_ctr. intros k Hk. destruct (Hfg k Hk) as [Hf Hg].
        by split.
  }
  set idT := ibanach_fixed_point T2.

  unshelve epose (H3 := _ : {y : tensor_prod (A ~~> A, B ~~> B) & y = T2 y}).
  {
    exists (eprod_mor (eid{Y} tt) (eid{Y} tt)).
    by rewrite /eprod_mor /T2 /= !ebimap_id !ecomp_eid_right !eto_from.
  }

  assert (projT1 idT = projT1 H3) as H4.
  { apply fixpoint_unique. }

  unshelve epose (H5 := _ : {y : tensor_prod (A ~~> A, B ~~> B) & y = T2 y}).
  {
    exists (eprod_mor  (from' ∘e to') (to' ∘e from')).
    rewrite /eprod_mor /T2 /=. f_equal.
    - rewrite {1}Hto' {1}Hfrom'.
      rewrite !ecomp_assoc.
      rewrite -(@ecomp_assoc _ _ _ _ _ (efrom HB) _ _) efrom_to ecomp_eid_left.
      by rewrite ebimap_ecompose !ecomp_assoc.
    - rewrite {1}Hto' {2}Hfrom'.
      rewrite !ecomp_assoc.
      rewrite -(@ecomp_assoc _ _ _ _ _ (efrom HA) _ _) efrom_to ecomp_eid_left.
      by rewrite ebimap_ecompose !ecomp_assoc.
  }

  assert (projT1 H5 = projT1 H3) as H6. 
  { apply fixpoint_unique. }

  rewrite /= /eprod_mor in H6.
  injection H6 as from_to to_from .
  refine {| eto := to' ; efrom := from' ; eto_from := to_from ; efrom_to := from_to |}.
Qed. 
