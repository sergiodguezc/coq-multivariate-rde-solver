From sgdt Require Import ecategory efunctor ealgebra ofe banach econtractive.
From sgdt Require Import partial_econtractive eisomorphism ectr_compl.
From sgdt Require Import einstances icofe_monoidal.

Require Import ssreflect.

Definition second_efunctor_ctr {Y Z : eCategory} (F : eFunctorCtrSnd Y Z Z)
  (A : Y) : eFunctorCtr Z Z := toeFunctorCtr (second_efunctor_ctr_partial F A).

Definition muF_obj {Y Z : eCategory} (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A)) 
  : Y -> Z :=
  fun A => lfixpointF (second_efunctor_ctr F A)(H A).


Lemma muF_obj_iso {Y Z : eCategory} (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A : Y) : muF_obj F H A ≃ F (A, muF_obj F H A).
Proof.
  unfold muF_obj. 
  set (H2 := lfixpointF_iso (second_efunctor_ctr F A)).
  apply eiso_sym.
  apply H2.
Defined.

Lemma iso_T  {Y Z : eCategory} (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A : Y) 
  : (fun y : eobj[Z] => second_efunctor_ctr F A y ≃ y) (lfixpointF (second_efunctor_ctr F A) (H A)).
Proof.
  exact (lfixpointF_iso (second_efunctor_ctr F A) (H A)).
Qed.


  (* := fun h : muF_obj F A -n> muF_obj F B => to (projT2 (icofe_ctr_compl (second_functor_ctr F B))) ∘ bimap[F] f (id{iCOFE}) ∘ bimap[F] (id{iCOFE}) h ∘ from (projT2 (icofe_ctr_compl (second_functor_ctr F A))). *)
Definition T {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A B : Y) (f : A ~~{Y}~> B) : muF_obj F H A ~~> muF_obj F H B -c> muF_obj F H A ~~> muF_obj F H B.
Proof.
  unshelve refine {| ctr_mor := _ |}.
  - intros h.
    exact (eto (iso_T F H B) ∘e ebimap[F] f (eid{Z} tt) ∘e ebimap[F] (eid{Y} tt) h ∘e efrom (iso_T F H A)).
  - intros n x y Hxy.
    unfold ebimap.
    apply hom_ne. split ; last reflexivity.
    apply hom_ne; split ; simpl.
    + apply hom_ne. split ; first reflexivity.
      apply efmap_mor_ne. split ; simpl ; reflexivity.
    + by apply snd_funct_ctr.
Defined.

Lemma T_def {Y Z : eCategory}
    (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
    (A B : Y)
    (f : A ~~{Y}~> B) (h : muF_obj F H A ~~> muF_obj F H B) :
    T F H A B f h = eto (iso_T F H B) ∘e ebimap[F] f (eid{Z} tt) ∘e ebimap[F] (eid{Y} tt) h ∘e efrom (iso_T F H A).
Proof. reflexivity. Qed.

Lemma muF_fmap' {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  {A B : Y}
  (f : A ~~{Y}~> B) :
  { h : muF_obj F H A ~~> muF_obj F H B & h = T F H A B f h }.
Proof.
  destruct (ibanach_fixed_point (T F H A B f)) as [mFf HmFf].
  unfold muF_obj.
  exists mFf.
  exact HmFf.
Defined.

Definition muF_fmap {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
 {A B : Y} (f : A ~~{Y}~> B) := projT1 (muF_fmap' F H f).

Ltac solve_hom_ne :=
  repeat (
    apply hom_ne; split; 
    try reflexivity;
    try (simpl; reflexivity);
    try (simpl; unfold ebimap; rewrite ?efmap_funct_comp);
    try (assumption)
  ).

Lemma muF_fmap_ne {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  {A B : Y} : NonExpansive (@muF_fmap Y Z F H A B).
Proof.
  intros n f g Hfg.
  unfold muF_fmap.
  destruct (muF_fmap' F H f) as [h Hh].
  destruct (muF_fmap' F H g) as [t Ht]. simpl.
  rewrite Hh Ht.
  induction n.
  - apply hom_ne ; split ; simpl ; last reflexivity.
    apply hom_ne ; split ; simpl .
    + apply hom_ne ; split ; first reflexivity.
      apply hom_ne ; split  ; first apply Hfg.
      reflexivity.
    + apply snd_funct_ctr. intros m Hm.  lia.
  - apply hom_ne ; split ; simpl ; last reflexivity.
    apply hom_ne ; split ; simpl.
    + apply hom_ne ; split ; first reflexivity.
      apply hom_ne ; split ; first apply Hfg.
      reflexivity.
    + apply snd_funct_ctr. intros m Hm.  
      eapply ofe_mono with (n := n); [|lia]. rewrite Hh Ht.
      apply IHn. eapply ofe_mono ; [apply Hfg | lia].
Qed.

Definition muF_efmap {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
   {A B : Y} : (A ~~{Y}~> B) -n> (muF_obj F H A ~~> muF_obj F H B) :=
  {| ne_mor := @muF_fmap _ _ F H A B ;  hom_ne := @muF_fmap_ne _ _ F H A B |}.

Definition muF_fmap_fixed_point {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
 {A B : Y} (f : A ~~{Y}~> B) := projT2 (muF_fmap' F H f).

Lemma muF_fmap_id {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A : Y)
  : muF_fmap F H (eid[A] tt) = eid{Z} tt.
Proof.
  unshelve epose (H2 := _ : { y & y = T F H A A (eid{Y} tt) y }).
  { exists (eid{Z} tt).
    unfold T. simpl.
    assert (forall x, @eid_mor Y x = @eid Y x) as H2.
    { intros x. reflexivity. }
    rewrite !H2.
    set (H3 := @ebimap_id Y Z Z F).
    rewrite !H3.
    simplify_ecat.
    rewrite eto_from. reflexivity.
  } 

  unshelve epose (H3 := _ : { y & y = T F H A A (eid{Y} tt) y }).
  { exists (muF_fmap F H (eid{Y} tt)). apply muF_fmap_fixed_point. }
  assert (projT1 H3 = projT1 H2) as H4.
  { apply (@fixpoint_unique _ (T F H A A (eid{Y} tt))). }
  apply H4.
Qed.


Lemma muF_fmap_compose_aux
  {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A B C : Y)
  (f : B ~~{Y}~> C) (g : A ~~{Y}~> B) :
  { y & y = T F H A C (f ∘e g) y }.
Proof.
  exists (muF_fmap F H f ∘e muF_fmap F H g).
  rewrite {1}/muF_fmap {1}/muF_fmap.
  rewrite (muF_fmap_fixed_point F H f) (muF_fmap_fixed_point F H g).
  assert (projT1 (muF_fmap' F H f) = muF_fmap F H f) as -> by done.
  assert (projT1 (muF_fmap' F H g) = muF_fmap F H g) as -> by done.
  rewrite !T_def.
  rewrite !ecomp_assoc.
  rewrite -(@ecomp_assoc _ _ _ _ _ (efrom (iso_T F H B))).
  rewrite efrom_to ecomp_eid_left.
  rewrite -(@ecomp_assoc _ _ _ _ _ (ebimap[F] f (eid{Z} tt))).
  rewrite -ebimap_ecompose ecomp_eid_right ecomp_eid_left.
  rewrite -(@ecomp_assoc _ _ _ _ _ (ebimap[F] g (eid{Z} tt))).
  rewrite -ebimap_ecompose ecomp_eid_right ecomp_eid_left.
  rewrite -(@ecomp_assoc _ _ _ _ _ _ (ebimap[F] g (muF_fmap F H g))).
  rewrite -ebimap_ecompose.
  rewrite -(@ecomp_assoc _ _ _ _ _ _ (ebimap[F] (eid{Y} tt) (muF_fmap F H f ∘e muF_fmap F H g))).
  by rewrite -ebimap_ecompose !ecomp_eid_left ecomp_eid_right.
Defined.

Lemma muF_fmap_compose
  {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A B C : Y)
  (f : B ~~{Y}~> C) (g : A ~~{Y}~> B) :
  muF_fmap F H (f ∘e g) = muF_fmap F H f ∘e muF_fmap F H g.
Proof.
  unshelve epose (H2 := _ : { y & y = T F H A C (f ∘e g) y }).
  { exists (muF_fmap F H (f ∘e g)).
    apply muF_fmap_fixed_point.
  }

  assert (projT1 H2 = projT1 (muF_fmap_compose_aux F H A B C f g)) as H3.
  { apply (@fixpoint_unique _ (T F H A C (f ∘e g))). }
  apply H3.
Qed.


Lemma muF_mixin {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  : eFunctMixin Y Z (muF_obj F H) (@muF_efmap _ _ F H).
Proof.
  unshelve econstructor.
  - apply muF_fmap_ne.
  - apply muF_fmap_id.
  - apply muF_fmap_compose.
Qed.

Definition muF {Y Z: eCategory} (F : eFunctorCtrSnd Y Z Z)
  (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A)) : eFunctor Y  Z := {|
   efobj := muF_obj F H;
   efmap_mor := @muF_efmap _ _ F H;
   efunct_mixin := muF_mixin F H
  |}.

Lemma efmap_muF_eq {Y Z : eCategory} 
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (A B : Y) (f : A ~~{Y}~> B) :
  efmap (muF F H) f = muF_fmap F H f.
Proof. apply eq_refl. Qed.

Theorem muF_ctr {Y Z : eCategory}
  (F : eFunctorCtrSnd Y Z Z) (H : forall A : Y, eInitialAlg (second_efunctor_ctr F A))
  (H1 : iseFunctorCtrFst F) 
  : iseFunctorCtr (muF F H).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n x y Hfg.
  rewrite !efmap_muF_eq /muF_fmap.
  destruct (muF_fmap' F H x) as [x' Hx'].
  destruct (muF_fmap' F H y) as [y' Hy'].
  assert (x' = projT1 (existT (fun h : muF_obj F H A ~~> muF_obj F H B => h = T F H A B x h) x' Hx')) as <- by done.
  assert (y' = projT1 (existT (fun h : muF_obj F H A ~~> muF_obj F H B => h = T F H A B y h) y' Hy')) as <- by done.

  rewrite Hx' Hy' !T_def.
  rewrite !ecomp_assoc.
  rewrite -(@ecomp_assoc _ _ _ _ _ (ebimap[F] x (eid{Z} tt))).
  rewrite -(@ecomp_assoc _ _ _ _ _ (ebimap[F] y (eid{Z} tt))).

  induction n.
  - apply hom_ne; split ; simpl ; first reflexivity.
    apply hom_ne ; split ; simpl ;  last reflexivity.
    apply hom_ne ; split ; simpl .
    + set H3 := @fst_funct_ctr Y Z Z (toeFunctorCtrFst H1).
      simpl in H3.
      by apply H3.
    + apply snd_funct_ctr. intros m Hm. lia.
  - apply hom_ne; split ; simpl ; first reflexivity.
    apply hom_ne ; split ; simpl ;  last reflexivity.
    apply hom_ne; split ; simpl.
    + set H3 := @fst_funct_ctr Y Z Z (toeFunctorCtrFst H1).
      simpl in H3.
      by apply H3.
    + apply snd_funct_ctr. intros m Hm. 
      eapply ofe_mono with n ; last lia.
      rewrite Hx' Hy'. rewrite !T_def. simpl.
      assert (Hfg2 : dist_later n x y) .
      { intros k Hk. apply Hfg; lia. }
      specialize (IHn Hfg2).
      simpl in  IHn.
      rewrite !ecomp_assoc.
      rewrite !ecomp_assoc in IHn.
      apply IHn.
Qed.
