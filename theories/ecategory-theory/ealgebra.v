From sgdt Require Import ofe ecategory banach efunctor eisomorphism ectr_compl econtractive.
Require Import ssreflect.

Record eInitialAlg {Y : eCategory} (F : eFunctor Y Y) := mkEInitialAlg { 
  lfixpointF : Y;
  lfixpointF_iso : F (lfixpointF) ≃[Y] lfixpointF ;

  lfmap_lfixpointF_univ_map (A : Y) (f : F A ~~> A) : lfixpointF ~~> A ;

  lfmap_lfixpointF_univ_prop' (A : Y) (f : F A ~~> A) (h : lfixpointF ~~> A) :
   h = lfmap_lfixpointF_univ_map A f <-> h = f ∘e efmap F h ∘e efrom lfixpointF_iso
}.

Record isEInitialAlg {Y : eCategory} (F : eFunctor Y Y) (fixF : Y) := mkIsEInitialAlg {
  is_lfixpointF_iso : F fixF ≃[Y] fixF;

  is_lfmap_lfixpointF_univ_map (A : Y) (f : F A ~~> A) : fixF ~~> A ;

  is_lfmap_lfixpointF_univ_prop' (A : Y) (f : F A ~~> A) (h : fixF ~~> A) :
   h = is_lfmap_lfixpointF_univ_map A f <-> h = f ∘e efmap F h ∘e efrom is_lfixpointF_iso
}.

Definition toisEInitialAlg {Y : eCategory} {F : eFunctor Y Y} (H : eInitialAlg F) : isEInitialAlg F (lfixpointF F H)
:= {|
    is_lfixpointF_iso := lfixpointF_iso F H ;
    is_lfmap_lfixpointF_univ_map := lfmap_lfixpointF_univ_map F H ;
    is_lfmap_lfixpointF_univ_prop' := lfmap_lfixpointF_univ_prop' F H
  |}.

Definition toEInitialAlg {Y : eCategory} {F : eFunctor Y Y} (fixF : Y) (H : isEInitialAlg F fixF) : eInitialAlg F
:= {|
    lfixpointF := fixF ;
    lfixpointF_iso := is_lfixpointF_iso F fixF H ;
    lfmap_lfixpointF_univ_map := is_lfmap_lfixpointF_univ_map F fixF H ;
    lfmap_lfixpointF_univ_prop' := is_lfmap_lfixpointF_univ_prop' F fixF H
  |}.


Lemma lfmap_lfixpointF_univ_prop {Y : eCategory} (F : eFunctor Y Y) (H : eInitialAlg F) (A : Y) (f : F A ~~> A) :
  lfmap_lfixpointF_univ_map F H A f = f ∘e efmap F (lfmap_lfixpointF_univ_map F H A f) ∘e efrom (lfixpointF_iso F H).
Proof.
  destruct (lfmap_lfixpointF_univ_prop' F H A f (lfmap_lfixpointF_univ_map F H A f)) as [H1 _].
  apply H1. reflexivity.
Qed.

(* Every locally contractive endofunctor that has a fixed point has an initial algebra. *)
Theorem ctr_iso_is_initial_alg {Y : eCategory} (F : eFunctorCtr Y Y) 
  (H : { T : Y & F T ≃ T }) : isEInitialAlg F (projT1 H).
Proof.
  destruct H as [lfix lfix_iso].
  unshelve epose (H := _ : forall (A : eobj[Y]) (f : F A ~~{ Y }~> A) , { h : lfix ~~> A & h = f ∘e (efmap F h) ∘e efrom lfix_iso } ).
  { intros A f.

    set (T := fun h => f ∘e (efmap F h) ∘e efrom lfix_iso).
    unshelve epose (T' := _ : (lfix ~~> A) -c> (lfix ~~> A)).
    { exists T. intros n f1 f2 Hfg. unfold T; simpl.
      apply hom_ne. simpl.
      split. simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    exact (ibanach_fixed_point T').
  }

  unshelve refine {| is_lfixpointF_iso := lfix_iso ; is_lfmap_lfixpointF_univ_map := fun A f => projT1 (H A f) |}.
  intros A f h ; split ; intros Hh.
  - rewrite Hh.
    exact (projT2 (H A f)).
  - set (T := fun h => f ∘e (efmap F h) ∘e efrom lfix_iso).
    unshelve epose (T' := _ : (lfix ~~> A) -c> (lfix ~~> A)).
    { exists T. intros n f1 f2 Hfg. unfold T; simpl.
      apply hom_ne. simpl.
      split. simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    unshelve epose (H1 := _ : {y : lfix ~~> A & y = T' y}).
    { exists h. apply Hh. }
    unshelve epose (H2 := _ : {y : lfix ~~> A & y = T' y}).
    { exists (projT1 (H A f)).
      exact (projT2 (H A f)). }
  apply (fixpoint_unique T' H1 H2).
Qed.

Theorem ctr_compl_iso_is_initial_alg {Y : eCategory} `{eCategoryCtrComplete Y} (F : eFunctorCtr Y Y)
   : isEInitialAlg F (fixpointF F).
Proof.
  unshelve epose (H2 := _ : { T : Y & F T ≃ T }).
  { exists (fixpointF F). apply (fixpointF_iso F). }
  apply (ctr_iso_is_initial_alg _ H2). 
Qed.

(* Every locally contractive endofunctor that has a fixed point has an initial algebra. *)
Theorem ctr_iso_initial_alg {Y : eCategory} (F : eFunctorCtr Y Y) 
  (H : { T : Y & F T ≃ T }) : eInitialAlg F.
Proof.
  destruct H as [lfix lfix_iso].
  unshelve epose (H := _ : forall (A : eobj[Y]) (f : F A ~~{ Y }~> A) , { h : lfix ~~> A & h = f ∘e (efmap F h) ∘e efrom lfix_iso } ).
  { intros A f.

    set (T := fun h => f ∘e (efmap F h) ∘e efrom lfix_iso).
    unshelve epose (T' := _ : (lfix ~~> A) -c> (lfix ~~> A)).
    { exists T. intros n f1 f2 Hfg. unfold T; simpl.
      apply hom_ne. simpl.
      split. simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    exact (ibanach_fixed_point T').
  }

  unshelve refine {| lfixpointF := lfix ; lfixpointF_iso := lfix_iso ; lfmap_lfixpointF_univ_map := fun A f => projT1 (H A f) |}.
  intros A f h ; split ; intros Hh.
  - rewrite Hh.
    exact (projT2 (H A f)).
  - set (T := fun h => f ∘e (efmap F h) ∘e efrom lfix_iso).
    unshelve epose (T' := _ : (lfix ~~> A) -c> (lfix ~~> A)).
    { exists T. intros n f1 f2 Hfg. unfold T; simpl.
      apply hom_ne. simpl.
      split. simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    unshelve epose (H1 := _ : {y : lfix ~~> A & y = T' y}).
    { exists h. apply Hh. }
    unshelve epose (H2 := _ : {y : lfix ~~> A & y = T' y}).
    { exists (projT1 (H A f)).
      exact (projT2 (H A f)). }
  apply (fixpoint_unique T' H1 H2).
Defined.

Theorem ctr_compl_iso_initial_alg {Y : eCategory} `{eCategoryCtrComplete Y} (F : eFunctorCtr Y Y)
   : eInitialAlg F.
Proof.
  apply ctr_iso_initial_alg.
  exists (fixpointF F). apply (fixpointF_iso F).
Defined.

Theorem einitial_unique {Y : eCategory} (F : eFunctor Y Y) (H1 H2 : eInitialAlg F) : lfixpointF F H1 ≃ lfixpointF F H2.
Proof.
  destruct H1 as [lfix1 [eto1 efrom1 efrom_eto1 eto_efrom1] H1 H1'],
           H2 as [lfix2 [eto2 efrom2 efrom_eto2 eto_efrom2] H2 H2'] ; simpl in *.

  assert (H3 : forall A f, H2 A f = (f ∘e efmap F (H2 A f) ∘e efrom2) ).
  { intros A f; destruct (H2' A f (H2 A f)) as [H3 _] ; by apply H3. }
  assert (H4 : forall A f, H1 A f = (f ∘e efmap F (H1 A f) ∘e efrom1) ).
  { intros A f; destruct (H1' A f (H1 A f)) as [H4 _] ; by apply H4. }

  set eto := H1 lfix2 eto2.
  set efrom := H2 lfix1 eto1.
  assert (H1 lfix1 eto1 = eid{Y} tt) as H7.
  { symmetry. apply H1'.
    by rewrite efmap_mor_id ecomp_eid_right eto_efrom1.
  }
  assert (H1 lfix1 eto1 = efrom ∘e eto ). {
    symmetry. apply H1'.
    rewrite {1}/efrom {1}/eto.
    rewrite H3 H4.
    assert (eto = H1 lfix2 eto2) as <- by reflexivity.
    assert (efrom = H2 lfix1 eto1) as <- by reflexivity.
    rewrite !ecomp_assoc -(@ecomp_assoc _ _ _ _ _ efrom2) efrom_eto2 ecomp_eid_left.
    by rewrite -(@ecomp_assoc _ _ _ _ _ (efmap F efrom)) -efmap_ecomp. 
  }
  assert (H2 lfix2 eto2 = eid{Y} tt) as H8.
  { symmetry. apply H2'.
    by rewrite efmap_mor_id ecomp_eid_right eto_efrom2.
  }
  assert (H2 lfix2 eto2 = eto ∘e efrom). {
    symmetry. apply H2'.
    rewrite {1}/efrom {1}/eto.
    rewrite H3 H4.
    assert (eto = H1 lfix2 eto2) as <- by reflexivity.
    assert (efrom = H2 lfix1 eto1) as <- by reflexivity.
    rewrite !ecomp_assoc -(@ecomp_assoc _ _ _ _ _ efrom1) efrom_eto1 ecomp_eid_left.
    by rewrite -(@ecomp_assoc _ _ _ _ _ (efmap F eto)) -efmap_ecomp. 
  }

  eapply mkEISO with (eto := eto) (efrom := efrom).
  - by rewrite H in H7.
  - by rewrite H0 in H8.
Defined.
