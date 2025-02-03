From sgdt Require Import ecategory efunctor eisomorphism econtractive.
From sgdt Require Import banach ofe OFE iCOFE ofe_ccc icofe_ccc.

Require Import ssreflect.

Class eCategoryCtrComplete (Y : eCategory) : Type := {
  fixpointF (F : eFunctorCtr Y Y) : Y ;
  fixpointF_iso (F : eFunctorCtr Y Y) : F (fixpointF F) ≃[Y] fixpointF F ;
}.

Lemma op_efunct_ctr {Y Z : eCategory}  (F : eFunctorCtr Y Z) : eFunctorCtr Y^op Z^op.
Proof.
  unshelve refine {| efunct := op_efunct F ; efunct_ctr := _ |}.
  - intros A B n f g Hfg.
    unfold op_efunct. simpl.
    by apply efunct_ctr. 
Defined.

Global Instance op_op_ctr_compl {Y : eCategory} `{eCategoryCtrComplete Y} : eCategoryCtrComplete (Y^op^op).
Proof.
  rewrite eop_invol.
  unshelve refine {| fixpointF := fixpointF ; fixpointF_iso := fixpointF_iso |}.
Qed.

Global Instance op_ctr_compl {Y : eCategory} `{eCategoryCtrComplete Y} : eCategoryCtrComplete (Y^op).
Proof.
  unshelve refine {| fixpointF := _ |}.
  - intros F.
    exact (fixpointF (op_efunct_ctr F)).
  - intros F; simpl.
    destruct (fixpointF_iso (op_efunct_ctr F)) as [eto efrom eto_from efrom_to].
    simpl in *.
    by unshelve eapply mkEISO.
Qed.

(*
   Any fixed point of a contractive functor give rise to an initial algebra and final coalgebra structure.
   Therefore, the fixed point is unique up to isomorphism.
*)
Theorem unique_ctr_compl {Y : eCategory} (F : eFunctorCtr Y Y) (H1 H2 :  { T : Y & F T ≃ T }) 
   : projT1 H1 ≃ projT1 H2.
Proof.
  destruct H1 as [T1 H1], H2 as [T2 H2] ; simpl.
  set (T := fun h => eto H2 ∘e (efmap F h) ∘e efrom H1).
  unshelve epose (H3 := _ : (T1 ~~> T2) -c> (T1 ~~> T2)).
  { exists T. intros n f1 f2 Hfg. unfold T; simpl.
    apply hom_ne. simpl.
    split. simpl.
    + apply hom_ne. split; simpl ; first reflexivity.
      apply efunct_ctr. apply Hfg.
    + reflexivity.
  }
  pose (to' := ibanach_fixed_point H3).
  destruct to' as [to' Hto'] ; simpl in *.

  set (T' := fun h => eto H1 ∘e (efmap F h) ∘e efrom H2).
  unshelve epose (H4 := _ : (T2 ~~> T1) -c> (T2 ~~> T1)).
  { exists T'. intros n f1 f2 Hfg. unfold T'; simpl.
    apply hom_ne ; split ; simpl.
    + apply hom_ne. split; simpl ; first reflexivity.
      apply efunct_ctr. apply Hfg.
    + reflexivity.
  }
  pose (from' := ibanach_fixed_point H4).
  destruct from' as [from' Hfrom'] ; simpl in *.

  assert (to' ∘e from' = (eid{Y} tt)) as H9.
  {
    set (T''' := fun h : T2 ~~> T2 => eto H2 ∘e (efmap F h) ∘e efrom H2).
    unshelve epose (H5 := _ : (T2 ~~> T2) -c> (T2 ~~> T2)).
    { exists T'''. intros n f1 f2 Hfg. unfold T'''; simpl.
      apply hom_ne ; split ; simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    pose (idT2 := ibanach_fixed_point H5).
    unshelve epose (H6 := _ : {y : T2 ~~> T2 & y = T''' y}).
    { 
      simpl; exists (eid{Y} tt). 
      unfold T'''.
      by rewrite efmap_id {2}/ecomp eid_right eto_from.
    }

    assert (projT1 idT2 = projT1 H6) as H7.
    { apply fixpoint_unique. }

    unshelve epose (H8 := _ : {y : T2 ~~> T2 & y = T''' y}).
    { 
      exists ((to' ∘e from')).
      rewrite {1}Hto' {1}Hfrom'.
      unfold T, T', T'''; simpl.
      rewrite !(ecomp_assoc).
      rewrite -{1}(@ecomp_assoc _ _ _ _ _ (efrom H1) (eto H1) _).
      rewrite (efrom_to H1).
      rewrite efmap_mor_ecomp {3}/ecomp. rewrite eid_left.
      by rewrite !ecomp_assoc.
    }
    assert (projT1 idT2 = projT1 H8).
    { apply fixpoint_unique. }
    assert (projT1 H6 = projT1 H8). 
    { rewrite <- H. symmetry. auto. }
    
    unfold H6, H8 in H0 ; simpl in H0.
    symmetry in H0.
    by rewrite H0.
    }

  assert (from' ∘e to' = eid{Y} tt) as H10.
  {
    set (T''' := fun h => eto H1 ∘e (efmap F h) ∘e efrom H1).
    unshelve epose (H5 := _ : (T1 ~~> T1) -c> (T1 ~~> T1)).
    { exists T'''. intros n f1 f2 Hfg. unfold T'''; simpl.
      apply hom_ne ; split ; simpl.
      + apply hom_ne. split; simpl ; first reflexivity.
        apply efunct_ctr. apply Hfg.
      + reflexivity.
    }
    pose (idT2 := ibanach_fixed_point H5).
    (* destruct id' as [id' Hid'] ; simpl in *. *)
    unshelve epose (H6 := _ : {y : T1 ~~> T1 & y = T''' y}).
    { 
      simpl; exists (eid{Y} tt). 
      unfold T'''.
      by rewrite efmap_id {2}/ecomp eid_right eto_from.
    }

    assert (projT1 idT2 = projT1 H6) as H7.
    { apply fixpoint_unique. }

    unshelve epose (H8 := _ : {y : T1 ~~> T1 & y = T''' y}).
    { 
      exists ((from' ∘e to')).
      rewrite {1}Hto' {1}Hfrom'.
      unfold T, T', T'''; simpl.
      rewrite !ecomp_assoc.
      rewrite -{1}(@ecomp_assoc _ _ _ _ _ (efrom H2) (eto H2) _).
      rewrite (efrom_to H2).
      rewrite efmap_mor_ecomp {3}/ecomp. rewrite eid_left.
      by rewrite !ecomp_assoc.
    }

    assert (projT1 idT2 = projT1 H8).
    { apply fixpoint_unique. }
    assert (projT1 H6 = projT1 H8). 
    { rewrite <- H. symmetry. auto. }
    
    unfold H6, H8 in H0 ; simpl in H0.
    symmetry in H0.
    by rewrite H0.
  }
  by eapply mkEISO with (eto := to') (efrom := from').
Qed. 

Lemma fixpointF_iso_eq {Y : eCategory} (H : eCategoryCtrComplete Y) (F : eFunctorCtr Y Y) (H1 :  { T : Y & F T ≃ T }): 
  fixpointF F ≃ projT1 H1.
Proof.
  unshelve epose (H2 := _ : { T : Y & F T ≃ T }).
  { exists (fixpointF F). apply fixpointF_iso. }
  apply (unique_ctr_compl F H2 H1 ).
Qed.
