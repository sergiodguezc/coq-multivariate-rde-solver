From sgdt Require Import category_theory axioms ecategory efunctor eisomorphism.
From sgdt Require Import ofe banach iCOFE ofe_ccc icofe_ccc econtractive partial_econtractive ectr_compl.
From sgdt Require Import muF join_split ealgebra general_america_rutten ealgebra esym.
From sgdt Require Import einstances eicofe_ctr_compl product.

From Coq Require Import ssreflect Lia.

Theorem general_existence_base_case {Y : eCategory} `{eCategoryCtrComplete Y}
(F : eFunctorCtrSnd ((Y^op × Y) ** 0) (Y^op × Y) Y) :
{ FixF : (Y^op × Y) ** 0 →  Y & forall A, (F ∘[eFUNCT] (<| (eID _), (esym FixF) |>)) A ≃  FixF A }.
Proof.
  set F' := toeFunctorCtr (second_efunctor_ctr_partial F tt).
  destruct (general_america_rutten F') as [FixF FixFiso].
  exists (const_efunctor FixF).
  intros []; apply FixFiso.
Qed.

Theorem general_existence_base_case_ctr {Y : eCategory} `{eCategoryCtrComplete Y}
(F : eFunctorCtr ((Y^op × Y) ** 1) Y) :
{ FixF : eFunctorCtr ((Y^op × Y) ** 0) Y & forall A, (F ∘[eFUNCT] (<| (eID _), (esym FixF) |>)) A ≃  FixF A }.
Proof.
  set F' := toeFunctorCtr (second_efunctor_ctr_partial (CtrToSnd F) tt).
  destruct (general_america_rutten F') as [FixF FixFiso].
  exists (const_efunctor_ctr FixF).
  intros []; apply FixFiso.
Qed.

(* General case of the general existence theorem *)
(* Lemmas for the general case *)
Lemma partial_esymS_prop {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
(A : eobj[Z^op]) (B : eobj[Z]) : forall A0 B0 : eobj[Y^op × Y],
  Contractive (@efmap _ _ (second_efunctor_ctr (esymS_ctr F) (A, B)) A0 B0).
Proof.
  intros [A1 A2] [B1 B2] n [f1 f2] [g1 g2] Hfg ; split ; simpl in * ;
    apply @snd_funct_ctr 
    ; intros m Hm; destruct (Hfg m Hm) as [Hf Hg] ; by split.
Qed.

Definition partial_esymS {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
  (A : Z^op) (B : Z) : eFunctorCtr (Y^op × Y) (Y^op × Y) :=
  {| efunct := second_efunctor_ctr (esymS_ctr F) (A, B) ; efunct_ctr := partial_esymS_prop F A B |}.

Lemma partial_esymS_eq {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
  (A : Z^op) (B : Z) : partial_esymS F A B = second_efunctor_ctr (esymS_ctr F) (A, B).
Proof. apply efunctor_ctr_eq; reflexivity. Qed.

Lemma parametrized_initial_algebras {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
  (A B : Z) (x y : Y) (H1 : F(A, (x, y)) ≃ y) (H2 : F(B, (y, x)) ≃ x) :
  eInitialAlg (partial_esymS F B A).
Proof.
  apply ctr_iso_initial_alg.
  exists (x, y).
  simpl; apply eiso_to_eprod_cat ; split ; [apply eiso_op ; exact H2 | exact H1].
Defined.

Lemma parametrized_is_initial_algebras {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
  (A B : Z) (x y : Y) (H1 : F(A, (x, y)) ≃ y) (H2 : F(B, (y, x)) ≃ x) :
  isEInitialAlg (partial_esymS F B A) (x, y).
Proof.
  unshelve epose (ctr_iso_is_initial_alg (partial_esymS F B A) _). 
  { exists (x, y) ; simpl; apply eiso_to_eprod_cat ;
    split ; [apply eiso_op ; exact H2 | exact H1]. }
  apply i.
Qed.

Lemma parametrized_initial_algebras_swap {Y Z : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) Y)
  (A B : Z) (x y : Y)  (H : isEInitialAlg (partial_esymS F B A) (x, y)) :
  isEInitialAlg (partial_esymS F A B) (y, x).
Proof.
  set xy_eq := is_lfixpointF_iso _ _ H.
  simpl in xy_eq.
  destruct (eiso_eprod_cat xy_eq) as [Hx Hy].
  simpl in Hx, Hy.
  unshelve epose (H2 := _ : partial_esymS F A B (y, x) ≃ (y, x)).
  { simpl. apply eiso_to_eprod_cat ; split ; simpl.
    - apply eiso_op. exact Hy.
    - apply eiso_op in Hx.
      destruct Hx as [eto efrom efrom_to eto_from].
      simpl in eto_from, efrom_to. 
      by unshelve econstructor.
  }
  unshelve epose (H3 := _ : {X & partial_esymS F A B X ≃ X} ).
  { exists (y, x); exact H2. }
  apply (ctr_iso_is_initial_alg _ H3).
Qed.

Lemma op_efunct_2_mixin {Y : eCategory} (F : Y^op →  Y) : eFunctMixin Y Y^op F (fun A B f => efmap F f).
Proof.
  unshelve econstructor.
  - intros; by apply hom_ne.
  - intros A; rewrite - eop_id -efmap_id //.
  - intros A B C f g ; simpl.
    rewrite eop_mor_ecomp_eq /= efmap_mor_ecomp //.
Qed.

Definition op_efunct_2 {Y : eCategory} (F : Y^op →  Y) : Y →  Y^op := {|
    efobj := fun A : Y => F A : Y^op ;
    efmap_mor := fun (A B : Y) f => efmap F f ;
    efunct_mixin := op_efunct_2_mixin F
  |}.

Lemma unparametrized_mv_fixed_points {Y Z : eCategory} `{eCategoryCtrComplete Y}
(F : eFunctorCtrSnd Z (Y^op × Y) Y) (A B : Z) : 
{ X : Y & { W : Y & { HZ : F (B, (X, W)) ≃ W & F (A, (W, X)) ≃ X & A ≃ B -> X ≃ W } } } .
Proof.
  set G1 := toeFunctorCtr (second_efunctor_ctr_partial F A).
  set G2 := toeFunctorCtr (second_efunctor_ctr_partial F B).
  assert (H3 : (forall A : eobj[Y^op], eInitialAlg (second_efunctor_ctr (CtrToSnd G2) A))).
  { intros A1. apply ctr_compl_iso_initial_alg. }
  set G3 := toeFunctorCtr (compose_efunctor_ctr_left G1 (<| op_efunct_2 (muF (CtrToSnd G2) H3), eID _ |>)).
  set X_iso := fixpointF_iso G3.
  set X := fixpointF G3 in X_iso.
  exists X.
  exists ((muF (CtrToSnd G2) H3) X).
  assert (H1 : F (B, (X, (muF (CtrToSnd G2) H3 X))) ≃ (muF (CtrToSnd G2) H3 X)).
  { set H6 := @muF_obj_iso _ _ (CtrToSnd G2) H3 X.
    simpl.
    eapply eiso_trans.
    + apply eiso_sym. exact H6.
    + apply eiso_refl.
  }

  unshelve exists ; [apply H1 | apply X_iso |].
  intros H7.
  set H4 := @parametrized_initial_algebras _ _ F B A X ((muF (CtrToSnd G2) H3) X) H1 X_iso.
  unshelve epose (H5 := @parametrized_initial_algebras _ _ F B A ((muF (CtrToSnd G2) H3) X) X _ _).
  { eapply eiso_trans ; first (exact X_iso).
    unfold G3; simpl; apply efunctor_preserve_eiso, eiso_to_eprod_cat ; split ;
    simpl ; [apply (eiso_sym H7) | apply eiso_refl].
  }
  { eapply eiso_trans ; first apply H1.
    unfold G3; simpl; apply efunctor_preserve_eiso, eiso_to_eprod_cat ; split ;
    simpl ; [apply H7 | apply eiso_refl].
  }
  set H10 := @einitial_unique _ _ H4 H5.
  assert (H11 : lfixpointF (partial_esymS F A B) H4 = (X, (muF (CtrToSnd G2) H3 X))) by done.
  assert (H12 : lfixpointF (partial_esymS F A B) H5 = ((muF (CtrToSnd G2) H3 X), X)) by done.
  rewrite -> H11 in H10; rewrite -> H12 in H10.
  destruct (eiso_eprod_cat H10) as [[eto efrom efrom_to eto_from] H14];
  by unshelve econstructor.
Qed.

Lemma einitial_algebra_esymS_ctr {Y : eCategory} `{eCategoryCtrComplete Y}
  {n : nat} (F : eFunctorCtrSnd ((Y^op × Y) ** S n) (Y^op × Y) Y) :
  forall A, eInitialAlg (second_efunctor_ctr (esymS_ctr F) A).
Proof.
  intros [A B]; rewrite -partial_esymS_eq;
  destruct (unparametrized_mv_fixed_points F A B) as [X [W [HZ HW]]] ;
  eapply parametrized_initial_algebras ; [exact HZ | exact HW].
Qed.

Definition FixFS {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtrSnd ((Y^op × Y) ** (S n)) (Y^op × Y) Y) :=
    (psnd_efunct ∘[eFUNCT] (muF (@esymS_ctr _ _ _ F) (einitial_algebra_esymS_ctr F)) ∘[eFUNCT] delta).

Theorem general_existence {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtrSnd ((Y^op × Y) ** n) (Y^op × Y) Y) :
  { FixF : (Y^op × Y) ** n →  Y & forall A, (F ∘[eFUNCT] (<| (eID _), (esym FixF) |>)) A ≃  FixF A }.
Proof.
  destruct n.
  - apply (general_existence_base_case F). 
  - set Halg := einitial_algebra_esymS_ctr F.
    set FixF := FixFS F.
    exists FixF.
    intros A.
    assert (H1 : forall A, FixF A = snd (lfixpointF _ (Halg (delta A)))) by reflexivity.
    
    destruct ((lfixpointF (second_efunctor_ctr (esymS_ctr F) (delta A)) (Halg (delta A)))) as [X1 X2] eqn:HX.
    destruct A as [An A'] eqn:HA1.

    assert ((F∘[eFUNCT] (<| eID ((Y^op × Y) ** S n), esym FixF |>)) (An, A')
        = F ((An, A'), esymS FixF (delta An, A') )) as -> by done.

    destruct (delta An) as [Dop D]eqn:Hd , A' as [Aop Ah] eqn:HA2.

    assert (esymS FixF ( ((Dop, D), (Aop, Ah)) : eobj[(((Y^op × Y) ** n)^op × (Y^op × Y) ** n) × (Y^op × Y)] )
      = (FixF (Dop, (Ah, Aop)), FixF (D, (Aop, Ah))) ) as H2 by done; rewrite H2.

    assert (D = An) as -> by (by inversion Hd).
    assert (FixF (An, (Aop, Ah)) = X2) as H3 by (rewrite H1 HX //); rewrite !H3.

    assert (esymS FixF (delta An, (Aop, Ah)) = (FixF (Dop, (Ah, Aop)), FixF (An, (Aop, Ah))) ) as H4.
    { rewrite -H2 Hd //. }
    rewrite H3 in H4.
    assert (X2 = snd (esymS FixF (delta An, (Aop, Ah)))) as HX2 by (rewrite H4; done).

    set Dnop := (join_eobj n (eobj_of snd (split_eobj n Dop), eop_of fst (split_eobj n Dop))).
    assert (Dnop = An) as H5.
    { unfold Dnop; inversion Hd.
      set H6 := @split_join_id_eobj n Y (delta1_eobj (split_eobj n An)); simpl in H6.
      rewrite H6 /delta1_eobj.
      destruct (split_eobj n An) as [An1 An2] eqn:HsAn; simpl.
      rewrite eop_to_eobj_inv eobj_to_eop_inv -HsAn.
      set H7 := @join_split_id_eobj n Y An; simpl in H7; rewrite H7 //.
    }

    assert (delta ( (Dop, (Ah, Aop)) : eobj[(Y^op × Y) ** S n] )
      = ((Dnop, (Aop, Ah), (Dop, (Ah, Aop)) ))) as H6 by done.

    assert (FixF (Dop, (Ah, Aop)) ≃ X1) as H8.
    { 
      set Zop := join_eobj n (eobj_of snd (split_eobj n An), eop_of fst (split_eobj n An)) in HX.
      assert (Dop = Zop) as H8.
      { unfold Zop; inversion Hd.
        set H8' := @split_join_id_eobj n Y (delta1_eobj (split_eobj n An)); simpl in H8'.
        by destruct (split_eobj n An) as [An1 An2] eqn:H12; simpl.
      }
      assert (H9 : isEInitialAlg (partial_esymS F (Zop, (Ah, Aop)) (An, (Aop, Ah))) (X1, X2)).
      { rewrite partial_esymS_eq -HX ; apply toisEInitialAlg. }
      set (H10 := @parametrized_initial_algebras_swap _ _ F  (An, (Aop, Ah)) (Zop, (Ah, Aop)) X1 X2 H9 ).
      rewrite -> partial_esymS_eq in H10.
      rewrite -> partial_esymS_eq in H9.
      assert (H11 : lfixpointF _ (toEInitialAlg _ H10) = (X2, X1)) by done.
      rewrite H1.
      assert (delta ((Zop, (Ah, Aop)) :  eobj[(Y^op × Y) ** S n]) = ((An, (Aop, Ah)), (Zop, (Ah, Aop)) :  eobj[(Y^op × Y) ** S n])) as H12.
      { simpl; f_equal; f_equal. simpl. rewrite - H5 -H8 /Dnop //. }
      set Halg2 := (Halg (delta ((Zop, (Ah, Aop)) : eobj[(Y^op × Y) ** S n]))).
      rewrite H12 in Halg2.
      set H13 := @einitial_unique _ _ Halg2 (toEInitialAlg _ H10).
      rewrite H8.
      
      assert (H14 : snd (lfixpointF (second_efunctor_ctr (esymS_ctr F) (An, (Aop, Ah), (Zop, (Ah, Aop)))) Halg2)
                  ≃ snd (lfixpointF (second_efunctor_ctr (esymS_ctr F) (An, (Aop, Ah), (Zop, (Ah, Aop)))) (toEInitialAlg _ H10) )).
      { by apply (@efunctor_preserve_eiso (eprod_cat Y^op Y) Y psnd_efunct). }
      unfold Halg2 in H14.
      rewrite H12.
      
      eapply eiso_trans ; last apply H14.
      rewrite H11 /=; apply eiso_refl.
    }
    assert (F (An, (Aop, Ah), (FixF (Dop, (Ah, Aop)), X2)) ≃ F (An, (Aop, Ah), (X1, X2))) as H9.
    { apply efunctor_preserve_eiso; apply eiso_to_eprod_cat ; split  ; first exact eiso_refl;
      apply eiso_to_eprod_cat ; split  ; last exact eiso_refl ; apply eiso_op; apply H8.
    }
    eapply eiso_trans ; last exact H9.
    rewrite {2}HX2 /esymS /esymS_eobj {2}/efobj Hd /snd H1.
    destruct (eiso_eprod_cat (@lfixpointF_iso _ (second_efunctor_ctr (esymS_ctr F) (delta A)) (Halg (delta A)))) as [_ H10].
    rewrite -HA1; eapply eiso_trans ; first apply H10.
    rewrite HA1 HX; apply eiso_refl.
Qed.

Definition FixFS_ctr {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
(F : eFunctorCtr ((Y^op × Y) ** (S (S (n)))) Y) : iseFunctorCtr (FixFS (CtrToSnd F)).
Proof.
  apply compose_efunctor_isctr_left.
  apply compose_efunctor_isctr_right.
  apply muF_ctr.
  set F' := CtrToFst F.
  unshelve econstructor.
  intros [x1 x2] [[A1 [A2 A3]] [A4 [A5 A6]]] [[B1 [B2 B3]] [B4 [B5 B6]]] m.
  intros [[f1 [f2 f3]] [f4 [f5 f6]]] [[g1 [g2 g3]] [g4 [g5 g6]]] Hfg;
  split ; simpl in *.
  - apply (is_efunct_ctr_fst F') ; first (apply toiseFunctorCtrFst).
    intros k Hk; destruct (Hfg k Hk); apply H0.
  - apply (is_efunct_ctr_fst F') ; first (apply toiseFunctorCtrFst).
    intros k Hk; destruct (Hfg k Hk); apply H1.
Qed.

Lemma general_existence_ctr {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  { FixF : eFunctorCtr ((Y^op × Y) ** n) Y & forall A, (F ∘[eFUNCT] (<| (eID _), (esym FixF) |>)) A ≃  FixF A }.
Proof.
  destruct n.
  - apply (general_existence_base_case_ctr F). 
  - set G := CtrToSnd F.
    set Halg := einitial_algebra_esymS_ctr G.
    set FixF := toeFunctorCtr (FixFS_ctr F).
    exists FixF.
    intros A.

    assert (H1 : forall A, FixF A = snd (lfixpointF _ (Halg (delta A)))) by reflexivity.
    
    destruct ((lfixpointF (second_efunctor_ctr (esymS_ctr G) (delta A)) (Halg (delta A)))) as [X1 X2] eqn:HX.
    destruct A as [An A'] eqn:HA1.

    assert ((F∘[eFUNCT] (<| eID ((Y^op × Y) ** S n), esym FixF |>)) (An, A')
        = F ((An, A'), esymS FixF (delta An, A') )) as -> by done.

    destruct (delta An) as [Dop D]eqn:Hd , A' as [Aop Ah] eqn:HA2.

    assert (esymS FixF ( ((Dop, D), (Aop, Ah)) : eobj[(((Y^op × Y) ** n)^op × (Y^op × Y) ** n) × (Y^op × Y)] )
      = (FixF (Dop, (Ah, Aop)), FixF (D, (Aop, Ah))) ) as H2 by done; rewrite H2.

    assert (D = An) as -> by (by inversion Hd).
    assert (FixF (An, (Aop, Ah)) = X2) as H3 by (rewrite H1 HX //); rewrite !H3.

    assert (esymS FixF (delta An, (Aop, Ah)) = (FixF (Dop, (Ah, Aop)), FixF (An, (Aop, Ah))) ) as H4.
    { rewrite -H2 Hd //. }
    rewrite H3 in H4.
    assert (X2 = snd (esymS FixF (delta An, (Aop, Ah)))) as HX2 by (rewrite H4; done).

    set Dnop := (join_eobj n (eobj_of snd (split_eobj n Dop), eop_of fst (split_eobj n Dop))).
    assert (Dnop = An) as H5.
    { unfold Dnop; inversion Hd.
      set H6 := @split_join_id_eobj n Y (delta1_eobj (split_eobj n An)); simpl in H6.
      rewrite H6 /delta1_eobj.
      destruct (split_eobj n An) as [An1 An2] eqn:HsAn; simpl.
      rewrite eop_to_eobj_inv eobj_to_eop_inv -HsAn.
      set H7 := @join_split_id_eobj n Y An; simpl in H7; rewrite H7 //.
    }

    assert (delta ( (Dop, (Ah, Aop)) : eobj[(Y^op × Y) ** S n] )
      = ((Dnop, (Aop, Ah), (Dop, (Ah, Aop)) ))) as H6 by done.

    assert (FixF (Dop, (Ah, Aop)) ≃ X1) as H8.
    { 
      set Zop := join_eobj n (eobj_of snd (split_eobj n An), eop_of fst (split_eobj n An)) in HX.
      assert (Dop = Zop) as H8.
      { unfold Zop; inversion Hd.
        set H8' := @split_join_id_eobj n Y (delta1_eobj (split_eobj n An)); simpl in H8'.
        by destruct (split_eobj n An) as [An1 An2] eqn:H12; simpl.
      }
      assert (H9 : isEInitialAlg (partial_esymS G (Zop, (Ah, Aop)) (An, (Aop, Ah))) (X1, X2)).
      { rewrite partial_esymS_eq -HX ; apply toisEInitialAlg. }
      set (H10 := @parametrized_initial_algebras_swap _ _ G  (An, (Aop, Ah)) (Zop, (Ah, Aop)) X1 X2 H9 ).
      rewrite -> partial_esymS_eq in H10.
      rewrite -> partial_esymS_eq in H9.
      assert (H11 : lfixpointF _ (toEInitialAlg _ H10) = (X2, X1)) by done.
      rewrite H1.
      assert (delta ((Zop, (Ah, Aop)) :  eobj[(Y^op × Y) ** S n]) = ((An, (Aop, Ah)), (Zop, (Ah, Aop)) :  eobj[(Y^op × Y) ** S n])) as H12.
      { simpl; f_equal; f_equal. simpl. rewrite - H5 -H8 /Dnop //. }
      set Halg2 := (Halg (delta ((Zop, (Ah, Aop)) : eobj[(Y^op × Y) ** S n]))).
      rewrite H12 in Halg2.
      set H13 := @einitial_unique _ _ Halg2 (toEInitialAlg _ H10).
      rewrite H8.
      
      assert (H14 : snd (lfixpointF (second_efunctor_ctr (esymS_ctr G) (An, (Aop, Ah), (Zop, (Ah, Aop)))) Halg2)
                  ≃ snd (lfixpointF (second_efunctor_ctr (esymS_ctr G) (An, (Aop, Ah), (Zop, (Ah, Aop)))) (toEInitialAlg _ H10) )).
      { by apply (@efunctor_preserve_eiso (eprod_cat Y^op Y) Y psnd_efunct). }
      unfold Halg2 in H14.
      rewrite H12.
      
      eapply eiso_trans ; last apply H14.
      rewrite H11 /=; apply eiso_refl.
    }
    assert (G (An, (Aop, Ah), (FixF (Dop, (Ah, Aop)), X2)) ≃ G (An, (Aop, Ah), (X1, X2))) as H9.
    { apply efunctor_preserve_eiso; apply eiso_to_eprod_cat ; split  ; first exact eiso_refl;
      apply eiso_to_eprod_cat ; split  ; last exact eiso_refl ; apply eiso_op; apply H8.
    }
    eapply eiso_trans ; last exact H9.
    rewrite {2}HX2 /esymS /esymS_eobj {2}/efobj Hd /snd H1.
    destruct (eiso_eprod_cat (@lfixpointF_iso _ (second_efunctor_ctr (esymS_ctr G) (delta A)) (Halg (delta A)))) as [_ H10].
    rewrite -HA1; eapply eiso_trans ; first apply H10.
    rewrite HA1 HX; apply eiso_refl.
Qed.
    
(** COMPUTE FIXED POINT 'VALUE' FROM AN N-ARY CONTRACTIVE FUNCTOR *)
Fixpoint repeat_elem_eobj {Y : eCategory} (n : nat) (x : Y) : Y ** n := 
  match n with
  | O => tt
  | S n' => ((repeat_elem_eobj n' x), x)
  end.

Fixpoint repeat_elem_efmap {Y : eCategory} (n : nat) {A B : Y} (f : A ~~> B) : repeat_elem_eobj n A ~~> repeat_elem_eobj n B :=
  match n with
  | O => tt
  | S n' => ((repeat_elem_efmap n' f), f)
  end.

Lemma repeat_elem_mixin {Y : eCategory} (n : nat) : eFunctMixin Y (Y ** n) (repeat_elem_eobj n) (@repeat_elem_efmap _ n).
Proof.
  unshelve econstructor.
  - intros A B m f g Hfg.
    induction n ; first done.
    split ; first apply IHn ; apply Hfg.
  - intros A; induction n ; first done.
    simpl in *. unfold eprod_eid_mor. by rewrite IHn. 
  - intros A B C f g ; simpl.
    induction n ; first done.
    simpl. by rewrite IHn.
Qed.

Definition repeat_elem {Y : eCategory} (n : nat) : eFunctor Y (Y ** n) :=
  {| efobj := repeat_elem_eobj n ; efmap_mor := @repeat_elem_efmap _ n ; efunct_mixin := repeat_elem_mixin n |}.
Notation "A *& n" := (repeat_elem n A) (at level 20).

Definition repeat_elem_mv {Y : eCategory} (n : nat) : eFunctor (Y^op × Y) ((Y^op × Y) ** n) := repeat_elem n.
Notation "A **& n" := (repeat_elem_mv n (A, A)) (at level 20).

Lemma repeat_elem_split {Y : eCategory} {n : nat} (X : Y) :
  split n (X **& n) = ((eobj_of (X *& n), (X *& n)) : eobj[Y^op ** n × Y ** n]).
Proof.
  induction n ; first done.
  simpl; f_equal; f_equal ; simpl in IHn ; by rewrite IHn.
Qed.

Lemma repeat_elem_join {Y : eCategory} {n : nat} (X : Y) :
  join n (eobj_of (X *& n), X *& n) = X **& n.
Proof.
  induction n ; first done.
  simpl; f_equal; f_equal ; simpl in IHn ; by rewrite IHn.
Qed. 

Definition efunct_repeat_ecomp_is {Y : eCategory} {n} (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  iseFunctorCtr (F ∘[eFUNCT] repeat_elem_mv (S n)).
Proof. apply compose_efunctor_isctr_left, toiseFunctorCtr. Qed. 

Definition efunct_repeat_ecomp {Y : eCategory} {n} (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  eFunctorCtr (Y^op × Y) Y := toeFunctorCtr (efunct_repeat_ecomp_is F).
Notation "F -&" := (efunct_repeat_ecomp F) (at level 20).

(* COMPUTE FIXED-POINT VALUE USING THE GENERAL EXISTENCE THEOREM INDUCTIVELY *)
Corollary general_existence_value {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  { FixF : Y & F -& (FixF, FixF)  ≃ FixF }.
Proof.
  destruct (general_existence_ctr F) as [FixF HFixF].
  induction n.
  - exists (FixF tt); apply HFixF.
  - destruct (general_existence_ctr FixF) as [FixF' HFixF'].
    destruct (IHn FixF FixF' HFixF') as [X HX]; exists X.
    specialize (HFixF (X **& S n)).
    eapply eiso_trans ; first (apply HX).
    eapply eiso_trans ; first (apply HFixF); simpl.
    apply efunctor_preserve_eiso, eiso_to_eprod_cat ; split ; first apply eiso_refl ; simpl.
    eapply eiso_to_eprod_cat ; split ; simpl ; last (apply eiso_sym ; apply HX).
    assert ((join_eobj n (delta1_eobj (split_eobj n (X **& n))), (X, X)) = X **& (S n) ) as H2.
    { set H2 := @repeat_elem_split ; simpl in H2; rewrite H2 ; simpl ;
      set H3 := @repeat_elem_join ; simpl in H3;
      rewrite eop_to_eobj_inv H3 //.
    }
    rewrite H2.
    apply eiso_sym, eiso_op, HX.
Qed.

Definition fixpointF {Y : eCategory} `{eCategoryCtrComplete Y} {n} (F : eFunctorCtr ((Y^op × Y) ** S n) Y) : Y :=
  projT1 (general_existence_value F).

Definition fixpointF_iso {Y : eCategory} `{eCategoryCtrComplete Y} {n} (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  F -& (fixpointF F, fixpointF F) ≃ fixpointF F :=
  projT2 (general_existence_value F).

(* COMPUTE FIXED-POINT VALUE USING JUST THE AMERICAN RUTTEN THEOREM *)
Corollary general_existence_value_america_rutten {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtr ((Y^op × Y) ** S n) Y) :
  { FixF : Y & F -& (FixF, FixF)  ≃ FixF }.
Proof.
  set G' := F ∘[eFUNCT] (repeat_elem_mv (S n)).
  assert (H1 : iseFunctorCtr G') by (apply compose_efunctor_isctr_left, toiseFunctorCtr).
  set G := toeFunctorCtr H1.
  apply general_america_rutten.
Qed.

Lemma general_existence_unique' {Y : eCategory}  `{eCategoryCtrComplete Y} {n}
  (F : eFunctorCtr ((Y^op × Y) ** S n) Y) (H1 H2 : { FixF : Y & F -& (FixF, FixF)  ≃ FixF }) :
  projT1 H1 ≃ projT1 H2.
Proof.
  set G' := F ∘[eFUNCT] (repeat_elem_mv (S n)).
  assert (H3 : iseFunctorCtr G') by (apply compose_efunctor_isctr_left, toiseFunctorCtr).
  set G := toeFunctorCtr H3.
  unshelve epose (H1' := H1 : {FixF : eobj[Y] & G (FixF, FixF) ≃ FixF}).
  unshelve epose (H2' := H2 : {FixF : eobj[Y] & G (FixF, FixF) ≃ FixF}).
  apply (general_america_rutten_unique G H1' H2').
Qed.

Corollary general_existence_icofe {n : nat}
  (F : eFunctorCtr ((eiCOFE^op × eiCOFE) ** S n) eiCOFE) :
  { FixF : eiCOFE & F -& (FixF, FixF) ≃ FixF }.
Proof. apply general_existence_value. Qed.

Corollary general_existence_icofe_unique {n : nat}
  (F : eFunctorCtr ((eiCOFE^op × eiCOFE) ** S n) eiCOFE) (H1 H2 : { FixF : eiCOFE & F -& (FixF, FixF) ≃ FixF }) :
  projT1 H1 ≃ projT1 H2.
Proof. apply general_existence_unique'. Qed.

(* Print Assumptions general_existence_icofe. *)
