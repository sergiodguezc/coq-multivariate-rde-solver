From sgdt Require Import axioms ecategory ofe iCOFE icofe_ccc einstances efunctor econtractive.

Require Import ssreflect Lia.
(*
  Partial contractive functors
*)

Record eFunctorCtrSnd (X Y Z : eCategory)  : Type := {
  efunct_snd :> eFunctor (eprod_cat X Y) Z;
  efunct_ctr_snd {A B} : ContractiveSnd (@efmap _ _ efunct_snd A B)
}.
Arguments efunct_snd {_ _ _} .

Lemma eFunctorCtrSnd_eq {X Y Z : eCategory} (F G : eFunctorCtrSnd X Y Z) :
  (efunct_snd F = efunct_snd G) -> F = G.
Proof.
  intros H.
  destruct F, G. 
  assert (efunct_snd0 = efunct_snd1) as -> by apply H.
  f_equal. apply proof_irrelevance.
Qed.

Record iseFunctorCtrSnd {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) : Prop := {
  is_efunct_ctr_snd {A B} : ContractiveSnd (@efmap _ _ F A B)
}.

Lemma second_efunctor_ctr_partial {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z)
  (x : X) :
  iseFunctorCtr (second_efunct F x).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg.
  by apply efunct_ctr_snd.
Qed.

Lemma snd_funct_ctr {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) {A B C D} :
  forall n (x1 x2 : A ~~> D) (y1 y2 : B ~~> C),
  (x1 ≡{ n }≡ x2) -> 
  dist_later n y1 y2 ->
  ebimap[F] x1 y1 ≡{ n }≡ ebimap[F] x2 y2.
Proof.
  intros n x1 x2 y1 y2 Hx Hy.
  transitivity (ebimap[F] x1 y2).
  - apply efunct_ctr_snd. exact Hy.
  - apply hom_ne. split ; first exact Hx. reflexivity.
Qed.

Lemma is_snd_funct_ctr {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) (H : iseFunctorCtrSnd F) {A B C D} :
  forall n (x1 x2 : A ~~> D) (y1 y2 : B ~~> C),
  (x1 ≡{ n }≡ x2) -> 
  dist_later n y1 y2 ->
  ebimap[F] x1 y1 ≡{ n }≡ ebimap[F] x2 y2.
Proof.
  intros n x1 x2 y1 y2 H1 H2.
  transitivity (ebimap[F] x1 y2).
  - apply ((is_efunct_ctr_snd F) H). exact H2.
  - apply hom_ne. split ; first exact H1. reflexivity.
Qed.

Lemma toeFunctorCtrSnd {X Y Z : eCategory} {F : eFunctor (eprod_cat X Y) Z} (H : iseFunctorCtrSnd F) : eFunctorCtrSnd X Y Z.
Proof. refine {| efunct_snd := F ; efunct_ctr_snd := _ |}. apply H. Defined.

Lemma toiseFunctorCtrSnd {X Y Z : eCategory} (H : @eFunctorCtrSnd X Y Z) : iseFunctorCtrSnd (efunct_snd H).
Proof. refine {| is_efunct_ctr_snd := _ |}. apply efunct_ctr_snd. Defined.

Lemma compose_efunctor_ctrsnd_left {W X Y Z : eCategory}
(F : eFunctorCtrSnd W X Y) (G : eFunctor Y Z) : iseFunctorCtrSnd (G∘[eFUNCT] F).
Proof.
  unshelve econstructor.
  intros [A1 A2] [B1 B2] h n f g Hfg ; simpl in *.
  apply efmap_mor_ne, snd_funct_ctr ; [reflexivity | apply Hfg]. 
Qed.

Lemma compose_efunctor_isctrsnd_left {W X Y Z : eCategory}
  (F : eFunctor (eprod_cat W X) Y) (G : eFunctor Y Z) (H : iseFunctorCtrSnd F)
  : iseFunctorCtrSnd (G∘[eFUNCT] F).
Proof.
  unshelve econstructor.
  intros [A1 A2] [B1 B2] h n f g Hfg ; simpl in *.
  apply efmap_mor_ne, (is_snd_funct_ctr F H) ; [ reflexivity | apply Hfg].
Qed.

Record eFunctorCtrFst (X Y Z : eCategory)  : Type := {
  efunct_fst :> eFunctor (eprod_cat X Y) Z;
  (* efunct_ctr_fst {y : Y} {A B} : Contractive (@efmap _ _ (first_efunct efunct_fst y) A B) *)
  efunct_ctr_fst {A B} : ContractiveFst (@efmap _ _ efunct_fst A B)
}.
Arguments efunct_fst {_ _ _} .

Lemma eFunctorCtrFst_eq {X Y Z : eCategory} (F G : eFunctorCtrFst X Y Z) :
  (efunct_fst F = efunct_fst G) -> F = G.
Proof.
  intros H. destruct F, G. 
  assert (efunct_fst0 = efunct_fst1) as -> by apply H.
  f_equal. apply proof_irrelevance.
Qed.

Record iseFunctorCtrFst {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) : Prop := {
  (* is_efunct_ctr_fst {y : Y} {A B} : Contractive (@efmap _ _ (first_efunct F y) A B) *)
  is_efunct_ctr_fst {A B} : ContractiveFst (@efmap _ _ F A B)
}.

Lemma first_efunctor_ctr_partial {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z)
  (y : Y) :
  iseFunctorCtr (first_efunct F y).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg.
  by apply efunct_ctr_fst.
Qed.

Lemma fst_funct_ctr {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) {A B C D} :
  forall n (x1 x2 : A ~~> B) (y1 y2 : C ~~> D),
  (y1 ≡{ n }≡ y2) ->
  dist_later n x1 x2 ->
  ebimap[F] x1 y1 ≡{ n }≡ ebimap[F] x2 y2.
Proof.
  intros n x1 x2 y1 y2 Hy Hx.
  transitivity (ebimap[F] x2 y1).
  - apply efunct_ctr_fst. exact Hx.
  - apply hom_ne. split ; first reflexivity. exact Hy.
Qed.

Lemma is_fst_funct_ctr {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) (H : iseFunctorCtrFst F) {A B C D} :
  forall n (x1 x2 : A ~~> B) (y1 y2 : C ~~> D),
  (y1 ≡{ n }≡ y2) ->
  dist_later n x1 x2 ->
  ebimap[F] x1 y1 ≡{ n }≡ ebimap[F] x2 y2.
Proof.
  intros n x1 x2 y1 y2 Hy Hx.
  transitivity (ebimap[F] x2 y1).
  - apply ((is_efunct_ctr_fst F) H). exact Hx.
  - apply hom_ne. split ; first reflexivity. exact Hy.
Qed.

Lemma toeFunctorCtrFst {X Y Z : eCategory} {F : eFunctor (eprod_cat X Y) Z} (H : iseFunctorCtrFst F) : eFunctorCtrFst X Y Z.
Proof. refine {| efunct_fst := F ; efunct_ctr_fst := _ |}. apply H. Defined.

Lemma toiseFunctorCtrFst {X Y Z : eCategory} (H : eFunctorCtrFst X Y Z) : iseFunctorCtrFst (efunct_fst H).
Proof. refine {| is_efunct_ctr_fst := _ |}. apply efunct_ctr_fst. Defined.

(*
  Contractive Implies partially contractive in both variables
*)
Lemma CtrToSnd {X Y Z : eCategory} (F : eFunctorCtr (eprod_cat X Y) Z) :
  eFunctorCtrSnd X Y Z.
Proof.
  refine {| efunct_snd := F ; efunct_ctr_snd := _ |}.
  intros x A B n f g Hfg.
  unfold second_efunct. simpl.
  apply efunct_ctr. intros m Hm ; split ; simpl.
  - reflexivity.
  - eapply ofe_mono ; eauto.
Defined.


Lemma CtrToFst {X Y Z : eCategory} (F : eFunctorCtr (eprod_cat X Y) Z) :
  eFunctorCtrFst X Y Z.
Proof.
  refine {| efunct_fst := F ; efunct_ctr_fst := _ |}.
  intros y A B n f g Hfg.
  unfold first_efunct. simpl.
  apply efunct_ctr. intros m Hm ; split ; simpl.
  - eapply ofe_mono ; eauto.
  - reflexivity.
Defined.

  
Lemma fork_ctr_snd {W X Y Z : eCategory} (F : eFunctor (Z × Y) W) (G : eFunctor (Z × Y) X) :
  iseFunctorCtrSnd F /\ iseFunctorCtrSnd G -> iseFunctorCtrSnd (<| F, G |>) .
Proof.
  intros [HF HG].
  unshelve econstructor.
  intros [A1 A2] [B1 B2] h n f g Hfg ; split ; simpl in *.
  - apply (is_snd_funct_ctr F HF) ; [reflexivity | apply Hfg].
  - apply (is_snd_funct_ctr G HG) ; [reflexivity | apply Hfg].
Qed.

(*
  Characterization of contractive functors using the later category
 *)

Definition G_from_efunct_ctr_snd_efmap {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) :
  forall A B : eobj[X × later_ecat Y],
  A ~~{ X × later_ecat Y }~> B ->
  F A ~~{ Z }~> F B.
Proof.
  intros [A1 A2] [B1 B2] [f1 [f2]].
  apply (ebimap[F] f1 f2).
Defined.

Lemma G_from_efunct_ctr_snd_mixin {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) :
  eFunctMixin (eprod_cat X (later_ecat Y)) Z F (G_from_efunct_ctr_snd_efmap F).
Proof.
  unshelve econstructor.
  - intros [A1 A2] [B1 B2] n [f1 [f2]] [g1 [g2]] [Hfg1 Hfg2].
    transitivity (ebimap[F] g1 f2).
    + apply hom_ne; split ;  [exact Hfg1 | reflexivity].
    + apply efunct_ctr_snd. intros m Hm.
      destruct Hfg2 ; [lia | ].
      eapply ofe_mono ; eauto. lia.
  - intros [A1 A2]. simpl. rewrite ebimap_id //. 
  - intros [A1 A2] [B1 B2] [C1 C2] [f1 [f2]] [g1 [g2]]; simpl in *.
    by rewrite ebimap_ecompose.
Qed.

Definition G_from_efunct_ctr_snd {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z)
  : eFunctor (eprod_cat X (later_ecat Y)) Z :=
  {| efobj (X : eobj[X × later_ecat Y]) := F X ;
     efmap_mor := G_from_efunct_ctr_snd_efmap F ;
     efunct_mixin := G_from_efunct_ctr_snd_mixin F |}.

Lemma contractive_later_ecat_snd {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) : 
  { G : eFunctor (eprod_cat X (later_ecat Y)) Z | efunct_snd F = G ∘[eFUNCT] (times_efunctor (eID X) (enext_efunctor Y)) }.
Proof.
  exists (G_from_efunct_ctr_snd F).
  unshelve eapply efunctor_eq.
  - extensionality x; by destruct x.
  - intros [A1 A2] [B1 B2] [f1 f2]  ; simpl in *.
    apply eq_dep_refl.
Defined.

Lemma contractive_later_ecat_snd_char {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) :
  iseFunctorCtrSnd F <-> exists G, F = G ∘[eFUNCT] (times_efunctor (eID X) (enext_efunctor Y)).
Proof.
  split.
  - intros H.
    destruct (contractive_later_ecat_snd (toeFunctorCtrSnd H)) as [G H1].
    exists G; apply H1.
  - intros [G H]. subst F. unshelve econstructor.
    intros [A1 A2] [B1 B2] h n f g Hfg; simpl in *.
    apply efmap_mor_ne. split ; [reflexivity | ].
    destruct n ; [by left| right]. simpl.
    apply Hfg. lia.
Qed.

Definition G_from_efunct_ctr_fst_efmap {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) :
  forall A B : eobj[X × later_ecat Y],
  A ~~{ later_ecat X × Y }~> B ->
  F A ~~{ Z }~> F B.
Proof.
  intros [A1 A2] [B1 B2] [[f1] f2]; apply (ebimap[F] f1 f2).
Defined.
    
Lemma G_from_efunct_ctr_fst_mixin {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) :
  eFunctMixin (eprod_cat (later_ecat X) Y) Z F (G_from_efunct_ctr_fst_efmap F).
Proof.
  unshelve econstructor.
  - intros [A1 A2] [B1 B2] n [[f1] f2] [[g1] g2] [Hfg1 Hfg2] ; simpl in *.
    transitivity (ebimap[F] f1 g2).
    + apply hom_ne; split ; [reflexivity | exact Hfg2 ].
    + apply efunct_ctr_fst. intros m Hm.
      destruct Hfg1 ; [lia | ].
      eapply ofe_mono ; eauto; lia.
  - intros [A1 A2]. simpl. rewrite ebimap_id //. 
  - intros [A1 A2] [B1 B2] [C1 C2] [[f1] f2] [[g1] g2]; simpl in *.
    by rewrite ebimap_ecompose.
Qed.

Definition G_from_efunct_ctr_fst {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z)
  : eFunctor (eprod_cat (later_ecat X) Y) Z :=
  {| efobj (X : eobj[(later_ecat X) × Y]) := F X ;
     efmap_mor := G_from_efunct_ctr_fst_efmap F ;
     efunct_mixin := G_from_efunct_ctr_fst_mixin F |}.

Lemma contractive_later_ecat_fst {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) : 
  { G : eFunctor (eprod_cat (later_ecat X) Y) Z | efunct_fst F = compose_efunctor G (times_efunctor (enext_efunctor X) (eID Y)) }.
Proof.
  exists (G_from_efunct_ctr_fst F).
  unshelve eapply efunctor_eq.
  - extensionality x; by destruct x.
  - intros [A1 A2] [B1 B2] [f1 f2]; simpl in *.
    apply eq_dep_refl.
Defined.

Lemma contractive_later_ecat_fst_char {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) :
  iseFunctorCtrFst F <-> exists G, F = compose_efunctor G (times_efunctor (enext_efunctor X) (eID Y)).
Proof.
  split.
  - intros H.
    destruct (contractive_later_ecat_fst (toeFunctorCtrFst H)) as [G H1].
    exists G; apply H1.
  - intros [G H]. subst F. unshelve econstructor.
    intros [A1 A2] [B1 B2] h n f g Hfg; simpl in *.
    apply efmap_mor_ne. split ; [| reflexivity  ].
    destruct n ; [by left| right]. simpl.
    apply Hfg; lia.
Qed.
