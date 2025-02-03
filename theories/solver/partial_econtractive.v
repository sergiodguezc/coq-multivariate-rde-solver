From sgdt Require Import ecategory ofe iCOFE icofe_ccc einstances efunctor econtractive.

Require Import ssreflect PropExtensionality.
(*
  Partial contractive functors
*)

Record eFunctorCtrSnd (X Y Z : eCategory)  : Type := {
  efunct_snd :> eFunctor (eprod_cat X Y) Z;
  efunct_ctr_snd {x : X} {A B} : Contractive (@efmap _ _ (second_efunct efunct_snd x) A B)
}.
(* Coercion efunct_snd : eFunctorCtrSnd >-> eFunctor. *)
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
  is_efunct_ctr_snd {x : X} {A B} : Contractive (@efmap _ _ (second_efunct F x) A B)
}.

Lemma second_efunctor_ctr_partial {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z)
  (x : X) :
  iseFunctorCtr (second_efunct F x).
Proof.
  refine {| is_efunct_ctr := _ |}.
  apply efunct_ctr_snd.
Qed.

Lemma snd_funct_ctr {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) {A B C} :
  forall n  (y1 y2 : B ~~> C), dist_later n y1 y2 ->
  ebimap[F] (@eid_mor X A tt) y1 ≡{ n }≡ ebimap[F] (@eid_mor X A tt) y2.
Proof.
  intros n y1 y2 H.
  apply efunct_ctr_snd. exact H.
Qed.

Lemma is_snd_funct_ctr {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) (H : iseFunctorCtrSnd F) {A B C} :
  forall n  (y1 y2 : B ~~> C), dist_later n y1 y2 ->
  ebimap[F] (@eid_mor X A tt) y1 ≡{ n }≡ ebimap[F] (@eid_mor X A tt) y2.
Proof.
  intros n y1 y2 H1.
  apply (is_efunct_ctr_snd F H). exact H1.
Qed.

Lemma toeFunctorCtrSnd {X Y Z : eCategory} {F : eFunctor (eprod_cat X Y) Z} (H : iseFunctorCtrSnd F) : eFunctorCtrSnd X Y Z.
Proof. refine {| efunct_snd := F ; efunct_ctr_snd := _ |}. apply H. Defined.

Lemma toiseFunctorCtrSnd {X Y Z : eCategory} (H : @eFunctorCtrSnd X Y Z) : iseFunctorCtrSnd (efunct_snd H).
Proof. refine {| is_efunct_ctr_snd := _ |}. apply efunct_ctr_snd. Defined.

Lemma compose_efunctor_ctrsnd_left {W X Y Z : eCategory}
(F : eFunctorCtrSnd W X Y) (G : eFunctor Y Z) : iseFunctorCtrSnd (G∘[eFUNCT] F).
Proof.
  unshelve econstructor.
  intros x A B n f g Hfg ; simpl.
  rewrite -!ebimap_efmap.
  rewrite !efmap_ecomp_efunct. 
  apply hom_ne. 
  by apply snd_funct_ctr.
Qed.

Lemma compose_efunctor_isctrsnd_left {W X Y Z : eCategory}
  (F : eFunctor (eprod_cat W X) Y) (G : eFunctor Y Z) (H : iseFunctorCtrSnd F)
  : iseFunctorCtrSnd (G∘[eFUNCT] F).
Proof.
  unshelve econstructor.
  intros x A B n f g Hfg ; simpl.
  rewrite -!ebimap_efmap.
  rewrite !efmap_ecomp_efunct. 
  apply hom_ne. 
  rewrite ebimap_efmap.
  by apply (is_efunct_ctr_snd F H).
Qed.

Record eFunctorCtrFst (X Y Z : eCategory)  : Type := {
  efunct_fst :> eFunctor (eprod_cat X Y) Z;
  efunct_ctr_fst {y : Y} {A B} : Contractive (@efmap _ _ (first_efunct efunct_fst y) A B)
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
  is_efunct_ctr_fst {y : Y} {A B} : Contractive (@efmap _ _ (first_efunct F y) A B)
}.

Lemma first_efunctor_ctr_partial {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z)
  (y : Y) :
  iseFunctorCtr (first_efunct F y).
Proof.
  refine {| is_efunct_ctr := _ |}.
  apply efunct_ctr_fst.
Qed.

Lemma fst_funct_ctr {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) {A B C} :
  forall n  (x1 x2 : A ~~> B), dist_later n x1 x2 ->
  ebimap[F] x1 (@eid_mor Y C tt) ≡{ n }≡ ebimap[F] x2 (@eid_mor Y C tt).
Proof.
  intros n x1 x2 H.
  apply efunct_ctr_fst. exact H.
Qed.

Lemma is_fst_funct_ctr {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) (H : iseFunctorCtrFst F) {A B C} :
  forall n  (x1 x2 : A ~~> B), dist_later n x1 x2 ->
  ebimap[F] x1 (@eid_mor Y C tt) ≡{ n }≡ ebimap[F] x2 (@eid_mor Y C tt).
Proof.
  intros n x1 x2 H1.
  apply (is_efunct_ctr_fst F H). exact H1.
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

(*
  Characterization of contractive functors using the later category
 *)

(* Theorem G_from_efunct_ctr_snd {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) *)
(*   : eFunctor (eprod_cat X (later_ecat Y)) Z. *)
(* Proof. *)
(*   unshelve eexists. *)
(*   - unshelve eapply mkEFUNCT. *)
(*     + intros A. exact (F A). *)
(*     + intros [A1 A2] [B1 B2]. simpl in *. *)
(*       unshelve epose (g := _ : (A ~~> B) -c> (F A ~~> F B)). *)
(*       {  *)
(*         exists (fun (f : A ~~> B) => efmap F f). apply efunct_ctr. *)
(*       } *)
(*       destruct (contractive_ilaterT g) as [g' geq]. *)
(*       apply g'. *)
(*     + intros A. simpl. by simplify_efunct. *)
(*     + intros A B C [f] [g]. simpl. by simplify_efunct. *)
(*   - intros A B. simpl. *)
(*     unshelve eexists. *)
(*     + intros [f]. apply (efmap F f). *)
(*     + intros n [f1] [f2] Hf.  *)
(*       apply efunct_ctr. *)
(*       intros m Hm. *)
(*       destruct Hf ; [lia | ]. *)
(*       eapply ofe_mono ; eauto. lia. *)
(*   - intros A. simpl. by simplify_efunct. *)
(*   - intros A B C [f] [g]. simpl. by simplify_efunct. *)
(* Defined. *)

(* Lemma contractive_later_ecat_snd {X Y Z : eCategory} (F : eFunctorCtrSnd X Y Z) :  *)
(*   { G : eFunctor (eprod_cat X (later_ecat Y)) Z | efunct_snd F = compose_efunctor G (times_efunctor (eID X) (enext_efunctor Y)) }. *)
(* Proof. *)
(* Admitted. *)
(**)
(* Lemma contractive_later_ecat_fst {X Y Z : eCategory} (F : eFunctorCtrFst X Y Z) :  *)
(*   { G : eFunctor (eprod_cat (later_ecat X) Y) Z | efunct_fst F = compose_efunctor G (times_efunctor (enext_efunctor X) (eID Y)) }. *)
(* Proof. *)
(* Admitted. *)

(*
  Partial contractive functors
 *)

(* Lemma second_efunctor_ctr_partial {X Y Z : eCategory} (F : eFunctor (eprod_cat X Y) Z) *)
(*   (H : eFunctorCtrSnd F) (x : X) : *)
(*   iseFunctorCtr (second_efunct F x). *)
(* Proof. *)
(*   refine {| is_efunct_ctr := _ |}. *)
(*   intros A B n f g Hfg. *)
(*   destruct H as [G Geq]. rewrite Geq. *)
(*   unfold compose_efunctor. unfold second_efunct.  *)
(*   unfold ebimap, efmap. simpl. *)
(*   apply hom_ne ; split ; first reflexivity. *)
(*   destruct n; simpl ; [left ; trivial | right ; apply Hfg ; lia]. *)
(* Qed. *)
