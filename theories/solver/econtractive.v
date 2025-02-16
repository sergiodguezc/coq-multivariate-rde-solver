From sgdt Require Import axioms ofe ecategory functor later iCOFE icofe_ccc later efunctor einstances eisomorphism.
From Coq Require Import ssreflect Lia.

Record eFunctorCtr (Y Z : eCategory)  : Type := {
  efunct : eFunctor Y Z;
  efunct_ctr {A B} : Contractive (@efmap _ _ efunct A B)
}.
Coercion efunct : eFunctorCtr >-> eFunctor.

Notation eEndoFunctorCtr Y := (eFunctorCtr Y Y).

Lemma efunctor_ctr_eq {Y Z : eCategory} (F G : eFunctorCtr Y Z) :
  efunct _ _ F = efunct _ _ G -> F = G.
Proof. intros HFG. destruct F, G. simpl in *. subst. f_equal. apply proof_irrelevance. Qed.

Record iseFunctorCtr {Y Z : eCategory} (F : eFunctor Y Z) : Prop := {
  is_efunct_ctr {A B} : Contractive (@efmap _ _ F A B)
}.

Lemma toeFunctorCtr {Y Z : eCategory} {F : eFunctor Y Z} (H : iseFunctorCtr F) : eFunctorCtr Y Z.
Proof. refine {| efunct := F ; efunct_ctr := @is_efunct_ctr _ _ F H |}. Defined.

Lemma toiseFunctorCtr {Y Z : eCategory} (H : @eFunctorCtr Y Z) : iseFunctorCtr (efunct _ _ H).
Proof. refine {| is_efunct_ctr := @efunct_ctr _ _ H |}. Defined.

Coercion toFunctorCtr {Y Z : eCategory} {F : eFunctor Y Z} (H : iseFunctorCtr F) : eFunctorCtr Y Z := toeFunctorCtr H.

Definition const_efunctor_ctr {Y : eCategory} (A : Y) : eFunctorCtr one_ecat Y.
Proof.
  refine {| efunct := const_efunctor A ; efunct_ctr := _ |}.
  intros [] [] n [] [] Hfg.  reflexivity.
Defined.

Definition second_efunctor_ctr {X Y Z : eCategory} (F : eFunctorCtr (eprod_cat X Y) Z) (x : X) : eFunctorCtr Y Z.
Proof.
  refine {| efunct := second_efunct F x ; efunct_ctr := _ |}.
  intros A B n f g Hfg.
  apply efunct_ctr.
  split ; simpl  ; [reflexivity | by apply Hfg].
Defined.

Definition first_efunctor_ctr {X Y Z : eCategory} (F : eFunctorCtr (eprod_cat X Y) Z) (y : Y) : eFunctorCtr X Z.
Proof.
  refine {| efunct := first_efunct F y ; efunct_ctr := _ |}.
  intros A B n f g Hfg.
  apply efunct_ctr.
  split ; simpl  ; [by apply Hfg | reflexivity ].
Defined.

Lemma compose_efunctor_ctr_left {X Y Z : eCategory} (F : eFunctorCtr Y Z) (G : eFunctor X Y) : iseFunctorCtr (compose_efunctor F G).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg.
  apply efunct_ctr.
  intros m Hm.
  apply hom_ne. by apply Hfg.
Qed.

Lemma compose_efunctor_isctr_left {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) (H : iseFunctorCtr F) : iseFunctorCtr (compose_efunctor F G).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg.
  apply (is_efunct_ctr F H).
  intros m Hm.
  apply hom_ne. by apply Hfg.
Qed.

Lemma compose_efunctor_ctr_right {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctorCtr X Y) : iseFunctorCtr (compose_efunctor F G).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg ; simpl.
  apply efmap_mor_ne.
  by apply efunct_ctr.
Qed.

Lemma compose_efunctor_isctr_right {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) (H : iseFunctorCtr G) : iseFunctorCtr (compose_efunctor F G).
Proof.
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg ; simpl.
  apply efmap_mor_ne.
  by apply H.
Qed.

Lemma enext_efunctor_mixin (Y : eCategory) : eFunctMixin Y (later_ecat Y) (fun A => A) (fun A B f => next f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. destruct n ; [by left | right].
    simpl. eapply ofe_mono. by apply Hfg. lia.
  - intros A. reflexivity.
  - intros A. reflexivity.
Qed.

Definition enext_efunctor (Y : eCategory) : eFunctor Y (later_ecat Y) := {|
  efobj := fun A : Y => A : later_ecat Y ;
  efmap_mor := fun A B f => next f ;
  efunct_mixin := enext_efunctor_mixin Y
|}.


Definition G_from_efunct_ctr_efmap {Y Z : eCategory} (F : eFunctorCtr Y Z) (A B : later_ecat Y) (f : A ~~> B) : F A ~~> F B.
Proof.
  unshelve epose (g := _ : (A ~~{Y}~> B) -c> (F A ~~> F B)).
  { exists (fun (h : A ~~{Y}~> B) => efmap_mor F h). apply efunct_ctr. }
  destruct (contractive_ilaterT g) as [g' _].
  apply g'. exact f.
Defined.

Lemma G_from_efunct_ctr_mixin {Y Z : eCategory}
(F : eFunctorCtr Y Z) : eFunctMixin (later_ecat Y) Z  (fun A => F A) (@G_from_efunct_ctr_efmap _ _ F).
Proof.
  - unshelve econstructor.
    + intros A B n [f] [g] Hfg. simpl. apply efunct_ctr.
      intros m Hm. simpl in *.
      destruct Hfg ; first lia.
      eapply ofe_mono ; eauto. lia.
    + intros A.
      unfold G_from_efunct_ctr_efmap. by simplify_efunct.
    + intros A B C [f] [g].
      unfold G_from_efunct_ctr_efmap. by simplify_efunct.
Qed.

Definition G_from_efunct_ctr {Y Z : eCategory} (F : eFunctorCtr Y Z) : eFunctor (later_ecat Y) Z := {|
    efobj := fun A : later_ecat Y => F A ;
    efmap_mor := (@G_from_efunct_ctr_efmap _ _ F) ;
    efunct_mixin := G_from_efunct_ctr_mixin F
|}.
      
Theorem contractive_later_ecat {Y Z : eCategory} (F : eFunctorCtr Y Z) : 
  { G : eFunctor (later_ecat Y) Z | (efunct _ _ F) = compose_efunctor G (enext_efunctor Y) }. 
Proof.
  exists (G_from_efunct_ctr F).
  unshelve eapply efunctor_eq.
  - extensionality A. reflexivity.
  - intros A B f. 
    assert (eq_refl = (functional_extensionality F (G_from_efunct_ctr F∘[eFUNCT] enext_efunctor Y) (fun A0 : eobj[Y] => eq_refl))) as H.
    { apply proof_irrelevance. }
    rewrite -H.
    reflexivity.
Qed.

Theorem later_ecat_contractive {Y Z : eCategory} (F : eFunctor Y Z)
  (H : { G : eFunctor (later_ecat Y) Z | F = compose_efunctor G (enext_efunctor Y) })
  : iseFunctorCtr F.
Proof.
  destruct H as [G ->].
  refine {| is_efunct_ctr := _ |}.
  intros A B n f g Hfg.
  rewrite /= .
  apply efmap_mor_ne.
  destruct n ; [by left|].
  right. apply Hfg. lia.
Qed.

Theorem later_ecat_contractive_char {Y Z : eCategory} (F : eFunctor Y Z) :
  iseFunctorCtr F <-> exists G : eFunctor (later_ecat Y) Z , F = compose_efunctor G (enext_efunctor Y) .
Proof.
  split.
  - intros H. destruct (contractive_later_ecat (toeFunctorCtr H)) as [G H1].
    exists G. apply H1.
  - intros [G HG].
    apply later_ecat_contractive.
    by exists G.
Qed.

Theorem swap_funct_ctr {X Y Z : eCategory} (F : eFunctorCtr (X × Y) Z) : eFunctorCtr (Y × X) Z.
Proof.
  unshelve refine {| efunct := swap_efunct F |}.
  intros [A1 A2] [B1 B2] n [f1 f2] [g1 g2] Hfg.
  unfold swap_efunct in *; simpl in *.
  unfold dist_later in *; simpl in *.
  apply efunct_ctr ; intros m Hm.
  specialize (Hfg m Hm).
  by destruct Hfg.
Defined.
