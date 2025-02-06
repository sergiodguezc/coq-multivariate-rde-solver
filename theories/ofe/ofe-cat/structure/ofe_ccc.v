From sgdt Require Import ofe axioms ofe category_theory OFE.
From Coq Require Import ssreflect.

(* Lift any type to an mkOFE *)
Lemma ofe_lift_mixin (A : Type) : OfeMixin A (fun _ x y => x = y).
Proof.
  split.
  - intros n; split.
    + by intros x. 
    + by intros x y.
    + intros x y z H1 H2. by transitivity y .
  - intros x y. split ; [eauto|]. intros H. apply H. exact 0%nat. (* ?? *)
  - intros n m x y H1 Hm. destruct H1. split ; eapply ofe_mono with (m := m); eauto.
Qed.

Definition ofe_lift (A : Type) : ofe := {|
  ofe_car := A;
  ofe_dist := fun _ x y => x = y;
  ofe_mixin := ofe_lift_mixin A
|}.

(* Unit ofe *)
Definition ofe_unit : ofe := ofe_lift unit.
Arguments ofe_unit : simpl never.


(* Terminal object *)
Global Instance OFE_Terminal : Terminal OFE.
Proof. 
  eapply mkTerminal with (terminal_obj := ofe_unit) ; simpl.
  - intros A. exists (fun _ => tt). by intros n x y H. 
  - intros A f g. ne_eq. by destruct (f x), (g x).
Defined.

(* Initial object *)
Global Instance OFE_Initial : Initial OFE. 
Proof.
  eapply mkInitial with (initial_obj := ofe_lift False) ; simpl.
  - intros A. exists (False_rect _). intros n x y H. destruct x.
  - intros A f g. ne_eq. destruct x.
Defined.

(* Product is the product of two objects *)

(* Projections*)
Program Definition ofe_fst {A B : ofe} : (ofe_prod A B) -n> A :=
  {| ne_mor := fst |}.
Next Obligation. intros n [x1 x2] [y1 y2] H; apply H. Qed.

Program Definition ofe_snd {A B : ofe} : (ofe_prod A B) -n> B :=
  {| ne_mor := snd |}.
Next Obligation. intros n [x1 x2] [y1 y2] H; apply H. Qed.

Program Definition ofe_fork {A B C : ofe} (f : C -n> A) (g : C -n> B) : C -n> (ofe_prod A B) :=
  {| ne_mor x := (f x, g x) |}.
Next Obligation. intros n x y H; split ; by apply hom_ne. Qed.

Global Instance OFE_Product : (FiniteProducts OFE) OFE_Terminal.
Proof.
  eapply mkProducts with (p_prod := ofe_prod) (p_fst := @ofe_fst) (p_snd := @ofe_snd) (fork := @ofe_fork) ; simpl.
  intros A B C f g h. split ; intros H.
    + split ; ne_eq ; by rewrite H.
    + destruct H as [H1 H2]. ne_eq. rewrite H1 H2 ; simpl. 
      by destruct (h x).
Defined.

(* Exponetial *)
Lemma ofe_exp_mixin (A B : ofe) : OfeMixin (A ~{OFE}~> B)
  (fun (n : nat) (f g : A ~{OFE}~> B) => forall x, ofe_dist B n (f x) (g x)).
Proof.
  split.
  - intros n ; split.
    + intros f x. reflexivity.
    + intros f g H1 x. by symmetry. 
    + intros f g h H1 H2 x. by transitivity (g x).
  - intros f g. split.
    + intros -> n x. reflexivity.
    + intros H. ne_eq. apply ofe_eq. intros n. apply H.
  - intros n m f g H1 H2 x. eapply ofe_mono with (m := m) ; eauto.
Qed.

Definition ofe_exp (A B : ofe) : ofe := {|
  ofe_car := A ~{OFE}~> B;
  ofe_dist := fun (n : nat) (f g : A ~{OFE}~> B) => forall x, ofe_dist B n (f x) (g x) ;
  ofe_mixin := ofe_exp_mixin A B
 |}.

(* Curry *)
Definition ofe_curry_f {A B C : ofe} (f : A × B ~> C) : A -> B -> C :=
  fun a b => f (a, b).

Lemma ofe_curry_f_nonexpansive {A B C : ofe} (f : A × B ~> C) :
  forall a, NonExpansive (ofe_curry_f f a).
Proof.
  intros a n b1 b2 H. unfold ofe_curry_f.
  apply hom_ne. simpl. split ; first reflexivity.
  by apply H.
Qed.

Definition ofe_curry_mor {A B C : ofe} (f : A × B ~> C) : A -> (B -n> C).
Proof.
  intros a. exists (ofe_curry_f f a). apply ofe_curry_f_nonexpansive.
Defined.

Definition ofe_curry_hom {A B C : OFE} (f : A × B ~> C) : A ~> (ofe_exp B C).
Proof.
  exists (fun a => ofe_curry_mor f a). intros n a1 a2 H b. 
  unfold ofe_curry_mor, ofe_curry_f. destruct f as [f Hf]. simpl in *.
  apply Hf. split ; last reflexivity. by apply H.
Defined.

(* Uncurry *)
Definition ofe_uncurry_f {A B C : OFE} (f : A ~> (ofe_exp B C)) : A × B -> C :=
  fun x => f (fst x) (snd x).

Lemma  ofe_uncurry_f_nonexpansive {A B C : OFE} (f : A ~> (ofe_exp B C)) :
  NonExpansive (ofe_uncurry_f f).
Proof.
  intros n x1 x2 H. unfold ofe_uncurry_f. simpl in *. 
  destruct H .
  set (ffst1 := f (fst x1)). set (ffst2 := f (fst x2)).
  unfold ofe_exp in ffst1, ffst2. simpl in *.
  assert (ofe_dist (ofe_exp B C) n ffst1 ffst2) by (by apply hom_ne).
  unfold ofe_exp in H1. simpl in H1. 
  set (H2 := H1 (snd x1)). set (H3 := H1 (snd x2)). 
  assert (ofe_dist C n (ffst1 (snd x1)) (ffst1 (snd x2))) by (by apply hom_ne).
  etransitivity ; eauto.
Qed.

Definition ofe_uncurry_mor {A B C : OFE} (f : A ~> (ofe_exp B C)) : (ofe_prod A B) -n> C.
Proof.
  exists (ofe_uncurry_f f). apply ofe_uncurry_f_nonexpansive.
Defined.

Definition ofe_exp_iso {A B C : OFE} : (A × B ~> C) ≃[ TYPE ] (A ~> ofe_exp B C).
Proof.
  eapply mkISO with (to := @ofe_curry_hom A B C) (from := @ofe_uncurry_mor A B C) ; simpl.
  - extensionality f. ne_eq. apply ofe_eq. intros n.
    destruct x. reflexivity.
  - extensionality f. ne_eq. apply ofe_eq. intros n.
    unfold ofe_exp. simpl. intros b. apply ofe_equiv.
Defined.

Global Instance OFE_CCC : (CCC OFE) OFE_Product.
Proof.
  eapply mkCCC with (exp := ofe_exp) (exp_iso := @ofe_exp_iso) ; simpl.
  intros. apply ne_eq. intros x. apply ofe_eq. intros n. 
  unfold ofe_curry_hom, ofe_uncurry_mor, ofe_curry_mor, ofe_curry_f, ofe_uncurry_f. simpl.
  destruct x. reflexivity.
Defined.
