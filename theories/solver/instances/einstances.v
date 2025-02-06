From sgdt Require Import category functor efunctor ecategory ofe OFE ofe_ccc iCOFE icofe_ccc icofe_monoidal product.
From sgdt Require Import later.
Require Import ssreflect Lia.

Open Scope ofe_category_scope.
Open Scope ofe_morphism_scope.

Lemma eiCOFE_mixin :
  eCatMixin (obj[iCOFE]) (icofe_exp) (fun A _ => id[A]) (fun A B C '(f, g) => @compose iCOFE _ _ _ f g).
Proof.
  unshelve econstructor.
  - intros A n f g Hfg. reflexivity.
  - intros A B C n [f1 f2] [g1 g2] [Hf Hg] z. simpl in *.
    rewrite Hf. by apply hom_ne. 
  - intros A B. apply icne_eq. intros [f1 f2]. simpl in *. 
    by rewrite id_left.
  - intros A B. apply icne_eq. intros [f1 f2]. simpl in *. 
    by rewrite id_right.
  - intros A B C D. apply icne_eq. intros [[f1 f2] f3]. simpl in *.
    by rewrite comp_assoc.
Qed.

Definition eiCOFE : eCategory := {|
  eobj := obj[iCOFE];
  ehom := icofe_exp;
  eid_mor := fun A _ => id[A];
  ecompose_mor := fun A B C '(f, g) => @compose iCOFE _ _ _ f g;
  ecat_mixin := eiCOFE_mixin
|}.

Lemma later_ecat_mixin (Y : eCategory) :
  eCatMixin (eobj[Y]) (fun A B => ilaterF (ehom[Y] A B))
  (fun A _ => next (eid{Y} tt)) (fun A B C '(f, g) => 
      match f, g with
      | next f, next g => next (ecomp f g)
      end).
Proof.
  unshelve econstructor.
  - intros A n f g Hfg. reflexivity.
  - intros A B C n [[f1] [f2]] [[g1] [g2]] [Hf Hg]. unfold fst, snd in Hf, Hg.
    destruct n ; [by left | right].
    destruct Hf as [? | Hf] ; first lia. destruct Hg as [? | Hg] ; first lia.
    simpl in *; replace (n - 0) with n in * by lia.
    apply hom_ne. by split.
  - intros A B. apply icne_eq. intros [[] [f]]. simpl in *. 
    by simplify_ecat.
  - intros A B. apply icne_eq. intros [[f] []]. simpl in *. 
    by simplify_ecat.
  - intros A B C D. apply icne_eq. intros [[[f] [g]] [h]]. simpl in *.
    by rewrite ecomp_assoc.
Qed.

Definition later_ecat (Y : eCategory) : eCategory := {|
  eobj := eobj[Y];
  ehom := fun A B => ilaterF (ehom[Y] A B);
  eid_mor := fun A _ => next (eid{Y} tt);
  ecompose_mor := fun A B C '(f, g) => 
      match f, g with
      | next f, next g => next (ecomp f g)
      end;
  ecat_mixin := later_ecat_mixin Y
 |}.

Definition later_ecat_ehom_eq {Y : eCategory} (A B : Y) (f : A ~~{later_ecat Y}~> B)
  : ilaterF (A ~~{Y}~> B) := f.


Lemma later_prod_mixin (Y Z : eCategory) :
  eFunctMixin (later_ecat (eprod_cat Y Z)) (eprod_cat (later_ecat Y) (later_ecat Z))
  (fun A => A) (fun '(A1, A2) '(B1, B2) f => 
    match f with
    | next f =>
        match f with (f1, f2) => (next f1, next f2) end
    end).
Proof.
  unshelve econstructor.
  - intros [A1 A2] [B1 B2] n [[f1 f2]] [[g1 g2]] [Hfg1 | Hfg2]; simpl in *.
    + subst. split; simpl ; by left.
    + split; simpl ; right; simpl ;
      by destruct Hfg2 . 
  - intros [A1 A2]. reflexivity.
  - intros [A1 A2] [B1 B2] [C1 C2] [f1] [g1]. 
    destruct f1, g1. reflexivity.
Qed.

Definition later_prod {Y Z : eCategory } :
  eFunctor (later_ecat (eprod_cat Y Z)) (eprod_cat (later_ecat Y) (later_ecat Z)) := {|
    efobj := fun A : later_ecat (eprod_cat Y Z) => A : eprod_cat (later_ecat Y) (later_ecat Z);
    efmap_mor := fun '(A1, A2) '(B1, B2) f => 
      match f with
      | next f =>
          match f with (f1, f2) => (next f1, next f2) end
      end;
    efunct_mixin := later_prod_mixin Y Z
 |}.


Definition niCOFE := later_ecat eiCOFE.
