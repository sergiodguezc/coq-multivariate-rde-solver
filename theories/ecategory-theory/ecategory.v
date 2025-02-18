From sgdt Require Import axioms category functor isomorphism finite_products closed terminal.
From sgdt Require Import ofe iCOFE icofe_ccc icofe_monoidal product.
Require Import ssreflect.

Structure eCatMixin (eobj : Type) (ehom : eobj -> eobj -> obj[iCOFE]) 
    (eid_mor : forall {x}, icofe_unit -> ehom x x)
    (ecompose_mor : forall {x y z}, tensor_prod (ehom y z, ehom x y) -> ehom x z) := {
  mixin_eid_ne {x} : NonExpansive (eid_mor (x:=x));
  mixin_eid {x} : icofe_unit ~{iCOFE}~> ehom x x := {|
    ne_mor := eid_mor (x:=x);
    hom_ne := mixin_eid_ne (x:=x)
  |};

  mixin_ecompose_ne {x y z} : NonExpansive (ecompose_mor (x:=x) (y:=y) (z:=z));
  mixin_ecompose {x y z} : tensor_prod (ehom y z, ehom x y) ~{iCOFE}~> ehom x z := {|
    ne_mor := ecompose_mor (x:=x) (y:=y) (z:=z);
    hom_ne := mixin_ecompose_ne (x:=x) (y:=y) (z:=z)
  |};

  mixin_eid_left' : forall x y, 
    mixin_ecompose ∘[iCOFE] (bimap[tensor_prod] (@mixin_eid y) id[ehom x y]) = to_left (ehom x y);
  mixin_eid_right' : forall x y,
    mixin_ecompose ∘[iCOFE] (bimap[tensor_prod] id[ehom x y] (@mixin_eid x)) = to_right (ehom x y);
  mixin_ecomp_assoc' : forall x y z w,
    mixin_ecompose ∘ bimap[tensor_prod] mixin_ecompose id[ehom x y] =
    mixin_ecompose ∘ bimap[tensor_prod] id[ehom z w] mixin_ecompose ∘ @from_assoc (ehom z w) (ehom y z) (ehom x y);
}.


Record eCategory : Type := mkECAT {
  eobj : Type;

  ehom : eobj -> eobj -> obj[iCOFE];

  eid_mor {x} : icofe_unit -> ehom x x;
  ecompose_mor {x y z} : tensor_prod (ehom y z, ehom x y) -> ehom x z;

  edom {x y} (f : ehom x y) := x;
  ecod {x y} (f : ehom x y) := y;

  ecat_mixin : eCatMixin eobj ehom (@eid_mor) (@ecompose_mor);
}.

(* Lift mixin properties *)
Definition eid {Y : eCategory} {x} : icofe_unit ~{iCOFE}~> ehom Y x x := mixin_eid _ _ _ _ (ecat_mixin Y).

Definition ecompose {Y : eCategory} {x y z} : tensor_prod (ehom Y y z, ehom Y x y) ~{iCOFE}~> ehom Y x z := mixin_ecompose _ _ _ _ (ecat_mixin Y).

Lemma eid_left' {Y : eCategory} {x y} : 
  ecompose ∘[iCOFE] (bimap[tensor_prod] (@eid Y y) id[ehom Y x y]) = to_left (ehom Y x y).
Proof. eapply mixin_eid_left'. Qed. 

Lemma eid_right' {Y : eCategory} {x y} : 
  ecompose ∘[iCOFE] (bimap[tensor_prod] id[ehom Y x y] (@eid Y x)) = to_right (ehom Y x y).
Proof. eapply mixin_eid_right'. Qed.

Lemma ecomp_assoc' {Y : eCategory} {x y z w} : 
  ecompose ∘ bimap[tensor_prod] ecompose id[ehom Y x y] =
  ecompose ∘ bimap[tensor_prod] id[ehom Y z w] ecompose ∘ @from_assoc (ehom Y z w) (ehom Y y z) (ehom Y x y).
Proof. eapply mixin_ecomp_assoc'. Qed.

Definition ecomp {Y : eCategory} {x y z} (f : ehom Y y z) (g : ehom Y x y) :
  ehom Y x z := ecompose (f, g).

Arguments ecomp {_} {_ _ _} _ _ : simpl never.

Definition coerce_eobj {Y Z : eCategory} 
  (H : eobj Y = eobj Z) (A : eobj Y) : eobj Z := eq_rect _ (fun x => x) A _ H.

Lemma coerce_eobj_id {Y : eCategory} (H : eobj Y = eobj Y) x :
  coerce_eobj H x = x.
Proof.
  by assert (H = eq_refl (@eobj Y)) as -> by (by apply proof_irrelevance).
Qed.

Definition icofe_eq_rect :=
  fun (A : Type) (x : A) (P : A -> iCOFE) (f : P x) (a : A) (e : x = a) =>
  match e in (_ = a0) return (P a0) with
  | eq_refl => f
  end.

Definition coerce_ehom {Y Z : eCategory} (H : eobj Y  = eobj Z)
  : eobj Z -> eobj Z -> obj[iCOFE] := eq_rect _ (fun T => T -> T -> obj[iCOFE]) (ehom Y) (eobj Z) H.

Definition ehom_eq {Y Z : eCategory} (H : eobj Y = eobj Z) (x y : eobj Z)  : Prop :=
  coerce_ehom H x y = ehom Z x y.

Lemma coerce_ehom_eq_id {Y : eCategory} (H : eobj Y = eobj Y) (x y : eobj Y)  : coerce_ehom H x y = ehom Y x y.
Proof. 
  by assert (H = eq_refl) as -> by (by apply proof_irrelevance).
Qed.

Lemma coerce_ehom_proper_eq {Y : eCategory} (H1 H2 : eobj Y = eobj Y) (x y z w : eobj Y) :
  x = z  -> y = w ->
  coerce_ehom H1 x y = coerce_ehom H2 z w.
Proof. 
  intros -> ->.
  by assert (H1 = H2) as -> by (by apply proof_irrelevance).
Qed.

Lemma ehom_eq_lemma {Y : eCategory} (H : eobj Y = eobj Y) (x y : eobj Y) :
  ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) = ehom Y x y.
Proof.
  rewrite -!(@coerce_ehom_eq_id).
  set H1 := (@coerce_ehom_proper_eq Y eq_refl eq_refl). 
  assert (H = eq_refl) as -> by (by apply proof_irrelevance).
  assert (eq_refl = eq_sym eq_refl) as <- by (by apply proof_irrelevance).
  apply H1 ; by rewrite coerce_eobj_id.
Qed. 

(* The following definition expreses when two eid_mor are equal *)

Definition coerce_eid_mor {Y Z : eCategory} (H : eobj Y = eobj Z)
(H2 : forall x y : eobj Z, ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) = ehom Z x y) (x : eobj Z)
  := icofe_eq_rect _ _ (fun x => x) (@eid_mor Y (coerce_eobj (eq_sym H) x) tt) _ (H2 x x) .

Lemma coerce_eid_mor_id {Y : eCategory} (H : eobj Y = eobj Y)
  (H2 : forall x y : eobj Y, ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) = ehom Y x y)
  (x : eobj Y) :
  coerce_eid_mor H H2 x = @eid_mor Y x tt.
Proof.
  assert (H = eq_refl) as -> by (by apply proof_irrelevance).
  unfold coerce_eid_mor. 
  assert (H2 x x = eq_refl) as -> by (by apply proof_irrelevance).
  reflexivity.
Qed.

Definition coerce_emor {Y Z : eCategory} (H : eobj Y = eobj Z)
  (H2 : forall x y : eobj Z, ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) = ehom Z x y) {x y : eobj Z}
  (f : ehom Z x y) : ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y).
Proof.
  set (H' := H2 x y).
  rewrite H'.
  exact f.
Defined.

Lemma coerce_emor_eq { Y : eCategory} 
  (H2 : forall x y : eobj Y, ehom Y (coerce_eobj (eq_sym eq_refl) x) (coerce_eobj (eq_sym eq_refl) y) = ehom Y x y)
  (x y : eobj Y) (f : ehom Y x y) : coerce_emor eq_refl H2 f = f.
Proof.
  set (H' := H2 x y).
  unfold coerce_emor.
  assert (H2 x y = eq_refl) as -> by (by apply proof_irrelevance).
  reflexivity.
Qed.

(* The following definition expreses when two ecompose_mor are equal *)
Definition coerce_ecompose_mor {Y Z : eCategory}  (H : eobj Y = eobj Z)
  (H2 : forall x y : eobj Z, ehom Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) = ehom Z x y) (x y z : eobj Z) 
  (f : ehom Z y z) (g : ehom Z x y) :=
  icofe_eq_rect _ _ (fun x => x) (@ecompose_mor Y (coerce_eobj (eq_sym H) x) (coerce_eobj (eq_sym H) y) (coerce_eobj (eq_sym H) z)
  (coerce_emor H H2 f, coerce_emor H H2 g)) _ (H2 x z) .

Lemma coerce_ecompose_mor_id {Y : eCategory} 
  (H2 : forall x y : eobj Y, ehom Y (coerce_eobj (eq_sym eq_refl) x) (coerce_eobj (eq_sym eq_refl) y) = ehom Y x y)
  (x y z : eobj Y) (f : ehom Y y z) (g : ehom Y x y) :
  coerce_ecompose_mor eq_refl H2 x y z f g = @ecompose_mor Y x y z (f, g).
Proof.
  unfold coerce_ecompose_mor. 
  assert (H2 x z = eq_refl) as -> by (by apply proof_irrelevance).
  simpl.
  rewrite !coerce_emor_eq. reflexivity.
Qed.

Lemma eCategory_eq (Y Z : eCategory)
  (H1 : eobj Y = eobj Z)
  (H2 : forall x y, ehom Y (coerce_eobj (eq_sym H1) x) (coerce_eobj (eq_sym H1) y) = ehom Z x y)
  (H3 : forall x, coerce_eid_mor H1 H2 x = @eid_mor Z x tt) 
  (H4 : forall x y z f g, coerce_ecompose_mor H1 H2 x y z f g = @ecompose_mor Z x y z (f, g)) :
  Y = Z.
Proof.
  destruct Y , Z.
  assert (eobj0 = eobj1) as ->.
  { simpl in H1. exact H1. }
  assert (ehom0 = ehom1) as ->.
  { apply functional_extensionality_dep => x.
    apply functional_extensionality_dep => y.
    simpl in H2.
    assert (H1 = eq_refl) as -> by (by apply proof_irrelevance).
    set H3'  := (H2 x y).
    assert (eq_sym (eq_refl eobj1) = eq_refl) as H3'' by (by apply proof_irrelevance).
    rewrite - (H2 x y).
    unfold coerce_eobj. reflexivity.
  }
  assert (eid_mor0 = eid_mor1) as ->.
  { apply functional_extensionality_dep => x.
    apply functional_extensionality_dep => y.
    destruct y.
    assert (H1 = eq_refl) as -> by (by apply proof_irrelevance).
    simpl in H3.
    rewrite -(H3 x).
    unfold coerce_eid_mor. simpl.
    assert (H2 x x = eq_refl) as -> by (by apply proof_irrelevance).
    reflexivity.
  }
  assert (ecompose_mor0 = ecompose_mor1) as ->.
  { apply functional_extensionality_dep => x.
    apply functional_extensionality_dep => y.
    apply functional_extensionality_dep => z.
    apply functional_extensionality_dep => t.
    destruct t as [f g].
    set (H5 := H4 x y z f g). simpl in H5.
    assert (H1 = eq_refl) as -> by (by apply proof_irrelevance).
    (* rewrite -> (coerce_ecompose_mor_id H2 x y z f g) in H4'. *)
    unfold coerce_ecompose_mor in H5. simpl in H5.
    assert (H2 x z = eq_refl) as H6 by (by apply proof_irrelevance).
    rewrite -> H6 in H5.
    simpl in H5.
    unfold coerce_emor in H5.
    assert (H2 y z = eq_refl) as H7 by (by apply proof_irrelevance).
    assert (H2 x y = eq_refl) as H8 by (by apply proof_irrelevance).
    rewrite -> H7 in H5.
    rewrite -> H8 in H5.
    simpl in H5.
    unfold eq_rect_r in H5.
    assert (eq_sym (eq_refl eobj1) = eq_refl) as H9 by (by apply proof_irrelevance).
    rewrite H5.
    reflexivity.
  }
  f_equal. apply proof_irrelevance.
Qed.

Coercion eobj : eCategory >-> Sortclass.

Declare Scope ofe_category_scope.
Declare Scope ofe_morphism_scope.

Notation "eobj[ C ]" := (@eobj C)
  (at level 0, format "eobj[ C ]") : ofe_category_scope.
Notation "ehom[ C ]" := (@ehom C)
 (at level 0, format "ehom[ C ]") : ofe_category_scope.

Notation "x ~~> y" := (@ehom _ x y)
  (at level 90, right associativity) : ofe_category_scope.
Notation "x ~~{ C }~> y" := (@ehom C x y)
  (at level 90) : ofe_category_scope.

Notation "eid[ x ]" := (@eid _ x)
  (at level 9, format "eid[ x ]") : ofe_morphism_scope.

Notation "eid{ C }" := (@eid C _)
  (at level 9, format "eid{ C }") : ofe_morphism_scope.

Notation "f ∘e g" :=
  (@ecomp _ _ _ _ f g) (at level 40, no associativity) : ofe_morphism_scope.
Notation "f ∘e[ C ] g" :=
  (@ecomp C _ _ _ _ f g) (at level 40, no associativity) : ofe_morphism_scope.

Open Scope ofe_category_scope.
Open Scope ofe_morphism_scope.

Lemma eid_mor_eq {C : eCategory} {x} : @eid_mor C x = eid[x].
Proof. reflexivity. Qed.

Lemma ecompose_mor_eq {C : eCategory} {x y z} : @ecompose_mor C x y z = @ecompose C x y z.
Proof. reflexivity. Qed.

Lemma eid_left_aux {C : eCategory} {x y}  : 
  forall f : 1 × (x ~~{ C }~> y), (ecompose ∘[ iCOFE] bimap[tensor_prod] eid[y] id[ehom C x y]) f = p_snd f.
Proof. intros. rewrite eid_left'. reflexivity. Qed.
  
Lemma eid_left {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecompose (eid[y] tt, f) = f.
Proof. 
  intros.
  unshelve epose (f' := _ : 1 × (x ~~{ C }~> y)).
  { by split. }
  replace f with (p_snd f') by done.
  replace tt with (p_fst f') by done.
  rewrite -{2}eid_left_aux. reflexivity.
Qed.

Lemma ecomp_eid_left {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecomp (@eid_mor C y tt) f = f. 
Proof. apply eid_left. Qed.

Lemma eid_left_mor {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecompose_mor C (@eid_mor C y tt, f) = f. 
Proof. apply eid_left. Qed.

Lemma eid_right_aux {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y) × 1, (ecompose ∘[ iCOFE] bimap[tensor_prod] id[ehom C x y] eid[x]) f = p_fst f.
Proof. intros. rewrite eid_right'. reflexivity. Qed.

Lemma eid_right {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecompose (f, eid[x] tt) = f.
Proof.
  intros.
  unshelve epose (f' := _ : (x ~~{ C }~> y) × 1).
  { by split. }
  replace f with (p_fst f') by done.
  replace tt with (p_snd f') by done.
  rewrite -{2}eid_right_aux. reflexivity.
Qed.

Lemma ecomp_eid_right {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecomp f (eid[x] tt) = f.
Proof. apply eid_right. Qed.

Lemma eid_right_mor {C : eCategory} {x y}  : 
  forall f : (x ~~{ C }~> y), ecompose_mor C (f, @eid_mor C x tt) = f.
Proof. apply eid_right. Qed.

Lemma ecomp_assoc_aux {C : eCategory} {x y z w}  : 
  forall f : (z ~~{ C }~> w) × (y ~~{ C }~> z) × (x ~~{ C }~> y),
       (ecompose ∘[ iCOFE] bimap[tensor_prod] (ecompose) id{iCOFE}) f =
       ((ecompose ∘[ iCOFE] bimap[tensor_prod] id{iCOFE} (ecompose))
       ∘[ iCOFE] from_assoc (z ~~{ C }~> w) (y ~~{ C }~> z) (x ~~{ C }~> y)) f.
Proof. intros.  rewrite ecomp_assoc'. reflexivity. Qed.

Lemma ecompose_assoc {C : eCategory} {x y z w}  {f : z ~~{ C }~> w} {g : y ~~{ C }~> z} {h : x ~~{ C }~> y} :
  ecompose (ecompose (f, g), h) = ecompose (f, ecompose (g, h)).
Proof.
  unshelve epose (f' := _ : (z ~~{ C }~> w) × (y ~~{ C }~> z) × (x ~~{ C }~> y)).
  { by repeat split. }
  set H :=  @ecomp_assoc_aux C x y z w f'. by simpl in H.
Qed.

Lemma ecomp_assoc {C : eCategory} {x y z w}  {f : z ~~{ C }~> w} {g : y ~~{ C }~> z} {h : x ~~{ C }~> y} :
  ecomp (ecomp f g) h = ecomp f (ecomp g h).
Proof. apply ecompose_assoc. Qed.

Lemma ecomp_assoc_mor {C : eCategory} {x y z w}  {f : z ~~{ C }~> w} {g : y ~~{ C }~> z} {h : x ~~{ C }~> y} :
  ecompose_mor C (ecompose_mor C (f, g), h) = ecompose_mor C (f, ecompose_mor C (g, h)).
Proof. apply ecomp_assoc. Qed. 

(* Create a HintDB for the category laws *)
Create HintDb ecat_db.
Hint Rewrite @ecomp_assoc_mor : ecat_db.
Hint Rewrite @ecomp_assoc : ecat_db.
Hint Rewrite @ecomp_assoc : ecat_db.
Hint Rewrite @eid_left_mor : ecat_db.
Hint Rewrite @eid_right_mor : ecat_db.
Hint Rewrite @ecomp_eid_left : ecat_db.
Hint Rewrite @ecomp_eid_right : ecat_db.

(* A tactic to simplify using the HintDB *)
Ltac simplify_ecat := simpl ;autorewrite with ecat_db.

(*  CONSTRUCTIONS OF CATEGORIES *)
(*  Definition of the opposite category *)

Lemma eOpposite_mixin (Z : eCategory) : eCatMixin (eobj Z) (fun A B => @ehom Z B A) (@eid_mor Z) (fun x y z f => ecompose (snd f, fst f)).
Proof.
  unshelve econstructor.
  - intros x n [] [] []. reflexivity.
  - intros x y z n [f1 f2] [g1 g2] [Hfg1 Hfg2]. 
    apply hom_ne. by split.
  - intros x y. apply icne_eq. intros [[] z]. simpl.
    by rewrite eid_mor_eq ecompose_mor_eq eid_right.
  - intros x y. apply icne_eq. intros [z []]. simpl.
    by rewrite eid_mor_eq ecompose_mor_eq eid_left.
  - intros x y z w. apply icne_eq. intros [[f g] h]. simpl.
    by rewrite !ecompose_mor_eq ecompose_assoc.
Qed.

Definition eOpposite (Z : eCategory) : eCategory := {|
  eobj := eobj Z;
  ehom := fun A B => @ehom Z B A;
  eid_mor := @eid_mor Z;
  ecompose_mor := fun x y z f => ecompose (snd f, fst f);
  ecat_mixin := eOpposite_mixin Z;
|}.

Notation "C ^op" := (@eOpposite C)
  (at level 7, format "C ^op", left associativity) : ofe_category_scope.

Definition to_op_mor {C : eCategory} {x y} (f : x ~~{C}~> y) : y ~~{C^op}~> x := f.

(* Definition one_eid_mor {C : eCategory} x : icofe_unit -> ehom C x x. *)
Lemma one_mixin : eCatMixin unit (fun _ _ => icofe_unit) (fun _ => (ne_mor id{iCOFE})) (fun _ _ _ _ => tt).
Proof.
  unshelve econstructor.
  - intros [] n [] [] []. reflexivity.
  - intros [] [] [] n [] []. reflexivity.
  - intros [] []. apply icne_eq. intros [[] []].
    reflexivity.
  - intros [] []. apply icne_eq. intros [[] []].
    reflexivity.
  - intros [] [] [] []. apply icne_eq. intros [[[] []] []].
    reflexivity.
Qed.

Definition one_ecat : eCategory := {|
  eobj := unit;
  ehom := fun _ _ => icofe_unit;
  eid_mor := fun _ => (ne_mor id{iCOFE});
  ecompose_mor := fun _ _ _ _ => tt;
  ecat_mixin := one_mixin;
 |}.

Lemma one_ecat_op : one_ecat^op = one_ecat.
Proof.
  unshelve eapply eCategory_eq; simpl.
  - reflexivity.
  - intros [] []. reflexivity.
  - intros []. reflexivity.
  - intros [] [] [] []. reflexivity.
Qed.

Lemma eop_id {C : eCategory} : @eid (C^op) = @eid C.
Proof. simpl. unfold eid. extensionality x. apply icne_eq. intros []. reflexivity. Qed.

Lemma eop_obj_eq {C : eCategory} : eobj[C ^op] = eobj[C].
Proof. reflexivity. Qed.

Lemma eop_mor_ecomp_eq {Y : eCategory} {A B C} (f : A ~~{Y}~> B) (g : B ~~{Y}~> C) :
  @ecomp Y^op _ _ _ f g = @ecomp Y _ _ _ g f.
Proof. reflexivity. Qed.

Lemma eop_mor_ecompose_eq {Y : eCategory} {A B C} (f : A ~~{Y}~> B) (g : B ~~{Y}~> C) :
  @ecompose Y^op _ _ _ (f, g) = @ecompose Y _ _ _ (g, f).
Proof. reflexivity. Qed.

Lemma eop_invol {C : eCategory} : (C^op)^op = C.
Proof.
  unshelve eapply eCategory_eq; simpl.
  - reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

Definition eprod_ehom {Y Z : eCategory} (A B : prod Y Z)
  := tensor_prod ((fst A ~~{Y}~> fst B), (snd A ~~{Z}~> snd B)).

Definition eprod_eid_mor {Y Z : eCategory} (A : prod Y Z) : icofe_unit -> eprod_ehom A A
  := fun _ => (eid{Y} tt, eid{Z} tt).

Definition eprod_ecompose_mor {Y Z : eCategory} {A B C : prod Y Z} :
  tensor_prod (eprod_ehom B C, eprod_ehom A B) -> eprod_ehom A C :=
  fun '(f, g) => (ecompose (fst f, fst g), ecompose (snd f, snd g)). 


Lemma eprod_mixin (Y Z : eCategory) : eCatMixin (prod (eobj Y) (eobj Z)) eprod_ehom eprod_eid_mor (@eprod_ecompose_mor Y Z).
Proof.
  unshelve econstructor.
  - intros [A B] n [] [] Hgf. split; reflexivity. 
  - intros [A1 A2] [B1 B2] [C1 C2] n [[f1 f2] [g1 g2]] [[h1 h2] [k1 k2]] [[Hfg1 Hfg2] [Hhk1 Hhk2]].
    split. 
    + unfold eprod_ecompose_mor. unfold fst.
      apply hom_ne. by split.
    + unfold eprod_ecompose_mor. unfold snd.
      apply hom_ne. by split.
  - intros [A B] [C D]. apply icne_eq. intros [[] [f1 f2]]. simpl.
    rewrite !eid_left_mor.
    reflexivity.
  - intros [A B] [C D]. apply icne_eq. intros [[f1 f2] []]. simpl.
    rewrite !eid_right_mor.
    reflexivity.
  - intros [A B] [C D] [E F] [G H]. apply icne_eq. intros [[[f1 g1] [f2 g2]] [f3 g3]]. simpl.
    rewrite !ecomp_assoc_mor.
    reflexivity.
Qed.

Definition eprod_cat (Y Z : eCategory) : eCategory := {|
  eobj := prod (eobj Y) (eobj Z);
  ehom := eprod_ehom;
  eid_mor := eprod_eid_mor;
  ecompose_mor := (@eprod_ecompose_mor Y Z);
  ecat_mixin := eprod_mixin Y Z;
 |}.

Notation "Y × Z" := (@eprod_cat Y Z)
  (at level 40, left associativity) : ofe_category_scope.

(* The product of n copies of a eCategory *)
Fixpoint nprod_ecat (n : nat) (C : eCategory) : eCategory :=
  match n with
  | O => one_ecat
  | S n' => (nprod_ecat n' C) × C
  end.

Notation "C ** n" := (@nprod_ecat n C) : ofe_category_scope .

Lemma eop_prod {Y Z : eCategory} : (Y × Z)^op = Y^op × Z^op.
Proof.
  unshelve eapply eCategory_eq; simpl.
  - reflexivity.
  - intros [x1 x2] [y1 y2]. reflexivity.
  - intros [x1 x2]. reflexivity.
  - intros [x1 x2] [y1 y2] [z1 z2] [f1 f2] [g1 g2]. reflexivity.
Qed.


(* Lift two morphisms to the product category *)
Definition eprod_mor {Y Z : eCategory} {A B : Y} {C D : Z}
  (f : A ~~> B) (g : C ~~> D) : (A, C) ~~{Y × Z}~> (B, D) := (f, g).

Definition eprod_mor_fst {Y Z : eCategory} {A B : Y} {C D : Z}
  (f : (A, C) ~~{Y × Z}~> (B, D)) : A ~~> B := fst f.

Definition eprod_mor_snd {Y Z : eCategory} {A B : Y} {C D : Z}
  (f : (A, C) ~~{Y × Z}~> (B, D)) : C ~~> D := snd f.

Lemma eprod_mor_ecompose {Y Z : eCategory} {A B C : Y} {D E F : Z}
  (f : A ~~> B) (h : B ~~> C) (g : E ~~> F) (k : D ~~> E) 
  : eprod_mor (ecompose (h, f)) (ecompose (g, k)) = ecompose  (eprod_mor h g, eprod_mor f k).
Proof. reflexivity. Qed.

Definition fst_mor {Y Z : eCategory} {A B : Y × Z}
  (f : A ~~{Y × Z}~> B) : fst A ~~{Y}~> fst B .
Proof. destruct A, B. exact (fst f). Defined.

Definition snd_mor {Y Z : eCategory} {A B : Y × Z}
  (f : A ~~{Y × Z}~> B) : snd A ~~{Z}~> snd B .
Proof. destruct A, B. exact (snd f). Defined.

Lemma eprod_mor_ecompose_2 {Y Z : eCategory} {A B C : Y} {D E F : Z}
  (f : (A,D) ~~{Y × Z}~> (B,E)) (h : (B, E) ~~{Y × Z}~> (C, F))
  : (ecompose (fst_mor h , fst_mor f), ecompose (snd_mor h, snd_mor f)) = ecompose  (h, f).
Proof. destruct f, h. reflexivity. Qed.

Lemma eop_mor_eq {Y : eCategory} {A B C : Y} 
  (f : A ~~> B) (g : B ~~> C) : @ecompose (Y^op) _ _ _  (f, g) = ecompose (g, f).
Proof. reflexivity. Qed.

