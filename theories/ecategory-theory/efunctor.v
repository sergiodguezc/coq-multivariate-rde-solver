From sgdt Require Import axioms category ecategory ofe iCOFE eisomorphism.
From Coq Require Import ssreflect.

Structure eFunctMixin (Y Z : eCategory)
  (efobj : Y -> Z) (efmap : forall {A B : eobj Y}, (A ~~> B) -> ((efobj A) ~~> (efobj B))) := {

    mixin_efmap_ne {A B} : NonExpansive (@efmap A B);
    mixin_efmap {A B : eobj Y} : (A ~~> B) ~{iCOFE}~> ((efobj A) ~~> (efobj B)) := {|
      ne_mor := @efmap A B ;
      hom_ne := @mixin_efmap_ne A B
    |};

    mixin_efmap_id {A} : mixin_efmap (eid[A] tt) = eid[(efobj A)] tt;

    mixin_efmap_ecomp {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
        mixin_efmap (ecomp f g) = ecomp (mixin_efmap f) (mixin_efmap g)
}.

Record eFunctor (Y Z : eCategory) := mkEFUNCT
  { efobj : Y -> Z;
    efmap_mor {A B : eobj Y} : (A ~~> B) -> ((efobj A) ~~> (efobj B));

    efunct_mixin : eFunctMixin _ _ efobj (@efmap_mor)
  }.
Coercion efobj : eFunctor >-> Funclass.

(* Lift the mixin *)
Definition efmap {Y Z : eCategory} (F : eFunctor Y Z) {A B : eobj Y} :
  (A ~~> B) ~{iCOFE}~> ((F A) ~~> (F B)) := {|
    ne_mor := @efmap_mor _ _ F A B ;
    hom_ne := @mixin_efmap_ne _ _ F (@efmap_mor _ _ F) (efunct_mixin _ _ F) A B
  |}.
Arguments efmap {Y Z} F {A B} : rename.
Arguments efmap_mor {Y Z} F {A B} : rename.

Lemma efmap_mor_ne {Y Z : eCategory} (F : eFunctor Y Z) {A B} :
  NonExpansive (@efmap_mor Y Z F A B).
Proof. apply (mixin_efmap_ne _ _ F). apply efunct_mixin. Qed.

Lemma efmap_id {Y Z : eCategory} (F : eFunctor Y Z) {A} :
  efmap F (eid[A] tt) = eid[(F A)] tt.
Proof. apply mixin_efmap_id. Qed.

Lemma efmap_mor_id {Y Z : eCategory} (F : eFunctor Y Z) {A} :
  efmap_mor F (eid[A] tt) = eid[(F A)] tt.
Proof. apply efmap_id. Qed.

Lemma efmap_ecomp {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap F (ecomp f g) = ecomp (efmap F f) (efmap F g).
Proof. apply mixin_efmap_ecomp. Qed.

Lemma efmap_mor_ecomp {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap_mor F (ecomp f g) = ecomp (efmap_mor F f) (efmap_mor F g).
Proof. apply efmap_ecomp. Qed.

Lemma efmap_ecompose {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap F (ecompose (f, g)) = ecompose (efmap F f, efmap F g).
Proof. by rewrite efmap_ecomp. Qed.

Lemma efmap_mor_ecompose {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap_mor F (ecompose (f, g)) = ecompose (efmap_mor F f, efmap_mor F g).
Proof. by rewrite efmap_mor_ecomp. Qed.

Lemma efmap_ecompose_mor {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap F (ecompose_mor Y (f, g)) = ecompose_mor Z (efmap F f, efmap F g).
Proof. by rewrite efmap_ecompose. Qed.

Lemma efmap_mor_ecompose_mor {Y Z : eCategory} (F : eFunctor Y Z) {A B C : Y} (f : B ~~> C) (g : A ~~> B) :
  efmap_mor F (ecompose_mor Y (f, g)) = ecompose_mor Z (efmap_mor F f, efmap_mor F g).
Proof. by rewrite efmap_mor_ecompose. Qed.

Notation "F →  G" := (eFunctor F G) (at level 90) : ofe_category_scope.

Lemma efunctor_eq {Y Z : eCategory} (F G : eFunctor Y Z) ( H1 : efobj Y Z F = efobj Y Z G)
  ( H2 : forall x y (f : ehom Y x y), eq_dep ofe ofe_car _ (efmap F f) _ (efmap G f)) : F = G.
Proof.
  destruct F as [F fmapF HF1], G as [G fmapG HG1].
  assert (F = G) as -> by apply H1.
  assert (fmapF = fmapG) as -> .
  { extensionality x; extensionality y; extensionality f.
    set (H := H2 x y f); simpl in *.
    by apply eq_dep_eq.
  }
  f_equal ; apply proof_irrelevance.
Qed.

Lemma efunctor_preserve_eiso {Y Z : eCategory} (F : eFunctor Y Z) {x y : Y} (H : x ≃ y) :
  F x ≃ F y.
Proof.
  eapply mkEISO with (eto := efmap F (eto H)) (efrom := efmap F (efrom H)).
  - by rewrite - efmap_ecomp (efrom_to H) efmap_id.
  - by rewrite - efmap_ecomp (eto_from H) efmap_id.
Qed. 

Create HintDb efunct_db.
Hint Rewrite @efmap_id : efunct_db.
Hint Rewrite @efmap_mor_id : efunct_db.
Hint Rewrite @efmap_ecompose : efunct_db.
Hint Rewrite @efmap_mor_ecompose : efunct_db.
Hint Rewrite @efmap_mor_ecomp : efunct_db.
Hint Rewrite @efmap_ecomp : efunct_db.
Hint Rewrite @efmap_ecompose_mor : efunct_db.
Hint Rewrite @efmap_mor_ecompose_mor : efunct_db.

(* A tactic to simplify using the HintDB *)
Ltac simplify_efunct := simpl ; autorewrite with efunct_db ecat_db.

(* Constant efunctor *)
Lemma const_mixin {Y : eCategory} (X : Y) : eFunctMixin one_ecat Y (fun _ => X) (fun _ _ _ => eid{Y} tt).
Proof.
  unshelve econstructor.
  - intros [] [] n [] [] [].
    reflexivity.
  - intros []. reflexivity.
  - intros [] [] [] [] [].
    by rewrite !ecomp_eid_left.
Qed.

Definition const_efunctor {Y : eCategory} (X : Y) : one_ecat → Y := {|
  efobj := fun _ => X;
  efmap_mor := fun _ _ _ => eid{Y} tt;
  efunct_mixin := const_mixin X
 |}.


(*  Identity efunctor *)
Lemma id_efunct_mixing {Y : eCategory} : eFunctMixin Y Y (fun x => x) (fun A B f => f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. by apply Hfg.
  - intros A. reflexivity.
  - intros A B C f g. reflexivity.
Qed.

Definition id_efunctor (X : eCategory) : eFunctor X X := {|
  efobj := fun x => x;
  efmap_mor := fun A B f => f;
  efunct_mixin := @id_efunct_mixing X
|}.

Notation eID := id_efunctor.

(*  Composition of functors *)
Lemma compose_efunctor_mixin {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) :
  eFunctMixin X Z (fun x => F (G x)) (fun A B f => efmap F (efmap G f)).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. by repeat apply hom_ne.
  - intros A. by simplify_efunct.
  - intros A B C f g. by simplify_efunct.
Qed.

Definition compose_efunctor {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) : eFunctor X Z := {|
  efobj := fun x => F (G x);
  efmap_mor := fun A B f => efmap F (efmap G f);
  efunct_mixin := @compose_efunctor_mixin X Y Z F G
|}.

Notation "F ∘[eFUNCT] G" := (compose_efunctor F G) (at level 40) : ofe_category_scope.

Lemma efmap_ecomp_efunct {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) {A B : X} (f : A ~~{X}~> B) :
  efmap (F ∘[eFUNCT] G) f = efmap F (efmap G f).
Proof. reflexivity. Qed.

Lemma pfst_ne {Y Z : eCategory} (A B : eobj[Y × Z]) :
  NonExpansive (fun f : A ~~{ Y × Z }~> B => fst f).
Proof. 
  intros n [f1 f2] [g1 g2] [H1 H2]; by apply H1.
Qed.

Lemma pfst_efunct_mixin {Y Z : eCategory} : eFunctMixin (Y × Z) Y (fun x => fst x) (fun A B f => fst f).
Proof.
  unshelve econstructor.
  - apply pfst_ne.
  - intros [A B]. reflexivity.
  - intros [A B] [C D] [E F] [f1 f2] [g1 g2]. reflexivity.
Qed.

Definition pfst_efunct {Y Z : eCategory} : eFunctor (Y × Z) Y := {|
  efobj := fun x : Y × Z => fst x;
  efmap_mor := fun A B f => fst f;
  efunct_mixin := @pfst_efunct_mixin Y Z
|}.

Lemma psnd_efunct_mixin {Y Z : eCategory} : eFunctMixin (Y × Z) Z (fun x => snd x) (fun A B f => snd f).
Proof.
  unshelve econstructor.
  - intros [A B] [C D] n [f1 f2] [g1 g2] [H1 H2]; by apply H2.
  - intros [A B]. reflexivity.
  - intros [A B] [C D] [E F] [f1 f2] [g1 g2]. reflexivity.
Qed.

Definition psnd_efunct {Y Z : eCategory} : eFunctor (Y × Z) Z := {|
  efobj := fun x : Y × Z => snd x;
  efmap_mor := fun A B f => snd f;
  efunct_mixin := @psnd_efunct_mixin Y Z
 |}.

Lemma efmap_funct_comp {X Y Z : eCategory} (F : eFunctor Y Z) (G : eFunctor X Y) 
  {A B} (f : A ~~{X}~> B) : efmap (F ∘[eFUNCT] G) f = efmap F (efmap G f).
Proof. by simplify_efunct. Qed.

Definition eEndoFunctor (X : eCategory) : Type := eFunctor X X.

(*  Bifunctor *)
Definition eBiFunctor (X Y Z : eCategory) : Type := eFunctor (X × Y) Z.

Definition ebimap {C D E : eCategory} {F : eBiFunctor C D E} {x w : C} {y z : D}
           (f : x ~~{C}~> w) (g : y ~~{D}~> z) :
  F (x, y) ~~{E}~> F (w, z) := @efmap (eprod_cat C D) E F (x, y) (w, z) (f, g).

Notation "ebimap[ F ]" := (@ebimap _ _ _ F _ _ _ _)
  (at level 9, format "ebimap[ F ]") : ofe_category_scope.

Corollary ebimap_efmap {C D E : eCategory} {F : eBiFunctor C D E} {x w : C} {y z : D}
      (f : x ~~{C}~> w) (g : y ~~{D}~> z) :
  @efmap (eprod_cat C D) E F (x, y) (w, z) (eprod_mor f g) = ebimap f g.
Proof. reflexivity. Qed.

Lemma ebimap_id {C D E : eCategory} {F : eBiFunctor C D E} {A B} :
  ebimap[ F ] (eid[A] tt) (eid[B] tt) = eid{E} tt.
Proof. rewrite -ebimap_efmap. by simplify_efunct. Qed.

Lemma ebimap_ecompose {X Y Z : eCategory} {F : eBiFunctor X Y Z} {A B C D E G} (f : ehom X B C) (g : ehom X A B)  (h : ehom Y E G) (t : ehom Y D E) :
  ebimap[ F ] (ecomp f g) (ecomp h t) = ecomp (ebimap[ F ] f h) (ebimap[ F ] g t).
Proof. unfold ebimap; rewrite - efmap_ecomp. reflexivity. Qed.

(* Partial application of a bifunctor *)
Lemma second_efunct_mixin {X Y Z : eCategory} (F : eBiFunctor X Y Z) (x : X) :
  eFunctMixin Y Z (fun y => F (x, y)) (fun A B f => ebimap[ F ] (eid[x] tt) f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. apply hom_ne; split. 
    + reflexivity.
    + by apply Hfg. 
  - intros A. apply ebimap_id.
  - intros. rewrite -efmap_ecomp /ecomp /ebimap -eprod_mor_ecompose. by simplify_efunct.
Qed.

Definition second_efunct {X Y Z : eCategory} (F : eBiFunctor X Y Z) (x : X) : eFunctor Y Z := {|
  efobj := fun y => F (x, y);
  efmap_mor := fun A B f => ebimap[ F ] (eid[x] tt) f;
  efunct_mixin := @second_efunct_mixin X Y Z F x
 |}.

Lemma second_efunctor_compose_efunct_eq {V W X Y Z : eCategory}
  (F : eFunctor (eprod_cat Z W) (eprod_cat X Y))
  (G : eFunctor (eprod_cat X Y) V)
  (x : Z) 
  : second_efunct (G∘[eFUNCT] F) x = G ∘[eFUNCT] second_efunct F x.
Proof.
  unshelve eapply efunctor_eq ; first reflexivity.
  intros A B f. reflexivity.
Qed.

Lemma first_efunct_mixin {X Y Z : eCategory} (F : eBiFunctor X Y Z) (y : Y) :
  eFunctMixin X Z (fun x => F (x, y)) (fun A B f => ebimap[ F ] f (eid[y] tt)).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. apply hom_ne; split.
    + by apply Hfg.
    + reflexivity.
  - intros A. apply ebimap_id.
  - intros. rewrite -efmap_ecomp /ecomp /ebimap - eprod_mor_ecompose. by simplify_efunct.
Qed.

Definition first_efunct {X Y Z : eCategory} (F : eBiFunctor X Y Z) (y : Y) : eFunctor X Z := {|
  efobj := fun x => F (x, y);
  efmap_mor := fun A B f => ebimap[ F ] f (eid[y] tt);
  efunct_mixin := first_efunct_mixin F y
 |}.

Lemma first_efunctor_compose_efunct_eq {V W X Y Z : eCategory}
  (F : eFunctor (eprod_cat Z W) (eprod_cat X Y))
  (G : eFunctor (eprod_cat X Y) V)
  (x : W) 
  : first_efunct (G∘[eFUNCT] F) x = G ∘[eFUNCT] first_efunct F x.
Proof.
  unshelve eapply efunctor_eq ; first reflexivity.
  intros A B f. reflexivity.
Qed.

(*  Mixed variance functor *)
Definition mveFunctor (Y Z : eCategory) : Type := eBiFunctor Y^op Y Z.

(* Opposite functor *)

Lemma op_efunct_mixing {Y Z : eCategory} (F : eFunctor Y Z) :
  eFunctMixin Y^op Z^op (fun y => F y) (fun A B f => efmap F f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. apply hom_ne. by apply Hfg.
  - intros A. by simplify_efunct.
  - intros. rewrite /ecomp !eop_mor_eq.
    by simplify_efunct.
Qed.

Definition op_efunct {Y Z : eCategory} (F : eFunctor Y Z) : eFunctor Y^op Z^op := {|
  efobj := fun y : Y^op => F y : Z^op;
  efmap_mor := fun A B f => efmap F f;
  efunct_mixin := op_efunct_mixing F
 |}.

Lemma op_efmap {Y Z : eCategory} (F : eFunctor Y Z) {A B : eobj Y} (f : A ~~{Y}~> B) :
  efmap (op_efunct F) f = efmap F f.
Proof. reflexivity. Qed.

Lemma swap_efunct_mixin {X Y Z : eCategory} (F : eFunctor (X × Y) Z) :
  eFunctMixin (Y × X) Z (fun x => F (snd x, fst x)) (fun A B f => efmap F (eprod_mor (snd f) (fst f))).
Proof.
  unshelve econstructor.
  - intros [A1 A2] [B1 B2] n [f1 f2] [g1 g2] [H1 H2]. apply hom_ne. by split.
  - intros [A1 A2]. by simplify_efunct.
  - intros [A1 A2] [B1 B2] [C1 C2] [f1 f2] [g1 g2]. apply ebimap_ecompose.
Qed.

Definition swap_efunct {X Y Z : eCategory} (F : eFunctor (X × Y) Z) : eFunctor (Y × X) Z := {|
  efobj := fun x : Y × X => F (snd x, fst x);
  efmap_mor := fun A B f => efmap F (eprod_mor (snd f) (fst f));
  efunct_mixin := swap_efunct_mixin F
 |}.

Lemma fork_efunct_mixin {X Y Z : eCategory} (F : eFunctor Z X) (G : eFunctor Z Y) :
  eFunctMixin Z (X × Y) (fun z => (F z, G z)) (fun A B f => (efmap F f, efmap G f)).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. by split ; apply hom_ne.
  - intros A. by simplify_efunct.
  - intros. by simplify_efunct.
Qed.

Definition fork_efunct {X Y Z : eCategory} (F : eFunctor Z X) (G : eFunctor Z Y) : eFunctor Z (X × Y) := {|
  efobj := fun z => (F z, G z) : X × Y;
  efmap_mor := fun A B f => (efmap F f, efmap G f);
  efunct_mixin := fork_efunct_mixin F G
 |}.

Notation "<| F , G |>" := (fork_efunct F G) (at level 40) : ofe_category_scope.

Definition times_efunctor {X Y Z W : eCategory} (F : eFunctor X Y) (G : eFunctor Z W) : eFunctor (X × Z) (Y × W) :=
  <| F ∘[eFUNCT] pfst_efunct, G ∘[eFUNCT] psnd_efunct |>.

Example times_efunctor_id {X Y : eCategory} : times_efunctor (eID X) (eID Y) = eID (X × Y).
Proof.
  apply efunctor_eq; simpl.
  - extensionality x. destruct x as [x1 x2]. reflexivity.
  - intros [x1 x2] [y1 y2] [f1 f2]. simplify_efunct.
    apply eq_dep_refl.
Qed.

Lemma drop_one_efunct_mixin {X Y : eCategory} (F : eFunctor (one_ecat × X) Y) :
  eFunctMixin X Y (fun x => F (tt, x)) (fun A B f => ebimap[F] (eid{one_ecat} tt) f).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg. by apply hom_ne.
  - intros A. rewrite -ebimap_id. reflexivity.
  - intros. rewrite -efmap_ecomp. reflexivity.
Qed.

Definition drop_one_efunct {X Y : eCategory} (F : eFunctor (one_ecat × X) Y) : eFunctor X Y := {|
  efobj := fun x => F (tt, x);
  efmap_mor := fun A B f => ebimap[F] (eid{one_ecat} tt) f;
  efunct_mixin := drop_one_efunct_mixin F
 |}.


Lemma add_one_efunct_mixin {X Y : eCategory} (F : eFunctor X Y) :
  eFunctMixin (one_ecat × X) Y (fun x => F (snd x)) (fun A B f => efmap F (snd f)).
Proof.
  unshelve econstructor.
  - intros [[] A] [[] B] n f g Hfg. apply hom_ne. apply Hfg.
  - intros [[] A]. by simplify_efunct.
  - intros [[] A] [[] B] [[] C] [[] f] [[] g]. by simplify_efunct.
Qed.

Definition add_one_efunct {X Y : eCategory} (F : eFunctor X Y) : eFunctor (one_ecat × X) Y := {|
  efobj := fun x : one_ecat × X => F (snd x);
  efmap_mor := fun A B f => efmap F (snd f);
  efunct_mixin := add_one_efunct_mixin F
 |}.
