From sgdt Require Import efunctor ecategory ofe econtractive partial_econtractive join_split.
Require Import ssreflect.

Open Scope ofe_category_scope.
Open Scope ofe_morphism_scope.

(* Symmetrization of a efunctor with just a unit input *)
Definition esym0_eobj {Z : eCategory} (F : one_ecat →  Z) :
  eobj[one_ecat] -> Z^op × Z := fun _ => (F tt, F tt).

Definition esym0_efmap_mor {Z : eCategory} (F : one_ecat →  Z) :
  forall (A B : eobj[one_ecat]) (f : A ~~> B), esym0_eobj F A ~~{(Z^op × Z)}~> esym0_eobj F B :=
  fun _ _ _ => (eid{Z^op} tt, eid{Z} tt).

Lemma esym0_efmap_mor_ne {Z : eCategory} (F : one_ecat →  Z) A B :
  NonExpansive (esym0_efmap_mor F A B).
Proof. intros n [] [] [] ; split ; reflexivity. Qed.

Lemma esym0_efmap_id {Z : eCategory} (F : one_ecat →  Z) A :
  esym0_efmap_mor F A A (eid{one_ecat} tt) = eid{Z^op × Z} tt.
Proof. by rewrite /esym0_efmap_mor /=. Qed.

Lemma esym0_efmap_compose {Z : eCategory} (F : one_ecat →  Z) A B C
  (f : B ~~> C) (g : A ~~> B) :
  esym0_efmap_mor F A C (f ∘e g) = esym0_efmap_mor F B C f ∘e esym0_efmap_mor F A B g.
Proof. rewrite /esym0_efmap_mor /= /ecomp /=. by simplify_ecat. Qed.

Lemma esym0_mixin {Z : eCategory} (F : one_ecat →  Z) :
  eFunctMixin one_ecat (Z^op × Z) (esym0_eobj F) (esym0_efmap_mor F).
Proof.
  unshelve econstructor.
  - apply esym0_efmap_mor_ne.
  - apply esym0_efmap_id.
  - apply esym0_efmap_compose.
Qed.

Definition esym0 {Z : eCategory} (F : one_ecat →  Z) : one_ecat →  (Z^op × Z) := {|
 efobj := esym0_eobj F ;
 efmap_mor := esym0_efmap_mor F ;
 efunct_mixin := esym0_mixin F
 |}.

(* Symmetrization of a efunctor with more than one argument *)
Definition esymS_eobj {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z)
  : eobj[(X^op × X) × (Y^op × Y)] -> Z^op × Z :=
  fun '((X1, X2), (Y1, Y2)) => (F (X1, (Y2, Y1)), F (X2, (Y1, Y2))).


Definition esymS_efmap_mor {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) :
  forall (A B : eobj[((X^op × X) × (Y^op × Y))]) (f : A ~~> B),
  esymS_eobj F A ~~{(Z^op × Z)}~> esymS_eobj F B :=
  fun '((X1, X2), (Y1, Y2)) '((X1', X2'), (Y1', Y2')) '((fz1, fz2), (fy1, fy2)) =>
    eprod_mor (ebimap[F] fz1 (eprod_mor fy2 fy1)) (ebimap[F] fz2 (eprod_mor fy1 fy2)).

Lemma esymS_efmap_mor_ne {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) A B :
  NonExpansive (esymS_efmap_mor F A B).
Proof.
  destruct A as [[A1 A2] [A3 A4]], B as [[B1 B2] [B3 B4]].
  intros n [[f1 f2] [f3 f4]] [[g1 g2] [g3 g4]] [[H1 H2] [H3 H4]] ; split
  ; simpl in * ; apply hom_ne ; split ; [| split | | split ] ; simpl ; assumption.
Qed.

Lemma esymS_efmap_id {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) A :
  esymS_efmap_mor F A A (eid{((X^op × X) × (Y^op × Y))} tt) = eid{Z^op × Z} tt.
Proof.
  destruct A as [[A1 A2] [A3 A4]]  ; simpl.
  by rewrite !ebimap_id.
Qed.

Lemma esymS_efmap_compose {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) A B C
  (f : B ~~> C) (g : A ~~> B) :
  esymS_efmap_mor F A C (f ∘e g) = esymS_efmap_mor F B C f ∘e esymS_efmap_mor F A B g.
Proof.
  destruct A as [[A1 A2] [A3 A4]], B as [[B1 B2] [B3 B4]], C as [[C1 C2] [C3 C4]],
  f as [[f1 f2] [f3 f4]], g as [[g1 g2] [g3 g4]] ; simpl in *.
  rewrite !eprod_mor_ecompose !ebimap_ecompose /eprod_mor /ecomp /=.
  f_equal. 
  replace (ecompose_mor Y (f4, g4)) with (ecompose_mor Y^op (g4, f4)) by done.
  rewrite (@eprod_mor_ecompose_2 Y^op Y _ _ _ _ _ _ (f4, f3) (g4, g3)).
  by rewrite ebimap_ecompose.
Qed.

Lemma esymS_mixin {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) :
  eFunctMixin ((X^op × X) × (Y^op × Y)) (Z^op × Z) (esymS_eobj F) (esymS_efmap_mor F).
Proof.
  unshelve econstructor.
  - apply esymS_efmap_mor_ne.
  - apply esymS_efmap_id.
  - apply esymS_efmap_compose.
Qed.
  
Definition esymS {X Y Z : eCategory} (F : X × (Y^op × Y) →  Z) :
  (X^op × X) × (Y^op × Y) →  Z^op × Z := {|
 efobj := esymS_eobj F ;
 efmap_mor := esymS_efmap_mor F ;
 efunct_mixin := esymS_mixin F
|}.

Fixpoint eop_to_eobj {Y : eCategory} {n : nat} (x : eobj[Y ** n]) : eobj[(Y^op ** n)] := 
  match n return eobj[Y ** n] -> eobj[(Y^op ** n)] with
  | O => fun x => x
  | S n' => fun '(x1, x2) => (eop_to_eobj x1, x2)
  end x.
Notation "'eobj_of' x" := (eop_to_eobj x) (at level 20) : ofe_category_scope.

Fixpoint eobj_to_eop {Y : eCategory} {n : nat} (x : eobj[(Y^op ** n)]) : eobj[Y ** n] :=
  match n return eobj[(Y^op ** n)] -> eobj[Y ** n] with
  | O => fun A => A
  | S n' => fun '(A1, A2) => (eobj_to_eop A1, A2)
  end x.
Notation "'eop_of' x" := (eobj_to_eop x) (at level 20) : ofe_category_scope.

Lemma eop_to_eobj_inv {Y : eCategory} {n : nat} (x : eobj[Y ** n]) : eop_of (eobj_of x) = x.
Proof.
  induction n ; first by destruct x.
  destruct x as [x1 x2]. simpl. by rewrite IHn.
Qed.

Lemma eobj_to_eop_inv {Y : eCategory} {n : nat} (x : eobj[(Y^op ** n)]) : eobj_of (eop_of x) = x.
Proof.
  induction n ; first by destruct x.
  destruct x as [x1 x2]. simpl. by rewrite IHn.
Qed.

Fixpoint eophom_to_ehom {Y : eCategory} {n : nat}
(A B : eobj[Y ** n]) (f : A ~~{Y ** n}~> B) :  (eobj_of B) ~~{Y^op ** n}~> (eobj_of A) :=
match n return forall A B, A ~~{Y ** n}~> B -> (eobj_of B) ~~{Y^op ** n}~> (eobj_of A) with
  | O => fun A B f => f
  | S n' => fun '(A1, A2) '(B1, B2) '(f1, f2) => (eophom_to_ehom A1 B1 f1, f2)
  end A B f.
Notation "'ehom_of' f" := (eophom_to_ehom _ _ f) (at level 20) : ofe_morphism_scope.

Lemma ehom_of_ne {Y : eCategory} {n : nat} (A B : eobj[Y ** n]) :
  NonExpansive (@eophom_to_ehom Y n A B).
Proof.
  revert A B; induction n.
  - intros [] [] m [] [] H; reflexivity.
  - intros [An Ah] [Bn Bh] m [fn fh] [gn gh] [Hfgn Hfgh] ; split ; simpl in * ; last done.
    apply IHn; by apply Hfgn.
Qed.

Lemma ehom_of_id {Y : eCategory} {n : nat} (A : eobj[Y ** n]) :
  ehom_of (@eid (Y ** n) A tt) = eid{Y^op ** n} tt.
Proof.
  induction n ; first by destruct A.
  destruct A as [An Ah]. simpl. by rewrite IHn.
Qed.

Lemma ehom_of_ecomp {Y : eCategory} {n : nat} (A B C : eobj[Y ** n])
  (f : B ~~{Y ** n}~> C) (g : A ~~{Y ** n}~> B) :
  ehom_of (f ∘e g) = ehom_of g ∘e ehom_of f.
Proof.
  induction n ; destruct A, B, C, f, g; first done.
  by rewrite /= IHn.
Qed.


Fixpoint ehom_to_eophom {Y : eCategory} {n : nat}
(A B : eobj[(Y^op ** n)]) (f : A ~~{Y^op ** n}~> B) : (eop_of B) ~~{Y ** n}~> (eop_of A) :=
match n return forall A B, A ~~{Y^op ** n}~> B -> (eop_of B) ~~{Y ** n}~> (eop_of A) with
  | O => fun A B f => f
  | S n' => fun '(A1, A2) '(B1, B2) '(f1, f2) => (ehom_to_eophom A1 B1 f1, f2)
  end A B f.
Notation "'eophom_of' f" := (ehom_to_eophom _ _ f) (at level 20) : ofe_morphism_scope.

Lemma eophom_of_ne {Y : eCategory} {n : nat} (A B : eobj[(Y^op ** n)]) :
  NonExpansive (@ehom_to_eophom Y n A B).
Proof.
  revert A B; induction n.
  - intros [] [] m [] [] H; reflexivity.
  - intros [An Ah] [Bn Bh] m [fn fh] [gn gh] [Hfgn Hfgh] ; split ; simpl in * ; last done.
    apply IHn; by apply Hfgn.
Qed.

Lemma eophom_of_id {Y : eCategory} {n : nat} (A : eobj[(Y^op ** n)]) :
  eophom_of (@eid (Y^op ** n) A tt) = eid{Y ** n} tt.
Proof.
  induction n ; first by destruct A.
  destruct A as [An Ah]. by rewrite /= IHn.
Qed.

Lemma eophom_of_ecomp {Y : eCategory} {n : nat} (A B C : eobj[(Y^op ** n)])
  (f : B ~~{Y^op ** n}~> C) (g : A ~~{Y^op ** n}~> B) :
  eophom_of (f ∘e g) = eophom_of g ∘e eophom_of f.
Proof.
  induction n ; destruct A, B, C, f, g ; first done.
  by rewrite /= IHn.
Qed.

Definition delta1_eobj {Y : eCategory} {n : nat} :
  eobj[(Y^op ** n × Y ** n)] -> (Y^op ** n × Y ** n)^op :=
  fun '(A, B) => (eobj_of B, eop_of A).

Definition delta1_efmap_mor {Y : eCategory} {n : nat} :
  forall (A B : eobj[(Y^op ** n × Y ** n)]) (f : A ~~{(Y^op ** n × Y ** n)}~> B),
  delta1_eobj A ~~{((Y^op ** n × Y ** n)^op)}~> delta1_eobj B :=
  fun '(A1, A2) '(B1, B2) '(f1, f2) => (ehom_of f2, eophom_of f1).

Lemma delta1_mixin {Y : eCategory} {n : nat} :
  eFunctMixin (Y^op ** n × Y ** n) (Y^op ** n × Y ** n)^op delta1_eobj delta1_efmap_mor.
Proof.
  unshelve econstructor.
    - intros [A1 A2] [B1 B2] m [f1 f2] [g1 g2] Hfg ;
      split ; simpl in * ; [apply ehom_of_ne | apply eophom_of_ne] ; by destruct Hfg.
    - intros [A1 A2]. rewrite /= ehom_of_id eophom_of_id. done.
    - intros [A1 A2] [B1 B2] [C1 C2] [f1 f2] [g1 g2].
      rewrite /= ehom_of_ecomp eophom_of_ecomp. done.
Qed.

Definition delta1 {Y : eCategory} {n : nat} : Y^op ** n × Y ** n →  (Y^op ** n × Y ** n)^op :=
  {| efobj := delta1_eobj ; efmap_mor := delta1_efmap_mor ; efunct_mixin := delta1_mixin |}.

  

Lemma delta1_invol {Y : eCategory} {n : nat} (x : eobj[(Y^op ** n × Y ** n)]) :
  delta1_eobj (delta1_eobj x) = x.
Proof. destruct x as [A B]. by rewrite /= eop_to_eobj_inv eobj_to_eop_inv. Qed.

Definition delta_pi1 {Y : eCategory} {n : nat} :
  (Y^op × Y) ** n →  ((Y^op × Y) ** n)^op := op_efunct (join n) ∘[eFUNCT] delta1 ∘[eFUNCT] split n.

Definition esymS_new {Y Z : eCategory} {n : nat} (F : (Y^op × Y) ** S n →  Z) :
  (Y^op × Y) ** S n →  Z^op × Z := <| op_efunct F ∘[eFUNCT] delta_pi1 , F |>.

Definition delta {Y : eCategory} {n : nat} :
  (Y^op × Y) ** n →  ((Y^op × Y) ** n)^op × (Y^op × Y) ** n :=
  <| delta_pi1 ,  eID _ |>.

Definition esymS' {Y Z : eCategory} {n : nat} (F : (Y^op × Y) ** S n →  Z) :
  (Y^op × Y) ** n × (Y^op × Y) →  Z^op × Z :=
  esymS F ∘[eFUNCT] times_efunctor (@delta _ n) (eID (Y^op × Y)).

Definition esym {Y Z : eCategory} {n : nat} (F : (Y^op × Y) ** n →  Z)
  : (Y^op × Y) ** n →  Z^op × Z :=
  match n as m return ((Y^op × Y) ** m →  Z) -> (Y^op × Y) ** m →  Z^op × Z with
  | O => fun F' => esym0 F'
  | S n' => fun F' => esymS' F'
  end F.

Definition esym_new {Y Z : eCategory} {n : nat} (F : (Y^op × Y) ** n →  Z)
  : (Y^op × Y) ** n →  Z^op × Z :=
  match n as m return ((Y^op × Y) ** m →  Z) -> (Y^op × Y) ** m →  Z^op × Z with
  | O => fun F' => esym0 F'
  | S n' => fun F' => esymS_new F'
  end F.

Lemma esymS_ctr_prop {Y Z W : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y) W) :
  forall (x : eobj[Z^op × Z]) (A B : eobj[Y^op × Y]),
  Contractive (@efmap _ _ (second_efunct (esymS F) x) A B).
Proof.
  intros [x1 x2] [A1 A2] [B1 B2] m [f1 f2] [g1 g2] Hfg  ; split ; simpl in * ;
  apply @snd_funct_ctr; intros m' Hm'; destruct (Hfg m' Hm') ; by split.
Qed.

Lemma fork_ctr_snd {W X Y Z : eCategory} (F : eFunctor (Z × Y) W) (G : eFunctor (Z × Y) X) :
  iseFunctorCtrSnd F /\ iseFunctorCtrSnd G -> iseFunctorCtrSnd (<| F, G |>) .
Proof.
  intros [HF HG].
  unshelve econstructor.
  intros x A B m f g Hfg ; split ;  simpl in *.
  - by apply is_snd_funct_ctr . 
  - by apply is_snd_funct_ctr . 
Qed.

(* Lemma esymS_new_ctr_prop {Y Z W : eCategory} {n} (F : eFunctorCtrSnd ((Y^op × Y) ** n) (Y^op × Y) W) : *)
(*   iseFunctorCtrSnd (esymS_new F). *)
(* Proof. *)
(*   apply fork_ctr_snd ; split ; last apply toiseFunctorCtrSnd. *)
(*   unshelve econstructor. *)
(*   intros x [A1 A2] [B1 B2] m [f1 f2] [g1 g2] Hfg ; simpl in *. *)
(*   rewrite -!ebimap_efmap !efmap_ecomp_efunct /=. *)
(**)
(*   set HH := @snd_funct_ctr _ _ _ F (join_eobj n *)
(*          (eobj_of snd (split_eobj n x), eop_of fst (split_eobj n x))) (B2, B1) (A2, A1) m. *)
(*           *)
(*   apply HH. *)
(*     apply (@is_snd_funct_ctr . *)
(*     first apply toiseFunctorCtrSnd. *)
(*     intros m' Hm'. destruct (Hfg m' Hm') ; by split. *)
(*   - rewrite -!ebimap_efmap !efmap_ecomp_efunct /=. *)
(*     apply @is_snd_funct_ctr. *)
(*     intros m' Hm'. destruct (Hfg m' Hm') ; by split. *)
(*    *)
(* Admitted. *)

Definition esymS_ctr {Y Z W : eCategory} (F : eFunctorCtrSnd Z (Y^op × Y)  W)
  : eFunctorCtrSnd (Z^op × Z) (Y^op × Y) (W^op × W) :=
  {| efunct_snd := esymS F ; efunct_ctr_snd := esymS_ctr_prop F |}.
