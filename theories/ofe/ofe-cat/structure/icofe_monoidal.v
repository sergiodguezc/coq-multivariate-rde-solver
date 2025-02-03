(*
  In this file, we present the proof of the monoidal structure of the category
   of iCOFEs and non-expansive functions.
*)

From sgdt Require Import product category_theory ofe OFE ofe_ccc iCOFE icofe_ccc.
From Coq.ssr Require Import ssreflect.

(* The associator and its inverse *)
(* Associator *)
Definition left_tensor : BiFunctor iCOFE (prod_cat iCOFE iCOFE) iCOFE :=
  tensor_prod ∘[FUNCT] (times_functor (ID iCOFE) tensor_prod).

Definition right_tensor_fobj : (prod_cat iCOFE (prod_cat iCOFE iCOFE)) -> iCOFE :=
  fun '(A1, (A2, A3)) => (A1 × A2) × A3.

Definition right_tensor_fmap (A B : prod_cat iCOFE (prod_cat iCOFE iCOFE))
  (f : A ~{prod_cat iCOFE (prod_cat iCOFE iCOFE)}~> B) :
  right_tensor_fobj A ~{iCOFE}~> right_tensor_fobj B.
Proof.
  destruct A as [A1 [A2 A3]], B as [B1 [B2 B3]]. 
  destruct f as [f1 [f2 f3]]. 
  by repeat apply times_mor.
Defined.

Lemma right_tensor_mixin : FunctMixin (prod_cat iCOFE (prod_cat iCOFE iCOFE)) iCOFE right_tensor_fobj right_tensor_fmap.
Proof.
  split.
  - intros [A1 [A2 A3]]. by rewrite -!times_mor_id.
  - intros [A1 [A2 A3]] [B1 [B2 B3]] [C1 [C2 C3]] [f1 [f2 f3]] [g1 [g2 g3]].
    assert ( ((f1, (f2, f3)) ∘[ prod_cat iCOFE (prod_cat iCOFE iCOFE)] (g1, (g2, g3))) = (f1 ∘ g1, (f2 ∘ g2, f3 ∘ g3)))  as H by done.
    rewrite /right_tensor_fmap H !times_mor_eq. 
    rewrite times_mor_comp. 
    simplify_fork.
    unfork ; rewrite -!comp_assoc; by unfork'.
Qed.

Definition right_tensor : BiFunctor iCOFE (prod_cat iCOFE iCOFE) iCOFE := {|
  fobj := right_tensor_fobj;
  fmap := right_tensor_fmap;
  funct_mixin := right_tensor_mixin;
|}.
  

(* The unit object *)
Definition assoc_to : NatTrans (left_tensor) (right_tensor).
Proof.
  unshelve eapply mkNAT.
  - intros [A1 [A2 A3]]. exists (fun '(x, (y, z)) => ((x, y), z)).
    intros n [x1 [x2 x3]] [y1 [y2 y3]] [H1 [H2 H3]]. by repeat split ; simpl in *.
  - intros [A1 [A2 A3]] [B1 [B2 B3]] [f1 [f2 f3]]. icne_eq. destruct  x as [x1 [x2 x3]]. by simpl in *.
Defined.

Definition assoc_from : NatTrans (right_tensor) (left_tensor).
Proof.
  unshelve eapply mkNAT.
  - intros [A1 [A2 A3]]. exists (fun '((x, y), z) => (x, (y, z))).
    intros n [[x1 x2] x3] [[y1 y2] y3] [[H1 H2] H3]. by repeat split ; simpl in *.
  - intros [A1 [A2 A3]] [B1 [B2 B3]] [f1 [f2 f3]]. icne_eq. destruct  x as [[x1 x2] x3]. by simpl in *.
Defined.

Program Definition assoc : NatIso (left_tensor) (right_tensor) := {|
  to_nt_iso := assoc_to ;
  from_nt_iso := assoc_from ;
 |}.
Next Obligation.
  apply nat_eq. intros [A1 [A2 A3]]. icne_eq. destruct x as [[x1 x2] x3]. by simpl in *.
Qed.
Next Obligation.
  apply nat_eq. intros [A1 [A2 A3]]. icne_eq. destruct x as [x1 [x2 x3]]. by simpl in *.
Qed.

Program Definition left_unitor_to : NatTrans (second_funct tensor_prod 1) (ID iCOFE) :=
  {| nt A := p_snd |}.
Next Obligation. by ne_eq. Qed.

Program Definition left_unitor_from : NatTrans (ID iCOFE) (second_funct tensor_prod 1)
  := {| nt A := fork (![A]) id{iCOFE} |}.
Next Obligation. by ne_eq. Qed.

(* The unit is just the terminal object 1 *)
Program Definition left_unitor : NatIso (second_funct tensor_prod 1) (ID iCOFE) :=
  {| to_nt_iso := left_unitor_to ; from_nt_iso := left_unitor_from |}.
Next Obligation.
  apply nat_eq; intros A; simpl; by ne_eq.
Qed.
Next Obligation.
  apply nat_eq; intros A; simpl; ne_eq; by destruct x as [[] a]. 
Qed.

Program Definition right_unitor_to : NatTrans (first_funct tensor_prod 1) (ID iCOFE) := 
  {| nt A := p_fst |}.
Next Obligation. by ne_eq. Qed.

Program Definition right_unitor_from : NatTrans (ID iCOFE) (first_funct tensor_prod 1) :=
  {| nt A := fork id{iCOFE} (![A]) |}.
Next Obligation. by ne_eq. Qed.

Program Definition right_unitor : NatIso (first_funct tensor_prod 1) (ID iCOFE) :=
  {| to_nt_iso := right_unitor_to ; from_nt_iso := right_unitor_from |}.
Next Obligation.
  apply nat_eq; intros A; simpl; by ne_eq.
Qed.
Next Obligation.
  apply nat_eq; intros A; simpl; ne_eq; by destruct x as [a []]. 
Qed.

(* Definition of shortcuts *)
Definition to_right (A : iCOFE) : tensor_prod (A, 1) ~> A := nt (to_nt_iso right_unitor) A.
Definition from_right (A : iCOFE) : A ~> tensor_prod (A, 1) := nt (from_nt_iso right_unitor) A.
Definition to_left (A : iCOFE) : tensor_prod (1, A) ~> A := nt (to_nt_iso left_unitor) A.
Definition from_left (A : iCOFE) : A ~> tensor_prod (1, A) := nt (from_nt_iso left_unitor) A.

Definition to_assoc (A B C : iCOFE) : left_tensor (A, (B, C)) ~> right_tensor (A, (B, C)) :=
  nt (to_nt_iso assoc) (A, (B, C)).

Definition from_assoc (A B C : iCOFE) : right_tensor (A, (B, C)) ~> left_tensor (A, (B, C)) :=
  nt (from_nt_iso assoc) (A, (B, C)).

(* The triangle identity *)
Lemma triangle_identity {A B : iCOFE} :
  bimap[tensor_prod] (to_right A) (id[B]) = bimap[tensor_prod] (id[A]) (to_left B) ∘ from_assoc A 1 B.
Proof.
  apply icne_eq. intros [[a b] c]. by destruct b. 
Qed.

(* The pentagon identity *)
Lemma pentagon_identity {w x y z : iCOFE} :
  bimap[tensor_prod] (to_assoc w x y) (id[z]) ∘ to_assoc w (tensor_prod (x, y)) z ∘ bimap[tensor_prod] (id[w]) (to_assoc x y z) =
  to_assoc (tensor_prod (w, x)) y z ∘ to_assoc w x (tensor_prod (y, z)).
Proof.
  icne_eq. destruct x0 as [a [b [c d]]]. reflexivity.
Qed.
