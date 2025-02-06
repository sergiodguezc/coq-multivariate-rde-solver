From sgdt Require Import functor efunctor ecategory category ofe.
From sgdt Require Import iCOFE ofe_ccc icofe_ccc icofe_monoidal.
From sgdt Require product econtractive partial_econtractive.
Require Import ssreflect.

Open Scope ofe_category_scope.
Open Scope ofe_morphism_scope.

(* split efunctor *)
Fixpoint split_eobj (n : nat) {Y : eCategory} : (Y^op × Y) ** n ->  (Y^op ** n × Y ** n) :=
  match n return (Y^op × Y) ** n ->  (Y^op ** n × Y ** n) with
  | O => fun A => (A, A) 
  | S n' => fun '(A1, A2) =>
      ((fst (split_eobj n' A1), fst A2), (snd (split_eobj n' A1), snd A2))
  end.

Fixpoint split_ehom (n : nat) {Y : eCategory} 
  (A B : (Y^op × Y) ** n) (f : A ~~> B) : (split_eobj n A) ~~> (split_eobj n B) :=
  match n return forall A B, A ~~> B -> (split_eobj n A) ~~> (split_eobj n B) with
  | 0 => fun _ _ _ => (tt, tt)
  | S n' => 
      fun A B f =>
        match A, B, f with
        | (An, (_, _)), (Bn, (_, _)), (fn, (fop, fh)) =>
            match (split_ehom n' An Bn fn) with
            | (g1, g2) => ((g1, fop), (g2, fh))
            end
        end
  end A B f.

Lemma split_ehom_0 {Y : eCategory} (A B : (Y^op × Y) ** 0) (f : A ~~> B) :
  split_ehom 0 A B f = (eid[A] tt, eid[B] tt).
Proof. by destruct A, B, f. Qed.

Lemma split_ehom_S n (Y : eCategory) (A B : (Y^op × Y) ** (S n)) (f : A ~~> B) :
  split_ehom (S n) A B f =
    match A, B, f with
    | (An, (Aop, Ah)), (Bn, (Bop, Bh)), (fn, (fop, fh)) =>
        match (split_ehom n An Bn fn) return split_eobj (S n) (An, (Aop, Ah)) ~~{(Y^op ** (S n) × Y ** (S n))}~> split_eobj (S n) (Bn, (Bop, Bh)) with
        | (g1, g2) => ((g1, fop), (g2, fh))
        end
    end.
Proof. by destruct A, B, f. Qed.

Lemma split_ehom_ne n (Y : eCategory) (A B : (Y^op × Y) ** n) :
  NonExpansive (@split_ehom n Y A B).
Proof.
  induction n ; intros m f g Hfg.
  - by destruct A, B, f.
  - rewrite !split_ehom_S.
    destruct A as [An [Aop Ah]], B as [Bn [Bop Bh]], f as [fn [fop fh]], g as [gn [gop gh]].
    assert (split_ehom n An Bn fn ≡{ m }≡ split_ehom n An Bn gn) as Hff.
    { apply IHn; by destruct Hfg. }
    destruct (split_ehom n An Bn fn) as [f1 f2],
             (split_ehom n An Bn gn) as [g1 g2],
             Hfg as [Hfg1 [Hfg2 Hfg3]].
    split ; simpl.
    + split ; [by destruct Hff | apply Hfg2].
    + split ; [by destruct Hff | apply Hfg3].
Qed.

Lemma split_id n (Y : eCategory) (A : (Y^op × Y) ** n) :
  split_ehom n A A (eid{(Y^op × Y) ** n} tt) = eid{Y^op ** n × Y ** n} tt.
Proof.
  induction n ; first by destruct A.
  destruct A as [An [Aop Ah]] eqn:Heq. simpl.
  destruct (split_ehom n An An (eid_mor ((Y^op × Y) ** n) tt)) as [f1 f2] eqn:Heq'.
  unfold eprod_eid_mor. 
  assert ((f2, @eid_mor Y Ah tt) = (@eid (Y ** n × Y) (snd (split_eobj n An), Ah) tt)) as H2.
  { simpl; f_equal.
    assert (f2 = snd (split_ehom n An An (eid_mor ((Y^op × Y) ** n) tt))) as -> by (by rewrite Heq').
    by rewrite -> IHn. }
  assert ((f1, @eid_mor Y^op Aop tt) = (@eid (Y^op ** S n) (fst (split_eobj n An), Aop) tt)) as H1.
  { simpl; f_equal.
    assert (f1 = fst (split_ehom n An An (eid_mor ((Y^op × Y) ** n) tt))) as -> by (by rewrite Heq').
    by rewrite -> IHn. }
  by rewrite H1 H2.
Qed.

Lemma split_ecomp n (Y : eCategory) (A B C : (Y^op × Y) ** n) (f : B ~~> C) (g : A ~~> B) :
  split_ehom n A C (f ∘e g) = split_ehom n B C f ∘e split_ehom n A B g.
Proof.
  induction n ; first by destruct A, B, C, f, g.
  destruct A as [An [Aop Ah]], B as [Bn [Bop Bh]], C as [Cn [Cop Ch]],
           f as [fn [fop fh]], g as [gn [gop gh]].
  rewrite !split_ehom_S; simpl in *.
  destruct (split_ehom n An Cn (ecompose_mor ((Y^op × Y) ** n) (fn, gn))) as [fgn1 fgn2] eqn:Heq1.
  destruct (split_ehom n Bn Cn fn) as [fn1 fn2] eqn:Heq2.
  destruct (split_ehom n An Bn gn) as [gn1 gn2] eqn:Heq3.
  unfold ecomp; simpl in *.

  assert (fgn1 = ecompose_mor (Y^op ** n) (fn1, gn1))  as ->.
  { assert (fgn1 = fst (split_ehom n An Cn (ecompose_mor ((Y^op × Y) ** n) (fn, gn)))) as -> by (by rewrite Heq1).
    rewrite IHn.
    assert (fn1 = fst (split_ehom n Bn Cn fn)) as -> by (by rewrite Heq2).
    assert (gn1 = fst (split_ehom n An Bn gn)) as -> by (by rewrite Heq3).
    reflexivity. 
  }

  assert (fgn2 = ecompose_mor _ (fn2, gn2))  as ->.
  { assert (fgn2 = snd (split_ehom n An Cn (ecompose_mor _ (fn, gn)))) as -> by (by rewrite Heq1).
    rewrite IHn.
    assert (fn2 = snd (split_ehom n Bn Cn fn)) as -> by (by rewrite Heq2).
    assert (gn2 = snd (split_ehom n An Bn gn)) as -> by (by rewrite Heq3).
    reflexivity. 
  }
  reflexivity.
Qed.
  

Lemma split_mixin n (Y : eCategory) :
  eFunctMixin ((Y^op × Y) ** n) (Y^op ** n × Y ** n) (@split_eobj n Y) (@split_ehom n Y).
Proof.
  unshelve econstructor.
  - apply split_ehom_ne.
  - apply split_id.
  - apply split_ecomp.
Qed.

Definition split {Y : eCategory} (n : nat) :
  eFunctor ((Y^op × Y) ** n) (Y^op ** n × Y ** n) := {|
    efobj := @split_eobj n Y;
    efmap_mor := @split_ehom n Y;
    efunct_mixin := split_mixin n Y
  |}.

(*  join eFunctor *)
Fixpoint join_eobj {Y : eCategory} (n : nat) 
  (A : Y^op ** n × Y ** n) : (Y^op × Y) ** n :=
  match n as m return (Y^op ** m × Y ** m) -> (Y^op × Y) ** m with
  | 0 => fun _ => tt
  | S n' =>
      fun '((Anop, Aop), (An, Ah)) =>
        (join_eobj n' (Anop, An), (Aop, Ah))
  end A.

Fixpoint join_ehom  {Y : eCategory} (n : nat)
  (A B : Y^op ** n × Y ** n) (f : A ~~> B) : (join_eobj n A) ~~> (join_eobj n B) :=
  match n return forall A B, A ~~> B -> (join_eobj n A) ~~> (join_eobj n B) with
  | 0 => fun _ _ _ => tt
  | S n' => 
      fun '((Anop, Aop), (An, Ah)) '((Bnop, Bop), (Bn, Bh)) '((fnop, fop), (fn, fh)) =>
                (join_ehom n' (Anop, An) (Bnop, Bn) (fnop, fn), (fop, fh))
  end A B f.

Lemma join_ehom_0 {Y : eCategory} (A B : Y^op ** 0 × Y ** 0) (f : A ~~> B) :
  join_ehom 0 A B f = tt.
Proof. by destruct A, B, f. Qed.

Lemma join_ehom_S n (Y : eCategory) (A B : Y^op ** (S n) × Y ** (S n)) (f : A ~~> B) :
  join_ehom (S n) A B f =
    match A, B, f with
    | ((Anop, Aop), (An, Ah)), ((Bnop, Bop), (Bn, Bh)), ((fnop, fop), (fn, fh)) =>
       (join_ehom n (Anop, An) (Bnop, Bn) (fnop, fn), (fop, fh))
    end.
Proof. destruct A as [[Anop Aop] [An Ah]], B as [[Bnop Bop] [Bn Bh]]; by destruct f. Qed.
  
Lemma join_ehom_ne n (Y : eCategory) (A B : Y^op ** n × Y ** n) :
  NonExpansive (@join_ehom Y n A B).
Proof.
  revert A B; induction n.
  - intros [] [] m [] [] H; reflexivity.
  - intros [[Anop Aop] [An Ah]] [[Bnop Bop] [Bn Bh]] m [[fnop fop] [fn fh]] [[gnop gop] [gn gh]] [[Hfnop Hfop] [Hfn Hfh]] ; simpl.
    split ; first by apply IHn.
    by split.
Qed.

Lemma join_id n (Y : eCategory) (A : Y^op ** n × Y ** n) :
  join_ehom n A A (eid{Y^op ** n × Y ** n} tt) = eid{(Y^op × Y) ** n} tt.
Proof.
  induction n ; first by destruct A.
  destruct A as [[Anop Aop] [An Ah]]; simpl.
  rewrite IHn //.
Qed.

Lemma join_ecomp n (Y : eCategory) (A B C : Y^op ** n × Y ** n) (f : B ~~> C) (g : A ~~> B) :
  join_ehom n A C (f ∘e g) = join_ehom n B C f ∘e join_ehom n A B g.
Proof.
  induction n ; first by destruct A, B, C, f, g.
  destruct A as [[Anop Aop] [An Ah]], B as [[Bnop Bop] [Bn Bh]], C as [[Cnop Cop] [Cn Ch]],
           f as [[fnop fop] [fn fh]], g as [[gnop gop] [gn gh]].
  rewrite !join_ehom_S /ecomp. simpl in *.
  f_equal.

  assert (ecompose_mor _ (fnop, gnop) = @ecomp (Y^op ** n) _ _ _ fnop gnop) as -> by done.
  assert (ecompose_mor _ (fn, gn) = @ecomp (Y ** n) _ _ _ fn gn) as -> by done.

  assert ((@ecomp (Y^op ** n) _ _ _ fnop gnop, @ecomp (Y ** n) _ _ _ fn gn) = @ecomp (Y^op ** n × Y ** n) (Anop, An) (Bnop, Bn) (Cnop, Cn) (fnop, fn) (gnop, gn)) as H by done.
  rewrite H.
  rewrite IHn. reflexivity.
Qed.

Lemma join_mixin n (Y : eCategory) :
  eFunctMixin (Y^op ** n × Y ** n) ((Y^op × Y) ** n) (@join_eobj Y n) (@join_ehom Y n).
Proof.
  unshelve econstructor.
  - apply join_ehom_ne.
  - apply join_id.
  - apply join_ecomp.
Qed.

Definition join {Y : eCategory} (n : nat) :
  eFunctor (Y^op ** n × Y ** n) ((Y^op × Y) ** n) := {|
    efobj := @join_eobj Y n;
    efmap_mor := @join_ehom Y n;
    efunct_mixin := join_mixin n Y
  |}.

(* join-split Lemmas *)
Lemma join_split_id_eobj n (Y : eCategory) (A : (Y^op × Y) ** n) :
  join n (split n A) = A.
Proof.
  induction n ; first by destruct A.
  destruct A as [An [Aop A]] ; simpl in *.
  
  assert ((fst (split_eobj n An), snd (split_eobj n An)) = split_eobj n An) as H1.
  { destruct (split_eobj n An) as [An1 An2]; reflexivity. }
  by rewrite H1 IHn.
Qed.

Lemma split_join_id_eobj n (Y : eCategory) (A : Y^op ** n × Y ** n) :
  split n (join n A) = A.
Proof.
  induction n ; first by destruct A as [[] []].
  destruct A as [[Anop Aop] [An Ah]]; simpl in *.
  by rewrite IHn.
Qed.
