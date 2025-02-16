From sgdt Require Import axioms category terminal closed ecategory efunctor eisomorphism ofe iCOFE icofe_ccc.
From sgdt Require Import einstances econtractive ectr_compl banach.
Require Import ssreflect.

(* From sgdt.ofe Require Import ofe ofe_cat endo_cofe banach. *)

Require Import ssreflect Lia.

Fixpoint Fn (F : eEndoFunctor eiCOFE) (n : nat) : eiCOFE :=
  match n with
  | O => icofe_unit
  | S n' => F (Fn F n')
  end.
Notation "F $ n" := (Fn F n) (at level 20).

Lemma Fn_S {F : eEndoFunctor eiCOFE} {n : nat} : F $ (S n) = F (F $ n).
Proof. done. Qed.

Lemma coerce_Fn {F : eEndoFunctor eiCOFE} {n m} (H : n = m) : F $ n = F $ m.
Proof. by destruct H. Qed.

Fixpoint f {F : eEndoFunctor eiCOFE} (n : nat) : F $ n ~~> F $ (S n) :=
  match n with
  | O => inhabitant_icofe_exp (F $ O) (F $ (S O))
  | S n' => @efmap _ _ F (F $ n') (F $ (S n')) (f n')
  end.

Fixpoint g {F : eEndoFunctor eiCOFE} (n : nat) : F $ (S n) ~~> F $ n :=
  match n with
  | O => ![(F $ (S O))]
  | S n' => @efmap _ _ F (F $ (S n')) (F $ n') (g n')
  end.

Definition f_S {F : eEndoFunctor eiCOFE} (n : nat) : f (S n) = @efmap _ _ F (F $ n) (F $ (S n)) (f n) := eq_refl.
Definition g_S {F : eEndoFunctor eiCOFE} (n : nat) : g (S n) = @efmap _ _ F (F $ (S n)) (F $ n) (g n) := eq_refl.

Lemma gf {F : eEndoFunctor eiCOFE} {n}  : (g n ∘e (f n)) = eid[F $ n] tt.
Proof.
  induction n.
  - simpl; ne_eq. rewrite /= ; by destruct x.
  - rewrite f_S g_S -efmap_ecomp IHn efmap_id //.
Qed.

Lemma gfx {F : eEndoFunctor eiCOFE} {n} (x : F $ n) : g n (f n x) = x.
Proof.
  assert (x = eid[F $ n] tt x) as H by done.
  by rewrite {2}H -gf.
Qed.

Lemma contractive_0 {A B : eiCOFE} (F : eEndoFunctorCtr eiCOFE ) {x y : B ^ A} : efmap F x ≡{0}@{(F B) ^ (F A) }≡ efmap F y.
Proof. intros H. apply (@efunct_ctr _ _ F). intros m Hm; lia. Qed.

Lemma contractive_0x {A B : eiCOFE} (F : eEndoFunctorCtr eiCOFE) {x y : B ^ A} {z : F A} : efmap F x z ≡{0}@{F B}≡ efmap F y z.
Proof. apply (@efunct_ctr _ _ F). intros m Hm; lia. Qed.

Lemma contractive_S {A B : eiCOFE} (F : eEndoFunctorCtr eiCOFE) {n} {x y : B ^ A} : x ≡{n}≡ y -> efmap F x ≡{S n}@{(F B) ^ (F A) }≡ efmap F y.
Proof.
  intros H; apply (@efunct_ctr _ _ F) ; intros m Hm. 
  apply ofe_mono with (n := n); auto. lia.
Qed.

Lemma contractive_ne_x {A B : eiCOFE} (F : eEndoFunctorCtr eiCOFE) {n} {x y : B ^ A} {z : F A} : x ≡{n}≡ y -> efmap F x z ≡{n}@{F B}≡ efmap F y z.
Proof.
  intros H; apply (@efunct_ctr _ _ F) ; intros m Hm.
  apply ofe_mono with (n := n); auto. lia.
Qed.


Lemma contractive_Sx {A B : eiCOFE} (F : eEndoFunctorCtr eiCOFE) {n} {x y : B ^ A} {z : F A} : x ≡{n}≡ y -> efmap F x z ≡{S n}@{F B}≡ efmap F y z.
Proof.
  intros H; apply (@efunct_ctr _ _ F) ; intros m Hm. 
  apply ofe_mono with (n := n); auto. lia.
Qed.

Lemma fg {F : eEndoFunctorCtr eiCOFE} {k} (x : F $ (S (S k))) : f (S k) ∘e (g (S k)) ≡{k}@{ (F $ (S (S k))) ^ (F $ (S (S k)))}≡ eid{eiCOFE} tt.
Proof.
  induction k.
  - rewrite /g /f -efmap_ecomp -efmap_id.
    apply (@efunct_ctr _ _ F). intros m Hm. lia.
  - rewrite f_S g_S -efmap_ecomp -efmap_id.
    apply contractive_S. 
    apply IHk. by apply g.
Qed.

Record tower (F : eEndoFunctor eiCOFE) : Type :=
  { tower_car k :> F $ k;
    g_tower k : g k (tower_car (S k)) = tower_car k;
  }.

Lemma f_tower {F : eEndoFunctorCtr eiCOFE} k (X : tower F) : f (S k) (X (S k)) ≡{k}≡ X (S (S k)).
Proof.  
  rewrite -g_tower; apply (fg (X (S (S k))) (X (S (S k)))).
Qed.

Lemma tower_eq {F : eEndoFunctor eiCOFE} (X Y : tower F) : X = Y <-> forall k, X k = Y k.
Proof.
  split.
  - by intros -> k. 
  - intros H. destruct X, Y.
    assert (tower_car0 = tower_car1) as -> by (extensionality k; apply H).
    by f_equal ; apply proof_irrelevance.
Qed.

Lemma ofe_tower_mixin (F : eEndoFunctor eiCOFE) :
  OfeMixin (tower F) (fun n X Y => forall k, X k ≡{n}≡ Y k).
Proof.
  split.
  - intros n ; split.
    + intros X k. reflexivity.
    + intros X Y H k. rewrite (H k). reflexivity.
    + intros X Y Z H1 H2 k. rewrite (H1 k) (H2 k). reflexivity.
  - intros X Y ; split.
    + intros H n k. rewrite H. reflexivity.
    + intros H. apply tower_eq. intros k.
      apply ofe_eq; intros n; apply H.
  - intros n m X Y Hm HXY k.
    apply ofe_mono with (n := n); auto.
Qed.

Definition tower_ofe (F : eEndoFunctor eiCOFE) : ofe := {| ofe_car := tower F; ofe_mixin := ofe_tower_mixin F |}.

Definition tower_chain {F : eEndoFunctor eiCOFE} (c : cchain (tower_ofe F)) (k : nat) : cchain (F $ k).
Proof.
  refine {| chain n := c n k |}.
  intros n ? ?. 
  apply (chain_cauchy _ c n); abstract (lia).
Defined.

Definition tower_cofe (F : eEndoFunctor eiCOFE) : cofe.
Proof.
  unshelve refine {| _ofe := tower_ofe F |}.
  - intros c. refine {| tower_car k := compl (F $ k) (tower_chain c k) |} ;
    intros k.
    + apply ofe_eq. intros n.
      pose (H' := conv_compl (F $ (S k)) (tower_chain c (S k)) n).
      rewrite (conv_compl (F $ k) (tower_chain c k) n).
      transitivity (g k (tower_chain c (S k) n)).
      * by apply hom_ne.
      * rewrite g_tower /tower_chain /=; reflexivity.
  - intros c n k; simpl.
    rewrite (conv_compl (F $ k) (tower_chain c k) n).
    reflexivity.
Defined.

Fixpoint ff {k} {F : eEndoFunctor eiCOFE} (i : nat) : F $ k ~~{eiCOFE}~> F $ (i + k) :=
  match i with 0 => (eid{eiCOFE} tt) | S i => f (i + k) ∘e ff i end.

Fixpoint gg {k} {F : eEndoFunctor eiCOFE} (i : nat) : F $ (i + k) ~~{eiCOFE}~> F $ k :=
  match i with 0 => (eid{eiCOFE} tt) | S i => gg i ∘e  g (i + k) end.

Lemma ggff {k i} {F : eEndoFunctorCtr eiCOFE} (x : F $ k) : gg i (ff i x) = x.
Proof. induction i as [|i IH]; simpl; [done|by rewrite (gfx (ff i x)) IH]. Qed.

Lemma ff_tower k i {F : eEndoFunctorCtr eiCOFE} (X : tower F) : ff i (X (S k)) ≡{k}≡ X (i + S k).
Proof.
  induction i as [|i IH]; simpl; [reflexivity|].
  transitivity (f (i + S k) (X (i + S k))); [by apply hom_ne |].
  rewrite PeanoNat.Nat.add_succ_r.
  eapply ofe_mono with (i + k) ; [apply (f_tower (i + k) X) | lia].
Qed.

Lemma gg_tower k i {F : eEndoFunctor eiCOFE} (X : tower F) : gg i (X (i + k)) = X k.
Proof. by induction i as [|i IH]; simpl; [done|rewrite g_tower IH]. Qed.


Definition coerce {F : eEndoFunctor eiCOFE} {i j : nat} (H : i = j) : F $ i ~~> F $ j :=
  eq_rect _ (fun i' => F $ i ~~{eiCOFE}~> F $ i') (eid{eiCOFE} tt) _ H.

Lemma coerce_id {i} {F : eEndoFunctor eiCOFE} (H : i = i) (x : F $ i) : coerce H x = x.
Proof.
  unfold coerce; by assert (H = eq_refl i) as -> by (by apply proof_irrelevance).
Qed.

Lemma coerce_proper {i j} {F : eEndoFunctor eiCOFE} (x y : F $ i) (H1 H2 : i = j) :
  x = y -> coerce H1 x = coerce H2 y.
Proof. by destruct H1; rewrite !coerce_id. Qed.

Lemma g_coerce {k j} {F : eEndoFunctor eiCOFE} (H : S k = S j) (x : F $ (S k)) :
  g j (coerce H x) = coerce (PeanoNat.Nat.succ_inj _ _ H) (g k x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.

Lemma coerce_f {k j} {F : eEndoFunctor eiCOFE} (H : S k = S j) (x : F $ k) :
  coerce H (f k x) = f j (coerce (PeanoNat.Nat.succ_inj _ _ H) x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.

Lemma gg_gg {k i i1 i2 j} {F : eEndoFunctor eiCOFE} : forall (H1: k = i + j) (H2: k = i2 + (i1 + j)) (x: F $ k),
  gg i (coerce H1 x) = gg i1 (gg i2 (coerce H2 x)).
Proof.
  intros Hij -> x. assert (i = i2 + i1) as -> by lia. revert j x Hij.
  induction i2 as [|i2 IH]; intros j X Hij ; simpl ;
    [by rewrite coerce_id|by rewrite g_coerce IH].
Qed.

Lemma ff_ff {k i i1 i2 j} {F : eEndoFunctor eiCOFE} : forall (H1: i + k = j) (H2: i1 + (i2 + k) = j) (x: F $ k),
  coerce H1 (ff i x) = coerce H2 (ff i1 (ff i2 x)).
Proof.
  intros ? <- x. assert (i = i1 + i2) as -> by lia.
  induction i1 as [|i1 IH]; simpl;
    [by rewrite coerce_id|by rewrite coerce_f IH].
Qed.

Definition embed_coerce {k} {F : eEndoFunctor eiCOFE} (i : nat) : F $ k ~~{eiCOFE}~> F $ i :=
  match Compare_dec.le_lt_dec i k with
         | left H => (@gg i F (k - i)) ∘e coerce (eq_sym (PeanoNat.Nat.sub_add _ _ H))
         | right H => coerce (PeanoNat.Nat.sub_add k i (PeanoNat.Nat.lt_le_incl _ _ H)) ∘e (@ff k F (i - k))
  end.
    
Lemma g_embed_coerce {k i} {F : eEndoFunctorCtr eiCOFE} (x : F $ k) :
  g i (embed_coerce (S i) x) = embed_coerce i x.
Proof.
  unfold embed_coerce; destruct (Compare_dec.le_lt_dec (S i) k), (Compare_dec.le_lt_dec i k) ; simpl .
  - symmetry; by erewrite (@gg_gg _ _ 1 (k - S i)); simpl.
  - lia.
  - assert (i = k) by lia; subst. 
    rewrite (ff_ff _ (eq_refl (1 + (0 + k)))) /= gfx.
    by rewrite (gg_gg _ (eq_refl (0 + (0 + k)))).
  - assert (H : 1 + ((i - k) + k) = S i) by lia.
    rewrite (ff_ff _ H) /= -{2}(gfx  (ff (i - k) x)) g_coerce.
    by erewrite coerce_proper by done.
Qed.

Definition embed {F : eEndoFunctorCtr eiCOFE} (n : nat) (x : F $ n) : tower_cofe F.
Proof.
  refine {| tower_car k := (@embed_coerce n F k) x |}.
  intros k; apply g_embed_coerce.
Defined.

Definition tower_icofe (F : eEndoFunctorCtr eiCOFE) : eiCOFE.
Proof.
  refine {| icofe_car := tower_cofe F; icofe_inh := @embed F 0 tt |}.
Defined.

Definition embed' {F : eEndoFunctorCtr eiCOFE} (k : nat) : F $ k ~~{eiCOFE}~> (tower_icofe F).
Proof.
  exists (embed k). 
  intros n x y Hxy i. simpl. by apply hom_ne.
Defined.

Lemma embed_f k {F : eEndoFunctorCtr eiCOFE} (x : F $ k) : embed' (S k) (f k x) = embed' k x.
Proof.
  apply tower_eq; intros i;
  rewrite /embed /= /embed_coerce.
  destruct (Compare_dec.le_lt_dec i (S k)), (Compare_dec.le_lt_dec i k); simpl.
  - assert (H : S k = S (k - i) + (0 + i)) by lia; rewrite (gg_gg _ H) /=.
    rewrite (@g_coerce _ (k - i + i) F H ) gfx.
    by erewrite coerce_proper by done.
  - assert (S k = 0 + (0 + i)) as H by lia.
    rewrite (gg_gg _ H).
    simpl in *; subst.
    by rewrite (ff_ff _ (eq_refl (1 + (0 + k)))).
  - lia.
  - assert (H : (i - S k) + (1 + k) = i) by lia; rewrite (ff_ff _ H) /=.
    by erewrite coerce_proper by done.
Qed.

Lemma embed_tower k {F : eEndoFunctorCtr eiCOFE}(X : tower F) : embed' (S k) (X (S k)) ≡{k}≡ X.
Proof.
  intros i; rewrite /= /embed_coerce.
  destruct (Compare_dec.le_lt_dec i (S k)) as [H|H]; simpl.
  - rewrite -(gg_tower i (S k - i) X).
    apply hom_ne. simpl. destruct (eq_sym _).  reflexivity.
  - destruct (PeanoNat.Nat.sub_add _ _ _); simpl.
    apply (ff_tower k (i - S k) X).
Qed.


Lemma eicofe_comp  {A B C : eiCOFE} (g : B ~~> C) (f : A ~~> B)  (x : A) : (g ∘e f) x = g (f x).
Proof. done. Qed.

Lemma icofe_comp  {A B C : iCOFE} (g : hom iCOFE B C) (f : hom iCOFE A B)  (x : A) : (compose g f) x = g (f x).
Proof. done. Qed.

Definition unfold_chain {F : eFunctorCtr eiCOFE eiCOFE} (X : tower_icofe F) : cchain (F (tower_icofe F)).
Proof.
  refine {| chain n := efmap F (embed' n) (X (S n)) |}.
  intros n m Hnm.
  assert (exists k, m = n + k) as [k ?] by (exists (m - n); lia); subst ; clear Hnm.
  induction k as [| k IH] ; simpl .
  - replace (n + 0) with n by lia. reflexivity.
  - rewrite -IH.
    replace (n + S k) with (S (n + k)) by lia.
    eapply ofe_mono with (n + k) ;  [| lia].
    set (H := f_tower (n + k) X).
    transitivity (efmap F (embed' (S (n + k))) (f (S (n + k)) (X (S (n + k)))) ).
    + apply hom_ne. simpl in *. symmetry. exact H.
    + rewrite /= -eicofe_comp -efmap_ecomp.
      apply (@efmap_mor_ne _ _ F).
      intros x. rewrite icofe_comp embed_f. reflexivity.
Defined.

Definition unfold {F : eEndoFunctorCtr eiCOFE} : tower_icofe F ~~> F (tower_icofe F).
Proof.
  refine {| ne_mor := fun X => compl _ (unfold_chain X) |}.
  intros n x y Hxy.
  rewrite (conv_compl _ (unfold_chain x) n).
  rewrite (conv_compl _ (unfold_chain y) n).
  apply hom_ne.
  apply (Hxy (S n)).
Defined.

Lemma unfold_def {F : eEndoFunctorCtr eiCOFE} {X : tower_icofe F} : unfold X = compl _ (unfold_chain X).
Proof. done. Qed.

Definition project {F : eEndoFunctorCtr eiCOFE} k : (tower_icofe F) ~~{eiCOFE}~> F $ k.
Proof. exists (fun X => tower_car F X k). by intros X Y HX. Defined.

Lemma g_project {F : eEndoFunctorCtr eiCOFE} k : g k ∘e (@project F (S k)) = project k.
Proof. 
  rewrite /project /=.
  apply ne_eq. intros x. simpl.
  apply g_tower.
Qed.

Definition fold {F : eEndoFunctorCtr eiCOFE} : F (tower_icofe F) ~~> tower_icofe F.
Proof.
  unshelve refine {| ne_mor := fun X => _ |}.
  - refine {| tower_car n := g n (efmap F (project n) X) |}.
    intros k .
    rewrite /= -!eicofe_comp.
    rewrite (@ecomp_assoc eiCOFE _ _ _ _ (@g F k)).
    rewrite -efmap_ecomp !eicofe_comp.
    f_equal.
    by rewrite -(g_project k).
  - intros n x y Hxy k. simpl.
    by apply hom_ne ; apply hom_ne. 
Defined.

Lemma fold_unfold {F : eEndoFunctorCtr eiCOFE} : forall X, (@fold F ∘e unfold) X = X.
Proof.
  intros X. apply ofe_eq; intros n k.
  rewrite icofe_comp.
  rewrite /unfold /fold /= -g_tower -(gg_tower _ n).
  apply hom_ne.
  transitivity (efmap F (gg n) (X (S (n + k)))).
  - transitivity (efmap F (project k) (unfold_chain X (n + k))).
    + apply hom_ne. eapply ofe_mono with (n + k); [apply (conv_compl _ (unfold_chain X) (n + k))| lia].
    + transitivity (efmap F (project k) (unfold_chain X n)) .
      * apply hom_ne. eapply ofe_mono with n; [apply (chain_cauchy _ (unfold_chain X) _)|] ; lia.
      * transitivity (efmap F (project k) (unfold_chain X (S (n + k)))).
         -- apply hom_ne. symmetry. apply (chain_cauchy _ (unfold_chain X) n (S (n + k))). lia.
         -- rewrite /= -eicofe_comp -efmap_ecomp.
            set (H := f_tower (n + k) X).
            assert (n <= n + k) as H' by lia.
            eapply ofe_mono in H ; [| exact H'].
            transitivity ( efmap F (project k ∘[iCOFE] embed' (S (n + k))) (f (S (n + k)) (X (S (n + k))) ) ).
            ++ apply hom_ne. symmetry. exact H.
            ++ clear H H'. rewrite -eicofe_comp.
               rewrite -efmap_ecomp. 
               (* rewrite -ecomp_assoc. *)

               assert ( (fix f (F0 : eEndoFunctor eiCOFE) (n0 : nat) {struct n0} :
               F0 $ n0 ~~{ eiCOFE }~> F0 $ S n0 :=
             match n0 as n1 return (F0 $ n1 ~~{ eiCOFE }~> F0 $ S n1) with
             | 0 => inhabitant_icofe_exp (F0 $ 0) (F0 $ 1)
             | S n' => efmap F0 (f F0 n')
             end) F (n + k) = f (n + k)) as -> by done.
             rewrite -eicofe_comp.

               apply contractive_ne_x. intros x.
               rewrite !icofe_comp.
                 (* -(comp_assoc _ (project k) _ _) !icofe_comp. *)
               rewrite (embed_f _ x).  rewrite /= /embed_coerce.
               destruct (Compare_dec.le_lt_dec _ _) ; simpl ; [|lia].
               set (H := @gg_gg (n + k) (n + k - k) 0 n k F (eq_sym (PeanoNat.Nat.sub_add k (n + k) l)) eq_refl x).
               rewrite H /=. reflexivity.
  - assert (forall i k (x : F $ (S i + k)) (H : S i + k = i + S k),
      efmap F (gg i) x = gg i (coerce H x)) as map_ff_gg.
    { intros i; induction i as [|i IH]; intros k' x H; simpl.
      { by rewrite coerce_id efmap_mor_id. }
      rewrite efmap_mor_ecompose g_coerce; apply IH. }
    assert (H: S n + k = n + S k) by lia.
    rewrite map_ff_gg. apply hom_ne. destruct H. simpl.
    reflexivity.
Qed.


Lemma embed_project' {F : eEndoFunctorCtr eiCOFE} n x k (H : k <= n) :  (embed' n ∘e project n) x k ≡{ n }@{ F $ k }≡ x k.
Proof.
  rewrite icofe_comp /= /embed_coerce /=.
  destruct (Compare_dec.le_lt_dec k n) ; try lia.
  rewrite -(@gg_tower k (n - k) F x). 
  assert (n = n - k + k) as H1 by lia.
  rewrite icofe_comp (@gg_gg n (n - k) 0 (n - k) k F ((eq_sym (PeanoNat.Nat.sub_add k n l))) H1 (x n)) /=.
  apply hom_ne; destruct H1 ; reflexivity.
Defined.

Lemma embed_project {F : eEndoFunctorCtr eiCOFE} n: embed' (S n) ∘e project (S n) ≡{ n }@{ tower_icofe F ^ tower_icofe F }≡ eid{eiCOFE} tt.
Proof.
  intros x k.
  destruct (Compare_dec.le_lt_dec k n).
  - apply ofe_mono with (S n); [|lia ].
    apply embed_project' ; lia.
  - rewrite icofe_comp.
    set (H := @embed_tower n F x k).
    transitivity (embed' (S n) (x (S n)) k).
    + apply hom_ne. reflexivity.
    + apply H.
Defined.

Lemma unfold_fold {F : eEndoFunctorCtr eiCOFE} : forall X, (@unfold F ∘e fold) X = X.
Proof.
  intros X. apply ofe_eq; intros n .
  rewrite icofe_comp unfold_def.
  set (H := conv_compl _ (unfold_chain (fold X)) (S n)).
  transitivity (unfold_chain (fold X) (S n)).
  { eapply ofe_mono with (S n) ; [ apply H | lia]  . }
  rewrite /= -!eicofe_comp -!efmap_ecomp.
  rewrite ecomp_assoc.
  assert (efmap_mor F (g n) = g (S n)) by done.
  rewrite H0 (@g_project F (S n)).
  replace (X) with (efmap F (eid{eiCOFE} tt) X) at 2.
  apply contractive_ne_x. 
  apply embed_project.
  by rewrite efmap_id.
Qed. 
  
Global Instance eiCOFE_CtrCompl : eCategoryCtrComplete (eiCOFE).
Proof.
  unshelve (econstructor).
  -  intros F. exact (tower_icofe F).
  -  intros F. unshelve eapply mkEISO with (eto := @fold F) (efrom := @unfold F) ; simpl ; ne_eq.
     + by rewrite unfold_fold.
     + by rewrite fold_unfold.
Qed.
