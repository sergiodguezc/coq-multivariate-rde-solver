From sgdt Require Import category_theory ofe ofe_ccc cofe_ccc OFE COFE iCOFE icofe_ccc.
Require Import ssreflect.

(* Later ofe *)
Inductive later_car (F : ofe) :=
  | next : F -> (later_car F).
Arguments next {_} _.

Definition get_car {F : ofe} (x : later_car F) : F :=
  match x with | next x => x end.

Definition later_dist (F : ofe) : nat -> later_car F -> later_car F -> Prop :=
  fun n x y => n = 0%nat \/ F.(ofe_dist) (n - 1) (get_car x) (get_car y).

Lemma ofe_later_mixin (F : ofe) : OfeMixin (later_car F) (later_dist F).
Proof.
  split.
  - intros n; split.
    (* Refl *)
    + intros x.
      destruct x, n ; [by left | right]. reflexivity. 
    (* Sym *)
    + intros x y H. destruct x, y, n, H ; [by left | | inversion H |] ; right ; by symmetry.
    (* Trans *)
    + intros x y z H1 H2. destruct n, x, y, z ; [by left | ].
      * destruct H1; [inversion H|]. 
        right. destruct H2 ; [inversion H0 |]. 
        etransitivity ; first (apply H). apply H0.
  (* Eq *)
  - intros x y. split. 
    + intros -> n. destruct y ; right. reflexivity.
    + intros H. destruct x, y.
      f_equal. apply ofe_eq.
      intros n. specialize (H (S n)). destruct H. lia.
      by replace (S n - 1) with n in H by lia.
  (* Mono *)
  - intros n m x y H1 H2. destruct x, y. destruct H1 ; [left ; lia | right].
    assert (m - 1 <= n - 1) by lia. eapply ofe_mono with (m := m - 1); eauto.
Qed.

Definition ofe_later (F : OFE) : OFE := {|
  ofe_car := later_car F;
  ofe_dist := later_dist F;
  ofe_mixin := ofe_later_mixin F
|}.

Notation "▶  F" := (ofe_later F) (at level 20, right associativity).

(* Later of a cofe is a cofe. *)
Definition cchain_from_later {A : ofe} (c : cchain (▶  A)) : cchain A.
Proof.
  refine {| chain n := get_car (c (S n)) |}.
  intros n m Hnm. unfold get_car. simpl.
  destruct (c (S n)) eqn:H1, (c (S m)) eqn:H2. destruct c as [c Hc]. simpl in *.
  unfold later_dist in Hc. simpl in Hc.
  assert (H : S n <= S m) by lia.
  specialize (Hc (S n) (S m) H). rewrite H1 in Hc. rewrite H2 in Hc.
  destruct Hc.
  - lia.
  - by replace (S n - 1) with n in H0 by lia. 
Defined.

Definition cofe_later_compl {A : cofe} (c : cchain (▶  A)) : ▶  A.
Proof.
  pose (cl := cchain_from_later c).
  pose (x := compl A cl). exact (next x).
Defined.

Definition cofe_later (A : COFE) : COFE.
Proof.
  eapply mkCOFE with (_ofe := ▶  A) (compl := cofe_later_compl).
  intros c. pose (cl := cchain_from_later c).
  set (x := compl A cl).
  set (Hx := conv_compl A cl).
  intros n. simpl.
  destruct (c n) eqn:H. destruct n ; [by left | right].
  replace (S n - 1) with n by lia.
  assert (H' : cl n = o).
  { simpl. unfold get_car. by rewrite H. }
  specialize (Hx n). rewrite H' in Hx. by apply Hx.
Defined.

Definition icofe_later (A : iCOFE) : iCOFE := {|
  icofe_car := cofe_later A ;
  icofe_inh := next (icofe_inh A)
|}.

(* Later is an endofunctor. *)
Definition olater_fmap {A B : ofe} (f : A -n> B) : ▶  A -n> ▶  B.
Proof.
  exists (fun x => next (f (get_car x))).
  intros n x y Hxy.
  destruct n ; [by left | right].
  replace (S n - 1) with n by lia.
  destruct x, y. simpl in *. destruct Hxy ; [lia | ].
  apply hom_ne. by replace n with (n - 0) by lia.
Defined.

Lemma olaterF_mixin : FunctMixin OFE OFE ofe_later (@olater_fmap).
Proof.
  split.
  - intros A. apply ne_eq. intros x. simpl. by destruct x.
  - intros A B C f g. apply ne_eq. intros x. simpl. by destruct x.
Qed.

Definition olaterF : EndoFunctor OFE := {|
  fobj := ofe_later;
  fmap := @olater_fmap;
  funct_mixin := olaterF_mixin
|}.

Lemma laterF_mixin : FunctMixin COFE COFE cofe_later (@olater_fmap).
Proof.
  split.
  - intros A. apply cne_eq. intros x. simpl. by destruct x.
  - intros A B C f g. apply cne_eq. intros x. simpl. by destruct x.
Qed.

Definition laterF : EndoFunctor COFE := {|
  fobj := cofe_later;
  fmap := @olater_fmap;
  funct_mixin := laterF_mixin
|}.

Lemma ilaterF_mixin : FunctMixin iCOFE iCOFE icofe_later (@olater_fmap).
Proof.
  split.
  - intros A. apply icne_eq. intros x. simpl. by destruct x.
  - intros A B C f g. apply icne_eq. intros x. simpl. by destruct x.
Qed.

Definition ilaterF : EndoFunctor iCOFE := {|
  fobj := icofe_later;
  fmap := @olater_fmap;
  funct_mixin := ilaterF_mixin
|}.

(* Later preserve exponentials *)
Definition later_preserve_exp {A B : COFE} : laterF (B ^ A) ~{COFE}~> (laterF B) ^ (laterF A).
Proof.
  unshelve epose (f := _ : laterF (B ^ A) -> (laterF B) ^ (laterF A)).
  { intros [f]. apply laterF. exact f. }
  exists f.
  intros n [x] [y] Hxy. simpl in *.
  destruct Hxy ; [by left | right].
  apply H.
Defined.

Definition ilater_preserve_exp {A B : iCOFE} : ilaterF (B ^ A) ~{iCOFE}~> (ilaterF B) ^ (ilaterF A).
Proof. simpl ; apply later_preserve_exp. Defined.

(* Later is preserve products and isomorphism *)
Definition later_preserve_prod {A B : COFE} : laterF (A × B) ~{COFE}~> (laterF A) × (laterF B).
Proof.
  unshelve epose (f := _ : laterF (A × B) -> (laterF A) × (laterF B)).
  { intros [[x y]]. split ; by apply next. }
  exists f.
  intros n [[x1 x2]] [[y1 y2]] Hxy; split; simpl in *.
  - destruct Hxy; [by left | right]. apply H.
  - destruct Hxy; [by left | right]. apply H.
Defined.

Definition later_preserve_prod_inv {A B : COFE} : (laterF A) × (laterF B) ~> laterF (A × B).
Proof.
  unshelve epose (f := _ : (laterF A) × (laterF B) -> laterF (A × B)).
  { intros [[x] [y]]. by apply next. }
  exists f.
  intros n [[x]] [[y]] [H1 H2]; simpl in *.
  destruct n ; [by left | right] ; simpl.
  replace (n - 0) with n by lia. split.
  - destruct o, o0. simpl in *. destruct H1; try lia.
    simpl in *. by replace (n - 0) with n in H by lia. 
  - destruct o, o0. simpl in *. destruct H2; try lia.
    simpl in *. by replace (n - 0) with n in H by lia.
Defined.

Definition later_prod_iso {A B : COFE} : laterF (A × B) ≃  (laterF A) × (laterF B) .
Proof.
  eapply mkISO with (to := later_preserve_prod) (from := later_preserve_prod_inv) ; cne_eq ; simpl.
  - by destruct x, o. 
  - by destruct x, o, o0. 
Qed.

Definition ilater_preserve_prod {A B : iCOFE} : ilaterF (A × B) ~{iCOFE}~> (ilaterF A) × (ilaterF B).
Proof. simpl in *. exact later_preserve_prod. Defined.

Definition ilater_preserve_prod_inv {A B : iCOFE} : (ilaterF A) × (ilaterF B) ~> ilaterF (A × B).
Proof. simpl in *. apply later_preserve_prod_inv. Defined.

Definition ilater_prod_iso {A B : iCOFE} : ilaterF (A × B) ≃[iCOFE]  (ilaterF A) × (ilaterF B) .
Proof. 
  eapply mkISO with (to := ilater_preserve_prod) (from := ilater_preserve_prod_inv) ; icne_eq ; simpl.
  - by destruct x, o.
  - by destruct x, o, o0.
Qed.


(* Next is a natural transformation from the identity functor to the later functor. *)
Definition onext_nat : NatTrans (id_functor OFE) olaterF.
Proof.
  unshelve eapply mkNAT with (nt := _).
  { intros. simpl in *. exists (fun x => next x).
    intros n x y H. simpl. destruct n ; [by left | right].
    simpl. replace (n - 0) with n by lia. eapply ofe_mono with (n := S n) ; eauto.
  } 
  intros B C f. ne_eq. reflexivity.
Defined.

Definition next_nat : NatTrans (id_functor COFE) laterF.
Proof.
  unshelve eapply mkNAT with (nt := _).
  { intros. simpl in *. exists (fun x => next x).
    intros n x y H. simpl. destruct n ; [by left | right].
    simpl. replace (n - 0) with n by lia. eapply ofe_mono with (n := S n) ; eauto.
  } 
  intros B C f. cne_eq. reflexivity.
Defined.

(* Definition inext_nat_nt : forall B, (id_functor iCOFE) B ~> ilaterF B. *)
(* Proof. intros; simpl in *; apply next_nat_nt. Defined. *)

Definition inext_nat : NatTrans (id_functor iCOFE) ilaterF.
Proof.
  unshelve eapply mkNAT with (nt := _) .
  { intros . exists (fun x => next x).
    intros n x y H. destruct n ; [by left | right].
    simpl. replace (n - 0) with n by lia. eapply ofe_mono with (n := S n) ; eauto.
  } 
  intros B C f. icne_eq. reflexivity.
Defined.

(* Contractive characterization using later *)
Definition g_from_contractive {A B : COFE} (f : A -c> B)  : laterF A ~> B.
Proof.
  exists (fun x => f (get_car x)).
  intros n x y Hxy.
  destruct n ; simpl in *.
  - apply hom_ctr. intros m Hm. lia.
  - destruct Hxy ; [lia |].
    apply hom_ctr. intros m Hm. replace (S n - 1) with n in H by lia. 
    assert (m <= n) by lia. 
    apply ofe_mono with (n := n) ; eauto.
Defined.

Lemma contractive_laterT {A B : COFE} (f : A -c> B) :
  { g : laterF A ~> B | ctr_map f = g ∘ (nt next_nat A) }.
Proof.
  exists (g_from_contractive f); unfold g_from_contractive; simpl.
  destruct f. by ne_eq.
Defined.

Lemma contractive_later {A B : COFE} (f : A -> B) :
  Contractive f <-> exists g : laterF A ~> B, f = g ∘ (nt next_nat A).
Proof.
  split.
  - intros H.
    unshelve epose (g := _ : A -c> B). 
    { refine {| ctr_mor := f ; hom_ctr := H |}. }
    exists (g_from_contractive g). 
    unfold g_from_contractive. by extensionality x.
  - intros [g ->] n x y Hxy.
    destruct n ; simpl ; apply hom_ne ; [by left | right].
    replace (S n - 1) with n by lia. apply Hxy. lia.
Qed.

Definition ig_from_contractive {A B : iCOFE} (f : A -c> B) : ilaterF A ~> B.
Proof.
  simpl; by pose (g := g_from_contractive f).
Defined.

Lemma contractive_ilaterT {A B : iCOFE} (f : A -c> B) :
  { g : ilaterF A ~> B | ctr_map f = g ∘ (nt inext_nat A) }.
Proof.
  exists (ig_from_contractive f); unfold ig_from_contractive; simpl.
  destruct f. by ne_eq.
Defined.

Lemma contractive_ilater {A B : iCOFE} (f : A -> B) :
  Contractive f <-> exists g : ilaterF A ~> B, f = g ∘ (nt inext_nat A).
Proof.
  split.
  - intros H.
    unshelve epose (g := _ : A -c> B). 
    { refine {| ctr_mor := f ; hom_ctr := H |}. }
    exists (ig_from_contractive g).
    by extensionality x.
  - intros [g ->] n x y Hxy.
    destruct n ; simpl ; apply hom_ne ; [by left | right].
    replace (S n - 1) with n by lia. apply Hxy. lia.
Qed.
