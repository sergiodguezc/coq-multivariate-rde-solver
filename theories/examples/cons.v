From sgdt Require Import category_theory ofe OFE ofe_ccc later.

Definition inf_seq_dist {A : ofe} n (x y : nat -> A) : Prop := 
  forall m, m <= n -> x m ≡{n}@{A}≡ y m.

Definition inf_seq_mixing {A : ofe}  : OfeMixin (nat -> A) (@inf_seq_dist A).
Proof.
  split.
  - intros n; split.
    + intros x m Hm. reflexivity.
    + intros x y Hxy m Hm. symmetry. apply Hxy. assumption.
    + intros x y z Hxy Hyz m Hm. etransitivity; [apply Hxy|apply Hyz]; assumption.
  - intros x y. split.
    + intros ->. intros n m Hm. reflexivity.
    + intros Hxy. extensionality n. apply ofe_eq. intros m.
      destruct (Compare_dec.le_ge_dec n m) as [Hnm|Hnm].
      * specialize (Hxy m). apply Hxy. assumption.
      * specialize (Hxy n). unfold inf_seq_dist in Hxy.
        eapply ofe_mono with n.
         apply Hxy. lia. assumption.
  - intros n m x y Hxy Hmn k Hkm. 
    eapply ofe_mono with n. apply Hxy. lia. assumption.
Qed.

Definition inf_seq (A : ofe) : ofe := {|
  ofe_car := nat -> A;
  ofe_dist := @inf_seq_dist A;
  ofe_mixin := @inf_seq_mixing A;
 |}.

Program Definition cons {A : ofe} : ofe_prod A (inf_seq A) -n> inf_seq A :=
  {| ne_mor '(x, s) n := match n with 0 => x | S n => s n end; |}.
Next Obligation.
  intros n [x s1] [y s2] [Hxy1 Hxy2] m Hm; destruct m.
  - apply Hxy1.
  - apply Hxy2. lia.
Qed.

Definition dcons {A : Type} := @cons (ofe_lift A).

(* If the type A has at least two distinct elements, then dcons is not contractive *)
Lemma dcons_not_ctr {A : Type} (x y : A) (H : x <> y) : ~ Contractive (@dcons A).
Proof.
  intros HCtr.
  set s1 := (fun n => x) : inf_seq (ofe_lift A).
  set s2 := (fun n => y) : inf_seq (ofe_lift A).
  assert (H1 : @dist_later (ofe_prod (ofe_lift A) (inf_seq (ofe_lift A))) 0 (x, s1) (y, s2)) by (intros k Hk ; lia).
  specialize (HCtr 0 (x, s1) (y, s2) H1 0 ltac:(lia)).
  contradiction.
Qed.

(* However, dcons is always contractive in the  second argument *)
Lemma cons_ctr_snd {A : Type} : ContractiveSnd (@dcons A).
Proof.
  intros x n f g Hfg m Hm. 
  destruct n.
  - assert (m = 0) as -> by lia; reflexivity.
  - destruct m ; first reflexivity.
    specialize (Hfg m ltac:(lia) m ltac:(lia)). 
    apply Hfg. 
Qed.
