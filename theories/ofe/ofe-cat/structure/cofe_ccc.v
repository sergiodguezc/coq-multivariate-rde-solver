From sgdt Require Import category_theory ofe COFE ofe_ccc.
From Coq Require Import ssreflect.

(* Unit is a cofe. *)
Program Definition cofe_unit : cofe :=
  {| _ofe := ofe_unit ; compl := fun _ => tt |}.
Next Obligation. by destruct (c 0%nat), (c n). Qed.
Arguments cofe_unit : simpl never.

Global Instance COFE_Terminal : Terminal COFE.
Proof.
  eapply mkTerminal with (terminal_obj := cofe_unit) ; simpl.
  - intros. exists (fun _ => tt). by intros n x y H.
  - intros. ne_eq. by destruct (f x), (g x).
Defined.

(* Product of two cofes is a cofe. *)
Program Definition cofe_prod (A B : cofe) : cofe :=
  {| _ofe := ofe_prod A B ;
     compl := fun c => (compl A (chain_map ofe_fst c), compl B (chain_map ofe_snd c)) |}.
Next Obligation.
  pose (H1 := conv_compl A (chain_map ofe_fst c));
  pose (H2 := conv_compl B (chain_map ofe_snd c));
  split; [apply H1 | apply H2].
Qed. 
Arguments cofe_prod : simpl never.

Definition cofe_fst {A B : cofe} : (cofe_prod A B) -n> A := ofe_fst.
Arguments cofe_fst : simpl never.

Definition cofe_snd {A B : cofe} : (cofe_prod A B) -n> B := ofe_snd.
Arguments cofe_snd : simpl never.

Definition cofe_fork {A B C : cofe} (f : C -n> A) (g : C -n> B) : C -n> (cofe_prod A B) := ofe_fork f g.

Global Instance COFE_Product : (FiniteProducts COFE) (COFE_Terminal). 
Proof.
  eapply mkProducts with (p_prod := cofe_prod) (p_fst := @cofe_fst) (p_snd := @cofe_snd)
  (fork := @cofe_fork) ; simpl.
  intros. split ; intros H.
  - split ; ne_eq ; simpl ; rewrite H ; reflexivity.
  - destruct H as [H1 H2]. rewrite H1 H2. ne_eq. simpl.
    by destruct (h x).
Defined.

(* Exponential of two cofes is a cofe. *)

Program Definition exp_chain {A B : ofe} (c : cchain (ofe_exp A B)) (a : A) : cchain B :=
  {| chain n := c n a |}.
Next Obligation.
  destruct c as [c Hc]; by apply Hc.
Qed.  

Program Definition cofe_exp_compl {A B : cofe} (c : cchain (ofe_exp A B)) : ofe_exp A B :=
  {| ne_mor a := compl B (exp_chain c a) |}.
Next Obligation.
  intros n a1 a2 H. 
  set (cl := exp_chain c).
  specialize (conv_compl B (cl a1) n). intros Hcl1.
  specialize (conv_compl B (cl a2) n). intros Hcl2.
  destruct c as [c Hc]. simpl in *.
  rewrite Hcl1 Hcl2.
  by apply hom_ne.
Qed.

Program Definition cofe_exp (A B : cofe) : cofe :=
  {| _ofe := ofe_exp A B ; compl := cofe_exp_compl |}.
Next Obligation. apply conv_compl. Qed.
Arguments cofe_exp : simpl never.

Definition cofe_exp_iso {A B C : COFE} : (A × B ~> C) ≃[ TYPE ] (A ~> cofe_exp B C).
Proof. simpl in *. apply ofe_exp_iso. Defined.

Global Instance COFE_CCC : (CCC COFE) COFE_Product.
Proof.
  eapply mkCCC with (exp := cofe_exp) (exp_iso := @cofe_exp_iso) ; simpl.
  intros. ne_eq. apply ofe_eq. intros n. 
  simpl. destruct x. reflexivity.
Defined.
