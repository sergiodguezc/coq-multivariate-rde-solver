From sgdt Require Import category_theory ofe OFE iCOFE ofe_ccc cofe_ccc.
From Coq Require Import ssreflect.

Definition icofe_unit : icofe := {| icofe_car := cofe_unit ; icofe_inh := tt |}.
Arguments icofe_unit : simpl never.

Global Instance iCOFE_Terminal : Terminal iCOFE.
Proof. 
  eapply mkTerminal with (terminal_obj := icofe_unit) ; simpl.
  - intros A. exists (fun _ => tt). by intros n x y H. 
  - intros A f g. ne_eq. by destruct (f x), (g x).
Defined.

(* Product of two icofes is a icofe. *)
Definition icofe_prod (A B : icofe) : icofe := {|
    icofe_car := cofe_prod A B ;
    icofe_inh := (icofe_inh A, icofe_inh B)
  |}.
Arguments icofe_prod : simpl never.

Definition icofe_fst {A B : icofe} : (icofe_prod A B) -n> A := cofe_fst.
Arguments icofe_fst : simpl never.
Definition icofe_snd {A B : icofe} : (icofe_prod A B) -n> B := cofe_snd.
Arguments icofe_snd : simpl never.

Definition icofe_fork {A B C : icofe} (f : C -n> A) (g : C -n> B) : C -n> (icofe_prod A B)
  := cofe_fork f g.
Arguments icofe_fork : simpl never.

Global Instance iCOFE_Product : (FiniteProducts iCOFE) (iCOFE_Terminal).
Proof.
  eapply mkProducts with (p_prod := icofe_prod) (p_fst := @icofe_fst) (p_snd := @icofe_snd) (fork := @icofe_fork) ; simpl.
  intros A B C f g h. split ; intros H.
    + split ; ne_eq ; by rewrite H.
    + destruct H as [H1 H2]. ne_eq. rewrite H1 H2 ; simpl. 
      by destruct (h x).
Defined.

(* Exponential of two icofes is a icofe. *)

Definition inhabitant_icofe_exp (A B : icofe) : cofe_exp A B.
Proof. exists (fun _ => icofe_inh B). intros n x y H. reflexivity. Defined.

Definition icofe_exp (A B : icofe) : icofe.
Proof.
  refine {| icofe_car := cofe_exp A B ;
            icofe_inh := inhabitant_icofe_exp A B |}.
Defined.
Arguments icofe_exp : simpl never.

Definition icofe_exp_iso {A B C : iCOFE} : (A × B ~> C) ≃[ TYPE ] (A ~> icofe_exp B C).
Proof. simpl in *. apply ofe_exp_iso. Defined.

Global Instance iCOFE_CCC : (CCC iCOFE) iCOFE_Product.
Proof.
  eapply mkCCC with (exp := icofe_exp) (exp_iso := @icofe_exp_iso) ; simpl.
  intros. apply ne_eq. intros x. apply ofe_eq. intros n. 
  unfold ofe_curry_hom, ofe_uncurry_mor, ofe_curry_mor, ofe_curry_f, ofe_uncurry_f. simpl.
  destruct x. reflexivity.
Defined.
