From sgdt Require Import category isomorphism type structure.
From Coq Require Import FunctionalExtensionality.

 (* TYPE is a cartesian closed category *)
Global Instance Terminal_TYPE : Terminal TYPE.
Proof.
  eapply mkTerminal with (terminal_obj := unit) ; simpl.
  - intros; exact tt.
  - intros A f g; extensionality x; destruct (f x), (g x). reflexivity.
Defined.

(*  TYPE has finite products *)
Instance FiniteProducts_TYPE : FiniteProducts TYPE Terminal_TYPE.
Proof.
  eapply mkProducts with (p_prod := fun (A B : obj[TYPE] ) => (A * B)%type)
  (fork := fun A B C f g => fun x => (f x, g x))
  (p_fst := @fst) (p_snd := @snd) ; simpl.
  intros A B C f g h.
  split ; intros H.
  - split; extensionality x; simpl; rewrite H; reflexivity.
  - destruct H as [Hf1' Hf2']. rewrite Hf1', Hf2'. extensionality x.
    destruct (h x) eqn:H. unfold compose. simpl. rewrite H. reflexivity.
Defined.

(*  TYPE satisfies the universal property of exponentials *)
Definition type_exp_iso {A B C : TYPE} : (A × B ~> C) ≃[ TYPE ] (A ~> (B -> C)).
Proof.
  simpl in *.
  pose (to := fun (f : A * B -> C) (x : A) => (fun (y : B) => f (x, y))).
  pose (from := fun (f : A -> (B -> C)) => (fun (x : A * B) => f (fst x) (snd x))).
  eapply mkISO with (to := to) (from := from) ; simpl.
  - extensionality f. extensionality x. unfold from, to. destruct x. reflexivity.
  - extensionality f. extensionality x. extensionality y. unfold from, to. reflexivity.
Defined.

(*  TYPE is a cartesian closed category *)
Instance CCC_TYPE : CCC TYPE FiniteProducts_TYPE.
Proof.
  eapply mkCCC with (exp := fun A B => A -> B ) (exp_iso := @type_exp_iso).
  intros A B C f. simpl. extensionality x. destruct x. reflexivity.
Defined.
