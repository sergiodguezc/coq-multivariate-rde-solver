From sgdt Require Import axioms category isomorphism ofe OFE.
Require Import ssreflect.

(* COFE is the category of complete ordered families of equivalences. *)
Lemma icofe_cat_mixin : CatMixin icofe (@NonExpansiveMaps) (@ofe_id) (@ofe_comp).
Proof. split; intros; by apply ne_eq. Qed.

(* Definition of the category of inhabited COFEs. *)
Definition iCOFE : Category := {|
  obj := icofe;
  hom := NonExpansiveMaps;
  id := @ofe_id;
  compose := @ofe_comp;
  cat_mixin := icofe_cat_mixin
|}.

(* In case we want to use the iCOFE category as a notation *)
Definition icofe_comp_cat {A B C : icofe} (f : B -n> C) (g : A -n> B)  :
  ofe_comp f g = f ∘[iCOFE] g := eq_refl.

(* Two morphisms are equal if they are pointwise equal. *)
Lemma icne_eq : forall {A B : iCOFE} {f g : A ~{iCOFE}~> B},
    (forall x, f x = g x) -> f = g.
Proof.
  intros; destruct f, g . 
  assert (ne_mor = ne_mor0) as -> by (extensionality x; auto);
  f_equal; apply proof_irrelevance.
Qed.

(* Tactic to simplify goals involving iCOFEs. *)
Ltac icne_eq := apply icne_eq; intros.

Program Definition iso_icofe_to_ofe  {A B : icofe} (H : @iso iCOFE A B) : @iso OFE A B :=
  {| to := to H; from := from H ; from_to := from_to H ; to_from := to_from H |}.
