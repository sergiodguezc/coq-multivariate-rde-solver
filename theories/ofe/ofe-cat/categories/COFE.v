From sgdt Require Import axioms category ofe OFE.
From Coq Require Import ssreflect.

(* COFE is the category of complete ordered families of equivalences. *)
Lemma cofe_cat_mixin : CatMixin cofe (@NonExpansiveMaps) (@ofe_id) (@ofe_comp).
Proof. split; intros; by apply ne_eq. Qed.

(* Definition of the category of COFEs. *)
Definition COFE : Category := {|
  obj := cofe;
  hom := NonExpansiveMaps;
  id := @ofe_id;
  compose := @ofe_comp;
  cat_mixin := cofe_cat_mixin
|}.

(* Two morphisms are equal if they are pointwise equal. *)
Lemma cne_eq : forall {A B : COFE} {f g : A ~{COFE}~> B},
    (forall x, f x = g x) -> f = g.
Proof.
  intros; destruct f, g. 
  assert (ne_mor = ne_mor0) as -> by (extensionality x; auto);
  f_equal; apply proof_irrelevance.
Qed.

(* Tactic to simplify goals involving COFEs. *)
Ltac cne_eq := apply cne_eq; intros.
