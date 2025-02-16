From Coq Require Import ssreflect Lia RelationClasses Relation_Definitions SetoidClass.
From sgdt Require Import axioms category isomorphism.

(* Ordered Family of Equivalences (OFE) *)

(* Structure defining the mixin for an OFE *)
Structure OfeMixin (A : Type) (dist : nat -> relation A) := {
    mixin_ofe_equiv' n : Equivalence (dist n);  (* Each distance relation is an equivalence relation *)
    mixin_ofe_eq x y : x = y <-> forall n, dist n x y;  (* Equality is equivalent to distance at all levels *)
    mixin_ofe_mono n m x y : dist n x y -> m <= n -> dist m x y;  (* Distance is monotonic in the level *)
  }.

(* Record defining an OFE *)
Record ofe : Type := {
  ofe_car : Type;  (* The underlying type *)
  ofe_dist : nat -> relation ofe_car;  (* The distance relation at each level *)
  ofe_mixin : OfeMixin ofe_car ofe_dist  (* The mixin containing the OFE properties *)
}.

Coercion ofe_car : ofe >-> Sortclass.
Global Arguments ofe_car : simpl never.

(* Instance proving that the distance relation at each level is an equivalence relation *)
Global Instance ofe_equiv (A : ofe) n : Equivalence (ofe_dist A n).
Proof. apply mixin_ofe_equiv', ofe_mixin. Qed.

(* Lemma stating that equality is equivalent to distance at all levels *)
Lemma ofe_eq {A : ofe} (x y : A) : x = y <-> forall n, ofe_dist A n x y.
Proof. apply mixin_ofe_eq, ofe_mixin. Qed.

(* Lemma stating that distance is monotonic in the level *)
Lemma ofe_mono {A : ofe} (n m : nat) (x y : A) : ofe_dist A n x y -> m <= n -> ofe_dist A m x y.
Proof. apply mixin_ofe_mono, ofe_mixin. Qed.

(* Notation for distance at a specific level *)
Notation "x ≡{ n }≡  y" := (ofe_dist _ n x y) (at level 70, no associativity).
Notation "x ≡{ n }@{ A }≡ y" := (ofe_dist A n x y) (at level 70, no associativity).

(* Product of two OFEs is an OFE *)

(* Lemma proving that the product of two OFEs satisfies the OFE mixin *)
Lemma ofe_prod_mixin (A B : ofe) : OfeMixin (A * B)
  (fun (n : nat) (x y : A * B) =>
    ofe_dist A n (fst x) (fst y) /\ ofe_dist B n (snd x) (snd y)).
Proof.
  split.
  - intros n ; split.
    + intros [x1 x2] ; split ; apply ofe_equiv.  (* Reflexivity *)
    + intros [x1 x2] [y1 y2] [H1 H2]; split ; simpl in *; by apply ofe_equiv.  (* Symmetry *)
    + intros [x1 x2] [y1 y2] [z1 z2] [H1 H2] [H3 H4] ; split ; simpl in *;
      etransitivity ; eauto.  (* Transitivity *)
  - intros x y. split.
    + intros -> n. split; reflexivity.  (* Equality implies distance at all levels *)
    + intros H. destruct x as [x1 x2], y as [y1 y2].
      f_equal ; apply ofe_eq ; intros n ; apply H.  (* Distance at all levels implies equality *)
  - intros n m x y H1 Hm. destruct H1. split ; eapply ofe_mono with (m := m); eauto.  (* Monotonicity *)
Qed.

(* Definition of the product of two OFEs *)
Definition ofe_prod (A B : ofe) : ofe := {|
  ofe_car := A * B;
  ofe_dist := fun n x y => ofe_dist A n (fst x) (fst y) /\ ofe_dist B n (snd x) (snd y);
  ofe_mixin := ofe_prod_mixin A B
 |}.

(* Definition of a non-expansive function between OFEs *)
Definition NonExpansive {A B : ofe} (f : A -> B) : Prop :=
  forall n, Proper (ofe_dist A n ==> ofe_dist B n) f.

(* Record defining a non-expansive map between OFEs *)
Record NonExpansiveMaps (A B : ofe) : Type := 
  { ne_mor : A -> B;  (* The underlying function *)
    hom_ne : NonExpansive ne_mor  (* Proof that the function is non-expansive *)
  }.

Notation "A -n> B" := (NonExpansiveMaps A B) (at level 99).

Coercion ne_mor : NonExpansiveMaps >-> Funclass.
Arguments ne_mor {A B} f _ : rename.

(* Lemma stating that two non-expansive maps are equal if their underlying functions are equal *)
Lemma ne_eq : forall {A B : ofe} {f g : A -n> B},
    (forall x, f x = g x) -> f = g.
Proof.
  intros; destruct f, g.
  assert (ne_mor0 = ne_mor1) as -> by (extensionality x; auto);
  f_equal; apply proof_irrelevance.
Qed.

(* Tactic to prove equality of non-expansive maps by extensionality *)
Ltac ne_eq := apply ne_eq; intros.

(* Composition of morphisms *)
Program Definition ofe_comp {A B C : ofe} (f : B -n> C) (g : A -n> B) : A -n> C :=
  {| ne_mor := fun x => f (g x) |}.
Next Obligation.
  intros n x y H; by repeat apply hom_ne.
Qed.

(* Identity morphism *)
Program Definition ofe_id {A : ofe} : A -n> A := {| ne_mor := fun x => x |}.
Next Obligation.
  by intros n x y H.
Qed.


(* Lemma stating that the composition of two non-expansive maps is non-expansive *)
Lemma ne_trans {A B C : ofe} (f : B -n> C) (g : A -n> B) : A -n> C.
Proof.
  refine {| ne_mor := fun x => f (g x) |}. 
  intros n x y H. by repeat apply hom_ne.  (* Apply non-expansiveness of f and g *)
Defined.

(* Definition of a distance relation for later levels *)
Definition dist_later {A : ofe} n (x y : A) : Prop :=
  forall m, m < n -> ofe_dist A m x y .

(* Definition of a distance relation for finite levels *)
Definition dist_later_fin {A : ofe} (n : nat) (x y : A) :=
  match n with 0 => True | S n => x ≡{n}≡ y end.

(* Lemma stating that the distance relation for later levels is equivalent to the finite distance relation *)
Lemma later_dist_iff_dist_later {A : ofe} n x y :
  dist_later n x y <-> @dist_later_fin A n x y.
Proof.
  destruct n; unfold dist_later_fin.
  - split; intros H.
    + trivial.  (* Trivial case for n = 0 *)
    + intros m Hm. lia.  (* No need to check distance for m < 0 *)
  - split; intros H.
    + apply H. lia.  (* Apply the distance relation for m < n *)
    + intros m Hm. eapply ofe_mono; eauto. lia.  (* Use monotonicity of distance *)
Qed.

(* Definition of a contractive function between OFEs *)
Definition Contractive {A B : ofe} (f : A -> B) : Prop :=
   forall n, Proper (dist_later n ==> ofe_dist B n) f.

(* Record defining a contractive map between OFEs *)
Record ContractiveMaps (A B : ofe) : Type :=
  { ctr_mor : A -> B;  (* The underlying function *)
    hom_ctr : Contractive ctr_mor  (* Proof that the function is contractive *)
  }.
Coercion ctr_mor : ContractiveMaps >-> Funclass.

Notation "A -c> B" := (ContractiveMaps A B) (at level 99).

(* Program definition of the first morphism in the product OFE *)
Program Definition FirstMor {A B C : ofe} (f : ofe_prod A B -n> C) (b : B) : A -n> C := {|
  ne_mor a := f (a, b)
 |}.
Next Obligation.
  intros n a1 a2 Ha. apply hom_ne ; split ; [apply Ha | reflexivity ].  (* Apply non-expansiveness of f *)
Qed.

(* Program definition of the second morphism in the product OFE *)
Program Definition SecondMor {A B C : ofe} (f : ofe_prod A B -n> C) (a : A) : B -n> C := {|
  ne_mor b := f (a, b)
 |}.
Next Obligation.
  intros n b1 b2 Hb. apply hom_ne ; split ; [reflexivity | apply Hb].  (* Apply non-expansiveness of f *)
Qed.

(* Definition of a contractive first morphism in the product OFE *)
Definition ContractiveFst {A B C : ofe} (f : ofe_prod A B -n> C) := forall x, Contractive (FirstMor f x).

(* Definition of a contractive second morphism in the product OFE *)
Definition ContractiveSnd {A B C : ofe} (f : ofe_prod A B -n> C) := forall x, Contractive (SecondMor f x).

(* Lemma stating that a contractive function is non-expansive *)
Lemma ctr_ne {A B : ofe} (f : A -> B) :
  Contractive f -> NonExpansive f.
Proof.
  intros H n x y H1; apply H; intros m Hm; apply ofe_mono with (n := n) ; [eauto | lia].  (* Use contractiveness and monotonicity *)
Qed.

(* Program definition of a contractive map as a non-expansive map *)
Program Definition crt_maps_ne {A B : ofe} (f : A -c> B) : A -n> B :=
{| ne_mor := f |}.
Next Obligation. apply ctr_ne, hom_ctr. Qed.
Coercion crt_maps_ne : ContractiveMaps >-> NonExpansiveMaps.

(* Lemma stating that a contractive map is non-expansive *)
Lemma hom_ctr_ne {A B : ofe} (f : A -c> B) : NonExpansive f.
Proof. apply ctr_ne, hom_ctr. Qed.

(* The composition of a contractive map with a non-expansive map is contractive *)
Program Definition comp_ctr_ne_contractive {A B C : ofe} (f : B -n> C) (g : A -c> B) : A -c> C :=
  {| ctr_mor := fun x => f (g x) |}.
Next Obligation.
  intros n x y H; apply hom_ne;
  apply hom_ctr; intros m Hm; destruct n ; [lia |];
  apply ofe_mono with (n := n) ; [apply H | ] ; lia.  
Qed.

(* The composition of a non-expansive map with a contractive map is contractive *)
Program Definition comp_ne_ctr_contractive {A B C : ofe} (f : B -c> C) (g : A -n> B) : A -c> C :=
  {| ctr_mor := fun x => f (g x) |}.
Next Obligation.
  intros n x y H; apply hom_ctr; intros m Hm; apply hom_ne;
  apply H; lia.
Qed.

(* The product of two contractive maps is contractive *)
Program Definition prod_ctr_contractive {A B C D : ofe} (f : A -c> B) (g : D -c> C) : ofe_prod A D -c> ofe_prod B C :=
  {| ctr_mor := fun '(x, y) => (f x, g y) |}.
Next Obligation.
  intros n [x1 x2] [y1 y2] H; split ; [apply hom_ctr | apply hom_ctr]; intros m Hm; apply H; lia.
Qed.

(* Complete OFE *)

(* Record defining a Cauchy chain in an OFE *)
Record cchain (A : ofe) := {
  chain :> nat -> A;  (* The sequence of elements *)
  chain_cauchy n m : n <= m -> ofe_dist A n (chain m) (chain n)  (* Cauchy condition *)
}.

(* Program definition of a shifted Cauchy chain *)
Program Definition chain_shift {A : ofe} (c : cchain A) (m : nat ) : cchain A :=
  {| chain n := c (n + m) |}.
Next Obligation. 
  rename m0 into k.
  destruct c; simpl.
  assert (H1 : n + m <= k + m) by lia. 
  specialize (chain_cauchy0 (n + m) (k + m) H1).
  eapply ofe_mono with (n := n + m); eauto. lia.  (* Use monotonicity of distance *)
Qed.

(* Program definition of a mapped Cauchy chain *)
Program Definition chain_map {A B : ofe} (f : A -n> B) (c : cchain A) : cchain B :=
  {| chain n := f (c n) |}.
Next Obligation. apply hom_ne, chain_cauchy; lia. Qed.  (* Apply non-expansiveness of f *)

(* COFE (Complete Ordered Family of Equivalences) *)

(* Record defining a COFE *)
Record cofe : Type := mkCOFE
  { _ofe : ofe;  (* The underlying OFE *)
    compl : cchain _ofe -> _ofe;  (* The completion function *)
    conv_compl (c : cchain _ofe) (n : nat) : ofe_dist _ofe n (compl c) (c n)  (* Convergence condition *)
  }.
Coercion _ofe : cofe >-> ofe.

(* Inhabited COFE *)

(* Record defining an inhabited COFE *)
Record icofe := mkICOFE {
  icofe_car : cofe;  (* The underlying COFE *)
  icofe_inh : icofe_car  (* Proof that the COFE is inhabited *)
}.
Coercion icofe_car : icofe >-> cofe.
