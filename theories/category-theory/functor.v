From sgdt Require Import category isomorphism type.
From Coq Require Import ssreflect FunctionalExtensionality PropExtensionality.

(* Definition of a functor *)

(*
   FunctMixin is a structure that encapsulates the axioms of a functor:
   - Y, Z: the source and target categories.
   - fobj: the object mapping function.
   - fmap: the morphism mapping function.
   The structure also includes the functor laws:
   - mixin_fmap_id: preservation of identity morphisms.
   - mixin_fmap_compose: preservation of composition.
*)
Structure FunctMixin (Y Z : Category) (fobj : Y -> Z)
  (fmap : forall {A B : Y}, A ~> B -> fobj A ~> fobj B) := mkFunctMixin
  { mixin_fmap_id : forall A, fmap (id[A]) = id[(fobj A)];
    mixin_fmap_compose : forall A B C (f : B ~> C) (g : A ~> B), fmap (compose f g) = compose (fmap f) (fmap g)
  }.

(*
   Functor is a record that represents a functor, including:
   - fobj: the object mapping function.
   - fmap: the morphism mapping function.
   - funct_mixin: the functor axioms encapsulated in FunctMixin.
*)
Record Functor (Y Z : Category) := mkFUNCT
  { fobj : Y -> Z;
    fmap {A B} : A ~> B -> (fobj A) ~> (fobj B);
    funct_mixin : FunctMixin Y Z fobj (@fmap)
  }.

(* Coercion to treat a functor as a function on objects *)
Coercion fobj : Functor >-> Funclass.

(* Arguments directive to control simplification of fmap *)
Arguments fmap {Y Z} F {A B} f : rename.

(* Notation for functors *)
Notation "F →  G" := (Functor F G) (at level 90) : category_scope.

(* Lift functor laws from the mixin *)

(* Lemma showing that a functor preserves identity morphisms *)
Lemma fmap_id {Y Z : Category} (F : Functor Y Z) {A} : fmap F (id[A]) = id[F A].
Proof. apply (mixin_fmap_id _ _ _ _ (funct_mixin _ _ F)).  Qed.

(* Lemma showing that a functor preserves composition of morphisms *)
Lemma fmap_compose {Y Z : Category} (F : Functor Y Z) {A B C} (f : B ~> C) (g : A ~> B) :
  fmap F (compose f g) = compose (fmap F f) (fmap F g).
Proof. apply (mixin_fmap_compose _ _ _ _ (funct_mixin _ _ F)). Qed.

(* Definition to coerce a functor's object mapping *)
Definition coerce_functor {Y Z : Category} {F G : Functor Y Z}
  (H : @fobj Y Z F  = @fobj Y Z G) {A B} (f : F A ~{Z}~> F B)
  : G A ~{Z}~> G B := eq_rect _ (fun F => F A ~{Z}~> F B) f _ H.

(* Lemma showing that coercion with an identity proof is the identity *)
Lemma coerce_functor_id {Y Z : Category} {F : Functor Y Z}
  (H : @fobj Y Z F  = @fobj Y Z F) {A B} (f : F A ~{Z}~> F B)
  : coerce_functor H f = f.
Proof.
 by assert (H = eq_refl (@fobj Y Z F)) as -> by (apply proof_irrelevance).
Qed.

(* Lemma showing equality of functors given equality of object mappings and morphism mappings *)
Lemma functor_eq {Y Z : Category} (F G : Functor Y Z) ( H1 : fobj Y Z F = fobj Y Z G)
  ( H2 : forall x y (f : hom Y x y), coerce_functor H1 (fmap F f) = fmap G f) : F = G.
Proof.
  destruct F as [F fmapF HF], G as [G fmapG HG].
  assert (F = G) as -> by apply H1.
  assert (fmapF = fmapG) as -> .
  { extensionality x; extensionality y; extensionality f.
    set (H := H2 x y f). simpl in *.
    rewrite <- H. symmetry. 
    by assert (H1 = eq_refl G) as -> by (by apply proof_irrelevance).
  }
  f_equal ; apply proof_irrelevance.
Qed.

(* Lemma showing that functors preserve isomorphisms *)
Lemma functor_preserve_iso {Y Z : Category} (F : Functor Y Z) {x y : Y} (H : x ≃ y) :
  F x ≃ F y.
Proof.
  eapply mkISO with (to := fmap F (to H)) (from := fmap F (from H)).
  - by rewrite <- fmap_compose, (from_to H), fmap_id.
  - by rewrite <- fmap_compose, (to_from H), fmap_id.
Qed. 

(* Create a HintDB for the functor laws *)
Create HintDb funct_db.
Hint Rewrite @fmap_id : funct_db.
Hint Rewrite @fmap_compose : funct_db.

(* A tactic to simplify using the HintDB *)
Ltac simplify_funct := simpl ; autorewrite with funct_db cat_db.

(* Identity functor *)

(* Lemma showing that the identity functor satisfies the functor laws *)
Lemma id_mixin {Y : Category} : FunctMixin Y Y (fun x : Y => x) (fun A B f => f).
Proof. eapply mkFunctMixin ; intros ; by simplify_funct. Qed.

(* Definition of the identity functor *)
Definition id_functor (X : Category) : Functor X X :=
  {| fobj := fun x => x ; fmap := fun A B f => f ; funct_mixin := id_mixin |}.

Notation ID := id_functor.

(* Composition of functors *)

(* Lemma showing that the composition of two functors satisfies the functor laws *)
Lemma compose_mixin {X Y Z : Category} (F : Functor Y Z) (G : Functor X Y) :
  FunctMixin X Z (fun x => F (G x)) (fun A B f => fmap F (fmap G f)).
Proof.
  eapply mkFunctMixin ; intros ; by simplify_funct.
Qed.

(* Definition of the composition of two functors *)
Definition compose_functor {X Y Z : Category} (F : Functor Y Z) (G : Functor X Y) : Functor X Z
  := {| fobj := fun x => F (G x) ; fmap := fun A B f => fmap F (fmap G f) ; funct_mixin := compose_mixin F G |}.

Notation "F ∘[FUNCT] G" := (compose_functor F G) (at level 40) : category_scope.

(* Times functor *)

(* Lemma showing that the product of two functors satisfies the functor laws *)
Lemma times_mixin {X Y Z W : Category} (F : Functor X Y) (G : Functor Z W) :
  FunctMixin (X × Z) (Y × W) (fun x : X × Z => (F (fst x), G (snd x))) (fun A B f => (fmap F (fst f), fmap G (snd f))).
Proof. eapply mkFunctMixin ; intros ; by simplify_funct. Qed.

(* Definition of the product of two functors *)
Definition times_functor {X Y Z W : Category} (F : Functor X Y) (G : Functor Z W) : Functor (X × Z) (Y × W)
  := {| fobj := (fun x : X × Z => (F (fst x), G (snd x)):(Y × W)) ; fmap := (fun A B f => (fmap F (fst f), fmap G (snd f))) ; funct_mixin := times_mixin F G |}.

(* Definition of an endofunctor (a functor from a category to itself) *)
Definition EndoFunctor (X : Category) : Type := Functor X X.

(* Bifunctor *)

(* Definition of a bifunctor (a functor from a product category to another category) *)
Definition BiFunctor (X Y Z : Category) : Type := Functor (X × Y) Z.

(* Definition of the bimap operation for bifunctors *)
Definition bimap {C D E : Category} {F : BiFunctor C D E} {x w : C} {y z : D}
           (f : x ~{C}~> w) (g : y ~{D}~> z) :
  F (x, y) ~{E}~> F (w, z) := @fmap (prod_cat C D) E F (x, y) (w, z) (f, g).

Notation "bimap[ F ]" := (@bimap _ _ _ F _ _ _ _)
  (at level 9, format "bimap[ F ]") : category_scope.

(* Corollary showing that bimap is equivalent to fmap for product morphisms *)
Corollary bimap_fmap {C D E : Category} {F : BiFunctor C D E} {x w : C} {y z : D}
      (f : x ~{C}~> w) (g : y ~{D}~> z) :
  @fmap (prod_cat C D) E F (x, y) (w, z) (prod_mor f g) = bimap f g.
Proof. reflexivity. Qed.

(* Lemma showing that bimap preserves identity morphisms *)
Lemma bimap_id {C D E : Category} {F : BiFunctor C D E} {A B} :
  bimap[ F ] (id[A]) (id[B]) = id{E}.
Proof. rewrite <- bimap_fmap. by simplify_funct. Qed.

(* Lemma showing that bimap preserves composition of morphisms *)
Lemma bimap_compose {X Y Z : Category} {F : BiFunctor X Y Z} {A B C D E G} (f : hom X B C) (g : hom X A B)  (h : hom Y E G) (t : hom Y D E) :
  bimap[ F ] (compose f g) (compose h t) = compose (bimap[ F ] f h) (bimap[ F ] g t).
Proof. unfold bimap; rewrite <- fmap_compose. reflexivity. Qed.

(* Partial application of a bifunctor *)

(* Lemma showing that partial application of a bifunctor to the second argument satisfies the functor laws *)
Lemma second_funct_mixin {X Y Z : Category} (F : BiFunctor X Y Z) (x : X) :
  FunctMixin Y Z (fun y => F (x, y)) (fun A B f => @fmap _ _ F (x, A) (x, B) (prod_mor id{X} f)).
Proof.
  eapply mkFunctMixin ; intros ; simplify_funct ; try reflexivity.
  rewrite <- fmap_compose. rewrite <-prod_mor_compose. by simplify_funct.
Qed.

(* Definition of the partial application of a bifunctor to the second argument *)
Definition second_funct {X Y Z : Category} (F : BiFunctor X Y Z) (x : X) : Functor Y Z
  := {| fobj := fun y => F (x, y) ; fmap := fun A B f => @fmap _ _ F (x, A) (x, B) (prod_mor id{X} f) ; funct_mixin := second_funct_mixin F x |}.

(* Lemma showing that partial application of a bifunctor to the first argument satisfies the functor laws *)
Lemma first_funct_mixin {X Y Z : Category} (F : BiFunctor X Y Z) (y : Y) :
  FunctMixin X Z (fun x => F (x, y)) (fun A B f => @fmap _ _ F (A, y) (B, y) (prod_mor f id{Y})).
Proof.
  eapply mkFunctMixin ; intros ; simplify_funct ; try reflexivity.
  rewrite <- fmap_compose. rewrite <-prod_mor_compose. by simplify_funct.
Qed.

(* Definition of the partial application of a bifunctor to the first argument *)
Definition first_funct {X Y Z : Category} (F : BiFunctor X Y Z) (y : Y) : Functor X Z := {|
  fobj := fun x => F (x, y) ;
  fmap := fun A B f => @fmap _ _ F (A, y) (B, y) (prod_mor f id{Y}) ;
  funct_mixin := first_funct_mixin F y
|}.

(* Mixed variance functor *)

(* Definition of a mixed variance functor (a bifunctor with the first argument contravariant) *)
Definition mvFunctor (Y Z : Category) : Type := BiFunctor Y^op Y Z.

(* Opposite functor *)

(* Lemma showing that the opposite functor satisfies the functor laws *)
Lemma op_funct_mix {Y Z : Category} (F : Functor Y Z) : FunctMixin Y^op Z^op F (fun A B f => fmap F f).
Proof.
  eapply mkFunctMixin ; intros ; simplify_funct ;  try reflexivity.
  rewrite !op_mor_eq. by simplify_funct.
Qed.

(* Definition of the opposite functor *)
Definition op_funct {Y Z : Category} (F : Functor Y Z) : Functor Y^op Z^op := {|
  fobj := fun x : obj[Y^op] => (F x : obj[Z^op]) ;
  fmap := fun A B f => fmap F f ;
  funct_mixin := op_funct_mix F
|}.

(* Swap functor *)

(* Lemma showing that the swap functor satisfies the functor laws *)
Lemma swap_funct_mixin {X Y Z : Category} (F : Functor (X × Y) Z) :
  FunctMixin (Y × X) Z (fun x => F (snd x, fst x)) (fun A B f => fmap F (prod_mor (snd f) (fst f))).
Proof.
  eapply mkFunctMixin ; intros ; simplify_funct ; try reflexivity.
  rewrite <- fmap_compose. rewrite <- !prod_mor_compose_2. by simplify_funct.
Qed.

(* Definition of the swap functor (swaps the arguments of a bifunctor) *)
Definition swap_funct {X Y Z : Category} (F : Functor (X × Y) Z) : Functor (Y × X) Z := {|
    fobj := fun x : Y × X => F (snd x, fst x) ;
    fmap := fun A B f => fmap F (prod_mor (snd f) (fst f)) ;
    funct_mixin := swap_funct_mixin F
|}.

(* Fork functor *)

(* Lemma showing that the fork functor satisfies the functor laws *)
Lemma fork_funct_mixin {X Y Z : Category} (F : Functor Z X) (G : Functor Z Y) :
  FunctMixin Z (X × Y) (fun z => (F z, G z)) (fun A B f => prod_mor (fmap F f) (fmap G f)).
Proof. eapply mkFunctMixin ; intros ; by simplify_funct. Qed.

(* Definition of the fork functor (combines two functors into a product functor) *)
Definition fork_funct {X Y Z : Category} (F : Functor Z X) (G : Functor Z Y) : Functor Z (X × Y) := {|
  fobj := fun z => (F z, G z) : X × Y ;
  fmap := fun A B f => prod_mor (fmap F f) (fmap G f) ;
  funct_mixin := fork_funct_mixin F G
|}.

Notation "<| F , G |>" := (fork_funct F G) (at level 40) : category_scope.

(* Drop one functor *)

(* Lemma showing that the drop one functor satisfies the functor laws *)
Lemma drop_one_funct_mixin {X Y : Category} (F : Functor (one_cat × X) Y) :
  FunctMixin X Y (fun x => F (tt, x)) (fun A B f => fmap F (prod_mor id{one_cat} f)).
Proof.
  eapply mkFunctMixin ; intros ; simplify_funct ; try reflexivity.
  rewrite <- fmap_compose. unfold prod_mor. rewrite <- prod_mor_compose_2. by simplify_funct.
Qed.

(* Definition of the drop one functor (drops the first argument of a bifunctor) *)
Definition drop_one_funct {X Y : Category} (F : Functor (one_cat × X) Y) : Functor X Y := {|
  fobj := fun x => F (tt, x) ;
  fmap := fun A B f => fmap F (prod_mor id{one_cat} f) ;
  funct_mixin := drop_one_funct_mixin F
|}.

(* Add one functor *)

(* Lemma showing that the add one functor satisfies the functor laws *)
Lemma add_one_funct_mixin {X Y : Category} (F : Functor X Y) :
  FunctMixin (one_cat × X) Y (fun x => F (snd x)) (fun A B f => fmap F (snd f)).
Proof. eapply mkFunctMixin ; intros ; by simplify_funct. Qed.

Definition add_one_funct {X Y : Category} (F : Functor X Y) : Functor (one_cat × X) Y := {|
  fobj := fun x : one_cat × X => F (snd x) ;
  fmap := fun A B f => fmap F (snd f) ;
  funct_mixin := add_one_funct_mixin F
|}.

