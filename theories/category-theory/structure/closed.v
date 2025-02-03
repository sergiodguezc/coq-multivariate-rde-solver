From sgdt Require Import category functor isomorphism finite_products terminal type.
From Coq Require Import ssreflect.

(* STRUCTURE OF A CATEGORIES *)

(* Definition of a cartesian closed category (CCC) *)
Class CCC (Y : Category) `(FiniteProducts Y) := mkCCC
  { exp  : Y -> Y -> Y (* internal hom-set, representing B^A *)
     where "B ^ A" := (exp A B);

    exp_iso {A B C : Y} : (A × B ~> C) ≃[ TYPE ] (A ~> C^B);  (* Natural isomorphism between hom-sets *)

    curry {A B C : Y} : (A × B ~> C) -> (A ~> C ^ B) := to (@exp_iso A B C);  (* Currying operation *)
    uncurry {A B C : Y} : (A ~> C ^ B) -> (A × B ~> C) := from (@exp_iso A B C);  (* Uncurrying operation *)

    eval {A B : Y} : B^A × A ~> B := @uncurry _ _ _ id{Y};  (* Evaluation morphism *)

    exp_univ {A B C : Y} (f : A × B ~> C) :
      eval ∘ first_mor (curry f) = f  (* Universal property of exponentials *)
  }.

Arguments exp_iso {_ _ _ _} _.

Notation "B ^ A" := (@exp _ _ _ _ A B) 
  (at level 30, right associativity) : object_scope.

(* Definition of currying for morphisms from the terminal object *)
Definition curry_ter {Y : Category} `{CCC Y} {A B : Y} (f : A ~> B) :
  1 ~> B ^ A := curry (rw_iso_dom (iso_sym (prod_1_l A)) f).

(* Definition of uncurrying for morphisms to the terminal object *)
Definition uncurry_ter {Y : Category} `{CCC Y} {A B : Y} (f : 1 ~> B ^ A) : A ~> B
  := (rw_iso_dom (prod_1_l A) (uncurry f)).

(* Definition of a strong endofunctor in a CCC *)
Record StrongEndo (C : Category) `{CCC C} : Type :=
  { endo : Functor C C ;  (* The underlying endofunctor *)
    endoFxy {A B : C} : B ^ A ~{C}~> (endo B) ^ (endo A) ;  (* Action on exponentials *)
    strong {A B} (f : A ~{C}~> B) : endoFxy ∘ (curry_ter f) = curry_ter (fmap endo f)  (* Strength condition *)
  }.

Coercion endo : StrongEndo >-> Functor.
Arguments endoFxy {_ _ _ _}.
Arguments strong {_ _ _ _}.

(* Alternative definition of a strong endofunctor *)
Record isStrongEndo {C : Category} `{CCC C} (F : Functor C C) := {
  endoFxy' {A B : C} : B ^ A ~{C}~> (F B) ^ (F A) ;  (* Action on exponentials *)
  strong' {A B} (f : A ~{C}~> B) : endoFxy' ∘ (curry_ter f) = curry_ter (fmap F f)  (* Strength condition *)
}.
Arguments endoFxy' {_ _ _ _ _}. 
Arguments strong' {_ _ _ _ _}.

(* Relation between StrongEndo and isStrongEndo *)

(* Convert a StrongEndo to an isStrongEndo *)
Lemma to_isStrongEndo {C : Category} `{CCC C} (F : StrongEndo C) : isStrongEndo F.
Proof. refine {| endoFxy' := endoFxy F ; strong' := strong F |}. Defined.

(* Convert an isStrongEndo to a StrongEndo *)
Lemma to_StrongEndo {C : Category} `{CCC C} {F : Functor C C} (T : isStrongEndo F) : StrongEndo C.
Proof. refine {| endo := F ; endoFxy := endoFxy' T ; strong := strong' T |}. Defined.

Coercion to_StrongEndo : isStrongEndo >-> StrongEndo.

(* The composition of two strong endofunctors is a strong endofunctor. *)
Definition strong_comp_fxy {C : Category} `{CCC C} (F G : StrongEndo C) :
  forall (A B : C), (B ^ A) ~{C}~> ((compose_functor F G) B) ^ ((compose_functor F G) A)
  := fun A B => endoFxy F (G A) (G B) ∘ endoFxy G A B.

(* Prove that the composition of two strong endofunctors satisfies the strength condition *)
Lemma strong_comp {C : Category} `{CCC C} (F G : StrongEndo C) :
  isStrongEndo (compose_functor F G).
Proof.
  refine {| endoFxy' := strong_comp_fxy F G |}.
  unfold strong_comp_fxy. intros A B f.
  destruct F as [F Fxy Fstr], G as [G Gxy Gstr] ; simpl in *.
  rewrite <- comp_assoc, <- Fstr, Gstr. reflexivity.  (* Prove the strength condition *)
Defined.

(* Lemma stating that uncurrying after currying yields the original morphism *)
Lemma uncurry_curry {Y : Category} `{CCC Y} {A B C : Y} (f : A × B ~> C) :
  uncurry (curry f) = f.
Proof.
  unfold uncurry, curry. 
  assert (from (exp_iso A B C) (to (exp_iso A B C) f) =
  ((from (exp_iso A B C)) ∘[TYPE] (to (exp_iso A B C))) f) as -> by (by simplify_cat).
  by rewrite (from_to (exp_iso A B C)).  (* Use the isomorphism property *)
Qed.

(* Lemma stating that currying after uncurrying yields the original morphism *)
Lemma curry_uncurry {Y : Category} `{CCC Y} {A B C : Y} (f : A ~> C ^ B) :
  curry (uncurry f) = f.
Proof. 
  unfold uncurry, curry.
  assert (to (exp_iso A B C) (from (exp_iso A B C) f) = ((to (exp_iso A B C)) ∘[TYPE] (from (exp_iso A B C))) f) as -> by (by simplify_cat).
  by rewrite (to_from (exp_iso A B C)).  (* Use the isomorphism property *)
Qed.

(* Lemma stating that currying the evaluation morphism yields the identity *)
Lemma curry_eval {C : Category} `{CCC C} {A B : C} :
  curry eval = @id _ (B^A).
Proof.
  intros; unfold eval; simpl; simplify_cat.
  apply curry_uncurry.  (* Use the curry_uncurry lemma *)
Qed.

(* Lemma stating that currying is injective *)
Lemma curry_inj {Y : Category} `{CCC Y} {A B C : Y} (f g : A × B ~> C) :
  curry f = curry g -> f = g.
Proof.
  intros. by rewrite <- (uncurry_curry f), <- (uncurry_curry g), H2.  (* Use the uncurry_curry lemma *)
Qed.

(* Lemma stating that uncurrying is injective *)
Lemma uncurry_inj {Y : Category} `{CCC Y} {A B C : Y} (f g : A ~> C ^ B) :
  uncurry f = uncurry g -> f = g.
Proof.
  intros. by rewrite <- (curry_uncurry f), <- (curry_uncurry g), H2.  (* Use the curry_uncurry lemma *)
Qed.

(* Lemma relating evaluation, currying, and composition *)
Lemma eval_curry {Y : Category} `{CCC Y} {A B C D : Y}
   (f : B × C ~> D) (g : A ~> B) (h : A ~> C) :
  eval ∘ (<| (curry f ∘ g),  h |>) = f ∘ <| g, h |>.
Proof.
  intros.
  rewrite <- (exp_univ f) at 2.  (* Use the universal property of exponentials *)
  unfold first_mor, times_mor. simplify_cat.
  rewrite <- comp_assoc.
  rewrite fork_precompose.
  rewrite <- comp_assoc.
  rewrite p_fst_fork.
  rewrite p_snd_fork.
  reflexivity.
Defined.

(* Lemma stating that currying commutes with composition on the left *)
Lemma curry_comp_l {Y : Category} `{CCC Y} {A B C D : Y} (f : B × C ~> D) (g : A ~> B) :
  curry f ∘ g = curry (f ∘ first_mor g).
Proof.
  apply uncurry_inj.
  rewrite <- (exp_univ (uncurry (curry f ∘ g))).
  rewrite curry_uncurry.
  unfold first_mor, times_mor. simplify_cat.
  rewrite <- eval_curry.
  rewrite uncurry_curry.
  rewrite eval_curry.
  rewrite <- comp_assoc.
  rewrite eval_curry.
  reflexivity.
Defined.

(* Lemma stating that evaluation commutes with the first projection *)
Lemma eval_first {Y : Category} `{CCC Y} {A B C : Y} (f : A ~> C^B) :
  eval ∘ first_mor f = uncurry f.
Proof.
  rewrite <- (curry_uncurry f). 
  rewrite exp_univ. rewrite curry_uncurry. reflexivity.
Qed.

(* Lemma stating that currying commutes with composition *)
Lemma curry_comp {Y : Category} `{CCC Y} {A B C D : Y} (f : C ~> D) (g : A × B ~> C) :
  curry (f ∘ g) = curry (f ∘ eval) ∘ curry g.
Proof.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite eval_first.
  by rewrite uncurry_curry.
Qed.
