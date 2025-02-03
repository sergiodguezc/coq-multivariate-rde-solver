From sgdt Require Import ecategory efunctor ofe later einstances.
Require Import ssreflect.

(* Later is an enriched endofunctor *)
Program Definition elater_fmap {A B : ofe} (f : A -n> B) : ▶  A -n> ▶  B :=
  {| ne_mor x := next (f (get_car x)) |}.
Next Obligation.
  intros n x y Hxy.
  destruct n ; [by left | right].
  replace (S n - 1) with n by lia.
  destruct x, y. simpl in *. destruct Hxy ; [lia | ].
  apply hom_ne. by replace n with (n - 0) by lia.
Qed.

Lemma olaterF_mixin : eFunctMixin eiCOFE eiCOFE icofe_later (@elater_fmap).
Proof.
  unshelve econstructor.
  - intros A B n f g Hfg [z]. 
    destruct n ; [by left | right ; simpl].
    replace (n - 0) with n by lia.
    apply ofe_mono with (n := S n) ; eauto.
  - intros A. apply ne_eq. intros x. simpl. by destruct x.
  - intros A B C f g. apply ne_eq. intros x. simpl. by destruct x.
Qed.

Program Definition elaterF : eFunctor eiCOFE eiCOFE := {|
  efobj := icofe_later;
  efmap_mor := @elater_fmap;
  efunct_mixin := olaterF_mixin
|}.

