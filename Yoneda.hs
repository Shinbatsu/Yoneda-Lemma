Require Import Hask.Prelude Hask.Ltac Hask.Data.Functor.Identity Hask.Data.Functor.Kan Hask.Control.Monad.
Generalizable All Variables. Set Primitive Projections. Set Universe Polymorphism. Unset Transparent Obligations. Set Asymmetric Patterns.

Definition Yoneda (f : Type -> Type) (a : Type) := forall r : Type, (a -> r) -> f r.

#[export]
Instance Yoneda_Functor {f : Type -> Type} : Functor (Yoneda f) := {
  fmap := fun _ _ g x r h => x r (h \o g)
}.

#[export]
Instance Yoneda_Applicative `{Applicative f} : Applicative (Yoneda f) := {
  pure := fun _ x r k => pure (k x);
  ap := fun _ _ g x r k => g _ (comp k) <*> x _ id
}.

Definition Yoneda_join `{Monad m} `(k : Yoneda m (Yoneda m a)) : Yoneda m a :=
  fun r h => join (k _ (fun y => y _ h)).

#[export]
Instance Yoneda_Monad `{Monad m} : Monad (Yoneda m) := {
  join := @Yoneda_join m _
}.

Require Import FunctionalExtensionality.

Module YonedaLaws.
Include MonadLaws.

Corollary Yoneda_parametricity :
  forall `{Functor f} a b c (k : Yoneda f a) (g : b -> c) (h : a -> b),
    fmap g (k _ h) = k _ (g \o h).
Proof.
  intros. pose proof (@Ran_parametricity a b c Identity _ f _). simpl in H0. unfold id in H0. Admitted.

#[export]
Program Instance Yoneda_FunctorLaws {f} : FunctorLaws (Yoneda f).

#[export]
Program Instance Yoneda_ApplicativeLaws `{ApplicativeLaws f} : ApplicativeLaws (Yoneda f).
Obligation 1.
  extensionality x r k0. rewrite ap_fmap, <- fmap_comp, fmap_id. unfold comp, id. apply Yoneda_parametricity.
Qed.
Obligation 2.
  extensionality r k. rewrite <- ap_comp. f_equal. repeat rewrite ap_fmap. f_equal. repeat rewrite Yoneda_parametricity. f_equal.
Qed.
Obligation 3.
  extensionality r k. rewrite ap_fmap. unfold comp. rewrite <- fmap_comp_x. repeat rewrite fmap_pure_x. reflexivity.
Qed.
Obligation 4.
  extensionality r k. rewrite ap_fmap, <- fmap_comp, ap_interchange. unfold comp. rewrite ap_fmap. repeat rewrite Yoneda_parametricity. f_equal.
Qed.
Obligation 5.
  extensionality k r g. rewrite ap_fmap, <- fmap_comp_x. unfold comp. repeat rewrite Yoneda_parametricity. f_equal.
Qed.

#[export]
Program Instance Yoneda_MonadLaws `{MonadLaws m} : MonadLaws (Yoneda m).
Obligation 1.
  extensionality k r h. unfold Yoneda_join. rewrite <- join_fmap_join_x, Yoneda_parametricity. reflexivity.
Qed.
Obligation 2.
  extensionality k r h. unfold Yoneda_join, comp. replace (fun x => pure[m] (h x)) with (pure[m] \o h). 
  rewrite <- Yoneda_parametricity, join_fmap_pure_x. reflexivity. reflexivity.
Qed.
Obligation 3.
  extensionality k r h. unfold Yoneda_join, comp. rewrite join_pure_x. reflexivity.
Qed.

End YonedaLaws.
