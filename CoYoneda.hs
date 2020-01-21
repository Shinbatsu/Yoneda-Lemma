Inductive Coyoneda (f : Type -> Type) (a : Type) :=
  COYO : forall x, (x -> a) -> f x -> Coyoneda f a.

Arguments COYO {f a x} _ _.

Definition liftCoyoneda {f} {a} : f a -> Coyoneda f a := COYO id.

Definition lowerCoyoneda `{Functor f} {a} (c : Coyoneda f a) : f a :=
  match c with COYO _ g h => fmap g h end.

#[export]
Instance Coyoneda_Functor (f : Type -> Type) : Functor (Coyoneda f) := {
  fmap := fun _ _ f x => match x with COYO _ g h => COYO (f \o g) h end
}.

Module CoyonedaLaws.
Include FunctorLaws.

#[export]
Program Instance Coyoneda_FunctorLaws (f : Type -> Type) : FunctorLaws (Coyoneda f).
Obligation 1. extensionality x. destruct x. reflexivity. Qed.
Obligation 2. extensionality x. destruct x. reflexivity. Qed.

Theorem coyo_to `{FunctorLaws f} : forall a (x : f a),
  lowerCoyoneda (liftCoyoneda x) = x.
Proof.
  intros. unfold lowerCoyoneda, liftCoyoneda. rewrite fmap_id. reflexivity.
Qed.

Theorem coyo_lower_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o lowerCoyoneda = lowerCoyoneda \o fmap g.
Proof.
  intros. extensionality x. destruct x. simpl. rewrite fmap_comp_x. reflexivity.
Qed.

Axiom coyo_parametricity : forall `{FunctorLaws f} a b (g : a -> b),
  COYO g = COYO id \o fmap g.

Theorem coyo_lift_naturality `{FunctorLaws f} : forall a b (g : a -> b),
  fmap g \o liftCoyoneda = liftCoyoneda \o fmap g.
Proof.
  intros. unfold liftCoyoneda. extensionality x. simpl. replace (g \o id) with g by reflexivity. rewrite coyo_parametricity. reflexivity.
Qed.

Theorem coyo_from `{FunctorLaws f} : forall a (x : Coyoneda f a),
  liftCoyoneda (lowerCoyoneda x) = x.
Proof.
  intros. destruct x. unfold lowerCoyoneda. replace (liftCoyoneda (fmap g h)) with ((liftCoyoneda \o fmap g) h). 
  rewrite <- coyo_lift_naturality. reflexivity. reflexivity.
Qed.

End CoyonedaLaws.
