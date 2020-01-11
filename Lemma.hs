type Hom a = (->) a
type Nat f g = forall x. f x -> g x

to :: Functor f => Nat (Hom a) f -> f a
to = ($ id)

from :: Functor f => f a -> Nat (Hom a) f
from = \fa f -> fmap f fa
