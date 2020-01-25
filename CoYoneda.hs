{-# LANGUAGE GADTs #-}

-- Coyoneda encoding
data Coyoneda f a where
  Coyoneda :: (b -> a) -> f b -> Coyoneda f a

-- Functor instance
instance Functor (Coyoneda f) where
  fmap f (Coyoneda g fb) = Coyoneda (f . g) fb

-- Lift a value into Coyoneda
liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = Coyoneda id

-- Lower a Coyoneda value into the base functor
lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda g fb) = fmap g fb
