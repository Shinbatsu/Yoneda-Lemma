{-# LANGUAGE RankNTypes #-}

-- Yoneda encoding
newtype Yoneda f a = Yoneda { runYoneda :: forall r. (a -> r) -> f r }

-- Functor instance
instance Functor (Yoneda f) where
  fmap f (Yoneda k) = Yoneda (\g -> k (g . f))

-- Applicative instance
instance Applicative f => Applicative (Yoneda f) where
  pure x = Yoneda (\k -> pure (k x))
  Yoneda f <*> Yoneda x = Yoneda (\k -> f (k .) <*> x id)

-- Monad instance
instance Monad m => Monad (Yoneda m) where
  return = pure
  Yoneda k >>= f = Yoneda (\g -> k (\a -> runYoneda (f a) g))
