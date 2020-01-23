-- Identity law for lift and lower
prop_coyoIdentity :: (Eq (f a), Functor f) => f a -> Bool
prop_coyoIdentity x = lowerCoyoneda (liftCoyoneda x) == x

-- Round trip law for Yoneda
prop_yonedaIdentity :: (Eq (f a), Functor f) => Yoneda f a -> Bool
prop_yonedaIdentity y = runYoneda y id == lowerYoneda (liftYoneda (runYoneda y id))

-- Helper (not strictly needed)
liftYoneda :: f a -> Yoneda f a
liftYoneda fa = Yoneda (\k -> fmap k fa)

lowerYoneda :: Functor f => Yoneda f a -> f a
lowerYoneda (Yoneda k) = k id
