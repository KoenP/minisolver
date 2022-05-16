{-# language TypeFamilies #-}
{-# language RankNTypes #-}

main = undefined

type family F a
type family G a

type instance F [Int] = Int
type instance G [a]   = Bool

g :: forall b. b -> G b
g = undefined

asdf :: forall a. (a ~ [F a]) => a -> Bool
asdf x = g x
