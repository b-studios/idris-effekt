module Effekt.CpsUnstaged

public export
Cps : Type -> Type -> Type
Cps r a = (a -> r) -> r

shift0 : ((a -> r) -> r) -> Cps r a
shift0 = id

runIn0 : Cps r a -> (a -> r) -> r
runIn0 = id

reset0 : Cps r r -> r
reset0 m = runIn0 m id

pure : a -> Cps r a
pure a = \k => k a

push : (a -> Cps r b) -> (b -> r) -> (a -> r)
push f k = \a => f a k

bind : Cps r a -> (a -> Cps r b) -> Cps r b
bind m f = \k => m (push f k)

(>>=) : Cps r a -> (a -> Cps r b) -> Cps r b
m >>= f = bind m f

example : Int
example = 1 + reset0 (do
  x <- shift0 (\k => k (k 100))
  pure (10 + x))
