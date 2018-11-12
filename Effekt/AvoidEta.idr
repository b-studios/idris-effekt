module Effekt.AvoidEta

import Effekt.CpsUnstaged
import Effekt.CpsStaged
import Effekt.IteratedUnstaged

mutual
  public export
  data CTX : List Type -> Type -> Type -> Type where
    Static :   (Exp a -> STM rs b)   -> CTX rs a b
    Dynamic :  Exp (a -> Stm rs b)   -> CTX rs a b

  public export
  STM : List Type -> Type -> Type
  STM [] a = Exp a
  STM (r :: rs) a = CTX rs a r -> STM rs r

mutual
  export
  reify : STM rs a -> Exp (Stm rs a)
  reify {rs = []} m = m
  reify {rs = (q :: qs)} m =
    (Lam $ \ k =>  reify (m (Dynamic k)))

  export
  reflect : Exp (Stm rs a) -> STM rs a
  reflect {rs = []} m = m
  reflect {rs = (q :: qs)} m =
    \k => reflect (App (m)  ((reifyContext k)))

  export
  reifyContext : CTX rs a r -> Exp (a -> Stm rs r)
  reifyContext (Static k) = (Lam $ \ a =>  reify (k a))
  reifyContext (Dynamic k) = k

export
resume : CTX rs a r -> (Exp a -> STM rs r)
resume (Static k) = k
resume (Dynamic k) = \a => reflect (App (k)  (a))

export
pure : Exp a -> STM rs a
pure{  rs= []}         a = a
pure{  rs= r :: rs}  a = \k => resume k a

push : CTX (r :: rs) a b -> CTX rs b r -> CTX rs a r
push f k = Static (\a => resume f a k)

bind : STM rs a -> CTX rs a b -> STM rs b
bind{  rs= []}         m f = resume f m
bind{  rs= r :: rs}  m f = \k => m (push f k)

export
shift0 : (CTX rs a r -> STM rs r) -> STM (r :: rs) a
shift0 = id

export
runIn0 : STM (r :: rs) a -> CTX rs a r -> STM rs r
runIn0 = id

export
reset0 : STM (a :: rs) a -> STM rs a
reset0 m = runIn0 m (Static pure)

export
lift : STM rs a -> STM (r :: rs) a
lift = bind

export
(>>=) : STM rs a -> (Exp a -> STM rs b) -> STM rs b
m >>= f = bind m (Static f)

add : STM rs Int -> STM rs Int -> STM rs Int
add mx my = do
  x <- mx
  y <- my
  pure ((Add x y))

display : Exp String -> STM (IO () :: rs) ()
display {rs} s = shift0 (\c => do
  a <- resume c Uni
  pure {rs} ((Seq ((Dis s)) a)))

export
displayTwice : STM [] (IO ())
displayTwice = reset0 {rs=[]} (
  (>>=) {rs=[IO ()]} (display {rs=[]} (Str "hello ")) (\u =>
  (>>=) {rs=[IO ()]} (display {rs=[]} (Str "world")) (\o =>
  pure {rs=[IO ()]} Ski)))

export
ifthenelse : Exp Bool -> STM rs a -> STM rs a -> STM rs a
ifthenelse {rs} Tru t _ = t
ifthenelse {rs} Fls _ e = e
ifthenelse {rs=[]} b t e = Ite b t e
ifthenelse {rs=q::qs} b t e = \k => ifthenelse b (t k) (e k)

export
letrec : ((Exp a -> STM rs b) -> Exp a -> STM rs b) -> Exp a -> STM rs b
letrec body a = reflect (App (Rec (\f => \x =>
  reify (body (\y => reflect (App (f)  (y))) x)))  (a))

-- Iteration happens to be recursion.
export
loop : (Exp a -> STM (r :: rs) a) -> Exp a -> STM rs r
loop m = letrec (\k => \a => m a (Static k))

export
break : Exp r -> STM (r :: rs) a
break r = shift0 (\_ => pure r)

