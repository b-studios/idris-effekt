module Effekt.IteratedUnstaged

import Effekt.CpsUnstaged

public export
Stm : List Type -> Type -> Type
Stm [] a = a
Stm (r :: rs) a = Cps (Stm rs r) a

pure : a -> Stm rs a
pure{  rs= []}         a = a
pure{  rs= r :: rs}  a = \k => k a

push : (a -> Stm (r :: rs) b) -> (b -> Stm rs r) -> (a -> Stm rs r)
push f k = \a => f a k

bind : Stm rs a -> (a -> Stm rs b) -> Stm rs b
bind{  rs= []}         m f = f m
bind{  rs= r :: rs}  m f = \k => m (push f k)

(>>=) : Stm rs a -> (a -> Stm rs b) -> Stm rs b
(>>=) = bind

lift : Stm rs a -> Stm (r :: rs) a
lift = bind

shift0 : ((a -> Stm rs r) -> Stm rs r) -> Stm (r :: rs) a
shift0 = id

runIn0 : Stm (r :: rs) a -> (a -> Stm rs r) -> Stm rs r
runIn0 = id

reset0 : Stm (a :: rs) a -> Stm rs a
reset0 m = runIn0 m pure

shift00 : ((a -> Stm rs r) -> Stm rs r) -> Stm (r :: rs) a
shift00 k = shift0 k

shift01 : ((a -> Stm rs r) -> Stm rs r) -> Stm (q :: r :: rs) a
shift01 {r} {rs} k = lift {rs = r::rs} (shift0 {r} {rs} k)

shift02 : ((a -> Stm rs r) -> Stm rs r) -> Stm (p :: q :: r :: rs) a
shift02 {q} {r} {rs} k = lift {rs = q::r::rs} (lift {rs = r::rs} (shift0 {r} {rs} k))

reset01 : Stm (a :: a :: rs) a -> Stm rs a
reset01 {a} {rs} m = reset0 (reset0 {rs=(a :: rs)} m)

shift : ((a -> Stm (r :: rs) r) -> Stm (r :: rs) r) -> Stm (r :: rs) a
shift {r} {rs} body = shift0 (\k => reset0 (body (\a => lift {r} {rs} (k a))))

emit : Int -> Stm (List Int :: rs) ()
emit {rs} a = shift0 {rs} (\c =>
  bind {rs} (c ()) (\as =>
  pure {rs} (the (Int -> List Int -> List Int) (::) a as)))

partition : Int -> List Int -> Stm [List Int, List Int] ()
partition a l = case l of
  [] => do
    pure {rs=[List Int,List Int]} ()
  (h :: t) => if (a < h)
    then (
      bind {rs=[List Int,List Int]} (emit {rs=[List Int]} h) (\u =>
      partition a t))
    else (
      bind {rs=[List Int,List Int]} (lift {rs=[List Int]} (emit {rs=[]} h)) (\u =>
      partition a t))
