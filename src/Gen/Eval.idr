module Gen.Eval

import public Control.Monad.Identity
import public Control.Monad.Reader

-- 8YYYY 0   0  o8o  0    0   0  o8o  YY8YY _YYY_ 8YYYo
-- 8___  0   0 8   8 0    0   0 8   8   0   0   0 8___P
-- 8"""  "o o" 8YYY8 0    0   0 8YYY8   0   0   0 8""Yo
-- 8oooo  "8"  0   0 8ooo "ooo" 0   0   0   "ooo" 0   0

public export
Evaluator : Type -> Type -> Type
Evaluator e = ReaderT e (Either String)

public export
environment : Evaluator e e
environment = ask

public export
interface Eval e a where
	eval : a -> Evaluator e a

export
unless : Applicative f => Bool -> Lazy (f ()) -> f ()
unless False f = Force f
unless True f = pure ()

export
replicateM        : (Applicative m) => Nat -> m a -> m (List a)
replicateM cnt0 f = loop cnt0
where
	loop : Nat -> m (List a)
	loop Z     = pure []
	loop (S n) = liftA2 (::) f (loop n)

export
zipWithM          : (Applicative m) => (a -> b -> m c) -> List a -> List b -> m (List c)
zipWithM f xs ys  =  sequence (zipWith f xs ys)

export
groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy _  [] = []
groupBy eq (x::xs) = do
	let (ys, zs) = span (eq x) xs
	(x::ys) :: groupBy eq zs
