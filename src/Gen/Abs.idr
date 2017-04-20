module Gen.Abs

import Gen.Env
import Data.SortedMap
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Reader

public export
Abstracted : Type -> Type -> Type -> Type
Abstracted i e a = Reader (Environment i e) a

public export
interface Ord i => Abstract i e a where
	abstr : a -> Abstracted i e a

export
implementation Abstract i e a => Abstract i e (List a) where
	abstr xs = for xs abstr

export
abstractOver : Abstract i e a => List i -> a -> List e -> a
abstractOver [] m _  = m
abstractOver xs m vs = runIdentity $ runReaderT (abstr m) (fromList $ zip xs vs)
