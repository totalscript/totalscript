module Gen.Errors

import public Control.Catchable
import public Control.Monad.Identity
import public Control.Monad.Trans
import public Control.Monad.Reader
import public Control.Monad.State

CatchType : Type -> (Type -> Type) -> Type -> Type
CatchType t m a = m a -> (t -> m a) -> m a

liftCatchReader : CatchType e m a -> CatchType e (ReaderT r m) a
liftCatchReader f m h = RD $ \r => f (runReaderT m r) (\e => runReaderT (h e) r)

liftCatchState : CatchType e m (a,s) -> CatchType e (StateT s m) a
liftCatchState f m h = ST $ \ s => runStateT m s `f` \ e => runStateT (h e) s

export
(Monad m, Catchable m e) => Catchable (ReaderT r m) e where
	throw = lift . throw
	catch = liftCatchReader catch

export
(Monad m, Catchable m e) => Catchable (StateT s m) e where
	throw = lift . throw
	catch = liftCatchState catch
