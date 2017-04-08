module Gen.TypeChecker

import Control.Monad.Identity
import Control.Monad.State

public export
interface TypeCheckerState s sig defs ctx | s where
	typeCheckerSig : s -> sig
	putTypeCheckerSig : s -> sig -> s
	typeCheckerDefs : s -> defs
	putTypeCheckerDefs : s -> defs -> s
	addTypeCheckerDefs : s -> defs -> s
	typeCheckerCtx : s -> ctx
	putTypeCheckerCtx : s -> ctx -> s
	addTypeCheckerCtx : s -> ctx -> s
	typeCheckerNextName : s -> Int
	putTypeCheckerNextName : s -> Int -> s

public export
interface (TypeCheckerState s sig defs ctx, Monad m, MonadState s m) => TCMonad (m : Type -> Type) s sig defs ctx | m
where {}

public export
signature : TCMonad m s sig defs ctx => m (sig)
signature {s} = map (typeCheckerSig {s}) get

public export
putSignature : TCMonad m s sig defs ctx => sig -> m ()
putSignature {s} sig = do
	ss <- get
	put (putTypeCheckerSig {s} ss sig)

public export
definitions : TCMonad m s sig defs ctx => m (defs)
definitions {s} = map (typeCheckerDefs {s}) get

public export
putDefinitions : TCMonad m s sig defs ctx => defs -> m ()
putDefinitions {s} defs = do
	ts <- get
	put (putTypeCheckerDefs {s} ts defs)

public export
extendDefinitions : TCMonad m s sig defs ctx => defs -> m a -> m a
extendDefinitions {s} edefs tc = do
	ts <- get
	put (addTypeCheckerDefs {s} ts edefs)
	x <- tc
	putDefinitions {s} (typeCheckerDefs ts)
	pure x

public export
context : TCMonad m s sig defs ctx => m (ctx)
context {s} = map (typeCheckerCtx {s}) get

public export
putContext : TCMonad m s sig defs ctx => ctx -> m ()
putContext {s} ctx = do
	ts <- get
	put (putTypeCheckerCtx {s} ts ctx)

public export
extendContext : TCMonad m s sig defs ctx => ctx -> m a -> m a
extendContext {s} ectx tc = do
	ts <- get
	put (addTypeCheckerCtx {s} ts ectx)
	x <- tc
	putContext {s} (typeCheckerCtx ts)
	pure x

public export
newName : TCMonad m s sig defs ctx => m Int
newName {s} = do
	ts <- get
	let n = typeCheckerNextName {s} ts
	put (putTypeCheckerNextName ts (n+1))
	pure $ n



public export
interface TypeCheckerMetas s subs | s where
	typeCheckerNextMeta : s -> Int
	putTypeCheckerNextMeta : s -> Int -> s
	typeCheckerSubs : s -> subs
	putTypeCheckerSubs : s -> subs -> s

public export
interface (TCMonad m s sig defs ctx, TypeCheckerMetas s subs) => TCPolyMonad (m : Type -> Type) s sig defs ctx subs | m
where {}

public export
newMetaVar : TCPolyMonad m s sig defs ctx subs => m Int
newMetaVar {s} = do
	ts <- get
	let n = typeCheckerNextMeta {s} ts
	put (putTypeCheckerNextMeta ts (n+1))
	pure n

public export
substitution : TCPolyMonad m s sig defs ctx subs => m subs
substitution {s} = map (typeCheckerSubs {s}) get

public export
putSubstitution : TCPolyMonad m s sig defs ctx subs => subs -> m ()
putSubstitution {s} subs = do
	ts <- get
	put (putTypeCheckerSubs {s} ts subs)
