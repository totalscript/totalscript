module TermLang.TCUtil

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

import TermLang.Syntax
import TermLang.Env
import TermLang.Eval


||| De Bruijn levels
export
genName : Int -> String
genName n = "$" ++ show n

export
mkVar : Int -> Exp
mkVar k = EVar (genName k)

||| add term into context
addC : Context -> Pair Telescope Env -> List (Pair String Val) -> TC Context
addC gam _ [] = pure $ gam
addC gam ((y, a) :: as, nu) ((x, u) :: xus) = do
	a' <- eval a nu
	addC ((x, a') :: gam) (as, EvPair nu (y, u)) xus

-- Extract the type of a label as a closure
export
getLblType : String -> Exp -> TC (Pair Telescope Env)
getLblType c (EComp (ESum _ cas) r) with (lookup c cas)
	| Just as = pure (as, r)
	| Nothing = raise $ "Cannot get label type of " ++ c
getLblType c u = raise $ "Unexpected data type"

export
addTypeVal : Pair String Val -> TEnv -> TC TEnv
addTypeVal (x, v) (NewTEnv k rho gam) = pure $ NewTEnv (k+1) (EvPair rho (x, mkVar k)) ((x, v)::gam)

export
addType : Pair String Exp -> TEnv -> TC TEnv
addType (x, a) tenv = do
	a' <- eval a (TEnv.env tenv)
	addTypeVal (x, a') tenv

export
addBranch : List (Pair String Val) -> Pair Telescope Env -> TEnv -> TC TEnv
addBranch nvs (Telescope, env) (NewTEnv k rho gam) =
	pure $ NewTEnv (k + (cast $ length nvs)) (upds rho nvs) !(addC gam (Telescope, env) nvs)

export
addDef : Def -> TEnv -> TC TEnv
addDef (ts, es) (NewTEnv k rho gam) = do
	let rho' = EvDef rho (ts, es)
	es' <- evals es rho'
	gam' <- addC gam (ts, rho) es'
	pure $ NewTEnv k rho' gam'

export
addTele : Telescope -> TEnv -> TC TEnv
addTele [] lenv = pure $ lenv
addTele (x :: xs) lenv = do
	lenv' <- addType x lenv
	addTele xs lenv'

export
getIndex : TC Int
getIndex = pure $ TEnv.index !get

export
getFresh : TC Exp
getFresh = pure $ mkVar !getIndex

export
getEnv : TC Env
getEnv = pure $ TEnv.env !get

export
getContext : TC Context
getContext = pure $ TEnv.ctxt !get

||| Util functions
export
checkLocally : (TEnv -> TC TEnv) -> TC a -> TC a
checkLocally fme m = do
	e1 <- get
	e <- fme e1
	put e
	r <- m
	put e1
	pure r

export
checkMap : List a -> (a -> Eff b e) -> Eff (List b) e
checkMap [] f = pure []
checkMap (x :: xs) f = do
	x1 <- f x
	xs1 <- checkMap xs f
	pure (x1 :: xs1)

export
checkSeq : List a -> (a -> Eff () e) -> Eff () e
checkSeq xs f = do
	checkMap xs f
	pure ()
