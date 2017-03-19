module TermLang.Unify

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

import TermLang.Syntax
import TermLang.Env
import TermLang.Eval

import TermLang.TCUtil

-- unification -- we use simple unification for now
infixl 5 =?=
(=?=) : Exp -> Exp -> TC ()
s1 =?= s2 = if(s1 == s2)
	then pure ()
	else raise $ "Cannot commute " ++ show s1 ++ " with " ++ show s2

mutual
	-- Reification of a value to an expression
	reifyExp : Int -> Val -> TC Exp
	reifyExp _ EType = pure EType
	reifyExp k (EComp (ELam x t) r) = do
		t' <- eval t (EvPair r (x, mkVar k))
		r' <- reifyExp (k + 1) t'
		pure $ ELam (genName k) r'
	reifyExp k (EVar l) = pure $ EVar l
	reifyExp k (EApp u v)  = pure $ EApp !(reifyExp k u) !(reifyExp k v)
	reifyExp k (EPi  u v)  = pure $ EPi  !(reifyExp k u) !(reifyExp k v)
	reifyExp k (ECon n ts) = pure $ ECon n !(checkMap ts (reifyExp k))

	reifyExp k (EComp (ECase prim _) r) = pure $ EPrim prim !(reifyEnv k r)
	reifyExp k (EComp (ESum prim _) r) = pure $ EPrim prim !(reifyEnv k r)
	reifyExp k (EComp (EUndef prim) r) = pure $ EPrim prim !(reifyEnv k r)

	reifyEnv : Int -> Env -> TC (List Exp)
	reifyEnv _ EvEmpty = pure []
	reifyEnv k (EvPair r (_, u)) = do
		u' <- reifyExp k u
		r' <- reifyEnv k r
		pure $ r' ++ [u']
	reifyEnv k (EvDef r ts) = reifyEnv k r

export
unify : Val -> Val -> TC ()
unify a b = do
	k <- getIndex
	r1 <- reifyExp k a
	r2 <- reifyExp k b
	r1 =?= r2