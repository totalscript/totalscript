module TermLang.Eval

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

import TermLang.Syntax
import TermLang.Env

export
upds : Env -> List (Pair String Val) -> Env
upds = foldl EvPair

mutual
	export
	app : Val -> Val -> TC Val
	app (EComp (ELam x b) s) u = eval b (EvPair s (x, u))
	app (EComp (ECase _ ces) r) (ECon c us) with (lookup c ces)
		| Just (xs, e) = eval e (upds r (zip xs us))
		| Nothing      = raise "Cannot apply"
	app f u            = pure $ EApp f u

	export
	eval : Exp -> Env -> TC Val
	eval (EDef d e)   s = eval e (EvDef s d)
	eval (EApp t1 t2) s = do
		t1' <- eval t1 s
		t2' <- eval t2 s
		app t1' t2'
	eval (EPi a b)    s = do
		a' <- eval a s
		b' <- eval b s
		pure $ EPi a' b'
	eval (ECon c ts) s = do
		ts' <- evalList ts s
		pure $ ECon c ts'
	--pure $ ECon c (map (`eval` s) ts)
	eval (EVar k)     s = getE k s
	eval (EType n)    _ = pure $ (EType n)
	eval t            s = pure $ EComp t s

	export
	evalList : List Exp -> Env -> TC (List Val)
	evalList [] r = pure $ []
	evalList (e :: es) r = do
		e' <- eval e r
		es' <- evalList es r
		pure $ (e' :: es')

	export
	evals : List (Pair String Exp) -> Env -> TC (List (Pair String Exp))
	evals [] r = pure $ []
	evals ((x, e) :: es) r = do
		result <- eval e r
		rear <- evals es r
		pure $ (x, result) :: rear

	-- get variable
	export
	getE : String -> Env -> TC Exp
	getE x (EvPair s (y, u)) with (x == y)
		| True  = pure u
		| False = getE x s
	getE x r@(EvDef r1 d) = do
		ds' <- evals (snd d) r
		getE x $ upds r1 ds'
	getE x r = raise $ "Not found variable " ++ x