module TermLang.Terms

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

import TermLang.Syntax
import TermLang.Env
import TermLang.Eval

import TermLang.TCUtil
import TermLang.Unify

mutual
	checkDef : Def -> TC ()
	checkDef (xas, xes) = do
		putStrLn $ "Checking definition of " ++ show (map fst xes)
		checkTele xas
		rho <- getEnv
		result <- checkLocally (addTele xas) $ checks rho xas (map snd xes)
		putStrLn $ "Defined" ++ show xas
		pure result

	checkTele : Telescope -> TC ()
	checkTele [] = pure ()
	checkTele ((x, a) :: xas) = do
		checkType a
		checkLocally (addType (x, a)) $ checkTele xas

	||| check whether expression E is in type T
	check : Val -> Exp -> TC ()
	check t e = do
		putStrLn $ "Checking " ++ show e ++ " with " ++ show t
		check1 t e
	where
		check1 : Val -> Exp -> TC ()
		check1 a (ECon c es) = do
			(bs, nu) <- getLblType c a
			checks nu bs es
		check1 u@(EType n) (EPi a (ELam x b)) = do
			check u a
			checkLocally (addType (x, a)) $ check u b
		check1 u@(EType n) (ESum _ bs) = do
			checkSeq bs $ \(_, as) => checkTele as
		check1 t@(EPi (EComp (ESum _ cas) nu) f) e@(ECase _ ces) = do
			if (map fst ces == map fst cas)
				then checkSeq (zip ces cas) $ \(brc, (_, as)) => checkBranch (as, nu) f brc
				else raise $ "case branches " ++ show e ++ " does not match the data type " ++ show t
		check1 (EPi a f) (ELam x t) = do
			var <- getFresh
			checkLocally (addTypeVal (x, a)) $ check !(app f var) t
		check1 a (EDef d e) = do
			checkDef d
			checkLocally (addDef d) $ check a e
		check1 a (EUndef _) = pure ()
		check1 a x = do
			b <- infer x
			unify a b

	||| checkType : T is a valid type in universe N
	||| returns : universe number
	checkType : Exp -> TC Nat
	checkType (EType n) = pure n
	checkType (EPi a (ELam x b)) = do
		p <- checkType a
		q <- checkLocally (addType (x, a)) $ checkType b
		pure $ max p q
	checkType t = do
		u' <- infer t
		case u' of
			EType n => pure n
			otherwise => raise $ "Type of " ++ show t ++ " is not a universe."

	checkBranch : Pair Telescope Env -> Val -> Branch -> TC ()
	checkBranch (xas, nu) f (c, (xs, e)) = do
		k <- getIndex
		let l = cast (length xas)
		let us = map mkVar [k .. k+l-1]
		checkLocally (addBranch (zip xs us) (xas, nu)) $ check !(app f (ECon c us)) e

	||| infer : infer a type of an exp
	infer : Exp -> TC Val
	infer (EType n) = pure $ EType (n + 1)
	infer (EVar n) = do
		gam <- getContext
		case (lookup n gam) of
			Just v => pure v
			Nothing => raise $ show n ++ " is not declared."
	infer (EApp t u) = do
		c <- infer t
		case c of
			EPi a f => do
				check a u
				rho <- getEnv
				pure !(app f !(eval u rho))
			_ => raise "Not a projection"
	infer (EDef d t) = do
		checkDef d
		checkLocally (addDef d) $ infer t
	infer e = raise $ "Cannot infer type of " ++ show e

	||| checks : check a list
	checks : Env -> Telescope -> List Exp -> TC ()
	checks _ _ [] = pure ()
	checks nu ((x, a)::xas) (e::es) = do
		a' <- eval a nu
		check a' e
		rho <- getEnv
		e' <- eval e rho
		checks (EvPair nu (x, e')) xas es
	checks _ _ _ = raise "CHECKS"



one : Exp
one = EDef ([("Nat", EType 0)], [("Nat", ESum (0, "Nat") [("Z", []), ("S", [("pred", EVar "Nat")])])])
	$ EDef ([("zero", EVar "Nat")], [("zero", ECon "Z" [])])
	$ EDef ([("one", EVar "Nat")], [("one", ECon "S" [ECon "Z" []])])
	$ EDef ([("id", EPi (EType 0) $ ELam "a" $ EPi (EVar "a") $ ELam "_" (EVar "a"))], [("id", ELam "a" $ ELam "x" $ EVar "x")])
	$ EApp (EApp (EVar "id") (EVar "Nat")) (EVar "one")

-- it should infer to a sum type