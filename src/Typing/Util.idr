module Typing.Util

import Typing.Common

-- 8YYYY 0   0  o8o  0    0   0  o8o  YY8YY 8YYYY
-- 8___  0   0 8   8 0    0   0 8   8   0   8___
-- 8"""  "o o" 8YYY8 0    0   0 8YYY8   0   8"""
-- 8oooo  "8"  0   0 8ooo "ooo" 0   0   0   8oooo

export
evaluate : Term -> TypeChecker Term
evaluate m = do
	defs <- definitions {s=TCState}
	let scope = fromList $ [ (x,m') | (x,m',_) <- toList defs ]
	let evalResult = runReaderT (eval m) scope
	case evalResult of
		Left e   => throw e
		Right m' => pure m'

-- Y8Y 8o  0 oYYYo YY8YY  o8o  8o  0 YY8YY Y8Y  o8o  YY8YY 8YYYY 8_   _8 8YYYY YY8YY  o8o  oYYYo
--  0  8Yo 8 %___    0   8   8 8Yo 8   0    0  8   8   0   8___  8"o_o"8 8___    0   8   8 %___
--  0  8 Yo8 `"""p   0   8YYY8 8 Yo8   0    0  8YYY8   0   8"""  0  8  0 8"""    0   8YYY8 `"""p
-- o8o 0   8 YoooY   0   0   0 0   8   0   o8o 0   0   0   8oooo 0     0 8oooo   0   0   0 YoooY

export
instantiateMetas : Substitution -> Term -> Term

export
instantiateClause : Substitution -> Clause -> Clause

export
instantiateMetasCaseMotive : Substitution -> CaseMotive -> CaseMotive

export
instantiateMetasPat : Substitution -> Pattern -> Pattern
instantiateMetas _ (Var x) = Var x
instantiateMetas subs (Meta i) = case lookup i subs of
      Nothing => Meta i
      Just t  => instantiateMetas subs t
instantiateMetas _ (DottedVar m x) = DottedVar m x
instantiateMetas _ (AbsoluteDottedVar m x) = AbsoluteDottedVar m x
instantiateMetas subs (Ann m t) = Ann (instantiateMetas subs m) (instantiateMetas subs t)
instantiateMetas _ Star = Star
instantiateMetas subs (Pi plic a sc) = Pi plic
	(instantiateMetas subs a)
	(instantiateMetas subs <$> sc)
instantiateMetas subs (Lam plic sc) = Lam plic (instantiateMetas subs <$> sc)
instantiateMetas subs (App plic f a) = App plic
	(instantiateMetas subs f)
	(instantiateMetas subs a)
instantiateMetas subs (Con c as) = Con c (map (\(plic, a) => (plic, instantiateMetas subs a)) as)
instantiateMetas subs (Case as mot cs) = Case (map (instantiateMetas subs) as)
	(instantiateMetasCaseMotive subs mot)
	(map (instantiateClause subs) cs)

instantiateMetas subs (RecordType tele) = RecordType (instantiateMetasTelescope tele)
where
	instantiateMetasTelescope TelescopeNil = TelescopeNil
	instantiateMetasTelescope (TelescopeCons t sc) = TelescopeCons
		(instantiateMetas subs t)
		(instantiateMetasTelescope <$> sc)
instantiateMetas subs (RecordCon fields) = RecordCon [ (x,instantiateMetas subs m) | (x,m) <- fields ]
instantiateMetas subs (Project m x) = Project (instantiateMetas subs m) x

instantiateClause subs (NewClause psc sc) = NewClause
	(map (instantiateMetasPat subs) <$> psc)
	(instantiateMetas subs <$> sc)

instantiateMetasCaseMotive subs (CaseMotiveNil a) = CaseMotiveNil (instantiateMetas subs a)
instantiateMetasCaseMotive subs (CaseMotiveCons a sc) = CaseMotiveCons
	(instantiateMetas subs a)
	(instantiateMetasCaseMotive subs <$> sc)

instantiateMetasPat _ (VarPat x) = VarPat x
instantiateMetasPat subs (ConPat c ps) = ConPat c (map (\(plic,p) => (plic,instantiateMetasPat subs p)) ps)
instantiateMetasPat subs (AssertionPat m) = AssertionPat (instantiateMetas subs m)
instantiateMetasPat _ MakeMeta = MakeMeta

-- 0   0 8o  0  o8o  0    Y8Y  o8o  oYYYo
-- 0   0 8Yo 8 8   8 0     0  8   8 %___
-- 0   0 8 Yo8 8YYY8 0     0  8YYY8 `"""p
-- "ooo" 0   8 0   0 8ooo o8o 0   0 YoooY

export
unalias : String \/ FullName -> TypeChecker FullName
unalias (Left n) = do
	als <- aliases
	case lookup (Left n) als of
		Nothing => throw $ "The symbol " ++ n ++ " is not an alias for any "
							++ "module-declared symbol."
		Just p  => pure p
unalias (Right (m,n)) = do
	als <- aliases
	case lookup (Right (m,n)) als of
		Nothing => throw $ "The symbol " ++ m ++ "." ++ n ++ " is not an alias for any "
							++ "module-declared symbol."
		Just p  => pure p

-- YY8YY 0   0 8YYYo 8YYYY      Y8Y 8o  0
--   0   "o o" 8___P 8___  ____  0  8Yo 8
--   0     0   8"""  8"""  """"  0  8 Yo8
--   0     0   0     8oooo      o8o 0   8

export
typeInSignature : Constructor -> TypeChecker (Constructor >< ConSig Term)
typeInSignature (BareCon n0) = do
	consigs <- signature {s=TCState}
	(m,n) <- unalias (Left n0)
	case lookup (m,n) consigs of
		Nothing => throw $ "Unknown constructor: " ++ show (DottedCon m n)
		Just t  => pure (AbsoluteDottedCon m n, t)
typeInSignature (DottedCon m n) = do
	consigs <- signature {s=TCState}
	(m',n') <- unalias (Right (m,n))
	case lookup (m',n') consigs of
		Nothing => throw $ "Unknown constructor: " ++ show (DottedCon m' n')
		Just t  => pure (AbsoluteDottedCon m' n', t)
typeInSignature (AbsoluteDottedCon m n) = do
	consigs <- signature {s=TCState}
	case SortedMap.lookup (m,n) consigs of
		Nothing => throw $ "Unknown constructor: " ++ show (AbsoluteDottedCon m n)
		Just t  => pure (AbsoluteDottedCon m n, t)

export
absoluteDottedTypeInDefinitions : String -> String -> TypeChecker (FullName >< Term)
absoluteDottedTypeInDefinitions m x = do
	defs <- definitions
	case find (\(mx,_,_) => mx == (m,x)) (toList defs) of
		Nothing      => throw $ "Unknown constant/defined term: " ++ m ++ "." ++ x
		Just (_,_,t) => pure ((m, x), t)

export
dottedTypeInDefinitions : String -> String -> TypeChecker (FullName >< Term)
dottedTypeInDefinitions m x = do
	(m',x') <- unalias (Right (m,x))
	absoluteDottedTypeInDefinitions m' x'

export
typeInDefinitions : String -> TypeChecker (FullName >< Term)
typeInDefinitions x0 = do
	(m,x) <- unalias (Left x0)
	defs <- definitions
	case find (\(mx,_,_) => mx == (m,x)) (toList defs) of
		Nothing      => throw $ "Unknown constant/defined term: " ++ m ++ "." ++ x
		Just (_,_,t) => pure ((m,x),t)

export
typeInContext : Int -> TypeChecker Term
typeInContext i = do
	ctx <- context
	case find (\(j,_,_) => j == i) ctx of
		Nothing      => throw "Unbound automatically generated variable."
		Just (_,_,t) => pure t
