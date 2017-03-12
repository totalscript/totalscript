module Term0.Terms

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

mutual
	Label : Type
	Label = String
	
	-- Branch of the form: c x1 .. xn -> e
	Branch : Type
	Branch = Pair Label $ Pair (List String) Exp
	
	-- Telescope (x1 : A1) .. (xn : An)
	Telescope : Type
	Telescope = List $ Pair String Exp
	
	-- Labelled sum: c (x1 : A1) .. (xn : An)
	LblSum : Type
	LblSum = List $ Pair Label Telescope

	-- We, for now, do not care too much about the difference between expressions and values
	Val : Type
	Val = Exp

	-- Context gives type values to identifiers
	Context : Type
	Context = List $ Pair String Val

	-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
	Def : Type
	Def = Pair Telescope $ List $ Pair String Exp

	Prim : Type
	Prim = Pair Int String

	data Exp : Type where
		-- Closure
		EComp  : Exp -> Env -> Exp
		-- Application
		EApp   : Exp -> Exp -> Exp
		-- Pi type
		EPi    : Exp -> Exp -> Exp
		-- Abstraction
		ELam   : String -> Exp -> Exp
		-- LetRec
		EDef   : Def -> Exp -> Exp
		-- Variable
		EVar   : String -> Exp
		-- Universe
		EUniv  : Exp
		-- Construction
		ECon   : String -> List Exp -> Exp
		-- Case analysis
		ECase  : Prim -> List Branch -> Exp
		-- Sum type
		ESum   : Prim -> LblSum -> Exp
		-- Undefined
		EUndef : Prim -> Exp
		-- used for reification
		EPrim : Prim -> List Exp -> Exp
	
	data Env =
		EvEmpty
		| EvPair Env (Pair String Val)
		| EvDef Env Def

infixl 6 <//>
(<//>) : String -> String -> String
s <//> s1 = s ++ "\n" ++ s1

parens : String -> String
parens s = "(" ++ s ++ ")"

hcat : List String -> String
hcat [] = ""
hcat (x :: []) = x
hcat (x :: xs) = x ++ " " ++ hcat xs

vcat : List String -> String
vcat [] = ""
vcat (x :: []) = x
vcat (x :: xs) = x ++ "\n" ++ hcat xs

-- a show function
mutual
	showExps : List Exp -> String
	showExps = hcat . map showExp1

	showExp1 : Exp -> String
	showExp1 EUniv = "U"
	showExp1 (ECon c []) = c
	showExp1 (EVar x) = x
	showExp1 u@(ECase _ _) = showExp u
	showExp1 u@(ESum _ _) = showExp u
	showExp1 u@(EUndef _) = showExp u
	showExp1 u@(EPrim _ _) = showExp u
	showExp1 u@(EComp _ _) = showExp u
	showExp1 u = parens $ showExp u

	showEnv : Env -> String
	showEnv EvEmpty            = ""
	showEnv (EvPair env (x,u)) = parens $ showEnv1 env ++ showExp u
	showEnv (EvDef env xas)    = showEnv env

	showEnv1 : Env -> String
	showEnv1 EvEmpty            = ""
	showEnv1 (EvPair env (x,u)) = showEnv1 env ++ showExp u ++ ", "
	showEnv1 (EvDef env xas)    = showEnv env

	showExp : Exp -> String
	showExp e = case e of
		EApp e0 e1 => showExp e0 ++ " " ++ showExp1 e1
		EPi e0 e1 => "Pi" ++ showExps [e0,e1]
		ELam x e => "\\" ++ x ++ " -> " ++ showExp e
		EDef d e => showExp e ++ " where" <//> showDef d
		EVar x => x
		EUniv => "U"
		ECon c es => c ++ " " ++ showExps es
		ECase (n,str) _ => str ++ show n
		ESum (_,str) _ => str
		EUndef (n,str) => str ++ show n
		EPrim (n,str) es => "Prim{" ++ str ++ show n ++ "}" ++ showExps es
		EComp e env => showExp1 e ++ "@{" ++ showEnv env ++ "}"
	
	showDef : Def -> String
	showDef (_,xts) = vcat (map (\(x,t) => x ++ " = " ++ showExp t) xts)

Show Exp where
	show = showExp

-- De Bruijn levels
genName : Int -> String
genName n = "X" ++ show n

mkVar : Int -> Exp
mkVar k = EVar (genName k)

mutual
	Eq Env where
		EvEmpty == EvEmpty = True
		(EvPair e (s, v)) == (EvPair e' (s', v')) = (e == e') && (s == s') && (v == v')
		(EvDef e d) == (EvDef e' d') = (e == e') && (d == d')
		e == f = False

	Eq Exp where
		(EComp f e) == (EComp g h) = (f == g) && (e == h)
		(EApp f x) == (EApp g y)   = (f == g) && (x == y)
		(EPi t x) == (EPi t' x')   = (t == t') && (x == x')
		(ELam n e) == (ELam n' e') = (n == n') && (e == e')
		(EDef n e) == (EDef n' e') = (n == n') && (e == e')
		(EVar x) == (EVar y)       = x == y
		(EUniv) == (EUniv)         = True
		(ECon n e) == (ECon n' e') = (n == n') && (e == e')
		(ECase n e) == (ECase n' e') = (n == n') && (e == e')
		(ESum n e) == (ESum n' e') = (n == n') && (e == e')
		(EUndef e) == (EUndef e')  = (e == e')
		(EPrim n e) == (EPrim n' e') = (n == n') && (e == e')
		e1 == e2 = False

record TEnv where
	constructor NewTEnv
	index : Int
	env : Env
	ctxt : Context

tEmpty : TEnv
tEmpty = NewTEnv 0 EvEmpty []

TC : Type -> Type
TC a = Effects.SimpleEff.Eff a [EXCEPTION String, STATE TEnv, STDIO]

lets : List Def -> Exp -> Exp
lets [] e = e
lets (d :: ds) e = EDef d (lets ds e)

partial
defs : Env -> Exp -> Exp
defs EvEmpty e = e
defs (EvDef env d) e = defs env (EDef d e)
-- defs env _ = error $ "defs: environment be should a list of definitions."

upds : Env -> List (Pair String Val) -> Env
upds = foldl EvPair

mutual
	app : Val -> Val -> TC Val
	app (EComp (ELam x b) s) u = eval b (EvPair s (x, u))
	app (EComp (ECase _ ces) r) (ECon c us) with (lookup c ces)
		| Just (xs, e) = eval e (upds r (zip xs us))
		| Nothing      = raise "Cannot apply"
	app f u            = pure $ EApp f u

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
	eval EUniv        _ = pure $ EUniv
	eval t            s = pure $ EComp t s

	evalList : List Exp -> Env -> TC (List Val)
	evalList [] r = pure $ []
	evalList (e :: es) r = do
		e' <- eval e r
		es' <- evalList es r
		pure $ (e' :: es')

	evals : List (Pair String Exp) -> Env -> TC (List (Pair String Exp))
	evals [] r = pure $ []
	evals ((x, e) :: es) r = do
		result <- eval e r
		rear <- evals es r
		pure $ (x, result) :: rear

	-- get variable
	getE : String -> Env -> TC Exp
	getE x (EvPair s (y, u)) with (x == y)
		| True  = pure u
		| False = getE x s
	getE x r@(EvDef r1 d) = do
		ds' <- evals (snd d) r
		getE x $ upds r1 ds'
	getE x r = raise $ "Not found variable " ++ x

addC : Context -> Pair Telescope Env -> List (Pair String Val) -> TC Context
addC gam _ [] = pure $ gam
addC gam ((y, a) :: as, nu) ((x, u) :: xus) = do
	a' <- eval a nu
	addC ((x, a') :: gam) (as, EvPair nu (y, u)) xus

-- Extract the type of a label as a closure
getLblType : String -> Exp -> TC (Pair Telescope Env)
getLblType c (EComp (ESum _ cas) r) with (lookup c cas)
	| Just as = pure (as, r)
	| Nothing = raise $ "Cannot get label type of " ++ c
getLblType c u = raise $ "Unexpected data type"

addTypeVal : Pair String Val -> TEnv -> TC TEnv
addTypeVal (x, v) (NewTEnv k rho gam) = pure $ NewTEnv (k+1) (EvPair rho (x, mkVar k)) ((x, v)::gam)

addType : Pair String Exp -> TEnv -> TC TEnv
addType (x, a) tenv = do
	a' <- eval a (TEnv.env tenv)
	addTypeVal (x, a') tenv

addBranch : List (Pair String Val) -> Pair Telescope Env -> TEnv -> TC TEnv
addBranch nvs (Telescope, env) (NewTEnv k rho gam) =
	pure $ NewTEnv (k + (cast $ length nvs)) (upds rho nvs) !(addC gam (Telescope, env) nvs)

addDef : Def -> TEnv -> TC TEnv
addDef (ts, es) (NewTEnv k rho gam) = do
	let rho' = EvDef rho (ts, es)
	es' <- evals es rho'
	gam' <- addC gam (ts, rho) es'
	pure $ NewTEnv k rho' gam'

addTele : Telescope -> TEnv -> TC TEnv
addTele [] lenv = pure $ lenv
addTele (x :: xs) lenv = do
	lenv' <- addType x lenv
	addTele xs lenv'

getIndex : TC Int
getIndex = pure $ TEnv.index !get

getFresh : TC Exp
getFresh = pure $ mkVar !getIndex

getEnv : TC Env
getEnv = pure $ TEnv.env !get

getContext : TC Context
getContext = pure $ TEnv.ctxt !get

checkLocally : (TEnv -> TC TEnv) -> TC a -> TC a
checkLocally fme m = do
	e1 <- get
	e <- fme e1
	put e
	r <- m
	put e1
	pure r

-- unification -- we use simple unification for now
infixl 5 =?=
(=?=) : Exp -> Exp -> TC ()
s1 =?= s2 = if(s1 == s2) then pure () else raise $ "Cannot commute " ++ s1 ++ " with " ++ s2

mutual
	checkDef : Def -> TC ()
	checkDef (xas, xes) = do
		putStrLn $ "Checking definition of " ++ show (map fst xes)
		checkTele xas
		rho <- getEnv
		checkLocally (addTele xas) $ checks (xas, rho) (map snd xes)

	checkTele : Telescope -> TC ()
	checkTele [] = pure ()
	checkTele ((x, a) :: xas) = do
		check EUniv a
		checkLocally (addType (x, a)) $ checkTele xas

	mapE : List a -> (a -> Eff b e) -> Eff (List b) e
	mapE [] f = pure []
	mapE (x :: xs) f = do
		x1 <- f x
		xs1 <- mapE xs f
		pure (x1 :: xs1)

	seqE : List a -> (a -> Eff () e) -> Eff () e
	seqE xs f = do
		mapE xs f
		pure ()

	check : Val -> Exp -> TC ()
	check a (ECon c es) = do
		(bs, nu) <- getLblType c a
		checks (bs, nu) es
	check EUniv (EPi a (ELam x b)) = do
		check EUniv a
		checkLocally (addType (x, a)) $ check EUniv b
	check EUniv (ESum _ bs) = do
		seqE bs $ \(_, as) => checkTele as
	check t@(EPi (EComp (ESum _ cas) nu) f) e@(ECase _ ces) = do
		if (map fst ces == map fst cas)
			then seqE (zip ces cas) $ \(brc, (_, as)) => checkBranch (as, nu) f brc
			else raise $ "case branches " ++ e ++ " does not match the data type " ++ t
	check (EPi a f) (ELam x t) = do
		var <- getFresh
		checkLocally (addTypeVal (x, a)) $ check !(app f var) t
	check a (EDef d e) = do
		checkDef d
		checkLocally (addDef d) $ check a e
	check a (EUndef _) = pure ()
	check a t = do
		k <- getIndex
		t1 <- infer t
		r1 <- reifyExp k t1
		r2 <- reifyExp k a
		r1 =?= r2

	checkBranch : Pair Telescope Env -> Val -> Branch -> TC ()
	checkBranch (xas, nu) f (c, (xs, e)) = do
		k <- getIndex
		let l = cast (length xas)
		let us = map mkVar [k .. k+l-1]
		checkLocally (addBranch (zip xs us) (xas, nu)) $ check !(app f (ECon c us)) e

	infer : Exp -> TC Exp
	infer EUniv = pure EUniv -- really?
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

	checks : Pair Telescope Env -> List Exp -> TC ()
	checks _ [] = pure ()
	checks ((x, a)::xas, nu) (e::es) = do
		a' <- eval a nu
		check a' e
		rho <- getEnv
		e' <- eval e rho
		checks (xas, EvPair nu (x, e')) es
	checks _ _ = raise "CHECKS"

	-- Reification of a value to an expression
	reifyExp : Int -> Val -> TC Exp
	reifyExp _ EUniv = pure EUniv
	reifyExp k (EComp (ELam x t) r) = do
		t' <- eval t (EvPair r (x, mkVar k))
		r' <- reifyExp (k + 1) t'
		pure $ ELam (genName k) r'
	reifyExp k (EVar l) = pure $ EVar l
	reifyExp k (EApp u v)  = pure $ EApp !(reifyExp k u) !(reifyExp k v)
	reifyExp k (EPi  u v)  = pure $ EPi  !(reifyExp k u) !(reifyExp k v)
	reifyExp k (ECon n ts) = pure $ ECon n !(mapE ts (reifyExp k))

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

one : Exp
one = EDef ([("Nat", EUniv)], [("Nat", ESum (0, "?") [("Z", []), ("S", [("pred", EVar "Nat")])])])
	$ EDef ([("zero", EVar "Nat")], [("zero", ECon "Z" [])])
	$ EDef ([("one", EVar "Nat")], [("one", ECon "S" [ECon "Z" []])])
	$ EVar "one"

-- it should infer to a sum type