module TermLang.Syntax

mutual
	public export
	Label : Type
	Label = String
	
	-- Branch of the form: c x1 .. xn -> e
	public export
	Branch : Type
	Branch = Pair Label $ Pair (List String) Exp
	
	-- Telescope (x1 : A1) .. (xn : An)
	public export
	Telescope : Type
	Telescope = List $ Pair String Exp
	
	-- Labelled sum: c (x1 : A1) .. (xn : An)
	public export
	LblSum : Type
	LblSum = List $ Pair Label Telescope

	-- We, for now, do not care too much about the difference between expressions and values
	public export
	Val : Type
	Val = Exp

	-- Context gives type values to identifiers
	public export
	Context : Type
	Context = List $ Pair String Val

	-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
	public export
	Def : Type
	Def = Pair Telescope $ List $ Pair String Exp

	-- Prim : Tags for Sums and Cases
	public export
	Prim : Type
	Prim = Pair Int String

	public export
	data Exp : Type where
		-- Closure
		EComp  : Exp -> Env -> Exp
		-- Application
		EApp   : Exp -> Exp -> Exp
		-- Pi type
		-- Pi T (Lam x T)
		-- or
		-- Pi T (EComp (ELam x t) e)
		EPi    : Exp -> Exp -> Exp
		-- Abstraction
		ELam   : String -> Exp -> Exp
		-- LetRec
		EDef   : Def -> Exp -> Exp
		-- Variable
		EVar   : String -> Exp
		-- Universe
		EType  : Nat -> Exp
		-- Construction
		ECon   : String -> List Exp -> Exp
		-- Case analysis
		ECase  : Prim -> List Branch -> Exp
		-- Sum type
		ESum   : Prim -> LblSum -> Exp
		-- Undefined
		EUndef : Prim -> Exp
		-- used for reification
		EPrim  : Prim -> List Exp -> Exp
	
	public export
	data Env =
		EvEmpty
		| EvPair Env (Pair String Val)
		| EvDef Env Def


mutual
	||| equality
	export
	Eq Env where
		EvEmpty == EvEmpty = True
		(EvPair e (s, v)) == (EvPair e' (s', v')) = assert_total $  (e == e') && (s == s') && (v == v')
		(EvDef e d) == (EvDef e' d') = assert_total $ (e == e') && (d == d')
		e == f = False
	
	export
	Eq Exp where
		(EComp f e) == (EComp g h)   = assert_total $ (f == g) && (e == h)
		(EApp f x) == (EApp g y)     = (f == g) && (x == y)
		(EPi t x) == (EPi t' x')     = (t == t') && (x == x')
		(ELam n e) == (ELam n' e')   = (n == n') && (e == e')
		(EDef n e) == (EDef n' e')   = assert_total $ (n == n') && (e == e')
		(EVar x) == (EVar y)         = x == y
		(EType m) == (EType n)       = m == n
		(ECon n e) == (ECon n' e')   = assert_total $ (n == n') && (e == e')
		(ECase n e) == (ECase n' e') = assert_total $ (n == n') && (e == e')
		(ESum n e) == (ESum n' e')   = assert_total $ (n == n') && (e == e')
		(EUndef e) == (EUndef e')    = assert_total $ (e == e')
		(EPrim n e) == (EPrim n' e') = assert_total $ (n == n') && (e == e')
		e1 == e2 = False


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
	showExp1 (EType n) = "U" ++ show n
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
	showEnv (EvPair env (x,u)) = parens $ showEnv1 env ++ x ++ ":" ++ showExp u
	showEnv (EvDef env xas)    = showEnv env

	showEnv1 : Env -> String
	showEnv1 EvEmpty            = ""
	showEnv1 (EvPair env (x,u)) = showEnv1 env ++ x ++ ":" ++ showExp u ++ ", "
	showEnv1 (EvDef env xas)    = showEnv env

	export
	showExp : Exp -> String
	showExp e = case e of
		EApp e0 e1 => showExp e0 ++ " " ++ showExp1 e1
		EPi e0 (EComp (ELam x e1) env) => "(" ++ show x ++ " : " ++ showExp e0 ++ ") ->" ++ showExp e1 ++ "@{" ++ showEnv env ++ "}"
		EPi e0 (ELam x e1) => "(" ++ show x ++ " : " ++ showExp e0 ++ ") ->" ++ showExp e1
		EPi e0 e1 => "Pi{" ++ showExps [e0,e1] ++ "}"
		ELam x e => "\\" ++ x ++ " -> " ++ showExp e
		EDef d e => showExp e ++ " where" <//> showDef d
		EVar x => x
		EType n => "U" ++ show n
		ECon c es => c ++ " " ++ showExps es
		ECase (n,str) _ => str ++ show n
		ESum (_,str) _ => str
		EUndef (n,str) => str ++ show n
		EPrim (n,str) es => "Prim{" ++ str ++ show n ++ "}" ++ showExps es
		EComp e env => showExp1 e ++ "@{" ++ showEnv env ++ "}"
	
	showDef : Def -> String
	showDef (_,xts) = vcat (map (\(x,t) => x ++ " = " ++ showExp t) xts)

export
Show Exp where
	show = showExp