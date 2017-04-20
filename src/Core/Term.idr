module Core.Term

import Pruviloj
import Derive.Eq

import General

import Core.Variable

%language ElabReflection

%hide Language.Reflection.Elab.FunArg
%access private

--  oYYo _YYY_ 8o  0 oYYYo YY8YY 8YYYo 0   0  oYYo YY8YY _YYY_ 8YYYo
-- 0   " 0   0 8Yo 8 %___    0   8___P 0   0 0   "   0   0   0 8___P
-- 0   , 0   0 8 Yo8 `"""p   0   8""Yo 0   0 0   ,   0   0   0 8""Yo
--  YooY "ooo" 0   8 YoooY   0   0   0 "ooo"  YooY   0   "ooo" 0   0

public export
data Constructor = BareCon String | DottedCon String String | AbsoluteDottedCon String String

export
Interfaces.Eq Constructor where
	(BareCon x) == (BareCon x') = x == x'
	(DottedCon x y) == (DottedCon x' y') = x == x' && y == y'
	(AbsoluteDottedCon x y) == (AbsoluteDottedCon x' y') = x == x' && y == y'
	_ == _ = False

export
Show Constructor where
	show (BareCon con) = con
	show (DottedCon m con) = m ++ "." ++ con
	show (AbsoluteDottedCon m con) = m ++ "." ++ con

-- YY8YY 8YYYY 8YYYo 8_   _8 oYYYo
--   0   8___  8___P 8"o_o"8 %___
--   0   8"""  8""Yo 0  8  0 `"""p
--   0   8oooo 0   0 0     0 YoooY

mutual
	public export
	data Term : Type where
		-- Metavariable, or "hole"
		Meta : Int -> Term
		-- Bound variable
		Var : Variable -> Term
		-- Imported Variable
		DottedVar : String -> String -> Term
		AbsoluteDottedVar : String -> String -> Term
		-- Annotated term
		Ann : Term -> Term -> Term
		-- Universe
		Star : Term
		-- Function Type, “Pi”. Using HOAS for binding.
		Pi : Plict -> Term -> (Scope Term Term) -> Term
		-- Lambda abstraction
		Lam : Plict -> (Scope Term Term) -> Term
		-- Function Application
		App : Plict -> Term -> Term -> Term
		-- Data Construction
		Con : Constructor -> List (Plict >< Term) -> Term
		-- Case Analysis
		Case : List Term -> CaseMotive -> List Clause -> Term
		-- Record Types
		RecordType : Telescope -> Term
		-- Record Construction
		RecordCon : List (String, Term) -> Term
		-- Record Projection
		Project : Term -> String -> Term

	public export
	data CaseMotive
		= CaseMotiveNil Term
		| CaseMotiveCons Term (Scope Term CaseMotive)

	public export
	data Clause = NewClause (Scope Variable (List Pattern)) (Scope Term Term)

	public export
	data Pattern
		= VarPat Variable
		| ConPat Constructor (List (Plict >< Pattern))
		| AssertionPat Term
		| MakeMeta

	public export
	data Telescope
		= TelescopeNil
		| TelescopeCons Term (Scope Term Telescope)

-- 8YYYo 8YYYo 8YYYY YY8YY YY8YY 0   0      8YYYo 8YYYo Y8Y 8o  0 YY8YY
-- 8___P 8___P 8___    0     0   "o o" ____ 8___P 8___P  0  8Yo 8   0
-- 8"""  8""Yo 8"""    0     0     0   """" 8"""  8""Yo  0  8 Yo8   0
-- 0     0   0 8oooo   0     0     0        0     0   0 o8o 0   8   0

public export
data PatternParenLoc = ExplConPatArg | ImplConPatArg

derive Eq for PatternParenLoc

public export
ParenLoc Pattern where
	Loc = PatternParenLoc
	parenLoc (VarPat _)       = [ExplConPatArg,ImplConPatArg]
	parenLoc (ConPat _ _)     = [ImplConPatArg]
	parenLoc (AssertionPat _) = [ExplConPatArg,ImplConPatArg]
	parenLoc MakeMeta         = [ExplConPatArg,ImplConPatArg]

public export
data TermParenLoc
  = RootTerm
  | AnnLeft | AnnRight
  | FunArg | FunRet
  | LamBody | AppLeft | ExplAppRight | ImplAppRight
  | ExplConArg | ImplConArg | AssertionPatArg
  | RecDotArg
derive Eq for TermParenLoc

public export
ParenLoc Term where
	Loc = TermParenLoc
	parenLoc (Meta _) = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (Var _) = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (DottedVar _ _) = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (AbsoluteDottedVar _ _) = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (Ann _ _) = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
	parenLoc Star = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (Pi _ _ _) = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
	parenLoc (Lam _ _) = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
	parenLoc (App _ _ _) = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ImplAppRight,ImplConArg]
	parenLoc (Con _ []) = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg]
	parenLoc (Con _ _) = [FunArg,FunRet,AnnLeft,LamBody,ImplAppRight,ImplConArg]
	parenLoc (Case _ _ _) = [FunArg,FunRet,LamBody,ImplAppRight,ImplConArg]
	parenLoc (RecordType _) = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (RecordCon _) = [FunArg,FunRet,AnnLeft,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]
	parenLoc (Project _ _) = [AnnLeft,FunArg,FunRet,LamBody,AppLeft,ExplAppRight,ImplAppRight,ExplConArg,ImplConArg,AssertionPatArg,RecDotArg]

mutual
	export
	ParenRec Pattern where
		parenRec (VarPat x) = show x
		parenRec (ConPat c []) = show c
		parenRec (ConPat c ps) = show c ++ " " ++ unwords (map auxConPatArg ps)
		where
			auxConPatArg : (Plict,Pattern) -> String
			auxConPatArg (Expl,p) = parenthesize (Just ExplConPatArg) p
			auxConPatArg (Impl,p) = "{" ++ parenthesize (Just ImplConPatArg) p ++ "}"
		parenRec (AssertionPat m) = "." ++ parenthesize (Just AssertionPatArg) m
		parenRec MakeMeta = "?makemeta"

	export
	Show Pattern where
		show p = parenthesize Nothing p

	export
	ParenRec Term where
		parenRec (Meta i) = "?" ++ show i
		parenRec (Var x) = show x
		parenRec (DottedVar m x) = m ++ "." ++ x
		parenRec (AbsoluteDottedVar m x) = m ++ "." ++ x
		parenRec (Ann m ty) = parenthesize (Just AnnLeft) m ++ " : " ++ parenthesize (Just AnnRight) ty
		parenRec Star = "Type"
		parenRec (Pi plic a sc) = do
			let a0' = (unwords $ names sc) ++ " : " ++ parenthesize (Just FunArg) a
			let a' = case plic of
				Expl => "(" ++ a0' ++ ")"
				Impl => "{" ++ a0' ++ "}"
			a' ++ " -> " ++ parenthesize (Just FunRet) (descope (Var . Name) sc)
		parenRec (Lam plic sc) =
			let
				n0' = unwords (names sc)
				n' = case plic of
					Expl => n0'
					Impl => "{" ++ n0' ++ "}"
			in "\\" ++ n' ++ " => " ++ parenthesize (Just LamBody) (descope (Var . Name) sc)
		parenRec (App plic f a) =
			let
				a' = case plic of
					Expl => parenthesize (Just ExplAppRight) a
					Impl => "{" ++ parenthesize (Just ImplAppRight) a ++ "}"
			in parenthesize (Just AppLeft) f ++ " " ++ a'
		parenRec (Con c []) = show c
		parenRec (Con c as) = do
			let as' = [ case plic of
							Expl => parenthesize (Just ExplConArg) a
							Impl => "{" ++ parenthesize (Just ImplConArg) a ++ "}"
						| (plic, a) <- as ]
			hcat [
				(show c),
				" ",
				unwords as']
			-- Prelude.Strings.(++) (show c) $ Prelude.Strings.(++) " " (unwords as')
		parenRec (Case ms mot cs) = hcat [
				"case ",
				interlace " || " (map (parenthesize Nothing) ms),
				" motive ",
				show mot,
				" of ",
				interlace " | " (map auxClause cs),
				" end"
			]
			where
				auxClause : Clause -> String
				auxClause (NewClause psc sc) = hcat [
					interlace " || " (map show (descope Name psc)),
					" => ",
					parenthesize Nothing (descope (Var . Name) sc)
				]
		parenRec (RecordType tele)
			= case auxTelescope tele of
				[] => "Struct {}"
				fields => "Struct { " ++ interlace ", " fields ++ " }"
			where
				auxTelescope : Telescope -> List String
				auxTelescope TelescopeNil = []
				auxTelescope (TelescopeCons t sc) = do
					let f = unwords (names sc) ++ " : " ++ parenthesize Nothing t
					let fs = auxTelescope (descope (Var . Name) sc)
					f :: fs
		parenRec (RecordCon fields) = if (length fields == 0)
			then "new {}"
			else "new { " ++ interlace ", " [ x ++ " = " ++ parenthesize Nothing t | (x,t) <- fields ] ++ " }"
		parenRec (Project m x) = parenthesize (Just RecDotArg) m ++ "." ++ x

	export
	Show Term where
		show t = parenthesize Nothing t

	export
	Show CaseMotive where
		show (CaseMotiveNil ret) = show ret
		show (CaseMotiveCons arg sc)
			= "(" ++ unwords (names sc) ++ " : " ++ show arg ++ ") || "
				++ show (descope (Var . Name) sc)

-- 8888_ 8YYYY  oYYo 0     o8o  8YYYo YY8YY
-- 0   0 8___  0   " 0    8   8 8___P   0
-- 0   0 8"""  0   , 0    8YYY8 8""Yo   0
-- 8oooY 8oooo  YooY 8ooo 0   0 0   0   0

public export
data DeclArg = NewDeclArg Plict String Term

export
Show DeclArg where
	show (NewDeclArg Expl x t) = "(" ++ x ++ " : " ++ show t ++ ")"
	show (NewDeclArg Impl x t) = "{" ++ x ++ " : " ++ show t ++ "}"

-- 8_   _8 8YYYY YY8YY  o8o  oYYYo
-- 8"o_o"8 8___    0   8   8 %___
-- 0  8  0 8"""    0   8YYY8 `"""p
-- 0     0 8oooo   0   0   0 YoooY

export
metas : Term -> List Int
metas x = nub (go x)
where
	go : Term -> List Int
	goPat : Pattern -> List Int
	goCaseMotive : CaseMotive -> List Int
	goClause : Clause -> List Int
	goTele : Telescope -> List Int

	go (Meta i) = [i]
	go (Var _) = []
	go (DottedVar _ _) = []
	go (AbsoluteDottedVar _ _) = []
	go (Ann m t) = go m ++ go t
	go Star = []
	go (Pi _ a sc) = go a ++ go (descope (Var . Name) sc)
	go (Lam _ sc) = go (descope (Var . Name) sc)
	go (App _ f x) = go f ++ metas x
	go (Con _ xs) = concat (map (go . snd) xs)
	go (Case as mot cs) = concat (map go as) ++ goCaseMotive mot ++ concat (map goClause cs)
	go (RecordType tele) = goTele tele
	go (RecordCon fields) = concat (map (go . snd) fields)
	go (Project m _) = go m

	goPat (VarPat _) = []
	goPat (ConPat _ ps) = concat (map (goPat . snd) ps)
	goPat (AssertionPat m) = go m
	goPat MakeMeta = []

	goCaseMotive (CaseMotiveNil t) = go t
	goCaseMotive (CaseMotiveCons a sc) = go a ++ goCaseMotive (descope (Var . Name) sc)

	goClause (NewClause psc sc) = concat (map goPat (descope Name psc)) ++ go (descope (Var . Name) sc)

	goTele TelescopeNil = []
	goTele (TelescopeCons m sc) = go m ++ goTele (descope (Var . Name) sc)

-- 0   0 YY8YY Y8Y 0    Y8Y YY8YY Y8Y 8YYYY oYYYo
-- 0   0   0    0  0     0    0    0  8___  %___
-- 0   0   0    0  0     0    0    0  8"""  `"""p
-- "ooo"   0   o8o 8ooo o8o   0   o8o 8oooo YoooY

export
caseMotiveLength : CaseMotive -> Int
caseMotiveLength (CaseMotiveNil _) = 0
caseMotiveLength (CaseMotiveCons _ sc) = 1 + caseMotiveLength (descope (Var . Name) sc)

export
patternVars : Pattern -> List Variable
patternVars (VarPat v) = [v]
patternVars (ConPat _ ps) = ps >>= (patternVars . snd)
patternVars (AssertionPat _) = []
patternVars MakeMeta = []

export
termToPattern : Term -> Pattern
termToPattern (Var x) = VarPat x
termToPattern (Con c xs) = ConPat c [ (plic, termToPattern x) | (plic,x) <- xs ]
termToPattern m = AssertionPat m
