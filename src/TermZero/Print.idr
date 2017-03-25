||| 
||| Print.idr
||| Created: Sat Mar 25 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||

module TermZero.Print
import TermZero.Calculus

export
Var String where
	var s = show s

export
Universe String where
	univ n = "Type" ++ show n

export
Literal String where
	lInt = show
	lFloat = show
	lString s = "\"" ++ s ++ "\""

export
LetRec String where
	letrec defs x = x ++ " where {" ++ concat (map (\(n, t, e) => show n ++ " : " ++ t ++ " = " ++ e ++ ";") defs) ++ "}"

export
Pi String where
	pi x t b = "(" ++ show x ++ ":" ++ t ++ ") -> " ++ b
	lam x b = show x ++ " => " ++ b
	app a b = "(" ++ a ++ ") (" ++ b ++ ")"

export
Sigma String where
	sigma x t b = "(" ++ show x ++ ":" ++ t ++ ") >< " ++ b
	pair a b = "(" ++ a ++ ", " ++ b ++ ")"
	split x l r b = "split " ++ x ++ " as (" ++ show l ++ ", " ++ show r ++ ") => " ++ b

export
Finite String where
	finite xs = "Finite {" ++ unwords xs ++ "}"
	label l = "'" ++ l
	cases x cs = "case " ++ x ++ "{"
		++ concat (map (\(l, e) => "when " ++ l ++ " => " ++ e ++ ";") cs)
		++ "}"

export
Recurison String where
	rec s = "Rec " ++ s
	roll s = "roll " ++ s
	unroll s = "unroll " ++ s

export
CInf String where
	inf s = "Inf " ++ s
	delay s = "delay " ++ s
	force s = "force " ++ s

export
Equality String where
	equality l r = "(" ++ l ++ ") === (" ++ r ++ ")"
	refl x = "refl " ++ x
	eqElim x n y = "eqelim " ++ x ++ " | " ++ show n ++ "=>" ++ y

testShow1 : String
testShow1 = lam (NStr "a") $ lam (NStr "x") $ var (NStr "x")