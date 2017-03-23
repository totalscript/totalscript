||| 
||| Calculus.idr
||| Created: Thu Mar 23 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||

module TermZero.Calculus

Index : Type
Index = Int

data Name : Type where
	NStr : String -> Name
	NIndex : Int -> String -> Name

Eq Name where
	(NStr s) == (NStr s') = s == s'
	(NIndex a _) == (NIndex a1 _) = a == a1
	_ == _ = False

Show Name where
	show (NStr s) = s
	show (NIndex a s) = "#" ++ show a ++ "'" ++ s

Label : Type
Label = String

interface Var r where
	var : Name -> r

interface Pi r where
	pi : Name -> r -> r -> r
	lam : Name -> r -> r
	app : r -> r -> r

interface Sigma r where
	sigma : Name -> r -> r -> r
	pair : r -> r -> r
	split : r -> Name -> Name -> r -> r

interface Finite r where
	finite : List Label -> r
	label : Label -> r
	cases : r -> List (Label, r) -> r

interface Recurison r where
	rec : r -> r
	roll : r -> r
	unroll : r -> r

interface Inf r where
	inf : r -> r
	delay : r -> r
	force : r -> r

interface Equality r where
	equality : r -> r -> r
	refl : r -> r
	eqElim : r -> Name -> r

--- can we do this?
-- interface Theory ??? r where
-- 	TypeType : Type -> Type
-- 	IntroType : Type -> Type
-- 	ElimType : Type -> Type

-- 	type : TypeType ??? r -> r
-- 	intro : IntroType ??? r -> r
-- 	elim : ElimType ??? r-> r

-- Var String where
-- 	var s = s

-- Pi String where
-- 	pi x t b = "(" ++ x ++ ":" ++ t ++ ") -> " ++ b
-- 	lam x b = x ++ " => " ++ b
-- 	app a b = "(" ++ a ++ ") (" ++ b ++ ")"

-- Sigma String where
-- 	sigma x t b = "(" ++ x ++ ":" ++ t ++ ") >< " ++ b
-- 	pair a b = "(" ++ a ++ ", " ++ b ++ ")"
-- 	split x l r b = "split " ++ x ++ " as (" ++ l ++ ", " ++ r ++ ") => " ++ b

