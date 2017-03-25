||| 
||| Calculus.idr
||| Created: Thu Mar 23 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||

module TermZero.Calculus

public export
Index : Type
Index = Int

public export
data Name : Type where
	NStr : String -> Name
	NIndex : Int -> String -> Name

export
Eq Name where
	(NStr s) == (NStr s') = s == s'
	(NIndex a _) == (NIndex a1 _) = a == a1
	_ == _ = False

export
Show Name where
	show (NStr s) = s
	show (NIndex a s) = "#" ++ show a ++ "'" ++ s

public export
Label : Type
Label = String

||| "we can interpret a variable binding using evaluator r"
public export
interface Var r where
	var : Name -> r

public export
interface Universe r where
	univ : Nat -> r

public export
interface Literal r where
	lInt : Int -> r
	lFloat : Double -> r
	lString : String -> r

public export
interface LetRec r where
	letrec : List (Name, r, r) -> r -> r

public export
interface Pi r where
	pi : Name -> r -> r -> r
	lam : Name -> r -> r
	app : r -> r -> r

public export
interface Sigma r where
	sigma : Name -> r -> r -> r
	pair : r -> r -> r
	split : r -> Name -> Name -> r -> r

public export
interface Finite r where
	finite : List Label -> r
	label : Label -> r
	cases : r -> List (Label, r) -> r

public export
interface Recurison r where
	rec : r -> r
	roll : r -> r
	unroll : r -> r

public export
interface CInf r where
	inf : r -> r
	delay : r -> r
	force : r -> r

public export
interface Equality r where
	equality : r -> r -> r
	refl : r -> r
	eqElim : r -> Name -> r -> r

public export
interface NT a b where
	ntConv : a -> b
