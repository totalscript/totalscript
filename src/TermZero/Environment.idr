||| 
||| Environment.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.Environment

import Data.SortedMap

import TermZero.Location
import TermZero.Syntax

export
record PrintInfo where
	constructor MkPrintInfo
	name : Name
	expand : Bool

mutual
	public export
	Closure : Type -> Type
	Closure a = Pair a Context

	export
	Environment : Type
	Environment = SortedMap Index (Closure Term, Closure Term, PrintInfo)

	export
	EnvironmentEntry : Type
	EnvironmentEntry = Pair (Closure Term) (Closure Term)

	export
	data Context : Type where
		MkContext : List (Pair Name Index) -> Context
	
	export
	Eq Context where
		(MkContext a) == (MkContext b) = a == b

public export
interface CLOSURE a where
	getContext : a -> Context
	putContext : a -> Context -> a

export
emptyContext : Context
emptyContext = MkContext []

export
extendContext : Context -> Name -> Index -> Context
extendContext (MkContext s) x i = MkContext $ (x, i)::s

export
emptyEnvironment : Environment
emptyEnvironment = empty

export
partial
env_lookup_term : Index -> Environment -> Closure Term
env_lookup_term i e = case lookup i e of Just (t, _, _) => t

export
partial
env_lookup_printInfo : Index -> Environment -> PrintInfo
env_lookup_printInfo i e = case lookup i e of
	Just (t, a, p) => p

-- | Updates an existing entry and keeps the original printing info.
export
env_update_term : Index -> Closure Term -> Environment -> Environment
env_update_term i t e with (lookup i e)
	| Nothing = e
	| Just (_, a, p) = insert i (t, a, p) (delete i e)

||| closures
export
CLOSURE (Closure a) where
	getContext (_, s)   = s
	putContext (a, _) s = (a, s)

export
CLOSURE a => CLOSURE (Bind a) where
	getContext (_, a)   = getContext a
	putContext (x, a) s = (x, putContext a s)
