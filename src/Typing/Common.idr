module Typing.Common

import public General

import public Core.Variable
import public Core.Term
import public Core.Abstraction
import public Core.ConSig
import public Core.Evaluation

export
extract : (a -> Bool) -> List a -> Maybe (a, List a)
extract _ [] = Nothing
extract p (x::xs) with (p x)
	| True  = Just (x,xs)
	| False = do
		(y,xs') <- extract p xs
		pure (y,x::xs')

public export
Definitions : Type
Definitions = Environment FullName (Term >< Term)

public export
ContextEntry : Type
ContextEntry = Int >< String >< Term

public export
Context : Type
Context = List ContextEntry

public export
MetaVar : Type
MetaVar = Int

public export
Substitution : Type
Substitution = List $ MetaVar >< Term

public export
ModuleAliases : Type
ModuleAliases = List $ (String \/ FullName) >< FullName

-- YY8YY  oYYo oYYYo YY8YY  o8o  YY8YY 8YYYY
--   0   0   " %___    0   8   8   0   8___
--   0   0   , `"""p   0   8YYY8   0   8"""
--   0    YooY YoooY   0   0   0   0   8oooo

public export
record TCState where
	constructor NewTCState
	tcSig : Signature Term
	tcDefs : Definitions
	tcCtx : Context
	tcNextName : Int
	tcNextMeta : MetaVar
	tcSubs : Substitution
	tcAliases : ModuleAliases
	tcModuleNames : List String

public export
TypeCheckerState TCState (Signature Term) Definitions Context where
	typeCheckerSig = tcSig
	putTypeCheckerSig s sig = record { tcSig = sig } s
	typeCheckerDefs = tcDefs
	putTypeCheckerDefs s defs = record { tcDefs = defs } s
	addTypeCheckerDefs s edefs = record { tcDefs = fromList(toList edefs ++ toList (tcDefs s)) } s
	typeCheckerCtx = tcCtx
	putTypeCheckerCtx s ctx = record { tcCtx = ctx } s
	addTypeCheckerCtx s ectx = record { tcCtx = ectx ++ tcCtx s } s
	typeCheckerNextName = tcNextName
	putTypeCheckerNextName s n = record { tcNextName = n } s

public export
TypeCheckerMetas TCState Substitution where
	typeCheckerNextMeta = tcNextMeta
	putTypeCheckerNextMeta s n = record { tcNextMeta = n } s
	typeCheckerSubs = tcSubs
	putTypeCheckerSubs s subs = record { tcSubs = subs } s

-- YY8YY 0   0 8YYYo 8YYYY  oYYo 0   0 8YYYY  oYYo 0  oY 8YYYY 8YYYo
--   0   "o o" 8___P 8___  0   " 8___8 8___  0   " 8_oY  8___  8___P
--   0     0   8"""  8"""  0   , 8"""8 8"""  0   , 8"Yo  8"""  8""Yo
--   0     0   0     8oooo  YooY 0   0 8oooo  YooY 0  Yo 8oooo 0   0

public export
TypeChecker : Type -> Type
TypeChecker = StateT TCState (Either String)

public export
TCMonad TypeChecker TCState (Signature Term) Definitions Context where {}

public export
TCPolyMonad TypeChecker TCState (Signature Term) Definitions Context Substitution where {}

export
runTypeChecker : TypeChecker a ->
	Signature Term ->
	Definitions ->
	Context ->
	Int ->
	ModuleAliases ->
	List String ->
	String \/ (a >< TCState)
runTypeChecker checker sig defs ctx i als mods = runStateT checker (NewTCState sig defs ctx i 0 [] als mods)

export
aliases : TypeChecker ModuleAliases
aliases = map tcAliases get

export
putAliases : ModuleAliases -> TypeChecker ()
putAliases als = do
	s <- get
	put $ record { tcAliases = als } s

export
moduleNames : TypeChecker (List String)
moduleNames = map tcModuleNames get

-- Y8Y 8o  0 8YYYY 8YYYY 8YYYo 8YYYo 8YYYY 8888_
--  0  8Yo 8 8___  8___  8___P 8___P 8___  0   0
--  0  8 Yo8 8"""  8"""  8""Yo 8""Yo 8"""  0   0
-- o8o 0   8 0     8oooo 0   0 0   0 8oooo 8oooY

infix 4 <:>
||| Inferred and elaborated type
public export
data InferredF a b = (<:>) a b

public export
Inferred : Type
Inferred = InferredF Term Term

export
termHalf : Inferred -> Term
termHalf (x <:> t) = x

export
typeHalf : Inferred -> Term
typeHalf (x <:> t) = t
