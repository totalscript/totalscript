module Elab.Common

import public Core.Program
import public Typing.Common
import Typing.TypeChecking

public export
OpenFunctions : Type
OpenFunctions = SortedMap FullName (Term >< List Plict >< CaseMotive >< List Clause)

-- 8YYYY 0     o8o  8888. oYYYo YY8YY  o8o  YY8YY 8YYYY
-- 8___  0    8   8 8___Y %___    0   8   8   0   8___
-- 8"""  0    8YYY8 8"""o `"""p   0   8YYY8   0   8"""
-- 8oooo 8ooo 0   0 8ooo" YoooY   0   0   0   0   8oooo

public export
record ElabState where
	constructor NewElabState
	elabSig : Signature Term
	elabDefs : Definitions
	elabCtx : Context
	elabNextName : Int
	elabAliases : ModuleAliases
	elabModName : String
	elabModuleNames : List String
	elabOpenData : List FullName
	elabOpenFunctions : OpenFunctions

-- 8YYYY 0     o8o  8888. _YYY_ 8YYYo  o8o  YY8YY _YYY_ 8YYYo
-- 8___  0    8   8 8___Y 0   0 8___P 8   8   0   0   0 8___P
-- 8"""  0    8YYY8 8"""o 0   0 8""Yo 8YYY8   0   0   0 8""Yo
-- 8oooo 8ooo 0   0 8ooo" "ooo" 0   0 0   0   0   "ooo" 0   0

public export
Elaborator : Type -> Type
Elaborator = StateT ElabState (Either String)

export
runElaborator : Elaborator () -> String \/ ElabState
runElaborator elab = do
	(_, p) <- runStateT elab (NewElabState empty empty [] 0 [] "" [] [] empty)
	pure p

export
signature : Elaborator (Signature Term)
signature = elabSig <$> get

export
context : Elaborator Context
context = elabCtx <$> get

export
definitions : Elaborator Definitions
definitions = elabDefs <$> get

export
aliases : Elaborator ModuleAliases
aliases = elabAliases <$> get

export
moduleName : Elaborator String
moduleName = elabModName <$> get

export
putSignature : Signature Term -> Elaborator ()
putSignature sig = do
	s <- get
	put (record { elabSig = sig } s)

export
putContext : Context -> Elaborator ()
putContext ctx = do
	s <- get
	put (record { elabCtx = ctx} s)

export
putDefinitions : Definitions -> Elaborator ()
putDefinitions defs = do
	s <- get
	put (record {elabDefs = defs } s)

export
putAliases : ModuleAliases -> Elaborator ()
putAliases als = do
	s <- get
	put (record { elabAliases = als } s)

export
addAliasFor : String \/ FullName -> FullName -> Elaborator ()
addAliasFor a b = do
	als <- aliases
	putAliases ((a,b) :: als)

export
addAlias : String -> Elaborator ()
addAlias n = do
	m <- moduleName
	addAliasFor (Left n) (m,n)
	addAliasFor (Right (m,n)) (m,n)

export
putModuleName : String -> Elaborator ()
putModuleName m = do
	s <- get
	put (record { elabModName = m } s)

export
moduleNames : Elaborator (List String)
moduleNames = elabModuleNames <$> get

export
putModuleNames : List String -> Elaborator ()
putModuleNames ms = do
	s <- get
	put (record { elabModuleNames = ms } s)

export
addModuleName : String -> Elaborator ()
addModuleName m = do
	ms <- moduleNames
	unless (not (m `elem` ms))
		$ throw $ "A module is already declared with the name " ++ m
	putModuleNames (m :: ms)

export
openData : Elaborator (List FullName)
openData = elabOpenData <$> get

export
putOpenData : List FullName -> Elaborator ()
putOpenData od = do
	s <- get
	put (record { elabOpenData = od } s)

export
openFunctions : Elaborator OpenFunctions
openFunctions = elabOpenFunctions <$> get

export
putOpenFunctions : OpenFunctions -> Elaborator ()
putOpenFunctions fs = do
	s <- get
	put (record { elabOpenFunctions = fs } s)

export
when' : TypeChecker a -> Elaborator () -> Elaborator ()
when' tc e = do
	NewElabState sig defs ctx i als _ ms _ _ <- get
	case runTypeChecker tc sig defs ctx i als ms of
		Left _  => pure ()
		Right _ => e

export
liftTC : TypeChecker a -> Elaborator a
liftTC tc = do
	NewElabState sig defs ctx i als _ ms _ _ <- get
	case runTypeChecker tc sig defs ctx i als ms of
		Left e => throw e
		Right (a, s) => do
			s' <- get
			put $ record { elabNextName = tcNextName s } s'
			pure a

export
addDeclaration : String -> Term -> Term -> Elaborator ()
addDeclaration n def ty = do
	defs <- definitions
	m <- moduleName
	putDefinitions $ insert (m, n) (def, ty) defs

export
updateDeclaration : String -> Term -> Term -> Elaborator ()
updateDeclaration n def ty = do
	defs <- definitions
	m <- moduleName
	-- putDefinitions $ map (\(p, q, r) => if p == (m, n) then (p, def, ty) else (p, q, r)) defs
	putDefinitions $ fromList $
		map (\(p, q, r) => if p == (m, n) then (p, def, ty) else (p, q, r)) $ toList defs

export
addConstructorToModule : String -> String -> ConSig Term -> Elaborator ()
addConstructorToModule m c consig = do
	sig <- signature
	putSignature $ insert (m,c) consig sig

export
addConstructor : String -> ConSig Term -> Elaborator ()
addConstructor c consig = do
	m <- moduleName
	addConstructorToModule m c consig
