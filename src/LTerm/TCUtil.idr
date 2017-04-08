module Unification.TCUtil

import Data.List
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State

import Gen.Abs
import Gen.Eval
import Gen.Plict
import Gen.Scope
import Gen.Errors
import Gen.TypeChecker

import Core.Abstraction
import Core.ConSig
import Core.Evaluation
import Core.Term



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
Definitions = List $ FullName >< Term >< Term

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
	addTypeCheckerDefs s edefs = record { tcDefs = edefs ++ tcDefs s } s
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

-- 8YYYY 0   0  o8o  0    0   0  o8o  YY8YY 8YYYY
-- 8___  0   0 8   8 0    0   0 8   8   0   8___
-- 8"""  "o o" 8YYY8 0    0   0 8YYY8   0   8"""
-- 8oooo  "8"  0   0 8ooo "ooo" 0   0   0   8oooo

export
evaluate : Term -> TypeChecker Term
evaluate m = do
	defs <- definitions {s=TCState}
	let scope = [ (x,m') | (x,m',_) <- defs ]
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
	case lookup (m,n) consigs of
		Nothing => throw $ "Unknown constructor: " ++ show (AbsoluteDottedCon m n)
		Just t  => pure (AbsoluteDottedCon m n, t)

export
absoluteDottedTypeInDefinitions : String -> String -> TypeChecker (FullName >< Term)
absoluteDottedTypeInDefinitions m x = do
	defs <- definitions
	case find (\(mx,_,_) => mx == (m,x)) defs of
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
	case find (\(mx,_,_) => mx == (m,x)) defs of
		Nothing      => throw $ "Unknown constant/defined term: " ++ m ++ "." ++ x
		Just (_,_,t) => pure ((m,x),t)

export
typeInContext : Int -> TypeChecker Term
typeInContext i = do
	ctx <- context
	case find (\(j,_,_) => j == i) ctx of
		Nothing      => throw "Unbound automatically generated variable."
		Just (_,_,t) => pure t

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
