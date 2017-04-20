module Typing.TypeChecking

import Typing.Common
import Typing.Util
import Typing.Unification



export
inferify : Term -> TypeChecker Inferred
export
checkify : Term -> Term -> TypeChecker Term

export
checkifyCaseMotive : CaseMotive -> TypeChecker CaseMotive
export
checkifyPattern : Pattern -> Term -> TypeChecker (Pattern >< Term)
export
checkifyClause : Clause -> CaseMotive -> TypeChecker Clause
export
checkifyClauses : List Clause -> CaseMotive -> TypeChecker (List Clause)


-- Y8Y 8o  0 8YYYY 8YYYY 8YYYo Y8Y 8YYYY 0   0
--  0  8Yo 8 8___  8___  8___P  0  8___  "o o"
--  0  8 Yo8 8"""  8"""  8""Yo  0  8"""    0
-- o8o 0   8 0     8oooo 0   0 o8o 0       0

--         8_   _8 8YYYY YY8YY  o8o
-- ____    8"o_o"8 8___    0   8   8
-- """"    0  8  0 8"""    0   8YYY8
--         0     0 8oooo   0   0   0

inferify (Meta i) = throw $ "The metavariable " ++ show (Meta i)
	++ " appears in checkable code, when it should not."

--         0   0  o8o  8YYYo
-- ____    0   0 8   8 8___P
-- """"    "o o" 8YYY8 8""Yo
--          "8"  0   0 0   0

inferify (Var (Name x0)) = do
	((m,x),t) <- typeInDefinitions x0
	pure $ AbsoluteDottedVar m x <:> t

inferify (Var (Generated x i)) = do
	t <- typeInContext i
	pure $ Var (Generated x i) <:> t

inferify (DottedVar m x) = do
	((m',x'),t) <- dottedTypeInDefinitions m x
	pure $ AbsoluteDottedVar m' x' <:> t

inferify (AbsoluteDottedVar m x) = do
	((m',x'),t) <- absoluteDottedTypeInDefinitions m x
	pure $ AbsoluteDottedVar m' x'<:> t

--          o8o  8o  0 8o  0
-- ____    8   8 8Yo 8 8Yo 8
-- """"    8YYY8 8 Yo8 8 Yo8
--         0   0 0   8 0   8

inferify (Ann m t) = do
	t' <- checkify t Star
	et' <- evaluate t'
	m' <- checkify m et'
	subs <- substitution
	pure $ instantiateMetas subs m' <:> instantiateMetas subs et'

--         oYYYo YY8YY  o8o  8YYYo
-- ____    %___    0   8   8 8___P
-- """"    `"""p   0   8YYY8 8""Yo
--         YoooY   0   0   0 0   0

inferify Star = pure $ Star <:> Star

--         8YYYo Y8Y
-- ____    8___P  0
-- """"    8"""   0
--         0     o8o

inferify (Pi plic arg sc) = do
	arg' <- checkify arg Star
	i <- newName
	case head' (names sc) of
		Nothing => throw "Should not happen"
		Just hsc => do
			ret' <- extendContext [(i, hsc, arg')] $ checkify (instantiate sc [Var (Generated hsc i)]) Star
			let sc' = the (Scope Term Term) $ NewScope (names sc) (abstractOver [i] ret')
			subs <- substitution
			pure $ instantiateMetas subs (Pi plic arg' sc') <:> Star

--         0     o8o  8_   _8
-- ____    0    8   8 8"o_o"8
-- """"    0    8YYY8 0  8  0
--         8ooo 0   0 0     0

inferify (Lam _ _) = throw "Cannot infer the type of a lambda expression."

--          o8o  8YYYo 8YYYo
-- ____    8   8 8___P 8___P
-- """"    8YYY8 8"""  8"""
--         0   0 0     0

inferify (App plic f a) = do
	(f0 <:> t0) <- inferify f
	et0 <- evaluate t0
	(app' <:> t') <- insertImplicits f0 plic et0
	subs <- substitution
	pure $ instantiateMetas subs app' <:> instantiateMetas subs t'
where
	insertImplicits : Term -> Plict -> Term -> TypeChecker Inferred
	insertImplicits f' Expl (Pi Expl arg sc) = do
		earg <- evaluate arg
		a' <- checkify a earg
		pure $ App Expl f' a' <:> instantiate sc [a']
	insertImplicits f' Impl (Pi Impl arg sc) = do
		earg <- evaluate arg
		a' <- checkify a earg
		pure $ App Impl f' a' <:> instantiate sc [a']
	insertImplicits f' Expl (Pi Impl _ sc) = do
		meta <- newMetaVar
		let impla = Meta meta
		let newF' = App Impl f' impla
		newT' <- evaluate (instantiate sc [impla])
		insertImplicits newF' Expl newT'
	insertImplicits _ Impl (Pi Expl _ _)
		= throw $ "Expected an explicit argument but found an implicit argument "
					++ "when applying " ++ show f ++ " to " ++ show a ++ " in "
					++ "the expression " ++ show (App plic f a)
	insertImplicits _ _ t
		= throw $ "Cannot insert implicit arguments for non-function type " ++ show t

--          oYYo _YYY_ 8o  0
-- ____    0   " 0   0 8Yo 8
-- """"    0   , 0   0 8 Yo8
--          YooY "ooo" 0   8

inferify (Con c as) = do
	(unaliasedC,consig) <- typeInSignature c
	(as' <:> ret) <- inferifyConArgs consig as consig
	subs <- substitution
	pure $ instantiateMetas subs (Con unaliasedC as') <:> instantiateMetas subs ret
where
	inferifyConArgs : ConSig Term ->
		List (Plict >< Term) ->
		ConSig Term ->
		TypeChecker (InferredF (List (Plict >< Term)) Term)

	inferifyConArgs _ [] (ConSigNil ret) = pure $ [] <:> ret

	inferifyConArgs consig ((Expl, m) :: ms) (ConSigCons Expl arg sc) = do
		subs <- substitution
		earg <- evaluate (instantiateMetas subs arg)
		m' <- checkify m earg
		(ms' <:> ret) <- inferifyConArgs consig ms (instantiate sc [m])
		pure $ ((Expl,m') :: ms') <:> ret

	inferifyConArgs consig ((Impl, m) :: ms) (ConSigCons Impl arg sc) = do
		subs <- substitution
		earg <- evaluate (instantiateMetas subs arg)
		m' <- checkify m earg
		(ms' <:> ret) <- inferifyConArgs consig ms (instantiate sc [m])
		pure $ ((Impl,m') :: ms') <:> ret

	inferifyConArgs consig ms (ConSigCons Impl _ sc) = do
		meta <- newMetaVar
		let implm = Meta meta
		(ms' <:> ret) <- inferifyConArgs consig ms (instantiate sc [implm])
		pure $ ((Impl,implm) :: ms') <:> ret

	inferifyConArgs consig ((Impl,_) :: _) (ConSigCons Expl _ _)
		= throw $ "Expected an explicit argument but found an implicit argument "
					++ "when checking " ++ show (Con c as)
					++ " matches the signature " ++ showConSig (Var . Name) consig

	inferifyConArgs consig _ _ = do
		let las = length as
		let lsig = conSigLength (Var . Name) consig
		throw $ show c ++ " expects " ++ show lsig ++ " "
				++ (if lsig == 1 then "arg" else "args")
				++ " but was given " ++ show las

--          oYYo  o8o  oYYYo 8YYYY
-- ____    0   " 8   8 %___  8___
-- """"    0   , 8YYY8 `"""p 8"""
--          YooY 0   0 YoooY 8oooo

inferify (Case ms0 mot cs) = do
	mot' <- checkifyCaseMotive mot
	ms0' <- checkifyCaseArgs ms0 mot'
	cs' <- checkifyClauses cs mot'
	ret <- auxMotive ms0' mot'
	subs <- substitution
	pure $ instantiateMetas subs (Case ms0' mot' cs') <:> instantiateMetas subs ret
where
	checkifyCaseArgs : List Term -> CaseMotive -> TypeChecker (List Term)
	checkifyCaseArgs [] (CaseMotiveNil _) = pure []
	checkifyCaseArgs (m :: ms) (CaseMotiveCons a sc) = do
		ea <- evaluate a
		m' <- checkify m ea
		ms' <- checkifyCaseArgs ms (instantiate sc [m])
		pure $ (m' :: ms')
	checkifyCaseArgs _ _ = do
		let lms = length ms0
		let lmot = caseMotiveLength mot
		throw $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
					++ (if lmot == 1 then "arg" else "args")
					++ " but was given " ++ show lms

	auxMotive : List Term -> CaseMotive -> TypeChecker Term
	auxMotive [] (CaseMotiveNil a) = pure a
	auxMotive (m :: ms) (CaseMotiveCons _ sc) = auxMotive ms (instantiate sc [m])
	auxMotive _ _ = do
		let lms = length ms0
		let lmot = caseMotiveLength mot
		throw $ "Motive " ++ show mot ++ " expects " ++ show lmot ++ " case "
					++ (if lmot == 1 then "arg" else "args")
					++ " but was given " ++ show lms

--         8YYYo 8YYYY  oYYo _YYY_ 8YYYo 8888_ YY8YY 0   0 8YYYo 8YYYY
-- ____    8___P 8___  0   " 0   0 8___P 0   0   0   "o o" 8___P 8___
-- """"    8""Yo 8"""  0   , 0   0 8""Yo 0   0   0     0   8"""  8"""
--         0   0 8oooo  YooY "ooo" 0   0 8oooY   0     0   0     8oooo

inferify (RecordType tele) = do
	tele' <- checkifyTelescope tele
	pure $ RecordType tele' <:> Star
where
	checkifyTelescope : Telescope -> TypeChecker Telescope
	checkifyTelescope TelescopeNil = pure TelescopeNil
	checkifyTelescope (TelescopeCons t sc) = do
		t' <- checkify t Star
		i <- newName
		case head' (names sc) of
			Nothing => throw "Should not happen"
			Just hsc => do
				m' <- extendContext [(i, hsc, t')]
					$ checkifyTelescope (instantiate sc [Var (Generated hsc i)])
				pure $ TelescopeCons t' (NewScope (names sc) (abstractOver [i] m'))

--         8YYYo 8YYYY  oYYo _YYY_ 8YYYo 8888_  oYYo _YYY_ 8o  0
-- ____    8___P 8___  0   " 0   0 8___P 0   0 0   " 0   0 8Yo 8
-- """"    8""Yo 8"""  0   , 0   0 8""Yo 0   0 0   , 0   0 8 Yo8
--         0   0 8oooo  YooY "ooo" 0   0 8oooY  YooY "ooo" 0   8

inferify (RecordCon _) = throw "Cannot infer the type of a record expression."

--         8YYYo 8YYYY  oYYo _YYY_ 8YYYo 8888_ 8888_ _YYY_ YY8YY
-- ____    8___P 8___  0   " 0   0 8___P 0   0 0   0 0   0   0
-- """"    8""Yo 8"""  0   , 0   0 8""Yo 0   0 0   0 0   0   0
--         0   0 8oooo  YooY "ooo" 0   0 8oooY 8oooY "ooo"   0

inferify (Project m x) = do
	(m' <:> t) <- inferify m
	et <- evaluate t
	case et of
		RecordType tele => case lookupField m' x tele of
			Nothing => throw $ "Missing field " ++ x
			Just t' => pure $ Project m' x <:> t'
		t' => throw $ "Expecting a record type but found " ++ show t'
where
	lookupField : Term -> String -> Telescope -> Maybe Term
	lookupField _ _ TelescopeNil = Nothing
	lookupField m' f (TelescopeCons t sc) with (head' $ names sc)
		| Nothing = Nothing
		| Just (hsc) with (f == hsc)
			| True = Just t
			| _    = lookupField m' f $ instantiate sc [Project m' hsc]


--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o"
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0

--         8_   _8 8YYYY YY8YY  o8o
-- ____    8"o_o"8 8___    0   8   8
-- """"    0  8  0 8"""    0   8YYY8
--         0     0 8oooo   0   0   0

checkify (Meta i) _ = throw $ "The metavariable " ++ show (Meta i)
						++ " appears in checkable code, when it should not."

--         0     o8o  8_   _8          8YYYo Y8Y
-- ____    0    8   8 8"o_o"8    88    8___P  0
-- """"    0    8YYY8 0  8  0          8"""   0
--         8ooo 0   0 0     0    88    0     o8o

checkify (Lam plic sc) t = do
	et <- evaluate t
	case (head' (names sc), plic, et) of
		(Just hsc, Expl, Pi Expl arg sc') => do-- \x -> M : (x : A) -> B
			i <- newName
			eret <- evaluate (instantiate sc' [Var (Generated hsc i)])
			m' <- extendContext [(i, hsc, arg)] $ checkify (instantiate sc [Var (Generated hsc i)]) eret
			subs <- substitution
			pure $ instantiateMetas subs (Lam Expl (NewScope (names sc) (abstractOver [i] m')))
		(Just hsc, Impl, Pi Impl arg sc') => do -- \{y} -> M : {y : A} -> B
			i <- newName
			eret <- evaluate (instantiate sc' [Var (Generated hsc i)])
			m' <- extendContext [(i, hsc, arg)] $ checkify (instantiate sc [Var (Generated hsc i)]) eret
			subs <- substitution
			pure $ instantiateMetas subs (Lam Impl (NewScope (names sc) (abstractOver [i] m')))
		(Just hsc, Expl, Pi Impl arg sc') => do -- \x -> M : {y : A} -> B
			i <- newName
			eret <- evaluate (instantiate sc' [Var (Generated hsc i)])
			f' <- extendContext [(i, hsc, arg)] $ checkify (Lam Expl sc) eret
			subs <- substitution
			pure $ instantiateMetas subs (Lam Impl (NewScope ["_"] (abstractOver (the (List String) []) f')))
		(Just hsc, Impl, Pi Expl _ _) => -- \{y} -> M : (x : A) -> B
			throw $ "Expected an explicit argument but found an implicit argument "
				++ "when checking " ++ show (Lam plic sc)
				++ " matches the signature " ++ show t
		_ => throw $ "Cannot check term: " ++ show (Lam plic sc) ++ "\n"
			++ "Against non-function type: " ++ show t

--          oYYo _YYY_ 8o  0          YY8YY
-- ____    0   " 0   0 8Yo 8    88      0
-- """"    0   , 0   0 8 Yo8            0
--          YooY "ooo" 0   8    88      0

checkify (Con c as) t = do
	(unaliasedC,consig) <- typeInSignature c
	(ats, ret) <- dropConArgs as consig
	unify t ret
	as' <- traverse checkifyConArg ats
	subs <- substitution
	pure $ instantiateMetas subs (Con unaliasedC as')
where
	dropConArgs : List (Plict >< Term) -> ConSig Term ->
		TypeChecker (List ((Plict >< Term) \/ (Plict >< Term >< Term)) >< Term)

	dropConArgs [] (ConSigNil ret) = pure ([], ret)
	dropConArgs ((Expl,m) :: ms) (ConSigCons Expl arg sc) = do
		(ats,ret) <- dropConArgs ms (instantiate sc [m])
		pure (Right (Expl,m,arg) :: ats, ret)
	dropConArgs ((Impl,m) :: ms) (ConSigCons Impl arg sc) = do
		(ats,ret) <- dropConArgs ms (instantiate sc [m])
		pure (Right (Impl,m,arg) :: ats, ret)
	dropConArgs ms (ConSigCons Impl _ sc) = do
		meta <- newMetaVar
		let x = Meta meta
		(ats, ret) <- dropConArgs ms (instantiate sc [x])
		pure (Left (Impl,x) :: ats,ret)
	dropConArgs ((Impl,_) :: _) (ConSigCons Expl _ _)
		= throw $ "Mismatching plicits when checking " ++ show (Con c as)
					++ " has type " ++ show t
	dropConArgs _ _
		= throw $ "Mismatching number of arguments when checking " ++ show (Con c as)
					++ " has type " ++ show t

	checkifyConArg : (Plict >< Term) \/ (Plict >< Term >< Term) -> TypeChecker (Plict >< Term)
	checkifyConArg (Left pm) = pure pm
	checkifyConArg (Right (plic, m, arg)) = do
		subs <- substitution
		earg <- evaluate (instantiateMetas subs arg)
		m' <- checkify m earg
		pure (plic,m')

--         8YYYo 8YYYY  oYYo _YYY_ 8YYYo 8888_
-- ____    8___P 8___  0   " 0   0 8___P 0   0
-- """"    8""Yo 8"""  0   , 0   0 8""Yo 0   0
--         0   0 8oooo  YooY "ooo" 0   0 8oooY

checkify (RecordCon fields) t = case t of
	RecordType tele => do
		fields' <- checkifyFields fields tele
		pure $ RecordCon fields'
	_ => throw $ "Cannot check a record against type " ++ show t
where
	checkifyFields : List (String >< Term) -> Telescope -> TypeChecker (List (String >< Term))
	checkifyFields [] TelescopeNil = pure []
	checkifyFields [] (TelescopeCons _ sc) = throw $ "Missing record field " ++ unwords (names sc)
	checkifyFields _ TelescopeNil = throw $ "Mismatching number of record fields."
	checkifyFields xs (TelescopeCons t' sc) with (head' (names sc))
		| Nothing = throw "Incorrect record field."
		| Just hsc with (extract (\(x',_) => x' == hsc) xs)
			| Nothing = throw $ "Missing record field " ++ unwords (names sc)
			| Just ((x',m),xs') = do
				et' <- evaluate t'
				m' <- checkify m et'
				fields' <- checkifyFields xs' (instantiate sc [m'])
				pure $ (x',m') :: fields'

--          oYYo 8YYYY 8o  0 8YYYY 8YYYo  o8o  0
-- ____    0  __ 8___  8Yo 8 8___  8___P 8   8 0
-- """"    0  "8 8"""  8 Yo8 8"""  8""Yo 8YYY8 0
--          YooY 8oooo 0   8 8oooo 0   0 0   0 8ooo

checkify m t = do
	(m' <:> t') <- inferify m
	et <- evaluate t
	et' <- evaluate t'
	m'' <- subtype m' et' et
	subs <- substitution
	pure $ instantiateMetas subs m''
where
	subtype : Term -> Term -> Term -> TypeChecker Term
	subtype m (Pi Expl a sc) (Pi Expl a' sc') = do
		unify a a'
		subs <- substitution
		i <- newName
		case (head' $ names sc) of
			Just hsc => do
				let b = instantiateMetas subs (instantiate sc [Var (Generated hsc i)])
				let b' = instantiateMetas subs (instantiate sc' [Var (Generated hsc i)])
				subtype m b b'
			Nothing => throw "Should not happen"
	subtype m (Pi Expl a sc) (Pi Impl a' sc')
		= throw $ "The type " ++ show (Pi Expl a sc)
			++ " is not a subtype of " ++ show (Pi Impl a' sc')
	subtype m (Pi Impl a sc) (Pi Expl a' sc') = do
		i <- newMetaVar
		subs <- substitution
		let b = instantiate sc [Meta i]
		subtype (App Impl m (Meta i)) b (Pi Expl a' sc')
	subtype m (Pi Impl a sc) (Pi Impl a' sc') = do
		unify a a'
		i <- newName
		subs <- substitution
		case (head' $ names sc) of
			Just hsc => do
				let b = instantiateMetas subs (instantiate sc [Var (Generated hsc i)])
				let b' = instantiateMetas subs (instantiate sc' [Var (Generated hsc i)])
				subtype m b b'
			Nothing => throw "Should not happen"
	subtype m t t' = do
		unify t t'
		pure m

--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0  oYYo  o8o  oYYYo 8YYYY 8_   _8 _YYY_ YY8YY Y8Y 0   0 8YYYY
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o" 0   " 8   8 %___  8___  8"o_o"8 0   0   0    0  0   0 8___
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0   0   , 8YYY8 `"""p 8"""  0  8  0 0   0   0    0  "o o" 8"""
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0    YooY 0   0 YoooY 8oooo 0     0 "ooo"   0   o8o  "8"  8oooo

checkifyCaseMotive (CaseMotiveNil a) = do
	a' <- checkify a Star
	pure $ CaseMotiveNil a'
checkifyCaseMotive (CaseMotiveCons a sc) with (head' $ names sc)
	| Just hsc = do
		a' <- checkify a Star
		i <- newName
		b' <- extendContext [(i, hsc, a')]
				$ checkifyCaseMotive (instantiate sc [Var (Generated hsc i)])
		subs <- substitution
		pure $ instantiateMetasCaseMotive subs
			$ CaseMotiveCons a' $ NewScope (names sc) (abstractOver [i] b')
	| Nothing = throw "Should not happen"

--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0 8YYYo  o8o  YY8YY YY8YY 8YYYY 8YYYo 8o  0
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o" 8___P 8   8   0     0   8___  8___P 8Yo 8
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0   8"""  8YYY8   0     0   8"""  8""Yo 8 Yo8
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0   0     0   0   0     0   8oooo 0   0 0   8

checkifyPattern (VarPat (Name x)) _ = pure (VarPat (Name x), Var (Name x))
checkifyPattern (VarPat (Generated x i)) t = do
	t' <- typeInContext i
	unify t t'
	pure (VarPat (Generated x i), Var (Generated x i))
checkifyPattern (ConPat _ _) Star = throw "Cannot pattern match on a type."
checkifyPattern (ConPat c ps0) t = do
	(unaliasedC,sig) <- typeInSignature c
	(ps',xs,ret) <- checkifyPatConArgs sig ps0 sig
	subs <- substitution
	et <- evaluate (instantiateMetas subs t)
	eret <- evaluate (instantiateMetas subs ret)
	unify et eret
	subs' <- substitution
	pure (instantiateMetasPat subs' (ConPat unaliasedC ps'), instantiateMetas subs' (Con unaliasedC xs))
where
	checkifyPatConArgs : ConSig Term -> List (Plict >< Pattern) ->
		ConSig Term -> TypeChecker (List (Plict >< Pattern) >< List (Plict >< Term) >< Term)
	checkifyPatConArgs _ [] (ConSigNil ret) = pure ([],[],ret)
	checkifyPatConArgs consig ((Expl,p) :: ps) (ConSigCons Expl arg sc') = do
		earg <- evaluate arg
		(p',x) <- checkifyPattern p earg
		(ps', xs, ret) <- checkifyPatConArgs consig ps (instantiate sc' [x])
		pure ((Expl,p') :: ps', (Expl,x) :: xs, ret)
	checkifyPatConArgs consig ((Impl,p) :: ps) (ConSigCons Impl arg sc') = do
		earg <- evaluate arg
		(p',x) <- checkifyPattern p earg
		(ps',xs,ret) <- checkifyPatConArgs consig ps (instantiate sc' [x])
		pure ((Impl,p') :: ps', (Impl,x) :: xs, ret)
	checkifyPatConArgs consig ps (ConSigCons Impl _ sc') = do
		meta <- newMetaVar
		let x = Meta meta
		(ps',xs,ret) <- checkifyPatConArgs consig ps (instantiate sc' [x])
		pure ((Impl,AssertionPat x) :: ps', (Impl,x) :: xs, ret)
	checkifyPatConArgs consig ((Impl,_) :: _) (ConSigCons Expl _ _)
		= throw $ "Expected an explicit argument but found an implicit argument "
					++ "when checking " ++ show (ConPat c ps0)
					++ " matches the signature " ++ showConSig (Var . Name) consig
	checkifyPatConArgs consig _ _ = do
		let lps = length ps0
		let lsig = conSigLength (Var . Name) consig
		throw $ show c ++ " expects " ++ show lsig ++ " case "
				++ (if lsig == 1 then "arg" else "args")
				++ " but was given " ++ show lps
checkifyPattern (AssertionPat m) t = do
	m' <- checkify m t
	subs <- substitution
	let m'' = instantiateMetas subs m'
	pure (AssertionPat m'', m'')
checkifyPattern MakeMeta _ = throw $ show MakeMeta ++ " should not appear in a checkable pattern."

--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0  oYYo 0     o8o  0   0 oYYYo 8YYYY
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o" 0   " 0    8   8 0   0 %___  8___
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0   0   , 0    8YYY8 0   0 `"""p 8"""
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0    YooY 8ooo 0   0 "ooo" YoooY 8oooo

checkifyClause (NewClause psc sc0) motive = do
	ctx <- Traversable.for (names psc) $ \x => do
		i <- newName
		m <- newMetaVar
		pure (i, x, Meta m)
	let is = [ i | (i,_,_) <- ctx ]
	let xs1 = zipWith Generated (names psc) is
	let xs2 = map Var (removeByDummies (names psc) xs1)
	extendContext ctx $ do
		let ps = instantiate psc xs1
		(ps',ret) <- checkPatternsMotive ps motive
		subs <- substitution
		eret <- evaluate (instantiateMetas subs ret)
		m' <- checkify (instantiate sc0 xs2) eret
		subs' <- substitution
		let ps'' = map (instantiateMetasPat subs') ps'
		let psWithMsToBind = [ p | (MakeMeta, AssertionPat p) <- zip ps ps'' ]
		let msToBind = nub (psWithMsToBind >>= metas)
		newSubs <- Traversable.for msToBind $ \m => do
			i <- newName
			pure (m, Var (Generated ("_" ++ show i) i))
		addSubstitutions newSubs
		subs'' <- substitution
		let newPs = bindersByNewMetas ps (map (instantiateMetasPat subs'') ps'')
		let newVars = newPs >>= patternVars
		let (newNames, newIs) = unzip $ the (List $ String >< Int) $ do
			Generated x i <- newVars | _ => []
			pure (x, i)
		let newM = instantiateMetas subs'' m'
		pure $ NewClause (NewScope newNames (abstractOver newIs newPs))
			$ NewScope (removeByDummies newNames newNames)
				$ abstractOver (removeByDummies newNames newIs) newM
where
	bindersByNewMetas : List Pattern -> List Pattern -> List Pattern
	bindersByNewMetas [] [] = []
	bindersByNewMetas (MakeMeta :: guides) (AssertionPat x :: ps)
		= termToPattern x :: bindersByNewMetas guides ps
	bindersByNewMetas (_ :: guides) (p :: ps) = p :: bindersByNewMetas guides ps

	checkPatternsMotive : List Pattern -> CaseMotive -> TypeChecker (List Pattern >< Term)
	checkPatternsMotive [] (CaseMotiveNil ret) = pure ([],ret)
	checkPatternsMotive (MakeMeta :: ps) (CaseMotiveCons _ sc') = do
		m <- newMetaVar
		(ps',ret) <- checkPatternsMotive ps (instantiate sc' [Meta m])
		pure (AssertionPat (Meta m) :: ps', ret)
	checkPatternsMotive (p :: ps) (CaseMotiveCons arg sc') = do
		earg <- evaluate arg
		(p', x) <- checkifyPattern p earg
		(ps', ret) <- checkPatternsMotive ps (instantiate sc' [x])
		pure (p'::ps', ret )
	checkPatternsMotive _ _ = do
		let lps = length (descope Name psc)
		let lmot = caseMotiveLength motive
		throw $ "Motive " ++ show motive ++ " expects " ++ show lmot ++ " case "
				++ (if lmot == 1 then "arg" else "args")
				++ " but was given " ++ show lps

--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0  oYYo 0     o8o  0   0 oYYYo 8YYYY oYYYo
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o" 0   " 0    8   8 0   0 %___  8___  %___
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0   0   , 0    8YYY8 0   0 `"""p 8"""  `"""p
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0    YooY 8ooo 0   0 "ooo" YoooY 8oooo YoooY

checkifyClauses [] _ = pure []
checkifyClauses (c :: cs) motive = do
	c' <- checkifyClause c motive
	cs' <- checkifyClauses cs motive
	pure $ c' :: cs'

--  oYYo 0   0 8YYYY  oYYo 0  oY Y8Y 8YYYY 0   0  oYYo _YYY_ 8o  0 oYYYo Y8Y  oYYo
-- 0   " 8___8 8___  0   " 8_oY   0  8___  "o o" 0   " 0   0 8Yo 8 %___   0  0  __
-- 0   , 8"""8 8"""  0   , 8"Yo   0  8"""    0   0   , 0   0 8 Yo8 `"""p  0  0  "8
--  YooY 0   0 8oooo  YooY 0  Yo o8o 0       0    YooY "ooo" 0   8 YoooY o8o  YooY

export
checkifyConSig : ConSig Term -> TypeChecker (ConSig Term)
checkifyConSig (ConSigNil ret) = do
	ret' <- checkify ret Star
	pure $ ConSigNil ret'
checkifyConSig (ConSigCons plic arg sc) with (head' $ names sc)
	| Just hsc = do
		arg' <- checkify arg Star
		i <- newName
		t <- extendContext [(i, hsc, arg')]
				$ checkifyConSig (instantiate sc [Var (Generated hsc i)])
		pure $ ConSigCons plic arg' (NewScope (names sc) (abstractOver [i] t))
	| Nothing = throw "Should not happen"

-- 8YYYo 0   0 8888. 0    Y8Y  oYYo    8YYYY 0   0 8o  0  oYYo YY8YY Y8Y _YYY_ 8o  0 oYYYo
-- 8___P 0   0 8___Y 0     0  0   "    8___  0   0 8Yo 8 0   "   0    0  0   0 8Yo 8 %___
-- 8"""  0   0 8"""o 0     0  0   ,    8"""  0   0 8 Yo8 0   ,   0    0  0   0 8 Yo8 `"""p
-- 0     "ooo" 8ooo" 8ooo o8o  YooY    0     "ooo" 0   8  YooY   0   o8o "ooo" 0   8 YoooY

export
metasSolved : TypeChecker ()
metasSolved = do
	s <- get
	unless (tcNextMeta s == cast (length $ tcSubs s))
		$ throw "Not all metavariables have been solved."

export
check : Term -> Term -> TypeChecker Term
check m t = do
	et <- evaluate t
	m' <- checkify m et
	metasSolved
	subs <- substitution
	pure $ instantiateMetas subs m'

export
infer : Term -> TypeChecker Inferred
infer m = do
	(m' <:> t) <- inferify m
	metasSolved
	subs <- substitution
	et <- evaluate (instantiateMetas subs t)
	pure $ instantiateMetas subs m' <:> et
