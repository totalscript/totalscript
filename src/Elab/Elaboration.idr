module Elab.Elaboration

import Elab.Common
import Typing.TypeChecking
import Typing.Util

-- 8YYYY 8o  0 oYYYo 0   0 8YYYo 8YYYY      _YYY_ oYYYo    0   0  o8o  0    Y8Y 8888_
-- 8___  8Yo 8 %___  0   0 8___P 8___  ____ 0   0 %___     0   0 8   8 0     0  0   0
-- 8"""  8 Yo8 `"""p 0   0 8""Yo 8"""  """" 0   0 `"""p    "o o" 8YYY8 0     0  0   0
-- 8oooo 0   8 YoooY "ooo" 0   0 8oooo      "ooo" YoooY     "8"  0   0 8ooo o8o 8oooY

ensureOpenSettingsAreValid : List OpenSettings -> Elaborator ()
ensureOpenSettingsAreValid oss = for_ oss ensure
where
	ensureModuleExists : String -> Elaborator ()
	ensureModuleExists m = do
		ms <- moduleNames
		unless (m `elem` ms)
			$ throw $ "The module " ++ m ++ " is not a known module."

	openAsIsValid : Maybe String -> Elaborator ()
	openAsIsValid Nothing = pure ()
	openAsIsValid (Just m') = do
		ms <- moduleNames
		unless (not (m' `elem` ms))
			$ throw $ "The module name " ++ m' ++ " is already in use."

	hidingUsingIsValid : String -> Maybe HidingUsing -> Elaborator ()
	hidingUsingIsValid _ Nothing = pure ()
	hidingUsingIsValid m (Just hu') = do
		defs <- definitions
		sig <- signature
		let ns = nub (case hu' of { Hiding ns' => ns' ; Using ns' => ns' })
		let known = nub ([ n | ((_,n),_,_) <- defs ] ++ [ n | ((_,n),_) <- sig ])
		let missing = ns \\ known
		unless (isNil missing)
			$ throw $ "The module " ++ m ++ " does not declare these symbols: "
							++ unwords missing

	showLR : String \/ FullName -> String
	showLR (Left n0) = n0
	showLR (Right (m0,n0)) = m0 ++ "." ++ n0

	renamingIsValid : String -> Maybe String -> Maybe HidingUsing -> List FullName -> Elaborator ()
	renamingIsValid m a hu r = do
		defs <- definitions
		sig <- signature
		let ns = nub [ n | (n,_) <- r ]
		let known = nub ([ n | ((m',n),_,_) <- defs, m' == m ] ++ [ n | ((m',n),_) <- sig, m' == m ])
		let missing = ns \\ known
		unless (isNil missing) $ throw $ "The module " ++ m ++ " does not declare these symbols: "
			++ unwords ns
		let knownBeingUsed = case hu of
			Nothing => known
			Just (Using used) => used
			Just (Hiding hidden) => known \\ hidden
		let missingUsed = ns \\ knownBeingUsed
		unless (isNil missingUsed)
			$ throw $ "The following symbols are not being opened: " ++ unwords missingUsed
		let ns' = [ n' | (_,n') <- r ]
		let preserved = known \\ ns
		let overlappingNames = [ x | (x :: xs) <- groupBy (==) (sort (ns' ++ preserved)), length xs /= 0 ]
		unless (isNil overlappingNames)
			$ throw $ "These symbols will be overlapping when the module " ++ m
				++ " is opened: " ++ unwords overlappingNames
		als <- aliases
		let combine = the (String -> String \/ FullName) $ case a of
			Nothing => Left
			Just m' => \n' => Right (m', n')
		let mns' = nub [ combine n' | (_,n') <- r ]
		let knownAls = nub [ al | (al,_) <- als ]
		let overlap = intersect mns' knownAls

		unless (isNil overlap) $ throw $ "These symbols are already in scope: "
			++ unwords (map showLR overlap)

	ensure : OpenSettings -> Elaborator ()
	ensure (NewOpenSettings m a hu r) = do
		ensureModuleExists m
		openAsIsValid a
		hidingUsingIsValid m hu
		renamingIsValid m a hu r

-- 8o  0 8YYYY 0     0  o8o  0    Y8Y  o8o  oYYYo 8YYYY oYYYo
-- 8Yo 8 8___  0  0  0 8   8 0     0  8   8 %___  8___  %___
-- 8 Yo8 8"""  8 _8_ 8 8YYY8 0     0  8YYY8 `"""p 8"""  `"""p
-- 0   8 8oooo "8* *8" 0   0 8ooo o8o 0   0 YoooY 8oooo YoooY

newAliases : Signature Term -> Definitions -> List OpenSettings -> ModuleAliases
newAliases _ _ [] = []
newAliases sig defs (os::oss) = do
	let als  = newAliasesFromSettings os
	let als' = newAliases sig defs oss
	als' ++ als
where
	used : Maybe HidingUsing -> List FullName -> List FullName
	used Nothing            = id
	used (Just (Hiding ns)) = filter (\(_,n) => not (n `elem` ns))
	used (Just (Using ns))  = filter (\(_,n) => (n `elem` ns))

	renamed : List FullName -> List FullName -> List (String >< FullName)
	renamed r mns = [ (maybe n id (lookup n r), (m,n)) | (m,n) <- mns ]

	ased : Maybe String -> List (String >< FullName) ->
		List ((String \/ FullName) >< FullName)
	ased Nothing   ns = [ (Left x, (m,n)) | (x,(m,n)) <- ns ]
	ased (Just m') ns = [ (Right (m',x), (m,n)) | (x,(m,n)) <- ns ]

	newAliasesFromSettings : OpenSettings -> ModuleAliases
	newAliasesFromSettings (NewOpenSettings m a hu r) = do
		let openedSymbols = [ (m',c) | ((m',c),_) <- sig, m' == m ] ++ [ (m',x) | ((m',x),_,_) <- defs, m' == m ]
		let usedSymbols = used hu openedSymbols
		let renamedSymbols = renamed r usedSymbols
		ased a renamedSymbols

extendAliases : List OpenSettings -> Elaborator a -> Elaborator a
extendAliases settings tc = do
	ensureOpenSettingsAreValid settings
	als <- aliases
	sig <- signature
	defs <- definitions
	let newAls = newAliases sig defs settings ++ als
	putAliases newAls
	x <- tc
	putAliases als
	pure x

-- 8888. 0   0 Y8Y 0    8888_ 0     o8o  8_   _8 8888. 8888_  o8o
-- 8___Y 0   0  0  0    0   0 0    8   8 8"o_o"8 8___Y 0   0 8   8
-- 8"""o 0   0  0  0    0   0 0    8YYY8 0  8  0 8"""o 0   0 8YYY8
-- 8ooo" "ooo" o8o 8ooo 8oooY 8ooo 0   0 0     0 8ooo" 8oooY 0   0

buildLambda : (List Term -> Term) -> List Plict -> Term
buildLambda f [] = f []
buildLambda f (plic :: plics) = Lam plic $
	NewScope ["_" ++ show (length plics)] $ \[x] => buildLambda (f . (x ::)) plics

-- 8YYYY 0     o8o  8888. YY8YY 8YYYY 8YYYo 8_   _8 8888_ 8YYYY  oYYo 0
-- 8___  0    8   8 8___Y   0   8___  8___P 8"o_o"8 0   0 8___  0   " 0
-- 8"""  0    8YYY8 8"""o   0   8"""  8""Yo 0  8  0 0   0 8"""  0   , 0
-- 8oooo 8ooo 0   0 8ooo"   0   8oooo 0   0 0     0 8oooY 8oooo  YooY 8ooo

export elabTermDecl : TermDeclaration -> Elaborator ()

--         oYYYo Y8Y 8_   _8 8YYYo 0    8YYYY
-- ____    %___   0  8"o_o"8 8___P 0    8___
-- """"    `"""p  0  0  8  0 8"""  0    8"""
--         YoooY o8o 0     0 0     8ooo 8oooo

elabTermDecl (SimpleTermDef n ty def) = do
	when' (typeInDefinitions n) $ throw ("Term already defined: " ++ n)
	ty' <- liftTC (check ty Star)
	m <- moduleName
	addAlias n
	def' <- liftTC (extendDefinitions [((m,n),def,ty')] (check def ty'))
	addDeclaration n def' ty'

--         8YYYo  o8o  YY8YY YY8YY 8YYYY 8YYYo 8o  0
-- ____    8___P 8   8   0     0   8___  8___P 8Yo 8
-- """"    8"""  8YYY8   0     0   8"""  8""Yo 8 Yo8
--         0     0   0   0     0   8oooo 0   0 0   8

elabTermDecl decl@(PatternTermDef n ty preclauses) = go n ty preclauses
where
	isVarPat : Pattern -> Bool
	isVarPat (VarPat _) = True
	isVarPat _ = False

	truePlicities : List Plict -> Term -> Maybe (List (Plict \/ Plict))
	truePlicities [] _ = Just []
	truePlicities (Expl::plics) (Pi Expl _ sc) = do
		rest <- truePlicities plics (descope (Var . Name) sc)
		pure $ Right Expl :: rest
	truePlicities (Expl::plics) (Pi Impl _ sc) = do
		rest <- truePlicities (Expl :: plics) (descope (Var . Name) sc)
		pure $ Left Impl :: rest
	truePlicities (Impl :: _) (Pi Expl _ _) = Nothing
	truePlicities (Impl :: plics) (Pi Impl _ sc) = do
		rest <- truePlicities plics (descope (Var . Name) sc)
		pure $ Right Impl :: rest

	motiveAux : Int -> Term -> CaseMotive
	motiveAux 0 t = CaseMotiveNil t
	motiveAux i (Pi _ a (NewScope ns b)) = CaseMotiveCons a $ NewScope ns (motiveAux (i - 1) . b)

	truePatterns : List (Plict \/ Plict) -> List Pattern -> List Pattern
	truePatterns [] [] = []
	truePatterns (Right _ :: plics) (p :: ps) = p :: truePatterns plics ps
	truePatterns (Left _ :: plics) ps = MakeMeta :: truePatterns plics ps

	go : String -> Term -> (List ClauseDeclT) -> Elaborator ()
	go n ty [] = throw "Cannot create an empty let-where definition."
	go n ty [(plics,(ps,xs,b))] with (all isVarPat ps)
		| True = elabTermDecl $ SimpleTermDef n ty (helperFold (uncurry lamHelper) (zip plics xs) b)
	go n ty preclauses@((_,(ps0,_,_)) :: _) = do
		let lps0 = length ps0
		unless (all (\(_,(ps,_,_)) => length ps == lps0) preclauses)
			$ throw "Mismatching number of patterns in different clauses of a pattern matching function."
		let (plics :: plicss) = map fst preclauses
		unless (all (plics ==) plicss)
			$ throw "Mismatching plicities in different clauses of a pattern matching function"
		case truePlicities plics ty of
			Nothing => throw $ "Cannot build a case expression motive from the type " ++ show ty
			Just truePlics => do
				let mot = motiveAux (cast $ length truePlics) ty
				let clauses = [ clauseHelper (truePatterns truePlics ps) xs b | (_,(ps,xs,b)) <- preclauses ]
				let plicsForLambdaAux = map (either id id) truePlics
				elabTermDecl $ SimpleTermDef n ty $
					buildLambda (\as => Case as mot clauses) plicsForLambdaAux

--         _YYY_ 8YYYo 8YYYY 8o  0
-- ____    0   0 8___P 8___  8Yo 8
-- """"    0   0 8"""  8"""  8 Yo8
--         "ooo" 0     8oooo 0   8

elabTermDecl (OpenTermDef n args ty) = do
	when' (typeInDefinitions n) $ throw ("Term already defined: " ++ n)
	let (ty,plics,mot) = convertArgs args
	ty' <- liftTC (checkify ty Star)
	mot' <- liftTC (checkifyCaseMotive mot)
	m <- moduleName
	fs <- openFunctions
	case lookup (m,n) fs of
		Nothing => do
				putOpenFunctions (((m,n),(ty',plics,mot',[])) :: fs)
				let initialDef = buildLambda (\xs => Case xs mot' []) plics
				addAlias n
				initialDef' <- liftTC $ extendDefinitions [((m,n),initialDef,ty')] (check initialDef ty')
				addDeclaration n initialDef' ty
		Just _ => throw $ "The open function " ++ show (DottedVar m n) ++ " has already been declared."
where
	convertArgs : List DeclArg -> (Term >< List Plict >< CaseMotive)
	convertArgs [] = (ty, [], CaseMotiveNil ty)
	convertArgs (NewDeclArg plic x t :: as) = do
		let (b, plics, mot) = convertArgs as
		(funHelper plic x t b, plic :: plics, consMotiveHelper x t mot)

--         Y8Y 8o  0 oYYYo YY8YY 8o  0  o8o   oYYo 8YYYY
-- ____     0  8Yo 8 %___    0   8Yo 8 8   8 0   " 8___
-- """"     0  8 Yo8 `"""p   0   8 Yo8 8YYY8 0   , 8"""
--         o8o 0   8 YoooY   0   0   8 0   0  YooY 8oooo

elabTermDecl (InstTermDef n preclauses) = do
	let aliasedName = the Term $ case n of
		Left n0 => Var (Name n0)
		Right (m0,n0) => DottedVar m0 n0
	(m',n') <- liftTC $ unalias n
	fs <- openFunctions
	case lookup (m',n') fs of
		Nothing => throw $ "No open function named " ++ show aliasedName ++ " has been declared."
		Just (ty,plics,mot,clauses) => do
			clauses' <- Traversable.for preclauses $ \(plics',(ps,xs,b)) => do
				case insertMetas plics plics' of
					Nothing => throw $ "Instance for open function " ++ show aliasedName ++
						" has invalid argument plicities."
					Just bs => pure $ clauseHelper (truePatterns bs ps) xs b
			let newClauses = clauses ++ clauses'
			let newDef = buildLambda (\xs => Case xs mot newClauses) plics
			let newOpenFunctions = ((m',n'),(ty,plics,mot,newClauses)) :: filter (\(p,_) => p /= (m',n')) fs
			newDef' <- liftTC $ extendDefinitions [((m',n'), newDef, ty)] (check newDef ty)
			putOpenFunctions newOpenFunctions
			defs <- definitions
			putDefinitions $ ((m',n'),newDef',ty) :: filter (\(p,_,_) => p /= (m',n')) defs
where
	insertMetas : List Plict -> List Plict -> Maybe (List Bool)
	insertMetas [] [] = Just []
	insertMetas (Expl :: args) (Expl :: plics) = do
		rest <- insertMetas args plics
		pure $ False :: rest
	insertMetas (Expl :: _) (Impl :: _) = Nothing
	insertMetas (Impl :: args) (Expl :: plics) = do
		rest <- insertMetas args plics
		pure $ True :: rest
	insertMetas (Impl :: args) (Impl :: plics) = do
		rest <- insertMetas args plics
		pure $ False :: rest
	insertMetas _ _ = Nothing

	truePatterns : List Bool -> List Pattern -> List Pattern
	truePatterns [] [] = []
	truePatterns (False :: plics) (p :: ps) = p :: truePatterns plics ps
	truePatterns (True :: plics) ps = MakeMeta :: truePatterns plics ps

-- 0   0  o8o  0    Y8Y 8888_  oYYo _YYY_ 8o  0 oYYYo Y8Y  oYYo
-- 0   0 8   8 0     0  0   0 0   " 0   0 8Yo 8 %___   0  0  __
-- "o o" 8YYY8 0     0  0   0 0   , 0   0 8 Yo8 `"""p  0  0  "8
--  "8"  0   0 8ooo o8o 8oooY  YooY "ooo" 0   8 YoooY o8o  YooY

validConSig : Constructor -> Constructor -> ConSig Term -> Elaborator ()
validConSig tycon c (ConSigNil (Con tc _)) = unless (tc == tycon) $
	throw $ "The constructor " ++ show c ++ " should constructor a value of the type " ++ show tycon
		++ " but instead produces a " ++ show tc
validConSig tycon c (ConSigNil a) = throw $
	"The constructor " ++ show c ++ " should constructor a value of the type " ++ show tycon
			++ " but instead produces " ++ show a
validConSig tycon c (ConSigCons _ _ sc) = validConSig tycon c (descope (Var . Name) sc)

-- 8YYYY 0     o8o  8888.  o8o  0    YY8YY
-- 8___  0    8   8 8___Y 8   8 0      0
-- 8"""  0    8YYY8 8"""o 8YYY8 0      0
-- 8oooo 8ooo 0   0 8ooo" 0   0 8ooo   0

elabAlt : String -> String -> ConSig Term -> Elaborator ()
elabAlt tycon c consig = do
	validConSig (BareCon tycon) (BareCon c) consig
	when' (typeInSignature (BareCon c))
		$ throw ("Constructor already declared: " ++ c)
	addAlias c
	consig' <- liftTC (checkifyConSig consig)
	addConstructor c consig'

-- 8YYYY 0     o8o  8888. Y8Y 8o  0 oYYYo YY8YY  o8o  8o  0  oYYo 8YYYY  o8o  0    YY8YY
-- 8___  0    8   8 8___Y  0  8Yo 8 %___    0   8   8 8Yo 8 0   " 8___  8   8 0      0
-- 8"""  0    8YYY8 8"""o  0  8 Yo8 `"""p   0   8YYY8 8 Yo8 0   , 8"""  8YYY8 0      0
-- 8oooo 8ooo 0   0 8ooo" o8o 0   8 YoooY   0   0   0 0   8  YooY 8oooo 0   0 8ooo   0

elabInstanceAlt : String -> Constructor -> String -> ConSig Term -> Elaborator ()
elabInstanceAlt m localTycon c consig = do
	validConSig localTycon (BareCon c) consig
	sig <- signature
	case lookup (m,c) sig of
		Just _ => throw ("Constructor already declared: " ++ c)
		Nothing => do
			addAliasFor (Left c) (m,c)
			consig' <- liftTC (checkifyConSig consig)
			addConstructorToModule m c consig'

-- 8YYYY 0     o8o  8888. YY8YY 0   0 8YYYo 8YYYY 8888_ 8YYYY  oYYo 0
-- 8___  0    8   8 8___Y   0   "o o" 8___P 8___  0   0 8___  0   " 0
-- 8"""  0    8YYY8 8"""o   0     0   8"""  8"""  0   0 8"""  0   , 0
-- 8oooo 8ooo 0   0 8ooo"   0     0   0     8oooo 8oooY 8oooo  YooY 8ooo

export elabTypeDecl : TypeDeclaration -> Elaborator ()

--         Y8Y 8o  0 8888_ 0   0  oYYo YY8YY Y8Y 0   0 8YYYY
-- ____     0  8Yo 8 0   0 0   0 0   "   0    0  0   0 8___
-- """"     0  8 Yo8 0   0 0   0 0   ,   0    0  "o o" 8"""
--         o8o 0   8 8oooY "ooo"  YooY   0   o8o  "8"  8oooo

elabTypeDecl (Inductive tycon tyconargs alts) = do
	let tyconSig = conSigHelper tyconargs Star
	when' (typeInSignature (BareCon tycon))
		$ throw ("Type constructor already declared: " ++ tycon)
	addAlias tycon
	tyconSig' <- liftTC (checkifyConSig tyconSig)
	addConstructor tycon tyconSig'
	traverse_ (uncurry (elabAlt tycon)) alts

--         8888_  o8o  YY8YY  o8o  8YYYY  o8o  8_   _8 Y8Y 0    0   0
-- ____    0   0 8   8   0   8   8 8___  8   8 8"o_o"8  0  0    "o o"
-- """"    0   0 8YYY8   0   8YYY8 8"""  8YYY8 0  8  0  0  0      0
--         8oooY 0   0   0   0   0 0     0   0 0     0 o8o 8ooo   0

elabTypeDecl (DataFamily tycon tyconargs) = do
	let tyconSig = conSigHelper tyconargs Star
	when' (typeInSignature (BareCon tycon))
		$ throw ("Type constructor already declared: " ++ tycon)
	addAlias tycon
	tyconSig' <- liftTC (checkifyConSig tyconSig)
	addConstructor tycon tyconSig'
	m <- moduleName
	od <- openData
	putOpenData ((m,tycon) :: od)

--         8888_  o8o  YY8YY  o8o  Y8Y 8o  0 oYYYo YY8YY  o8o  8o  0  oYYo 8YYYY
-- ____    0   0 8   8   0   8   8  0  8Yo 8 %___    0   8   8 8Yo 8 0   " 8___
-- """"    0   0 8YYY8   0   8YYY8  0  8 Yo8 `"""p   0   8YYY8 8 Yo8 0   , 8"""
--         8oooY 0   0   0   0   0 o8o 0   8 YoooY   0   0   0 0   8  YooY 8oooo

elabTypeDecl (DataInstance tycon alts) = do
	let aliasedName = case tycon of
						BareCon c => Left c
						DottedCon m c => Right (m,c)
	(m',c') <- liftTC $ unalias aliasedName
	od <- openData
	unless ((m',c') `elem` od)
		$ throw $ "The constructor " ++ show tycon ++ " is not an open data type."
	traverse_ (uncurry (elabInstanceAlt m' tycon)) alts

-- 8YYYY 0     o8o  8888. 8_   _8 _YYY_ 8888_ 0   0 0    8YYYY
-- 8___  0    8   8 8___Y 8"o_o"8 0   0 0   0 0   0 0    8___
-- 8"""  0    8YYY8 8"""o 0  8  0 0   0 0   0 0   0 0    8"""
-- 8oooo 8ooo 0   0 8ooo" 0     0 "ooo" 8oooY "ooo" 8ooo 8oooo

export elabModule : Module -> Elaborator ()
elabModule (NewModule m settings stmts0) = do
	addModuleName m
	putModuleName m
	ensureOpenSettingsAreValid settings
	als <- aliases
	sig <- signature
	defs <- definitions
	let newAls = newAliases sig defs settings ++ als
	putAliases newAls
	go stmts0
	putAliases als
where
	go : List Statement -> Elaborator ()
	go [] = pure ()
	go (TyDecl td :: stmts) = do
		elabTypeDecl td
		go stmts
	go (TmDecl td :: stmts) = do
		elabTermDecl td
		go stmts
