module Core.Abstraction

import General
import Core.Variable
import Core.Term
import Core.ConSig

%access export

--  o8o  8888. oYYYo YY8YY 8YYYo  o8o   oYYo YY8YY Y8Y _YYY_ 8o  0 oYYYo
-- 8   8 8___Y %___    0   8___P 8   8 0   "   0    0  0   0 8Yo 8 %___
-- 8YYY8 8"""o `"""p   0   8""Yo 8YYY8 0   ,   0    0  0   0 8 Yo8 `"""p
-- 0   0 8ooo" YoooY   0   0   0 0   0  YooY   0   o8o "ooo" 0   8 YoooY

implementation Abstract a b c => Abstract a b (Plict,c) where
	abstr (plic,x) = MkPair plic <$> abstr x

implementation (Abstract a b Pattern, Abstract a b Term) => Abstract a b Clause where
	abstr (NewClause psc sc) = NewClause <$> abstractScope psc <*> abstractScope sc

implementation Abstract a b Term => Abstract a b CaseMotive where
	abstr (CaseMotiveNil a) = CaseMotiveNil <$> abstr a
	abstr (CaseMotiveCons a sc) = CaseMotiveCons <$> abstr a <*> abstractScope sc

implementation Abstract a b Term => Abstract a b Telescope where
	abstr TelescopeNil = pure TelescopeNil
	abstr (TelescopeCons t sc) = TelescopeCons <$> abstr t <*> abstractScope sc

mutual
	implementation Abstract String Term Term where
		abstr (Meta i) = pure $ Meta i
		abstr (Var (Name x)) = asks $ \e => case SortedMap.lookup x e of
			Nothing => Var (Name x)
			Just m  => m
		abstr (Var (Generated x i)) = pure $ Var (Generated x i)
		abstr (DottedVar m var) = pure $ DottedVar m var
		abstr (AbsoluteDottedVar m var) = pure $ AbsoluteDottedVar m var
		abstr (Ann m ty) = Ann <$> abstr m <*> pure ty
		abstr Star = pure Star
		abstr (Pi plic a sc) = Pi plic <$> abstr a <*> abstractScope sc
		abstr (Lam plic sc) = Lam plic <$> abstractScope sc
		abstr (App plic f a) = App plic <$> abstr f <*> abstr a
		abstr (Con c as) = Con c <$> Traversable.for as (\(plic, a) => do a' <- abstr a ; pure (plic,a'))
		abstr (Case as t cs) = Case <$> traverse abstr as <*> abstr t <*> traverse abstr cs
		abstr (RecordType tele) = RecordType <$> abstr tele
		abstr (RecordCon fields) = RecordCon <$> (sequence [ MkPair x <$> abstr m | (x,m) <- fields ])
		abstr (Project m x) = Project <$> abstr m <*> pure x

	implementation Abstract String Term Pattern where
		abstr (VarPat x) = pure $ VarPat x
		abstr (ConPat c ps) = ConPat c <$> traverse abstr ps
		abstr (AssertionPat m) = AssertionPat <$> abstr m
		abstr MakeMeta = pure MakeMeta

mutual
	implementation Abstract Int Term Term where
		abstr (Meta i) = pure $ Meta i
		abstr (Var (Name x)) = pure $ Var (Name x)
		abstr (Var (Generated x i)) = asks $ \e => case SortedMap.lookup i e of
			Nothing => Var (Generated x i)
			Just m  => m
		abstr (DottedVar m var) = pure $ DottedVar m var
		abstr (AbsoluteDottedVar m var) = pure $ AbsoluteDottedVar m var
		abstr (Ann m ty) = Ann <$> abstr m <*> pure ty
		abstr Star = pure Star
		abstr (Pi plic a sc) = Pi plic <$> abstr a <*> abstractScope sc
		abstr (Lam plic sc) = Lam plic <$> abstractScope sc
		abstr (App plic f a) = App plic <$> abstr f <*> abstr a
		abstr (Con c as) = Con c <$> Traversable.for as (\(plic,a) => do a' <- abstr a ; pure (plic,a'))
		abstr (Case as t cs) = Case <$> traverse abstr as <*> abstr t <*> traverse abstr cs
		abstr (RecordType tele) = RecordType <$> abstr tele
		abstr (RecordCon fields) = RecordCon <$> (sequence [ MkPair x <$> abstr m | (x,m) <- fields ])
		abstr (Project m x) = Project <$> abstr m <*> pure x

	implementation Abstract Int Term Pattern where
		abstr (VarPat x) = pure $ VarPat x
		abstr (ConPat c ps) = ConPat c <$> traverse abstr ps
		abstr (AssertionPat m) = AssertionPat <$> abstr m
		abstr MakeMeta = pure MakeMeta

mutual
	implementation Abstract String Variable Term where
		abstr (Meta i) = pure $ Meta i
		abstr (Var (Name x)) = asks $ \e => case SortedMap.lookup x e of
			Nothing => Var (Name x)
			Just y  => Var y
		abstr (Var (Generated x i)) = pure $ Var (Generated x i)
		abstr (DottedVar m var) = pure $ DottedVar m var
		abstr (AbsoluteDottedVar m var) = pure $ AbsoluteDottedVar m var
		abstr (Ann m ty) = Ann <$> abstr m <*> pure ty
		abstr Star = pure Star
		abstr (Pi plic a sc) = Pi plic <$> abstr a <*> abstractScope sc
		abstr (Lam plic sc) = Lam plic <$> abstractScope sc
		abstr (App plic f a) = App plic <$> abstr f <*> abstr a
		abstr (Con c as) = Con c <$> Traversable.for as (\(plic,a) => do a' <- abstr a ; pure (plic,a'))
		abstr (Case as t cs) = Case <$> traverse abstr as <*> abstr t <*> traverse abstr cs
		abstr (RecordType tele) = RecordType <$> abstr tele
		abstr (RecordCon fields) = RecordCon <$> (sequence [ MkPair x <$> abstr m | (x,m) <- fields ])
		abstr (Project m x) = Project <$> abstr m <*> pure x

	implementation Abstract String Variable Pattern where
		abstr (VarPat (Name x)) = asks $ \e => case SortedMap.lookup x e of
			Nothing => VarPat (Name x)
			Just y  => VarPat y
		abstr (VarPat (Generated x i)) = pure $ VarPat (Generated x i)
		abstr (ConPat c ps) = ConPat c <$> traverse abstr ps
		abstr (AssertionPat m) = AssertionPat <$> abstr m
		abstr MakeMeta = pure MakeMeta

mutual
	implementation Abstract Int Variable Term where
		abstr (Meta i) = pure $ Meta i
		abstr (Var (Name x)) = pure $ Var (Name x)
		abstr (Var (Generated x i)) = asks $ \e => case SortedMap.lookup i e of
			Nothing => Var (Generated x i)
			Just y  => Var y
		abstr (DottedVar m var) = pure $ DottedVar m var
		abstr (AbsoluteDottedVar m var) = pure $ AbsoluteDottedVar m var
		abstr (Ann m ty) = Ann <$> abstr m <*> pure ty
		abstr Star = pure Star
		abstr (Pi plic a sc) = Pi plic <$> abstr a <*> abstractScope sc
		abstr (Lam plic sc) = Lam plic <$> abstractScope sc
		abstr (App plic f a) = App plic <$> abstr f <*> abstr a
		abstr (Con c as) = Con c <$> Traversable.for as (\(plic,a) => do a' <- abstr a ; pure (plic,a'))
		abstr (Case as t cs) = Case <$> traverse abstr as <*> abstr t <*> traverse abstr cs
		abstr (RecordType tele) = RecordType <$> abstr tele
		abstr (RecordCon fields) = RecordCon <$> (sequence [ MkPair x <$> abstr m | (x,m) <- fields ])
		abstr (Project m x) = Project <$> abstr m <*> pure x

	implementation Abstract Int Variable Pattern where
		abstr (VarPat (Name x)) = pure $ VarPat (Name x)
		abstr (VarPat (Generated x i)) = asks $ \e => case SortedMap.lookup i e of
			Nothing => VarPat (Generated x i)
			Just y  => VarPat y
		abstr (ConPat c ps) = ConPat c <$> traverse abstr ps
		abstr (AssertionPat m) = AssertionPat <$> abstr m
		abstr MakeMeta = pure MakeMeta

-- 0   0 8YYYY 0    8YYYo 8YYYY 8YYYo oYYYo
-- 8___8 8___  0    8___P 8___  8___P %___
-- 8"""8 8"""  0    8"""  8"""  8""Yo `"""p
-- 0   0 8oooo 8ooo 0     8oooo 0   0 YoooY

funHelper : Plict -> String -> Term -> Term -> Term
funHelper plic x a b = Pi plic a (scope [x] b)

lamHelper : Plict -> String -> Term -> Term
lamHelper plic x b = Lam plic (scope [x] b)

clauseHelper : List Pattern -> List String -> Term -> Clause
clauseHelper ps xs b = do
	let cleanedXs = fst $ runState (traverse cleanXs xs) 0
	let cleanedPs = fst $ runState (traverse cleanPs ps) 0
	NewClause (scope2 xs cleanedXs cleanedPs) (scope (filter isVar xs) b)
where
	cleanXs : String -> State Integer String
	cleanXs "_" = do
		i <- get
		put (i + 1)
		pure $ "$" ++ show i
	cleanXs x = pure x

	cleanPs : Pattern -> State Integer Pattern
	cleanPs (VarPat (Name "_")) = do
		i <- get
		put (i + 1)
		pure $ VarPat (Name ("$" ++ show i))
	cleanPs (VarPat (Name n)) = pure $ VarPat (Name n)
	cleanPs (VarPat (Generated n i)) = pure $ VarPat (Generated n i)
	cleanPs (ConPat c ps') = ConPat c <$> traverse (\(plic,p) => do { p' <- cleanPs p ; pure (plic,p') }) ps'
	cleanPs (AssertionPat m) = pure $ AssertionPat m
	cleanPs MakeMeta = pure MakeMeta

consMotiveHelper : String -> Term -> CaseMotive -> CaseMotive
consMotiveHelper x a b = CaseMotiveCons a (scope [x] b)

telescopeHelper : List (String, Term) -> Telescope
telescopeHelper [] = TelescopeNil
telescopeHelper ((x,t)::xts) = let tele = telescopeHelper xts in TelescopeCons t (scope [x] tele)

implementation Abstract a Term Term => Abstract a Term (ConSig Term) where
	abstr (ConSigNil a) = ConSigNil <$> abstr a
	abstr (ConSigCons plic a sc) = ConSigCons plic <$> abstr a <*> abstractScope sc

conSigHelper : List DeclArg -> Term -> ConSig Term
conSigHelper [] b = ConSigNil b
conSigHelper (NewDeclArg plic x a :: as) b = ConSigCons plic a (scope [x] (conSigHelper as b))
