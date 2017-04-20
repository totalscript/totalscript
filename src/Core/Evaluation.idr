module Core.Evaluation

import General

import Core.Variable
import Core.Term

%access export

-- 8_   _8  o8o  YY8YY  oYYo 0   0 8YYYo  o8o  YY8YY YY8YY 8YYYY 8YYYo 8o  0 oYYYo
-- 8"o_o"8 8   8   0   0   " 8___8 8___P 8   8   0     0   8___  8___P 8Yo 8 %___
-- 0  8  0 8YYY8   0   0   , 8"""8 8"""  8YYY8   0     0   8"""  8""Yo 8 Yo8 `"""p
-- 0     0 0   0   0    YooY 0   0 0     0   0   0     0   8oooo 0   0 0   8 YoooY

mutual
	private matchPattern : Pattern -> Term -> Maybe (List Term)
	private matchPatterns : (List (Plict,Pattern)) -> (List (Plict,Term)) -> Maybe (List Term)
	private matchClauses : (List Clause) -> (List (Plict,Term)) -> Maybe Term

	matchPattern (VarPat _) v = Just [v]
	matchPattern (ConPat c ps) (Con c' as) with (c == c')
		| True = matchPatterns ps as
	matchPattern (AssertionPat _) _ = Just []
	matchPattern _ _ = Nothing

	matchPatterns [] [] = Just []
	matchPatterns ((plic,p) :: ps) ((plic',m) :: ms) with (plic == plic')
		| True = do
			vs <- matchPattern p m
			vs' <- matchPatterns ps ms
			pure $ vs ++ vs'
	matchPatterns _ _ = Nothing

-- 8_   _8  o8o  YY8YY  oYYo 0   0  oYYo 0     o8o  0   0 oYYYo 8YYYY oYYYo
-- 8"o_o"8 8   8   0   0   " 8___8 0   " 0    8   8 0   0 %___  8___  %___
-- 0  8  0 8YYY8   0   0   , 8"""8 0   , 0    8YYY8 0   0 `"""p 8"""  `"""p
-- 0     0 0   0   0    YooY 0   0  YooY 8ooo 0   0 "ooo" YoooY 8oooo YoooY

matchClauses [] _ = Nothing
matchClauses (NewClause psc sc :: cs) ms
	= case matchPatterns [ (Expl, p) | p <- descope Name psc ] ms of
		Nothing => matchClauses cs ms
		Just vs => Just (instantiate sc (removeByDummies (names psc) vs))

-- 8YYYY 0   0  o8o  0
-- 8___  0   0 8   8 0
-- 8"""  "o o" 8YYY8 0
-- 8oooo  "8"  0   0 8ooo

-- Standard Eager Evaluation
Eval (Environment FullName Term) Term where
	eval (Meta i) = pure $ Meta i
	eval (Var x) = pure $ Var x

	eval (DottedVar mdl var) = do
		env <- environment
		case lookup (mdl,var) env of
			Nothing => throw $ "Unknown constant/defined term: " ++ show (DottedVar mdl var)
			Just m  => eval m

	eval (AbsoluteDottedVar mdl var) = do
		env <- environment
		case lookup (mdl,var) env of
			Nothing => throw $ "Unknown constant/defined term: " ++ show (AbsoluteDottedVar mdl var)
			Just m  => eval m

	eval (Ann m _) = eval m
	eval Star = pure Star
	eval (Pi plic a sc) = pure $ Pi plic a sc
	eval (Lam plic sc) = pure $ Lam plic sc
	eval (App plic f a) = do
		ef <- eval f
		ea <- eval a
		case ef of
			Lam plic' sc => if (plic == plic')
				then eval (instantiate sc [ea])
				else pure $ App plic ef ea -- should not happen
			_ => pure $ App plic ef ea

	eval (Con c aas) = do
		eas <- Traversable.for aas $ \(plic, a) => do
			a' <- eval a
			pure (plic, a')
		pure $ Con c eas

	eval (Case ms mot cs) = do
		ems <- Traversable.for ms eval
		case matchClauses cs [ (Expl,em) | em <- ems ] of
			Nothing => if any (\p => case p of { (Con _ _) => False ; _ => True }) ems
				then pure (Case ms mot cs)
				else throw $ "Incomplete pattern match: " ++ show (Case ms mot cs)
			Just b  => eval b

	eval (RecordType tele) = pure $ RecordType tele

	eval (RecordCon fields) = RecordCon <$> sequence [ MkPair x <$> eval m | (x,m) <- fields ]

	eval (Project m x) = do
		em <- eval m
		case em of
			RecordCon fields => case lookup x fields of
				Nothing => throw $ "Unknown field '" ++ x ++ "' in record " ++ show (RecordCon fields)
				Just m' => pure m'
			m' => pure $ Project m' x
