module Unification.Equate

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

import LTerm.TCUtil

-- 8YYYY _YYY_ 0   0  o8o  YY8YY Y8Y _YYY_ 8o  0
-- 8___  0 _ 8 0   0 8   8   0    0  0   0 8Yo 8
-- 8"""  0 "%8 0   0 8YYY8   0    0  0   0 8 Yo8
-- 8oooo "oooo "ooo" 0   0   0   o8o "ooo" 0   8

infix 4 ~~
public export
data Equation = (~~) Term Term

-- _YYY_  oYYo  oYYo 0   0 8YYYo oYYYo
-- 0   0 0   " 0   " 0   0 8___P %___
-- 0   0 0   , 0   , 0   0 8""Yo `"""p
-- "ooo"  YooY  YooY "ooo" 0   0 YoooY

export
occurs : MetaVar -> Term -> Bool
occurs x (Meta y)         = x == y
occurs _ (Var _)          = False
occurs _ (DottedVar _ _)  = False
occurs _ (AbsoluteDottedVar _ _)
                          = False
occurs x (Ann m t)        = occurs x m || occurs x t
occurs _ Star             = False
occurs x (Pi _ a sc)     = occurs x a || occurs x (descope (Var . Name) sc)
occurs x (Lam _ sc)       = occurs x (descope (Var . Name) sc)
occurs x (App _ f a)      = occurs x f || occurs x a
occurs x (Con _ as)       = any (occurs x . snd) as
occurs x (Case as mot cs) = any (occurs x) as || occursCaseMotive mot || any occursClause cs
where
	occursCaseMotive : CaseMotive -> Bool
	occursClause : Clause -> Bool
	occursPattern : Pattern -> Bool

	occursCaseMotive (CaseMotiveNil m) = occurs x m
	occursCaseMotive (CaseMotiveCons a sc)
		= occurs x a || occursCaseMotive (descope (Var . Name) sc)

	occursClause (NewClause psc sc) = any occursPattern (descope Name psc) || occurs x (descope (Var . Name) sc)

	occursPattern (VarPat _) = False
	occursPattern (ConPat _ xs) = any (occursPattern . snd) xs
	occursPattern (AssertionPat m) = occurs x m
	occursPattern MakeMeta = False
occurs x (RecordType tele)  = occursTelescope tele
where
	occursTelescope : Telescope -> Bool
	occursTelescope TelescopeNil = False
	occursTelescope (TelescopeCons t sc) = occurs x t || occursTelescope (descope (Var . Name) sc)
occurs x (RecordCon fields) = any (occurs x . snd) fields
occurs x (Project m _)    = occurs x m

export
evalWithSubs : Substitution -> Equation -> TypeChecker Equation
evalWithSubs subs (l ~~ r) = do
	l' <- evaluate (instantiateMetas subs l)
	r' <- evaluate (instantiateMetas subs r)
	pure (l' ~~ r')

--  oYYo _YYY_ 8_   _8 8YYYo  o8o  8YYYo 8YYYY  oYYo  o8o  oYYYo 8YYYY 8_   _8 _YYY_ YY8YY Y8Y 0   0 8YYYY
-- 0   " 0   0 8"o_o"8 8___P 8   8 8___P 8___  0   " 8   8 %___  8___  8"o_o"8 0   0   0    0  0   0 8___
-- 0   , 0   0 0  8  0 8"""  8YYY8 8""Yo 8"""  0   , 8YYY8 `"""p 8"""  0  8  0 0   0   0    0  "o o" 8"""
--  YooY "ooo" 0     0 0     0   0 0   0 8oooo  YooY 0   0 YoooY 8oooo 0     0 "ooo"   0   o8o  "8"  8oooo

export
compareCaseMotive : CaseMotive -> CaseMotive -> TypeChecker (List Equation)
compareCaseMotive (CaseMotiveNil a1) (CaseMotiveNil a2) = pure [(a1 ~~ a2)]
compareCaseMotive (CaseMotiveCons a1 sc1) (CaseMotiveCons a2 sc2) = do
	i <- newName {s=TCState}
	case (head' (names sc1), head' (names sc2)) of
		(Just h1, Just h2) => do
			reqs <- compareCaseMotive
				(instantiate sc1 [Var (Generated h1 i)])
				(instantiate sc2 [Var (Generated h2 i)])
			pure ((a1 ~~ a2) :: reqs)
		_ => throw "Should not happen"
compareCaseMotive mot mot' = throw $ "Motives not equal: " ++ show mot ++ " and " ++ show mot'

--  oYYo _YYY_ 8_   _8 8YYYo  o8o  8YYYo 8YYYY     oYYo 0     o8o  0   0 oYYYo 8YYYY
-- 0   " 0   0 8"o_o"8 8___P 8   8 8___P 8___     0   " 0    8   8 0   0 %___  8___
-- 0   , 0   0 0  8  0 8"""  8YYY8 8""Yo 8"""     0   , 0    8YYY8 0   0 `"""p 8"""
--  YooY "ooo" 0     0 0     0   0 0   0 8oooo     YooY 8ooo 0   0 "ooo" YoooY 8oooo

export
compareClauses : List Clause -> List Clause -> TypeChecker (List Equation)
export
comparePattern : Pattern -> Pattern -> TypeChecker (List Equation)
export
comparePatterns : List (Plict,Pattern) -> List (Plict,Pattern) -> TypeChecker (List Equation)


compareClauses [] [] = pure []
compareClauses (NewClause psc1 sc1::cs1) (NewClause psc2 sc2::cs2) = do
	unless (length (names psc1) == length (names psc2))
		$ throw "Patterns bind different numbers of arguments."
	is <- replicateM (length (names psc1)) $ newName
	let xs1 = zipWith Generated (names psc1) is
	let xs1' = map Var (removeByDummies (names psc1) xs1)
	let xs2 = zipWith Generated (names psc2) is
	let xs2' = map Var (removeByDummies (names psc2) xs2)
	reqss <- zipWithM comparePattern (instantiate psc1 xs1) (instantiate psc2 xs2)
	reqs' <- compareClauses cs1 cs2
	pure ((instantiate sc1 xs1' ~~ instantiate sc2 xs2') :: concat reqss ++ reqs')
compareClauses _ _ = throw $ "Mismatching number of clauses."



comparePattern (VarPat x) (VarPat x') = do
	unless (x == x')
		$ throw $ "Variable patters not equal: " ++ show x ++ " and " ++ show x'
	pure []
comparePattern (ConPat c ps) (ConPat c' ps') with (c == c')
	| True  = comparePatterns ps ps'
	| False = throw $ "Mismatching constructors " ++ show c ++ " and " ++ show c'
comparePattern _ _ = throw "Patterns not equal."



comparePatterns [] [] = pure []
comparePatterns ((plic1,p1)::ps1) ((plic2,p2)::ps2) = do
	unless (plic1 == plic2)
		$ throw "Mismatched plicities when trying to unify constructor sequences."
	eqs <- comparePattern p1 p2
	eqs' <- comparePatterns ps1 ps2
	pure $ eqs ++ eqs'
comparePatterns _ _ = throw "Patterns not equal."

--  oYYo _YYY_ 8_   _8 8YYYo  o8o  8YYYo 8YYYY YY8YY 8YYYY 0    8YYYY oYYYo  oYYo _YYY_ 8YYYo 8YYYY
-- 0   " 0   0 8"o_o"8 8___P 8   8 8___P 8___    0   8___  0    8___  %___  0   " 0   0 8___P 8___
-- 0   , 0   0 0  8  0 8"""  8YYY8 8""Yo 8"""    0   8"""  0    8"""  `"""p 0   , 0   0 8"""  8"""
--  YooY "ooo" 0     0 0     0   0 0   0 8oooo   0   8oooo 8ooo 8oooo YoooY  YooY "ooo" 0     8oooo

export
compareTelescope : Telescope -> Telescope -> TypeChecker (List Equation)
compareTelescope TelescopeNil TelescopeNil = pure []
compareTelescope (TelescopeCons t1 sc1) (TelescopeCons t2 sc2) = do
	unless (names sc1 == names sc2)
		$ throw $ "Mismatching record field names: " ++ unwords (names sc1) ++ " and " ++ unwords (names sc2)
	eqs' <- compareTelescope (descope (Var . Name) sc1) (descope (Var . Name) sc2)
	pure ((t1 ~~ t2) :: eqs')
compareTelescope _ _ = throw "Mismatched number of record fields."

--  oYYo _YYY_ 8_   _8 8YYYo  o8o  8YYYo 8YYYY 8YYYY Y8Y 8YYYY 0    8888_ oYYYo
-- 0   " 0   0 8"o_o"8 8___P 8   8 8___P 8___  8___   0  8___  0    0   0 %___
-- 0   , 0   0 0  8  0 8"""  8YYY8 8""Yo 8"""  8"""   0  8"""  0    0   0 `"""p
--  YooY "ooo" 0     0 0     0   0 0   0 8oooo 0     o8o 8oooo 8ooo 8oooY YoooY

export
compareFields : List (String,Term) -> List (String,Term) -> TypeChecker (List Equation)
compareFields [] [] = pure []
compareFields (_ :: _) [] = throw "Mismatching number of record fields."
compareFields [] (_ :: _) = throw "Mismatching number of record fields."
compareFields ((x,m)::xms) xms' = case extract (\(x',_) => x == x') xms' of
	Nothing      => throw "Mismatching record field names."
	Just ((_,m'),xms'') => do
		eqs' <- compareFields xms xms''
		pure ((m ~~ m') :: eqs')

-- 8YYYY _YYY_ 0   0  o8o  YY8YY 8YYYY
-- 8___  0 _ 8 0   0 8   8   0   8___
-- 8"""  0 "%8 0   0 8YYY8   0   8"""
-- 8oooo "oooo "ooo" 0   0   0   8oooo

export
equate : List Equation -> Substitution -> TypeChecker ()
equate eqs0 subs = go eqs0
where
	go : List Equation -> TypeChecker ()

	go [] = pure ()

	go ((Meta x ~~ Meta y) :: eqs) with (x == y)
		| True = go eqs
		| False = do
			eqs' <- traverse (evalWithSubs subs) eqs
			go eqs'

	go ((Meta x ~~ t2) :: eqs) = do
		unless (not (occurs x t2))
			$ throw $ "Cannot unify because " ++ show (Meta x)
				++ " occurs in " ++ show t2
		eqs' <- traverse (evalWithSubs subs) eqs
		go eqs'

	go ((t1 ~~ Meta y) :: eqs) = do
		unless (not (occurs y t1))
			$ throw $ "Cannot unify because " ++ show (Meta y)
				++ " occurs in " ++ show t1
		eqs' <- traverse (evalWithSubs subs) eqs
		go eqs'

	go ((Var x ~~ Var y) :: eqs) = do
		unless (x == y)
			$ throw $ "Cannot unify variables " ++ show (Var x)
				++ " and " ++ show (Var y)
		go eqs

	go ((DottedVar m1 x1 ~~ DottedVar m2 x2) :: eqs) = do
		unless (m1 == m2 && x1 == x2)
			$ throw $ "Cannot unify symbols " ++ show (DottedVar m1 x1)
				++ " and " ++ show (DottedVar m2 x2)
		go eqs

	go ((AbsoluteDottedVar m1 x1 ~~ AbsoluteDottedVar m2 x2) :: eqs) = do
		unless (m1 == m2 && x1 == x2)
			$ throw $ "Cannot unify symbols " ++ show (AbsoluteDottedVar m1 x1)
				++ " and " ++ show (AbsoluteDottedVar m2 x2)
		go eqs

	go ((Ann m1 t1 ~~ Ann m2 t2) :: eqs) = go ((m1 ~~ m2) :: (t1 ~~ t2) :: eqs)

	go ((Star ~~ Star) :: eqs) = go eqs

	go ((Pi plic1 a1 sc1 ~~ Pi plic2 a2 sc2) :: eqs) = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (Pi plic1 a1 sc1) ++ " with "
						++ show (Pi plic2 a2 sc2)
		i <- newName
		case (head' (names sc1), head' (names sc2)) of
			(Just h1, Just h2) => do
				let b1 = instantiate sc1 [Var (Generated h1 i)]
				let b2 = instantiate sc2 [Var (Generated h2 i)]
				go ((a1 ~~ a2) :: (b1 ~~ b2) :: eqs)
			_ => throw "should not happen"

	go ((Lam plic1 sc1 ~~ Lam plic2 sc2) :: eqs) = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (Lam plic1 sc1) ++ " with "
						++ show (Lam plic2 sc2)
		i <- newName
		case (head' (names sc1), head' (names sc2)) of
			(Just h1, Just h2) => do
				let b1 = instantiate sc1 [Var (Generated h1 i)]
				let b2 = instantiate sc2 [Var (Generated h2 i)]
				go ((b1 ~~ b2) :: eqs)
			_ => throw "should not happen"

	go ((App plic1 f1 a1 ~~ App plic2 f2 a2) :: eqs) = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (App plic1 f1 a1) ++ " with "
						++ show (App plic2 f2 a2)
		go ((f1 ~~ f2) :: (a1 ~~ a2) :: eqs)

	go ((Con c1 as1 ~~ Con c2 as2) :: eqs) = do
		unless (c1 == c2) $ throw $ "Mismatching constructors " ++ show c1 ++ " and " ++ show c2
		unless (length as1 == length as2) $ throw $ "Mismatching number of arguments in "
			++ show (Con c1 as1) ++ " and "
			++ show (Con c2 as2)
		eqs' <- zipConArgs as1 as2
		go (eqs' ++ eqs)
	where
		zipConArgs : List (Plict, Term) -> List (Plict, Term) -> TypeChecker (List Equation)
		zipConArgs [] [] = pure []
		zipConArgs ((plic1',a1')::as1') ((plic2',a2')::as2') = if plic1' == plic2'
				then do
					eqs' <- zipConArgs as1' as2'
					pure $ (a1' ~~ a2') :: eqs'
				else
					throw "Mismatching plicity."
		zipConArgs _ _ = throw "Mismatching number of arguments."

	go ((Case as1 mot1 cs1 ~~ Case as2 mot2 cs2) :: eqs) = do
		unless(length as1 == length as2)
			$ throw $ "Mismatching number of case arguments in "
						++ show (Case as1 mot1 cs1) ++ " and "
						++ show (Case as2 mot2 cs2)
		unless (length cs1 == length cs2)
			$ throw $ "Mismatching number of clauses in "
						++ show (Case as1 mot1 cs1) ++ " and "
						++ show (Case as2 mot2 cs2)
		let argEqs = zipWith (~~) as1 as2
		motEqs <- compareCaseMotive mot1 mot2
		clauseEqs <- compareClauses cs1 cs2
		go (argEqs ++ motEqs ++ clauseEqs ++ eqs)

	go ((RecordType tele1 ~~ RecordType tele2) :: eqs) = do
		eqs' <- compareTelescope tele1 tele2
		go (eqs' ++ eqs)

	go ((RecordCon fields1 ~~ RecordCon fields2) :: eqs) = do
		eqs' <- compareFields fields1 fields2
		go (eqs' ++ eqs)

	go ((Project m1 x1 ~~ Project m2 x2) :: eqs) = do
		unless (x1 == x2) $ throw $ "Field names not equal: " ++ x1 ++ " and " ++ x2
		go ((m1 ~~ m2) :: eqs)

	go ((m ~~ m') :: _) = throw $ "Terms not equal: " ++ show m ++ " and " ++ show m'
