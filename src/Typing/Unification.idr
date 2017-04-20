module Typing.Unification

import Typing.Common
import Typing.Util
import Typing.Equate

-- oYYYo _YYY_ 0    0   0 8YYYY
-- %___  0   0 0    0   0 8___
-- `"""p 0   0 0    "o o" 8"""
-- YoooY "ooo" 8ooo  "8"  8oooo

solve : List Equation -> TypeChecker Substitution
solve eqs0 = go eqs0 []
where
	go : List Equation -> Substitution -> TypeChecker Substitution

	go [] subs' = pure subs'

	go ((Meta x ~~ Meta y) :: eqs) subs' with (x == y)
		| True = go eqs subs'
		| False = do
			eqs' <- traverse (evalWithSubs ((x, Meta y)::subs')) eqs
			go eqs' ((x, Meta y)::subs')

	go ((Meta x ~~ t2) :: eqs) subs' = do
		unless (not (occurs x t2))
			$ throw $ "Cannot unify because " ++ show (Meta x)
				++ " occurs in " ++ show t2
		eqs' <- traverse (evalWithSubs ((x,t2) :: subs')) eqs
		go eqs' ((x,t2) :: subs')

	go ((t1 ~~ Meta y) :: eqs) subs' = do
		unless (not (occurs y t1))
			$ throw $ "Cannot unify because " ++ show (Meta y)
				++ " occurs in " ++ show t1
		eqs' <- traverse (evalWithSubs ((y,t1) :: subs')) eqs
		go eqs' ((y,t1) :: subs')

	go ((Var x ~~ Var y) :: eqs) subs' = do
		unless (x == y)
			$ throw $ "Cannot unify variables " ++ show (Var x)
				++ " and " ++ show (Var y)
		go eqs subs'

	go ((DottedVar m1 x1 ~~ DottedVar m2 x2) :: eqs) subs' = do
		unless (m1 == m2 && x1 == x2)
			$ throw $ "Cannot unify symbols " ++ show (DottedVar m1 x1)
				++ " and " ++ show (DottedVar m2 x2)
		go eqs subs'

	go ((AbsoluteDottedVar m1 x1 ~~ AbsoluteDottedVar m2 x2) :: eqs) subs' = do
		unless (m1 == m2 && x1 == x2)
			$ throw $ "Cannot unify symbols " ++ show (AbsoluteDottedVar m1 x1)
				++ " and " ++ show (AbsoluteDottedVar m2 x2)
		go eqs subs'
	go ((Ann m1 t1 ~~ Ann m2 t2) :: eqs) subs' = go ((m1 ~~ m2) :: (t1 ~~ t2) :: eqs) subs'

	go ((Star ~~ Star) :: eqs) subs' = go eqs subs'

	go ((Pi plic1 a1 sc1 ~~ Pi plic2 a2 sc2) :: eqs) subs' = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (Pi plic1 a1 sc1) ++ " with "
						++ show (Pi plic2 a2 sc2)
		i <- newName
		case (head' (names sc1), head' (names sc2)) of
			(Just h1, Just h2) => do
				let b1 = instantiate sc1 [Var (Generated h1 i)]
				let b2 = instantiate sc2 [Var (Generated h2 i)]
				go ((a1 ~~ a2) :: (b1 ~~ b2) :: eqs) subs'
			_ => throw "should not happen"

	go ((Lam plic1 sc1 ~~ Lam plic2 sc2) :: eqs) subs' = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (Lam plic1 sc1) ++ " with "
						++ show (Lam plic2 sc2)
		i <- newName
		case (head' (names sc1), head' (names sc2)) of
			(Just h1, Just h2) => do
				let b1 = instantiate sc1 [Var (Generated h1 i)]
				let b2 = instantiate sc2 [Var (Generated h2 i)]
				go ((b1 ~~ b2) :: eqs) subs'
			_ => throw "should not happen"

	go ((App plic1 f1 a1 ~~ App plic2 f2 a2) :: eqs) subs' = do
		unless (plic1 == plic2)
			$ throw $ "Mismatched plicities when trying to unify "
						++ show (App plic1 f1 a1) ++ " with "
						++ show (App plic2 f2 a2)
		-- we should not assume all functions are injective
		-- so we will drop this equation simply, and check whether all
		-- holes are filled afterwards
		-- go ((f1 ~~ f2) :: (a1 ~~ a2) :: eqs) subs'
		go eqs subs'

	go ((Con c1 as1 ~~ Con c2 as2) :: eqs) subs' = do
		unless (c1 == c2)
			$ throw $ "Mismatching constructors " ++ show c1 ++ " and " ++ show c2
		unless (length as1 == length as2)
			$ throw $ "Mismatching number of arguments in "
						++ show (Con c1 as1) ++ " and "
						++ show (Con c2 as2)
		eqs' <- zipConArgs as1 as2
		go (eqs' ++ eqs) subs'
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

	go ((Case as1 mot1 cs1 ~~ Case as2 mot2 cs2) :: eqs) subs' = do
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
		go (argEqs ++ motEqs ++ clauseEqs ++ eqs) subs'

	go ((RecordType tele1 ~~ RecordType tele2) :: eqs) subs' = do
		eqs' <- compareTelescope tele1 tele2
		go (eqs' ++ eqs) subs'

	go ((RecordCon fields1 ~~ RecordCon fields2) :: eqs) subs' = do
		eqs' <- compareFields fields1 fields2
		go (eqs' ++ eqs) subs'

	go ((Project m1 x1 ~~ Project m2 x2) :: eqs) subs' = do
		unless (x1 == x2)
			$ throw $ "Field names not equal: " ++ x1 ++ " and " ++ x2
		go ((m1 ~~ m2) :: eqs) subs'

	go ((m ~~ m') :: _) _ = throw $ "Terms not equal: " ++ show m ++ " and " ++ show m'

export
addSubstitutions : Substitution -> TypeChecker ()
addSubstitutions subs0 = do
	completeSubstitution subs0
	substituteContext
where
	completeSubstitution : Substitution -> TypeChecker ()
	completeSubstitution subs' = do
		subs <- substitution
		let subs2 = subs' ++ subs
		let subs2' = nubBy (\(a,_) => \(b,_) => a == b) (map (\(k,v) => (k, instantiateMetas subs2 v)) subs2)
		putSubstitution subs2'
	substituteContext : TypeChecker ()
	substituteContext = do
		ctx <- context
		subs <- substitution
		let ctx' = map (instCtx subs) ctx
		putContext ctx'
	where
		instCtx : Substitution -> ContextEntry -> ContextEntry
		instCtx subs (i, x, t) = (i, x, instantiateMetas subs t)


-- 0   0 8o  0 Y8Y 8YYYY 0   0
-- 0   0 8Yo 8  0  8___  "o o"
-- 0   0 8 Yo8  0  8"""    0
-- "ooo" 0   8 o8o 0       0

export
unify : Term -> Term -> TypeChecker ()
unify p q = do
	subs <- solve [p ~~ q]
	equate [p ~~ q] subs
	addSubstitutions subs
