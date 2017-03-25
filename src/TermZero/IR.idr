||| 
||| IR.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.IR
import TermZero.Calculus
import TermZero.Location

public export
data JImplicitiness = JExplicit | JImplicit

export
Eq JImplicitiness where
	JExplicit == JExplicit = True
	JImplicit == JImplicit = True
	_         == _        = False

public export
data ELiteral : Type where
	LInt : Int -> ELiteral
	LFloat : Double -> ELiteral
	LString : String -> ELiteral

export
Eq ELiteral where
	(LInt a) == (LInt b) = a == b
	(LFloat a) == (LFloat b) = a == b
	(LString a) == (LString b) = a == b
	_ == _ = False

public export
data Term : Type where
	EVar      : Location -> Name -> Term
	ELit      : Location -> ELiteral -> Term
	EUniv     : Location -> Nat -> Term
	-- letrec
	ELetRec   : Location -> (List (Name, Term, Term)) -> Term -> Term
	-- Pi
	EPi       : Location -> Name -> Term -> Term -> Term
	ELam      : Location -> Name -> Term -> Term
	EApp      : Location -> Term -> Term -> Term
	-- Sigma
	ESigma    : Location -> Name -> Term -> Term -> Term
	EPair     : Location -> Term -> Term -> Term
	ESplit    : Location -> Term -> Name -> Name -> Term -> Term
	-- Finite types
	EFinite   : Location -> (List Label) -> Term
	ELabel    : Location -> Label -> Term
	ECases    : Location -> Term -> (List $ Pair Label Term) -> Term
	-- Laziness
	EInf      : Location -> Term -> Term
	EDelay    : Location -> Term -> Term
	EForce    : Location -> Term -> Term
	-- Recurison
	ERec      : Location -> Term -> Term
	ERoll     : Location -> Term -> Term
	EUnroll   : Location -> Term -> Term
	-- Equality
	EEquality : Location -> Term -> Term -> Term
	ERefl     : Location -> Term -> Term
	EEqElim   : Location -> Term -> Name -> Term -> Term
	-- Holes
	EHole     : Location -> Index -> Term

export
Var Term where
	var = EVar Unknown

export
Universe Term where
	univ = EUniv Unknown

export
Literal Term where
	lInt = ELit Unknown . LInt
	lFloat = ELit Unknown . LFloat
	lString = ELit Unknown . LString

export
LetRec Term where
	letrec = ELetRec Unknown

export
Pi Term where
	pi = EPi Unknown
	lam = ELam Unknown
	app = EApp Unknown

export
Sigma Term where
	sigma = ESigma Unknown
	pair = EPair Unknown
	split = ESplit Unknown

export
Finite Term where
	finite = EFinite Unknown
	label = ELabel Unknown
	cases = ECases Unknown

export
Recurison Term where
	rec = ERec Unknown
	roll = ERoll Unknown
	unroll = EUnroll Unknown

export
CInf Term where
	inf = EInf Unknown
	delay = EDelay Unknown
	force = EForce Unknown

export
Equality Term where
	equality = EEquality Unknown
	refl = ERefl Unknown
	eqElim = EEqElim Unknown


-- We do not add "letrec" into Term — they will be handled separately.
public export
Eq Term where
	(EVar _ n0) == (EVar _ n1) = n0 == n1
	(ELit _ n0) == (ELit _ n1) = n0 == n1
	(ELetRec _ p0 t0) == (ELetRec _ p1 t1) = p0 == p1 && t0 == t1
	(EUniv _ u0) == (EUniv _ u1) = u0 == u1
	(EPi _ a0 b0 c0) == (EPi _ a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(ELam _ a0 b0) == (ELam _ a1 b1) = a0 == a1 && b0 == b1
	(EApp _ a0 b0) == (EApp _ a1 b1) = a0 == a1 && b0 == b1
	(ESigma _ a0 b0 c0) == (ESigma _ a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(EPair _ a0 b0) == (EPair _ a1 b1) = a0 == a1 && b0 == b1
	(ESplit _ a0 b0 c0 d0) == (ESplit _ a1 b1 c1 d1) = a0 == a1 && b0 == b1 && c0 == c1 && d0 == d1
	(EFinite _ a0) == (EFinite _ a1) = a0 == a1
	(ELabel _ a0) == (ELabel _ a1) = a0 == a1
	(ECases _ a0 b0) == (ECases _ a1 b1) = a0 == a1 && b0 == b1
	(EInf _ a0) == (EInf _ a1) = a0 == a1
	(EDelay _ a0) == (EDelay _ a1) = a0 == a1
	(EForce _ a0) == (EForce _ a1) = a0 == a1
	(ERec _ a0) == (ERec _ a1) = a0 == a1
	(ERoll _ a0) == (ERoll _ a1) = a0 == a1
	(EUnroll _ a0) == (EUnroll _ a1) = a0 == a1
	(EEquality _ a0 b0) == (EEquality _ a1 b1) = a0 == a1 && b0 == b1
	(ERefl _ a0) == (ERefl _ a1) = a0 == a1
	(EEqElim _ a0 b0 c0) == (EEqElim _ a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(EHole _ a0) == (EHole _ a1) = a0 == a1
	_ == _ = False

export
GetLoc Term where
	getLoc (EVar    l _  ) = l
	getLoc (EUniv   l _) = l
	getLoc (ELetRec l _ _) = l
	getLoc (EPi     l _ _ _) = l
	getLoc (ELam    l _ _) = l
	getLoc (EApp    l _ _) = l
	getLoc (ESigma  l _ _ _) = l
	getLoc (EPair   l _ _) = l
	getLoc (ESplit  l _ _ _ _) = l
	getLoc (EFinite l _  ) = l
	getLoc (ELabel  l _  ) = l
	getLoc (ECases  l _ _) = l
	getLoc (EInf   l _  ) = l
	getLoc (EDelay  l _  ) = l
	getLoc (EForce  l _  ) = l
	getLoc (ERec    l _  ) = l
	getLoc (ERoll   l _  ) = l
	getLoc (EUnroll l _) = l
	getLoc (EEquality l _ _) = l
	getLoc (ERefl l _) = l
	getLoc (EEqElim l _ _ _) = l
	getLoc (EHole l _) = l
	getLoc _ = Unknown
