||| 
||| Syntax.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.Syntax
import TermZero.Location

public export
Name : Type
Name = String

public export
Index : Type
Index = Int

public export
data JImplicitiness = JExplicit | JImplicit

export
Eq JImplicitiness where
	JExplicit == JExplicit = True
	JImplicit == JImplicit = True
	_         == _        = False

public export
data Literal : Type where
	LInt : Int -> Literal
	LFloat : Double -> Literal
	LString : String -> Literal

export
Eq Literal where
	(LInt a) == (LInt b) = a == b
	(LFloat a) == (LFloat b) = a == b
	(LString a) == (LString b) = a == b
	_ == _ = False

public export
data Quantifier : Type -> Type where
	Pi     : Name -> b -> JImplicitiness -> Quantifier b
	Lam    : Name -> b -> JImplicitiness -> Quantifier b
	Sigma  : Name -> b -> JImplicitiness -> Quantifier b
	Hole   : Index -> b -> Quantifier b
	Guess  : Index -> b -> b -> Quantifier b

export
Eq b => Eq (Quantifier b) where
	(Pi a0 b0 c0) == (Pi a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(Lam a0 b0 c0) == (Lam a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(Sigma a0 b0 c0) == (Sigma a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	(Hole a0 b0) == (Hole a1 b1) = a0 == a1 && b0 == b1
	(Guess a0 b0 c0) == (Guess a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
	_ == _ = False

public export
Bind : Type -> Type
Bind a = Pair Name a

public export
Label : Type
Label = String

mutual
	public export
	data ProgramEntry : Type where
		Decl : Location -> Name -> Term -> ProgramEntry
		Defn : Location -> Name -> Term -> ProgramEntry
	
	public export
	Prog : Type
	Prog = List ProgramEntry

	public export
	data Term   = EVar      Location Name                         -- variables
				| ELit      Location Literal                      -- literals
				| ELet      Location Prog Term                    -- letrec :   let G in t ; G is a program, i.e. a sequence of delcarations x : T and possibly recursive definitions x = t
				| EUniv     Location Int                          -- universes
				| EQ        Location (Quantifier Term) Term       -- quantified
				| EApp      JImplicitiness Term Term              -- application : t u / t {u}
				| EPair     Location JImplicitiness Term Term     -- pairs : (t,u) / ({t}, u)
				| ESplit    Location Term (Bind (Bind Term))      -- Sigma elim : split t |% x => y => u
				-- Finite types
				| EFinite   Location (List Label)                 -- enumerations (finite types)
				| ELabel    Location Label                        -- labels
				| ECase     Location Term (List $ Pair Label Term)-- case t of { L1 => u1 | ... | L1 => un }
				-- Laziness
				| EInf      Location Term                         -- Laziness
				| EDelay    Location Term                         -- delay (box) : %delay t
				| EForce    Location Term                         -- box opener : %force t
				-- Recurison
				| ERec      Location Term                         -- Rec T
				| EFold     Location Term                         -- fold t
				| EUnfold   Location Term (Bind Term)             -- unfold t |% x => u
				-- Equality
				| EEquality Location Term Term                    -- x =%= y
				| ERefl     Location Term                         -- %Refl x
				| EEqElim   Location Term (Bind Term)             -- %eqelim t |% x => y
				-- Holes
				| EHole     Location Index
	
	public export
	EType : Type
	EType = Term

	public export
	Eq ProgramEntry where
		(Decl _ n0 t0) == (Decl _ n1 t1) = n0 == n1 && t0 == t1
		(Defn _ n0 t0) == (Defn _ n1 t1) = n0 == n1 && t0 == t1
		_ == _ = False

	public export
	Eq Term where
		(EVar _ n0) == (EVar _ n1) = n0 == n1
		(ELit _ n0) == (ELit _ n1) = n0 == n1
		(ELet _ p0 t0) == (ELet _ p1 t1) = p0 == p1 && t0 == t1
		(EUniv _ u0) == (EUniv _ u1) = u0 == u1
		(EQ _ a0 b0) == (EQ _ a1 b1) = a0 == a1 && b0 == b1
		(EApp a0 b0 c0) == (EApp a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
		(EPair _ a0 b0 c0) == (EPair _ a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
		(ESplit _ a0 b0) == (ESplit _ a1 b1) = a0 == a1 && b0 == b1
		(EFinite _ a0) == (EFinite _ a1) = a0 == a1
		(ELabel _ a0) == (ELabel _ a1) = a0 == a1
		(ECase _ a0 b0) == (ECase _ a1 b1) = a0 == a1 && b0 == b1
		(EInf _ a0) == (EInf _ a1) = a0 == a1
		(EDelay _ a0) == (EDelay _ a1) = a0 == a1
		(EForce _ a0) == (EForce _ a1) = a0 == a1
		(ERec _ a0) == (ERec _ a1) = a0 == a1
		(EFold _ a0) == (EFold _ a1) = a0 == a1
		(EUnfold _ a0 b0) == (EUnfold _ a1 b1) = a0 == a1 && b0 == b1
		(EEquality _ a0 b0) == (EEquality _ a1 b1) = a0 == a1 && b0 == b1
		(ERefl _ a0) == (ERefl _ a1) = a0 == a1
		(EEqElim _ a0 b0) == (EEqElim _ a1 b1) = a0 == a1 && b0 == b1
		(EHole _ a0) == (EHole _ a1) = a0 == a1
		_ == _ = False

export
GetLoc Term where
	getLoc (EVar    l _  ) = l
	getLoc (ELet    l _ _) = l
	getLoc (EUniv   l _) = l
	getLoc (EQ      l _ _) = l
	getLoc (EApp    _ t _) = getLoc t
	getLoc (EPair   l _ _ _) = l
	getLoc (ESplit  l _ _) = l
	getLoc (EFinite l _  ) = l
	getLoc (ELabel  l _  ) = l
	getLoc (ECase   l _ _) = l
	getLoc (EInf   l _  ) = l
	getLoc (EDelay  l _  ) = l
	getLoc (EForce  l _  ) = l
	getLoc (ERec    l _  ) = l
	getLoc (EFold   l _  ) = l
	getLoc (EUnfold l _ _) = l
	getLoc (EEquality l _ _) = l
	getLoc (EEqElim l _ _) = l
	getLoc (ERefl l _) = l
	getLoc (EHole l _) = l
	