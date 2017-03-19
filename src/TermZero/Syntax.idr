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
data Quantifier = Pi | Sigma | PiImp | SigmaImp

public export
Show Quantifier where
	show Pi = "Pi"
	show Sigma = "Sigma"
	show PiImp = "Pi.Implicit"
	show SigmaImp = "Sigma.Implicit"

public export
Eq Quantifier where
	Pi == Pi = True
	Sigma == Sigma = True
	PiImp == PiImp = True
	SigmaImp == SigmaImp = True
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
				| ELet      Location Prog Term                    -- letrec :   let G in t ; G is a program, i.e. a sequence of delcarations x : T and possibly recursive definitions x = t
				| EUniv     Location Int                          -- universes
				| EQuant    Location Quantifier (Term, Bind Term) -- quantified
				| ELam      Location (Bind Term)                  -- x => t
				| EILam     Location (Bind Term)                  -- {x} => t
				| EApp      Term Term                             -- application : t u
				| EInst     Term Term                             -- application : t {u}
				| EPair     Location Term Term                    -- pairs : (t,u)
				| EIPair    Location Term Term                    -- pairs : ({t},u)
				| ESplit    Location Term (Bind (Bind Term))      -- Sigma elim : split t |% x => y => u
				| EISplit   Location Term (Bind (Bind Term))      -- Sigma elim : split t |% x => y => u
				| EEnum     Location (List Label)                 -- enumerations (finite types)
				| ELabel    Location Label                        -- labels
				| ECase     Location Term (List $ Pair Label Term)-- case t of { L1 => u1 | ... | L1 => un }
				| ELazy     Location Term                         -- Laziness
				| EDelay    Location Term                         -- delay (box) : %delay t
				| EForce    Location Term                         -- box opener : %force t
				| ERec      Location Term                         -- Rec T
				| EFold     Location Term                         -- fold t
				| EUnfold   Location Term (Bind Term)             -- unfold t |% x => u
				| EEquality Location Term Term                    -- x =%= y
				| ERefl     Location Term                         -- %Refl x
				| EEqElim   Location Term (Bind Term)             -- %eqelim t |% x => y
				| EUndefined Index
	
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
		(ELet _ p0 t0) == (ELet _ p1 t1) = p0 == p1 && t0 == t1
		(EUniv _ u0) == (EUniv _ u1) = u0 == u1
		(EQuant _ a0 b0) == (EQuant _ a1 b1) = a0 == a1 && b0 == b1
		(ELam _ (x0, t0)) == (ELam _ (x1, t1)) = x0 == x1 && t0 == t1
		(EILam _ (x0, t0)) == (EILam _ (x1, t1)) = x0 == x1 && t0 == t1
		(EApp a0 b0) == (EApp a1 b1) = a0 == a1 && b0 == b1
		(EInst a0 b0) == (EInst a1 b1) = a0 == a1 && b0 == b1
		(EPair _ a0 b0) == (EPair _ a1 b1) = a0 == a1 && b0 == b1
		(EIPair _ a0 b0) == (EIPair _ a1 b1) = a0 == a1 && b0 == b1
		(ESplit _ a0 b0) == (ESplit _ a1 b1) = a0 == a1 && b0 == b1
		(EISplit _ a0 b0) == (EISplit _ a1 b1) = a0 == a1 && b0 == b1
		(EEnum _ a0) == (EEnum _ a1) = a0 == a1
		(ELabel _ a0) == (ELabel _ a1) = a0 == a1
		(ECase _ a0 b0) == (ECase _ a1 b1) = a0 == a1 && b0 == b1
		(ELazy _ a0) == (ELazy _ a1) = a0 == a1
		(EDelay _ a0) == (EDelay _ a1) = a0 == a1
		(EForce _ a0) == (EForce _ a1) = a0 == a1
		(ERec _ a0) == (ERec _ a1) = a0 == a1
		(EFold _ a0) == (EFold _ a1) = a0 == a1
		(EUnfold _ a0 b0) == (EUnfold _ a1 b1) = a0 == a1 && b0 == b1
		(EEquality _ a0 b0) == (EEquality _ a1 b1) = a0 == a1 && b0 == b1
		(ERefl _ a0) == (ERefl _ a1) = a0 == a1
		(EEqElim _ a0 b0) == (EEqElim _ a1 b1) = a0 == a1 && b0 == b1
		(EUndefined a0) == (EUndefined a1) = a0 == a1
		_ == _ = False

export
GetLoc Term where
	getLoc (EVar    l _  ) = l
	getLoc (ELet    l _ _) = l
	getLoc (EUniv   l _) = l
	getLoc (EQuant  l _ _) = l
	getLoc (ELam    l _  ) = l
	getLoc (EILam   l _  ) = l
	getLoc (EApp    t _) = getLoc t
	getLoc (EInst   t _) = getLoc t
	getLoc (EPair  l _ _) = l
	getLoc (EIPair  l _ _) = l
	getLoc (ESplit  l _ _) = l
	getLoc (EISplit l _ _) = l
	getLoc (EEnum   l _  ) = l
	getLoc (ELabel  l _  ) = l
	getLoc (ECase   l _ _) = l
	getLoc (ELazy   l _  ) = l
	getLoc (EDelay  l _  ) = l
	getLoc (EForce  l _  ) = l
	getLoc (ERec    l _  ) = l
	getLoc (EFold   l _  ) = l
	getLoc (EUnfold l _ _) = l
	getLoc (EEquality l _ _) = l
	getLoc (EEqElim l _ _) = l
	getLoc (ERefl l _) = l