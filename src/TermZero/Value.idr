||| 
||| Value.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.Value

import TermZero.Syntax
import Data.SortedMap

public export
data Judgement : Type -> Type where
	BType  : b -> Judgement b
	BValue : b -> Judgement b
	BHole  : b -> Judgement b
	BGuess : b -> Judgement b

public export
Environment : Type -> Type
Environment b = SortedMap Index (Judgement b)

public export
Context : Type
Context = List $ Pair Name Index

public export
Closure : Type -> Type
Closure a = Pair a Context

mutual
	-- WHNF value of TTS
	public export
	data Value  = VVar Index
				| VLit Literal
				| VUniv Int
				| VQ (Quantifier $ Closure Value) (Closure Value)
				| VApp JImplicitiness Value (Closure Value)
				| VPair JImplicitiness Value (Closure Value)
				| VFinite (List Label)
				| VLabel Label
				| VInf Value
				| VDelay Value
				| VRec Value
				| VFold Value
				| VEquality Value Value
				| VRefl Value
	
	export
	Eq Value where
		(VVar a0) == (VVar a1) = a0 == a1
		(VLit a0) == (VLit a1) = a0 == a1
		(VUniv a0) == (VUniv a1) = a0 == a1
		(VQ a0 b0) == (VQ a1 b1) = a0 == a1 && b0 == b1
		(VApp a0 b0 c0) == (VApp a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
		(VPair a0 b0 c0) == (VPair a1 b1 c1) = a0 == a1 && b0 == b1 && c0 == c1
		(VFinite a0) == (VFinite a1) = a0 == a1
		(VLabel a0) == (VLabel a1) = a0 == a1
		(VInf a0) == (VInf a1) = a0 == a1
		(VDelay a0) == (VDelay a1) = a0 == a1
		(VRec a0) == (VRec a1) = a0 == a1
		(VFold a0) == (VFold a1) = a0 == a1
		(VEquality a0 b0) == (VEquality a1 b1) = a0 == a1 && b0 == b1
		(VRefl a0) == (VRefl a1) = a0 == a1
		_ == _ = False
