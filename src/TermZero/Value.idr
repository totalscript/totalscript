||| 
||| Value.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.Value

import TermZero.Syntax
import TermZero.Environment

data Boxed : Type where
	MkBoxed : Closure Term -> Boxed

Eq Boxed where
	(MkBoxed a) == (MkBoxed b) = a == b

CLOSURE Boxed where
	getContext (MkBoxed c) = getContext c
	putContext (MkBoxed c) = MkBoxed . putContext c

mutual
	data Value = VNeutral Neutral
			| VUniv Int
			| VQ Quantifier  (Pair (Pair EType (Bind EType)) Context)
			| VLambda     (Bind (Closure Term))
			| VPair       (Closure (Pair Term Term))
			| VIPair      (Closure (Pair Term Term))
			| VEnum       (List Label)
			| VLabel       Label
			| VLift       (Closure EType)
			| VBox         Boxed
			| VRec        (Closure EType)
			| VFold       (Closure Term)
			| VEqual      (Closure (Pair Term Term))
			| VRefl       (Closure Term)
	

	data Neutral = NVar Index
				| NUndefined Index
				| NApp    Neutral (Closure Term)
				| NInst   Neutral (Closure Term)
				| NCase   Neutral (Closure $ List $ Pair Label Term)
				| NSplit  Neutral (Bind (Bind (Closure Term)))
				| NISplit Neutral (Bind (Bind (Closure Term)))
				| NForce  Neutral
				| NUnfold Neutral (Bind (Closure Term))
				| NEqElim Neutral (Bind (Closure Term))

	Eq Value where
		(VNeutral a0) == (VNeutral a1) = a0 == a1
		(VUniv a0) == (VUniv a1) = a0 == a1
		(VQ a0 b0) == (VQ a1 b1) = a0 == a1 && b0 == b1
		(VLambda a0) == (VLambda a1) = a0 == a1
		(VPair a0) == (VPair a1) = a0 == a1
		(VIPair a0) == (VIPair a1) = a0 == a1
		(VEnum a0) == (VEnum a1) = a0 == a1
		(VLabel a0) == (VLabel a1) = a0 == a1
		(VLift a0) == (VLift a1) = a0 == a1
		(VBox a0) == (VBox a1) = a0 == a1
		(VRec a0) == (VRec a1) = a0 == a1
		(VFold a0) == (VFold a1) = a0 == a1
		(VEqual a0) == (VEqual a1) = a0 == a1
		(VRefl a0) == (VRefl a1) = a0 == a1
		_ == _ = False
	
	Eq Neutral where
		(NVar a0) == (NVar a1) = a0 == a1
		(NUndefined a0) == (NUndefined a1) = a0 == a1
		(NApp a0 b0) == (NApp a1 b1) = a0 == a1 && b0 == b1
		(NInst a0 b0) == (NInst a1 b1) = a0 == a1 && b0 == b1
		(NCase a0 b0) == (NCase a1 b1) = a0 == a1 && b0 == b1
		(NSplit a0 b0) == (NSplit a1 b1) = a0 == a1 && b0 == b1
		(NISplit a0 b0) == (NISplit a1 b1) = a0 == a1 && b0 == b1
		(NForce a0) == (NForce a1) = a0 == a1
		(NUnfold a0 b0) == (NUnfold a1 b1) = a0 == a1 && b0 == b1
		(NEqElim a0 b0) == (NEqElim a1 b1) = a0 == a1 && b0 == b1
		_ == _ = False
