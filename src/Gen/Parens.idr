module Gen.Parens

public export
interface ParenLoc a where
	Loc : Type
	parenLoc : a -> List Loc

public export
interface ParenRec a where
	parenRec : a -> String

export
parenthesize : (ParenLoc a, ParenRec a, Eq (Loc {a})) =>  Maybe (Loc {a}) -> a -> String
parenthesize l x =
	let rec = parenRec x
	in case l of
		Nothing => rec
		Just loc => if (loc `elem` parenLoc x) then rec else "(" ++ rec ++ ")"

record InstrlaceR a where
	constructor NewInterlaceR
	init : Bool
	acc : a

export interlace : (Monoid a, Foldable f) => a -> f a -> a
interlace sep list = acc $ foldl go (NewInterlaceR True neutral) list
where
	go : InstrlaceR a -> a -> InstrlaceR a
	go (NewInterlaceR True _) x = NewInterlaceR False x
	go (NewInterlaceR False y) x = NewInterlaceR False (y <+> sep <+> x)

export hcat : (Monoid a, Foldable f) => f a -> a
hcat list = interlace neutral list
