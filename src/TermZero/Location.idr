||| 
||| Location.idr
||| Created: Sun Mar 19 2017
||| Author:  Belleve Invis
||| 
||| Copyright (c) 2017 totalscript team
|||


module TermZero.Location

public export
data Location : Type where
	Unknown : Location
	Located : (filename : String) -> (line : Int) -> (column : Int) -> Location

public export
Show Location where
	show _ = ""

-- | Locations are always equal. This allows us to
-- derive equality for the abstract syntax that ignores
-- the locations.
public export
Eq Location where
	_ == _ = True

public export
locMessage : Location -> String
locMessage Unknown     = "<unknown>:"
locMessage (Located f l c) = concat [ f, ":", show l, ":", show c, ":"]

public export
interface GetLoc a where
	getLoc : a -> Location