module Gen.Env

import Data.SortedMap

||| An Environment is a correspondence between "key" and "value" type
public export
Environment : Type -> Type -> Type
Environment i a = SortedMap i a
-- Environment i a = List $ Pair i a
