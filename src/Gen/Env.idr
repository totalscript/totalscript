module Gen.Env

public export
Environment : Type -> Type -> Type
Environment i a = List $ Pair i a

