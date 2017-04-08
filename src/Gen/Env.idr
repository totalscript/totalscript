module Gen.Env

public export
Environment : Type -> Type -> Type
Environment i a = List $ Pair i a

infixr 3 /\
public export
(/\) : Type -> Type -> Type
(/\) = Pair

infixr 3 ><
public export
(><) : Type -> Type -> Type
(><) = Pair

infixr 2 \/
public export
(\/) : Type -> Type -> Type
(\/) = Either
