module Gen.Common

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
