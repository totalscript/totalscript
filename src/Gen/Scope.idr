module Gen.Scope

import Data.SortedMap
import Control.Monad.Identity
import Control.Monad.Reader

import Gen.Abs

public export
record Scope s a where
	constructor NewScope
	names : List String
	instantiate : List s -> a

export
abstractScope : Abstract i e a => Scope s a -> Abstracted i e (Scope s a)
abstractScope (NewScope ns f) = asks $ \e => NewScope ns $ \vs' => runIdentity $ runReaderT (abstr (f vs')) e

export
scope : Abstract String s a => List String -> a -> Scope s a
scope xs m = NewScope xs (abstractOver xs m)

export
scope2 : Abstract String s a => List String -> List String -> a -> Scope s a
scope2 xs xs' m = NewScope xs (abstractOver xs' m)

export
descope : (String -> s) -> Scope s a -> a
descope f sc = instantiate sc (map f (names sc))

export
Functor (Scope s) where
	map f (NewScope ns b) = NewScope ns (f . b)

export
helperFold : (a -> b -> b) -> List a -> b -> b
helperFold c xs n = foldr c n xs

export
isVar : String -> Bool
isVar s = (s == "_") || strHead s == '$'

export
removeByDummies : List String -> List a -> List a
removeByDummies ns xs = [ x | (n,x) <- zip ns xs, isVar n ]
