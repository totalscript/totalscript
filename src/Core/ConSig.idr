module Core.ConSig

import General

import Debug.Error

import Core.Variable

%language ElabReflection


--  oYYo _YYY_ 8o  0 oYYYo Y8Y  oYYo
-- 0   " 0   0 8Yo 8 %___   0  0  __
-- 0   , 0   0 8 Yo8 `"""p  0  0  "8
--  YooY "ooo" 0   8 YoooY o8o  YooY

public export
data ConSig a = ConSigNil a | ConSigCons Plict a (Scope a (ConSig a))

partial export
showConSig : Show a => (String -> a) -> ConSig a -> String
showConSig _ (ConSigNil a) = show a
showConSig f (ConSigCons plic a sc) with (length (names sc) == 1)
	| True = do
		let a0' = unwords (names sc) ++ " : " ++ show a
		let a' = case plic of
			Expl => "(" ++ a0' ++ ") "
			Impl => "{" ++ a0' ++ "} "
		a' ++ showConSig f (instantiate sc (map f (names sc)))
showConSig _ _ = error "ConSigs should have exactly one scope argument."

export
conSigLength : (String -> a) -> ConSig a -> Int
conSigLength _ (ConSigNil _) = 0
conSigLength f (ConSigCons _ _ sc) = 1 + conSigLength f (instantiate sc (map f (names sc)))

public export
Signature : Type -> Type
Signature a = List (FullName, ConSig a)
