module TermLang.Env

import Effects
import Effect.Exception
import Effect.State
import Effect.StdIO

import TermLang.Syntax

public export
record TEnv where
	constructor NewTEnv
	index : Int
	env : Env
	ctxt : Context

public export
tEmpty : TEnv
tEmpty = NewTEnv 0 EvEmpty []

public export
TC : Type -> Type
TC a = Effects.SimpleEff.Eff a [EXCEPTION String, STATE TEnv, STDIO]