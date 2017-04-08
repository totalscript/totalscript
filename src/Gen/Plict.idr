module Gen.Plict

public export
data Plict = Expl | Impl

export
Eq Plict.Plict where
	Expl == Expl = True
	Impl == Impl = True
	_    == _    = False

export
Show Plict.Plict where
	show Expl = "<Explicit>"
	show Impl = "<Implicit>"
