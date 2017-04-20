module Core.Program

import General

import Core.ConSig
import Core.Variable
import Core.Term

%access export


public export
ClauseDeclT : Type
ClauseDeclT = List Plict >< List Pattern >< List String >< Term

-- YY8YY 8YYYY 8YYYo 8_   _8 8888_ 8YYYY  oYYo 0
--   0   8___  8___P 8"o_o"8 0   0 8___  0   " 0
--   0   8"""  8""Yo 0  8  0 0   0 8"""  0   , 0
--   0   8oooo 0   0 0     0 8oooY 8oooo  YooY 8ooo

public export
data TermDeclaration
  = SimpleTermDef String Term Term
  | PatternTermDef String Term (List ClauseDeclT)
  | OpenTermDef String (List DeclArg) Term
  | InstTermDef (String \/ FullName) (List ClauseDeclT)
  | CloseTermDef (String \/ FullName)

showPattern : (Plict, Pattern) -> String
showPattern (Expl, p) = parenthesize (Just ExplConPatArg) p
showPattern (Impl, p) = parenthesize (Just ImplConPatArg) p

showPreclause : ClauseDeclT -> String
showPreclause (plics,(ps,_,b)) = interlace " || " (map showPattern (zip plics ps))
	++ " => " ++ show b

Show TermDeclaration where
	show (SimpleTermDef n ty def) = "define " ++ n ++ " : " ++ show ty ++ " = " ++ show def ++ " end"
	show (PatternTermDef n ty preclauses) = "define " ++ n ++ " : " ++ show ty ++ " where "
		++ interlace " | " (map showPreclause preclauses)
		++ " end"
	show (OpenTermDef n args ty) = "define family " ++ n ++ " " ++ unwords (map show args) ++ " : " ++ show ty ++ " end"
	show (InstTermDef n preclauses) = "define instance " ++ show n ++ " where "
		++ interlace " | " (map showPreclause preclauses)
	show (CloseTermDef n) = "%close " ++ show n

-- YY8YY 0   0 8YYYo 8YYYY 8888_ 8YYYY  oYYo 0
--   0   "o o" 8___P 8___  0   0 8___  0   " 0
--   0     0   8"""  8"""  0   0 8"""  0   , 0
--   0     0   0     8oooo 8oooY 8oooo  YooY 8ooo

-- Type Declarations
public export
data TypeDeclaration
  = Inductive String (List DeclArg) (List (String, ConSig Term))
  | DataFamily String (List DeclArg)
  | DataInstance Constructor (List (String, ConSig Term))

Show TypeDeclaration where
	show (Inductive tycon tyargs [])
		= "inductive " ++ tycon ++ concat (map (\x => " " ++ show x) tyargs) ++ " end"
	show (Inductive tycon tyargs alts)
		= "inductive " ++ tycon ++ concat (map (\x => " " ++ show x) tyargs) ++ " where"
			++ concat [ "\n" ++ c ++ " : " ++ showConSig (Var . Name) sig | (c,sig) <- alts ]
			++ "\nend"
	show (DataFamily tycon tyargs)
		= "data family " ++ tycon ++ concat (map (\x => " " ++ show x) tyargs) ++ " end"
	show (DataInstance tycon alts)
		= "data instance " ++ show tycon ++ " where"
			++ concat [ "\n" ++ c ++ " : " ++ showConSig (Var . Name) sig | (c,sig) <- alts ]
			++ "\nend"

-- oYYYo YY8YY  o8o  YY8YY 8YYYY 8_   _8 8YYYY 8o  0 YY8YY
-- %___    0   8   8   0   8___  8"o_o"8 8___  8Yo 8   0
-- `"""p   0   8YYY8   0   8"""  0  8  0 8"""  8 Yo8   0
-- YoooY   0   0   0   0   8oooo 0     0 8oooo 0   8   0

-- Programs
public export
data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

Show Statement where
	show (TyDecl td) = show td
	show (TmDecl td) = show td

public export
data HidingUsing
	= Hiding (List String)
	| Using (List String)

-- _YYY_ 8YYYo 8YYYY 8o  0 oYYYo 8YYYY YY8YY YY8YY Y8Y 8o  0  oYYo oYYYo
-- 0   0 8___P 8___  8Yo 8 %___  8___    0     0    0  8Yo 8 0  __ %___
-- 0   0 8"""  8"""  8 Yo8 `"""p 8"""    0     0    0  8 Yo8 0  "8 `"""p
-- "ooo" 0     8oooo 0   8 YoooY 8oooo   0     0   o8o 0   8  YooY YoooY

public export
record OpenSettings where
	constructor NewOpenSettings
	openModule : String
	openAs : Maybe String
	openHidingUsing : Maybe HidingUsing
	openRenaming : List FullName

Show OpenSettings where
	show (NewOpenSettings m a hu r) = m ++ a' ++ hu' ++ r'
	where
		a' = case a of
			Nothing => ""
			Just m' => " as " ++ m'
		hu' = case hu of
			Nothing => ""
			Just (Hiding ns) => " hiding (" ++ interlace "," ns ++ ")"
			Just (Using ns)  => " using (" ++ interlace "," ns ++ ")"
		r' = case r of
			[] => ""
			_ => " renaming (" ++ interlace ", " [ n ++ " to " ++ n' | (n,n') <- r ] ++ ")"

-- 8_   _8 _YYY_ 8888_ 0   0 0    8YYYY
-- 8"o_o"8 0   0 0   0 0   0 0    8___
-- 0  8  0 0   0 0   0 0   0 0    8"""
-- 0     0 "ooo" 8oooY "ooo" 8ooo 8oooo

public export
data Module = NewModule String (List OpenSettings) (List Statement)

Show Module where
	show (NewModule n [] stmts)
		= "module " ++ n ++ "\n\n" ++ interlace "\n\n" (map show stmts) ++ "\n\n"
	show (NewModule n settings stmts)
		= "module " ++ n ++ "\n\n" ++ interlace "\n" (map (("import " ++ ) . show) settings)
			++ "\n\n" ++ interlace "\n\n" (map show stmts) ++ "\n\n"
