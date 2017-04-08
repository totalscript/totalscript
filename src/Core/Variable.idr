module Core.Variable

--              0   0  o8o  8YYYo Y8Y  o8o  8888. 0    8YYYY
-- ____ ____    0   0 8   8 8___P  0  8   8 8___Y 0    8___
-- """" """"    "o o" 8YYY8 8""Yo  0  8YYY8 8"""o 0    8"""
--               "8"  0   0 0   0 o8o 0   0 8ooo" 8ooo 8oooo

public export
data Variable = Name String | Generated String Int

export
implementation Interfaces.Eq Variable where
	(Name x) == (Name y)               = x == y
	(Generated _ i) == (Generated _ j) = i == j
	_ == _                             = False

export
implementation Show Variable where
	show (Name x) = x
	show (Generated x _) = x

-- 8YYYY 0   0 0    0    8o  0  o8o  8_   _8 8YYYY
-- 8___  0   0 0    0    8Yo 8 8   8 8"o_o"8 8___
-- 8"""  0   0 0    0    8 Yo8 8YYY8 0  8  0 8"""
-- 0     "ooo" 8ooo 8ooo 0   8 0   0 0     0 8oooo

public export
FullName : Type
FullName = Pair String String
