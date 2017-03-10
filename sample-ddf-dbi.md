## Sample : DDF DBI

```tts
interface DBI (repr : Type -> Type -> Type) {
  z : repr (a >< h) a
  s : repr h b -> repr (a >< h) b
  lam : repr (a >< h) b -> repr h (a -> b)
  app : repr h (a -> b) -> repr h a -> repr h b
  mkprod : repr h (a -> b -> (a >< b))
  prodZro : repr h ((a >< b) -> a)
  prodFst : repr h ((a >< b) -> b)
  lit : Double -> repr h Double
  litZro : repr h Double
  litZro = lit 0
  litFst : repr h Double
  litFst = lit 1
  plus : repr h (Double -> Double -> Double)
  minus : repr h (Double -> Double -> Double)
  mult : repr h (Double -> Double -> Double)
  divide : repr h (Double -> Double -> Double)
  hoas : (repr (a >< h) a -> repr (a >< h) b) -> repr h (a -> b)
  hoas f = lam <| f z
  fix : repr h ((a -> a) -> a)
  left : repr h (a -> Either a b)
  right : repr h (b -> Either a b)
  sumMatch : repr h ((a -> c) -> (b -> c) -> Either a b -> c)
  unit : repr h ()
  exfalso : repr h (Void -> a)
  nothing : repr h (Maybe a)
  just : repr h (a -> Maybe a)
  optionMatch : repr h (b -> (a -> b) -> Maybe a -> b)
  ioRet : repr h (a -> IO a)
  ioBind : repr h (IO a -> (a -> IO b) -> IO b)
  nil : repr h (List a)
  cons : repr h (a -> List a -> List a)
  listMatch : repr h (b -> (a -> List a -> b) -> List a -> b)
}

record Eval (h : Type) (x : Type) { un : h -> x }

instance DBI Eval {
  z = new Eval fst
  s [a] = new Eval (a <. snd)
  lam [f] = new Eval <| a => h => f (h, a)
  app [f] [x] = new Eval <| h => f h (x h)
  ...
}

inductive AST : Type {
  Leaf : String -> AST
  App : String -> AST -> List AST -> AST
  Lam : String -> AST -> List AST -> AST
}

appAST : AST -> AST -> AST
appAST (Leaf f) x = App f x []
appAST (App f x l) r = App f x (l ++ [r])
appAST lam r = appAST (Leaf <| show lam) r

...

interface Diff (t : Type) { d : Type }
instance Diff Double   { d : (Double >< Double) }
instance Diff Unit     { d : Unit }
instance Diff (a -> b) { d : Diff a ~> Diff b }

record WDiff (repr : Type -> Type -> Type) (h : Type) (x : Type) {
  un : repr (Diff h).d (Diff x).d
}

interface NT (l : Type -> Type) (r : Type -> Type) {
  conv : l t -> r t
}
instance NT (repr l) (repr (a >< r)) | iD : DBI repr, iT : NT (repr l) (repr r) {
  conv = iD.s <. iT.conv
}

hlam :  {repr : Type -> Type; a, b, h : Type | DBI repr}
     -> (({k : Type -> Type | NT (repr (a >< h)) k} -> k a) -> repr (a >< h) b)
     -> repr h (a -> b)
-- this type is scary, but we have tactics
hlam = tactic {
  (repr,a,b,h) <- intros 4
  i_DBI_repr   <- intro
  f            <- intro
  apply i_DBI_repr.hoas
  -- ... |- repr (a >< h) a -> repr (a >< h) b
  x            <- intro
  -- ... |- repr (a >< h) b
  apply f
  -- ... |- {k : Type -> Type | NT (repr (a >< h)) k} -> k a
  k             <- intro
  i_NT_reprah_k <- intro
  -- ... |- k a
  apply i_NT_reprah_k.conv
  -- ... |- repr (a >< h) a
  exactly x
}

app2 : repr h (a -> b -> c) -> repr h a -> repr h b -> repr h c
app2 f a = app (app f a)

mkprod2 : repr h a -> repr h b -> repr h (a >< b)
mkprod2 = app2 mkprod
plus2 : repr h Double -> repr h Double -> repr h Double
plus2 = app2 plus
prodZro1 : repr h (a >< b) -> repr h a
prodZro1 = app prodZro
prodFst1 : repr h (a >< b) -> repr h b
prodFst1 = app prodFst

instance DBI (WDiff repr) | DBI repr {
  z = new WDiff z
  s [x] = new WDiff (s x)
  ...
  plus = tactic {
    intro; split
    apply hlam
    l <- intro
    apply hlam
    r <- intro
    apply mkprod2
    apply plus2
    apply prodZro1
    apply l; inst
    apply prodZro1
    apply r; inst
    apply plus2
    apply prodFst1
    apply l; inst
    apply prodFst1
    apply r; inst
  }
}
```

