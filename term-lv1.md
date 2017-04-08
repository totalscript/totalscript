## Term language, level 1

### Lexical

- Names can contain hyphens (`-`).
- Other literals follow common languages.
- Strings are encoded in Unicode code points. Byte sequence is `Bytes`.
- Boolean: `&&`, `||`, `!` vs Proposition: `\/`, `/\`, `~`.

### Notation for types

- Sorts: `Type`, `Prop` and `Interface`. All of them are `Kind`. `Kind` is `Kind2`, `Kind2` is `Kind3`, ...
- Pi :
  - Dependent : `(x : T) -> y` for explicit parameter. `{x : T} -> y` for implicit.
  - Simple : `T -> y` and `{T} -> y`.
- Sigma :
  - Dependent : `(x : T) >< (y : P x) >< z`.
  - Simple : `x >< y >< z`.
- Interface constraints : `(a | I a) -> b`,  `{a | I a} -> T a` or `{a : ...} -> {b : ...} -> {I a b} -> F a b`.
  - `(a | I b) -> b` is a shorthand for `(a : ...) -> {I a} -> b`.
  - You can actually omit `{a : ...} -> ` in some patterns, so `{I a} -> b`.
  - Multiple interfaces : `(a | Num a; Show a) -> b`, `{Num a; Show a} -> b`.
  - Also for Sigma: `(a : T | I a) >< b` = `(a : T) >< (I a) >< b`.

### Notation for terms

- Lambda : `(x : T) => y`, or `x => y` if type of `x` can be inferred. `{x : T} => y` for implicit parameters.
- Sigma : `(a, b, c)`.
- Points, `a.b`, are:
  - If `a` is a module → return exported term `b` in module `a`.
    - Module of current file is denoted as `exports`.
  - If `a` is an inductive type → return constructor/eliminator `b`, like `Equal.Refl`.
    - Eliminators are denoted as `Type.$elim`.
  - If `a` is a record or instance → return member `b`.
  - If `a` is a record type → return extractor, i.e. `x => x.b`.
  - If `a` is an interface → return overloaded function, i.e. `{t : Type} => {m : a t} => (x : t) => m.b x`.
- `<|` and `|>` for piping, while `<.` and `.>` for composition.
- Explicit instantiate : `@{terms}`, `@{name = term; name = term}`.
- Pattern matching : `match n { when Z : Z; when (S x) : S <| S <| x + x }`.
  - Also Haskell-style definitions.
  - Pattern for records: `[a, b, c, d]` (positional) or `[x = a, y = b]` (nominal).
  - Quote whole argument: `(list | Cons head rear)`.
- Do blocks : `do {x <- monad; y = plain; monad}`.
  - `do {x <- m; y}` = `m >>= (x => y)`
  - `do {x; y}` = `m >>= (_ => y)`
  - `do {x}` = `x`
  - `do {x = v; y}` = `let x = v in do { y }`
- Tactic blocks : `proof { x <- intro; exact x }`, similar to `do` but more complex (not discussed here).

### Notation for modules

- Importing : `import pattern from "location"`.
  - Import members : `import [Ring, Group] from "algebra"`.
  - Import all public members: `import * from "algebra"`.
  - Import as whole : `import as Algebra from "algebra"`.
  - Location → Resolved in the Node.js manner.
- Exporting :
  - Export type : `export x : A.`
  - Export type and definition : `export public x : A`.
  - Export other modules: `export as M from "loc"`, `export [a, b, c] from "loc"` , `export * from "loc"`.
- Totality markers : `theorem`, `total` and `lemma` would force a declaration total.
- Operators : Declared as an alias of a term, `operator * 500 left = multiply`; `operator - prefix = negate`.
  - These are NON-operators: `->`, `<-`, `=>`, `><`, `<|`, `|>`, `<.`, `.>`, `:`, `=`, `;` and `|-`.

### Inductive declaration

```
inductive Equal : {t : Type} -> t -> t -> Prop {
    Refl : t -> Equal t t
}
operator === 300 non-assoc = Equal
-- Eliminator is defined as Equal.$elim
```

### Record Declaration

```
record Identity : (a : Type) -> Type {
    it : a
}
-- constructor, new Identity, is implicitly defined as
new Identity : {a : Type} -> a -> Identity a
-- Identity.it is defined as
Identity.it : {a : Type} -> Identity a -> a
Identity.it (new Identity x) = x

-- usage
instance Functor Identity {
    map fn x = new Identity (fn x.it)
}
instance Applicative Identity {
    pure x = new Identity x
    f <*> g = new Identity (f.it g.it)
}
instance Monad Identity {
    x >>= k = k (x.it)
}
```

### Interface and Instance

```
-- canonical declaration
record VerifiedFunctor : (f : Type -> Type) -> {Functor f} -> Interface {
    identity : {a : Type} -> (x : f a) -> Functor.map id x === id x
    dist     : {a, b : Type} -> (x : f a) -> (g1, g2: a -> b)
               -> map (g2 <. g1) x === (map g2 <. map g1) x
}
-- convinent declaration
interface VerifiedFunctor (f | Functor f) {
    ...
}
-- canonical instance
vf_Maybe : VerifiedFunctor Maybe = new (VerifiedFunctor Maybe) {
    identity x = match x {
        when Nothing : Refl
        when (Just _) : Refl
    }
    dist x g1 g2 = match x {
        when Nothing : Refl
        when (Just _) : Refl
    }
}
-- convinent instance
instance VerifiedFunctor Maybe { ... }
```

### Polymorphic Functions

```
--- Tensor multplication
operator <&> 700 right = tensorMult
tensorMult : {Num a} -> Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) (w1 * w2) a
tensorMult m1 m2 = zipwith (\&\) (step1 m1 m2) (step2 m1 m2)
where {
    step1 : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w1 a
    step1 @{h2} m1 m2 = concat <| map (replicate h2) m1
    step2 : Matrix h1 w1 a -> Matrix h2 w2 a -> Matrix (h1 * h2) w2 a
    step2 @{h1} m1 m2 = concat <| replicate h1 m2
}
```

