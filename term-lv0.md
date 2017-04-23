# Term 0 proposal

1. The entire program is separated into multiple **frames**.
2. Each frame would be either a **inductive**, or a **function**.
3. Declarations within same frame can mutually recurse.
4. An **inductive** is...
5. A **function** corresponds a name, a type and a term. The type is an `expr` while the term is a **case tree** corresponds to a series of terms.

Example.

```
begin-frame

interfaces
condef Vect Nat Type : Type
condef Nil (auto a : Type) : Vect Z a
condef Cons (auto a : Type) (auto m : Nat) a (Vect m a) : Vect (S m) a
close inductive Vect = Nil; Cons
term append : (auto a : Type) -> (auto m : Nat) -> (auto n : Nat) ->
	Vect m a -> Vect n a -> Vect (m + n) a

implementation
append = intro auto a => {
  intro auto m => {
    intro auto n => {
      split car {
        [Nil ~a'] => intro cdr => cdr
        [Cons ~a' ~m' car' cdr'] => intro cdr =>
          Cons @a @(m' + n) car' (append @a @m' @n cdr' cdr)
      }
    }
  }
}

end-frame
```

The **case tree** is defined as:

```idris
-- tn for binding type; tm for term type
data CaseTree tn tm where
    Simply : tm -> CaseTree tn tm
    Intro : Plict -> tn -> tm -> CaseTree tn tm -> CaseTree tn tm
    Split : Plict -> tn -> tm -> -- plicity, binder, parameter type
        List (ConPattern tn , CaseTree tn tm) -> -- branches
        CaseTree tn tm
```

