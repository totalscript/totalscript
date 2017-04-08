## Sample: flip tree and proof

```tts
inductive Tree : Type -> Type {
    Empty : Tree a
    Branch : a -> Tree a -> Tree a -> Tree a
}

flipTree : Tree a -> Tree a
flipTree Empty = Empty
flipTree (Branch x l r) = Branch x (flipTree r) (flipTree l)

flipTreeSym : (t : Tree a) -> t === flipTree (flipTree t)
flipTreeSym Empty = Refl
flipTreeSym (Branch x l r) = let (rl = flipTreeSym l) in
                             let (rr = flipTreeSym r) in
                             Equality.comm2 rl rr (l' => r' => Branch x l' r')
```

