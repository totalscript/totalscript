## Term language, level 0

Main ideas:

1. Pi : `(x : T) -> y` or `{x : T} -> y`.

2. Sigma : `(x : T) >< y` or `{x : T} >< y`.

3. Finite types for tagging : `%Finite {%tag1, %tag2, ...}`.

    1. Matches only works on Finites.

4. Primitive equality, `a =!= b` and `%refl`.

5. Inductives are encoded as sigma and cases:
    ```
    inductive Vec : Nat -> Type -> Type {
        Nil : Vec 0 a
        Cons : a -> Vec n a -> Vec (S n) a
    }

    encoded into

    Vec : Nat -> Type -> Type
    Vec = n => a => (label : %Finite {%nil, %cons}) >< match label {
        when %nil  : 0 =!= n
        when %cons : (n' : Nat) >< {(S n') =!= n} >< a >< Vec A n'
    }
    Cons : (a : Type) -> (n : Nat) -> a -> Vec n a -> Vec (S n) a
    Cons = a => n => car => cdr => (%cons, n, %refl (S n), car, cdr)
    ```

6. Applications : `x y` for explicit Pi, `x @y` for implicit Pi.

7. Records are unrolled into Sigmas.

8. Recursive terms must be introduced explicitly.

