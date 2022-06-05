module natParity where

  open import equality
  open import nats

  data even : ℕ -> Set
  data odd : ℕ -> Set

  data even where
    zero-even : even zero
    succ-even : ∀ {n} -> odd n -> even n

  data odd where
    succ-odd : ∀ {n} -> even n -> odd n

  e+e=e : forall {x y} -> even x -> even y -> even (x + y)
  o+e=o : forall {x y} -> odd x  -> even y -> odd  (x + y)

  e+e=e  zero-even     ey = ey
  e+e=e (succ-even ox) ey = succ-even (o+e=o ox ey)

  o+e=o (succ-odd ex)  ey = succ-odd (e+e=e ex ey)

  o+o=e : forall {x y} -> odd x -> odd y -> even (x + y)
  o+o=e (succ-odd ex) (succ-odd ey) = e+e=e ex ey
