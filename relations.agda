module relations where

  data Total' {A : Set} (_R_ : A -> A -> Set) (x y : A) : Set where
    forward : x R y -> Total' _R_ x y
    flipped : y R x -> Total' _R_ x y

  data Total {A : Set} (_R_ : A -> A -> Set) : Set where
    totality : (∀ x y -> Total' _R_ x y) -> Total _R_
