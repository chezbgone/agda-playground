module natRels where
  open import equality
  open import nats
  open import relations

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : ∀ {n} -> zero ≤ n
    s≤s : ∀ {m n} -> m ≤ n -> succ m ≤ succ n

  s≤s-inversion : ∀ {m n} -> succ m ≤ succ n → m ≤ n
  s≤s-inversion (s≤s le) = le

  n≤z-inversion : ∀ {m} -> m ≤ zero → m ≡ zero
  n≤z-inversion z≤n = refl

  ≤-refl : ∀ {n} -> n ≤ n
  ≤-refl {zero}   = z≤n
  ≤-refl {succ n} = s≤s ≤-refl

  ≤-trans : ∀ {n m p} -> n ≤ m -> m ≤ p -> n ≤ p
  ≤-trans  z≤n       _        = z≤n
  ≤-trans (s≤s n≤m) (s≤s m≤p) = s≤s (≤-trans n≤m m≤p)

  ≤-antisymm : ∀ {n m} -> n ≤ m -> m ≤ n -> n ≡ m
  ≤-antisymm  z≤n       z≤n      = refl
  ≤-antisymm (s≤s n≤m) (s≤s m≤n) = cong succ (≤-antisymm n≤m (m≤n))

  ≤-total'-succ : ∀ {x y} -> Total' _≤_ x y -> Total' _≤_ (succ x) (succ y)
  ≤-total'-succ (forward rel) = forward (s≤s rel)
  ≤-total'-succ (flipped rel) = flipped (s≤s rel)

  ≤-total' : ∀ x y -> Total' _≤_ x y
  ≤-total' zero y = forward z≤n
  ≤-total' (succ x) zero = flipped z≤n
  ≤-total' (succ x) (succ y) = ≤-total'-succ (≤-total' x y)

  ≤-total : Total _≤_
  ≤-total = totality ≤-total'

  
