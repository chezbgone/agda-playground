module natRels where
  open import equality
  open import nats
  open import relations

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : ∀ {n} -> zero ≤ n
    s≤s : ∀ {m n} -> m ≤ n -> succ m ≤ succ n
  infix 4 _≤_

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

  ≤-total' : ∀ x y -> Total' _≤_ x y
  ≤-total' zero y = forward z≤n
  ≤-total' (succ x) zero = flipped z≤n
  ≤-total' (succ x) (succ y) = ≤-total'-succ (≤-total' x y)
    where
    ≤-total'-succ : ∀ {x y} -> Total' _≤_ x y -> Total' _≤_ (succ x) (succ y)
    ≤-total'-succ (forward rel) = forward (s≤s rel)
    ≤-total'-succ (flipped rel) = flipped (s≤s rel)

  ≤-total : Total _≤_
  ≤-total = totality ≤-total'

  ≤-+l-mono : ∀ {m n p : ℕ} → m ≤ n → p + m ≤ p + n
  ≤-+l-mono {p = zero} m≤n = m≤n
  ≤-+l-mono {p = succ p} m≤n = s≤s (≤-+l-mono m≤n)

  ≤-+r-mono : ∀ {m n p : ℕ} → m ≤ n → m + p ≤ n + p
  ≤-+r-mono {m} {n} {p} m≤n
    rewrite +-commutative m p
          | +-commutative n p
    = ≤-+l-mono m≤n

  ≤-+mono : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
  ≤-+mono m≤n p≤q = ≤-trans (≤-+r-mono m≤n) (≤-+l-mono p≤q)

  ≤-*l-mono : ∀ {m n : ℕ} p → m ≤ n → p * m ≤ p * n
  ≤-*l-mono zero m≤n = z≤n
  ≤-*l-mono (succ p) m≤n = ≤-+mono m≤n (≤-*l-mono p m≤n)

  ≤-*r-mono : ∀ {m n p : ℕ} → m ≤ n → m * p ≤ n * p
  ≤-*r-mono {m} {n} {p} m≤n
    rewrite *-commutative m p
          | *-commutative n p
    = ≤-*l-mono p m≤n

  ≤-*mono : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m * p ≤ n * q
  ≤-*mono {n = n} m≤n p≤q = ≤-trans (≤-*r-mono m≤n) (≤-*l-mono n p≤q)


  infix 4 _<_
  data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n} → zero < succ n
    s<s : ∀ {m n} → m < n → succ m < succ n

  <-trans : ∀ {n m p} -> n < m -> m < p -> n < p
  <-trans z<s (s<s m<p) = z<s
  <-trans (s<s n<m) (s<s m<p) = s<s (<-trans n<m m<p)

  data Trichotomy' n m : Set where
    less : n < m -> Trichotomy' n m
    equl : n ≡ m -> Trichotomy' n m
    more : m < n -> Trichotomy' n m

  data NatLtTrichotomy : Set where
    trichotomy : (∀ n m -> Trichotomy' n m) -> NatLtTrichotomy

  <-trichotomous : ∀ {n m} -> Trichotomy' n m
  <-trichotomous {zero} {zero} = equl refl
  <-trichotomous {zero} {succ m} = less z<s
  <-trichotomous {succ n} {zero} = more z<s
  <-trichotomous {succ n} {succ m} = <-trichotomous-succ <-trichotomous
    where
    <-trichotomous-succ : ∀ {n m} -> Trichotomy' n m
                          -> Trichotomy' (succ n) (succ m)
    <-trichotomous-succ (less n<m) = less (s<s n<m)
    <-trichotomous-succ (equl n=m) = equl (cong succ n=m)
    <-trichotomous-succ (more m<n) = more (s<s m<n)

  <-+l-mono : ∀ {m n p} → m < n → p + m < p + n
  <-+l-mono {p = zero} m<n = m<n
  <-+l-mono {p = succ p} m<n = s<s (<-+l-mono m<n)

  <-+r-mono : ∀ {m n p} → m < n → m + p < n + p
  <-+r-mono {m} {n} {p} m<n
    rewrite +-commutative m p
          | +-commutative n p
    = <-+l-mono m<n

  <-+mono : ∀ {m n p q} → m < n → p < q → m + p < n + q
  <-+mono m<n p<q = <-trans (<-+r-mono m<n) (<-+l-mono p<q)

  <-if-≤ : ∀ {m n} → succ m ≤ n → m < n
  <-if-≤ (s≤s z≤n) = z<s
  <-if-≤ (s≤s (s≤s mlen)) = s<s (<-if-≤ (s≤s mlen))

  ≤-if-< : ∀ {m n} → m < n → succ m ≤ n
  ≤-if-< {zero} {succ n} m<n = s≤s z≤n
  ≤-if-< {succ m} {succ n} (s<s m<n) = s≤s (≤-if-< m<n)

  <-weaken : ∀ {m n} → m < n → m ≤ n
  <-weaken z<s = z≤n
  <-weaken (s<s m<n) = s≤s (<-weaken m<n)

  <-trans-revisited : ∀ {n m p} → n < m → m < p → n < p
  <-trans-revisited n<m m<p = <-if-≤ (≤-trans (≤-if-< n<m) (<-weaken m<p))
