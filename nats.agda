module nats where

  open import equality

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixl 6 _+_
  _+_ : ℕ → ℕ → ℕ
  0      + n = n
  succ n + m = succ (n + m)
  {-# BUILTIN NATPLUS _+_ #-}

  +zero : ∀ x → x + 0 ≡ x
  +zero 0 = refl
  +zero (succ x) = cong succ (+zero x)

  +succ : ∀ x y → x + succ y ≡ succ (x + y)
  +succ 0 y = refl
  +succ (succ x) y = cong succ (+succ x y)

  +-associative : ∀ (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-associative 0 y z = refl
  +-associative (succ x) y z = cong succ (+-associative x y z)

  +-commutative : ∀ (x y : ℕ) → x + y ≡ y + x
  +-commutative x 0 = +zero x
  +-commutative x (succ y) =
    equational-reasoning
      x + succ y
        ≡ succ (x + y)   by  +succ x y
        ≡ succ (y + x)   by  cong succ (+-commutative x y)

  +-swap : ∀ m n p -> m + (n + p) ≡ n + (m + p)
  +-swap m n p =
    equational-reasoning
      m + (n + p)
      ≡ (m + n) + p   by  symm (+-associative m n p)
      ≡ (n + m) + p   by  cong (_+ p) (+-commutative m n)
      ≡ n + (m + p)   by  +-associative n m p

  +-rearrange : ∀ m n p q -> (m + n) + (p + q) ≡ m + (n + p) + q
  +-rearrange m n p q =
    equational-reasoning
      (m + n) + (p + q)
      ≡ m + (n + (p + q))   by  +-associative m n (p + q)
      ≡ m + ((n + p) + q)   by  cong (m +_) (symm (+-associative n p q))
      ≡ m + (n + p) + q     by  symm (+-associative m (n + p) q)

  infixl 7 _*_
  _*_ : ℕ → ℕ → ℕ
  0 * n = 0
  succ n * m = m + n * m
  {-# BUILTIN NATTIMES _*_ #-}

  *zero : ∀ x → x * 0 ≡ 0
  *zero zero = refl
  *zero (succ x) = *zero x

  *succ : ∀ x y → x * (succ y) ≡ x + x * y
  *succ zero y = refl
  *succ (succ x) y =
    equational-reasoning
      succ (y + x * succ y)
      ≡ succ (y + (x + x * y))   by  cong (λ e -> succ (y + e)) (*succ x y)
      ≡ succ (x + (y + x * y))   by  cong succ (+-swap y x (x * y))

  *-commutative : ∀ (x y : ℕ) → x * y ≡ y * x
  *-commutative 0 y = symm (*zero y)
  *-commutative (succ x) y =
    equational-reasoning
      y + x * y
      ≡ y + y * x    by  cong (y +_) (*-commutative x y)
      ≡ y * succ x   by  symm (*succ y x)

  *-distributive-l : ∀ x y z → x * (y + z) ≡ x * y + x * z
  *-distributive-l zero y z = refl
  *-distributive-l (succ x) y z =
    equational-reasoning
      (y + z) + x * (y + z)
      ≡ (y + z) + (x * y + x * z)   by  cong (y + z +_) (*-distributive-l x y z)
      ≡ y + (z + (x * y + x * z))   by  +-associative y z (x * y + x * z)
      ≡ y + (x * y + (z + x * z))   by  cong (y +_) (+-swap z (x * y) (x * z))
      ≡ (y + x * y) + (z + x * z)   by  symm (+-associative y (x * y) (z + x * z))

  *-distributive-r : ∀ x y z -> (y + z) * x ≡ y * x + z * x
  *-distributive-r x y z =
    equational-reasoning
      (y + z) * x
      ≡ x * (y + z)     by  *-commutative (y + z) x
      ≡ x * y + x * z   by  *-distributive-l x y z
      ≡ x * y + z * x   by  cong (x * y +_) (*-commutative x z)
      ≡ y * x + z * x   by  cong (_+ z * x) (*-commutative x y)

  *-associative : ∀ (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-associative 0 y z = refl
  *-associative (succ x) y z =
    equational-reasoning
      (y + x * y) * z
      ≡ y * z + x * y * z     by  *-distributive-r z y (x * y)
      ≡ y * z + x * (y * z)   by  cong (y * z +_) (*-associative x y z)

  infixl 6 _∸_
  _∸_ : ℕ → ℕ → ℕ
  n ∸ zero = n
  zero ∸ succ m = zero
  succ n ∸ succ m = n ∸ m
  {-# BUILTIN NATMINUS _∸_ #-}

  ∸zero : ∀ m -> zero ∸ m ≡ zero
  ∸zero zero = refl
  ∸zero (succ m) = refl

  ∸-associative : ∀ m n p -> m ∸ n ∸ p ≡ m ∸ (n + p)
  ∸-associative m zero p = refl
  ∸-associative zero (succ n) p = ∸zero p
  ∸-associative (succ m) (succ n) p = ∸-associative m n p

  infixr 8 _^_
  _^_ : ℕ → ℕ → ℕ
  m ^ zero = 1
  m ^ succ n = m * m ^ n

  ^+-distributive : forall m n p -> m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^+-distributive m zero p = symm (+zero (m ^ p))
  ^+-distributive m (succ n) p =
    equational-reasoning
      m * m ^ (n + p)
      ≡ m * (m ^ n * m ^ p)   by  cong (m *_) (^+-distributive m n p)
      ≡ m * m ^ n * m ^ p     by  symm (*-associative m (m ^ n) (m ^ p))

  *^-distributive : forall m n p -> (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  *^-distributive m n zero = refl
  *^-distributive m n (succ p) =
    equational-reasoning
      m * n * (m * n) ^ p
      ≡ (m * n) * (m ^ p * n ^ p)   by  cong (m * n *_) (*^-distributive m n p)
      ≡ ((m * n) * m ^ p) * n ^ p   by  symm (*-associative (m * n) (m ^ p) (n ^ p))
      ≡ (m * (n * m ^ p)) * n ^ p   by  cong (_* n ^ p) (*-associative m n (m ^ p))
      ≡ m * ((n * m ^ p) * n ^ p)   by  *-associative m (n * m ^ p) (n ^ p)
      ≡ m * (m ^ p * n * n ^ p)     by  cong (λ e -> m * (e * n ^ p)) (*-commutative n (m ^ p))
      ≡ m * (m ^ p * (n * n ^ p))   by  cong (m *_) (*-associative (m ^ p) n (n ^ p))
      ≡ m * m ^ p * (n * n ^ p)     by  symm (*-associative m (m ^ p) (n * n ^ p))

  one^ : ∀ n -> 1 ^ n ≡ 1
  one^ zero = refl
  one^ (succ n) = trans (+zero (1 ^ n)) (one^ n)

  ^-tower : ∀ m n p -> (m ^ n) ^ p ≡ m ^ (n * p)
  ^-tower _ zero p = one^ p
  ^-tower m (succ n) p =
    equational-reasoning
      (m * m ^ n) ^ p
      ≡ m ^ p * (m ^ n) ^ p   by  *^-distributive m (m ^ n) p
      ≡ m ^ p * m ^ (n * p)   by  cong (m ^ p *_) (^-tower m n p)
      ≡ m ^ (p + n * p)       by  symm (^+-distributive m p (n * p))
