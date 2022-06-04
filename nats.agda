module nats where

  open import equality

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixl 6 _+_
  _+_ : ℕ → ℕ → ℕ
  0 + n = n
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
    begin
      x + succ y
    ≡⟨ +succ x y ⟩
      succ (x + y)
    ≡⟨ cong succ (+-commutative x y) ⟩
      succ (y + x)
    ∎

  +-swap : ∀ m n p -> m + (n + p) ≡ n + (m + p)
  +-swap m n p =
    begin
      m + (n + p)
    ≡⟨ symm (+-associative m n p) ⟩
      (m + n) + p
    ≡⟨ cong (λ e -> e + p) (+-commutative m n) ⟩
      (n + m) + p
    ≡⟨ +-associative n m p ⟩
      n + (m + p)
    ∎

  +-rearrange : ∀ m n p q -> (m + n) + (p + q) ≡ m + (n + p) + q
  +-rearrange m n p q =
    begin
      (m + n) + (p + q)
    ≡⟨ +-associative m n (p + q) ⟩
      m + (n + (p + q))
    ≡⟨ cong (λ e -> m + e) (symm (+-associative n p q)) ⟩
      m + ((n + p) + q)
    ≡⟨ symm (+-associative m (n + p) q) ⟩
      m + (n + p) + q
    ∎

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
    begin
      succ (y + x * succ y)
    ≡⟨ cong (λ e -> succ (y + e)) (*succ x y) ⟩
      succ (y + (x + x * y))
    ≡⟨ cong succ (+-swap y x (x * y)) ⟩
      succ (x + (y + x * y))
    ∎

  *-commutative : ∀ (x y : ℕ) → x * y ≡ y * x
  *-commutative 0 y = symm (*zero y)
  *-commutative (succ x) y =
    begin
      y + x * y
    ≡⟨ cong (λ e -> y + e) (*-commutative x y) ⟩
      y + y * x
    ≡⟨ symm (*succ y x) ⟩
      y * succ x
    ∎

  *-distributive-l : ∀ x y z → x * (y + z) ≡ x * y + x * z
  *-distributive-l zero y z = refl
  *-distributive-l (succ x) y z =
    begin
      (y + z) + x * (y + z)
    ≡⟨ cong (λ e -> (y + z) + e) (*-distributive-l x y z) ⟩
      (y + z) + (x * y + x * z)
    ≡⟨ +-associative y z (x * y + x * z) ⟩
      y + (z + (x * y + x * z))
    ≡⟨ cong (λ e -> y + e) (+-swap z (x * y) (x * z)) ⟩
      y + (x * y + (z + x * z))
    ≡⟨ symm (+-associative y (x * y) (z + x * z)) ⟩
      (y + x * y) + (z + x * z)
    ∎

  *-distributive-r : ∀ x y z -> (y + z) * x ≡ y * x + z * x
  *-distributive-r x y z =
    begin
      (y + z) * x
    ≡⟨ *-commutative (y + z) x ⟩
      x * (y + z)
    ≡⟨ *-distributive-l x y z ⟩
      x * y + x * z
    ≡⟨ cong (λ e -> x * y + e) (*-commutative x z) ⟩
      x * y + z * x
    ≡⟨ cong (λ e -> e + z * x) (*-commutative x y) ⟩
      y * x + z * x
    ∎

  *-associative : ∀ (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-associative 0 y z = refl
  *-associative (succ x) y z =
    begin
      (y + x * y) * z
    ≡⟨ *-distributive-r z y (x * y) ⟩
      y * z + x * y * z
    ≡⟨ cong (λ e -> y * z + e) (*-associative x y z) ⟩
      y * z + x * (y * z)
    ∎

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

  infixl 8 _^_
  _^_ : ℕ → ℕ → ℕ
  m ^ zero = 1
  m ^ succ n = m * m ^ n

  ^+-distributive : forall m n p -> m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^+-distributive m zero p = symm (+zero (m ^ p))
  ^+-distributive m (succ n) p =
    begin
      m * m ^ (n + p)
    ≡⟨ cong (λ e -> m * e) (^+-distributive m n p) ⟩
      m * (m ^ n * m ^ p)
    ≡⟨ symm (*-associative m (m ^ n) (m ^ p)) ⟩
      m * m ^ n * m ^ p
    ∎

  *^-distributive : forall m n p -> (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  *^-distributive m n zero = refl
  *^-distributive m n (succ p) =
    begin
      m * n * (m * n) ^ p
    ≡⟨ cong (λ e → m * n * e) (*^-distributive m n p) ⟩
      (m * n) * (m ^ p * n ^ p)
    ≡⟨ symm (*-associative (m * n) (m ^ p) (n ^ p)) ⟩
      ((m * n) * m ^ p) * n ^ p
    ≡⟨ cong (λ e -> e * n ^ p) (*-associative m n (m ^ p)) ⟩
      (m * (n * m ^ p)) * n ^ p
    ≡⟨ *-associative m (n * m ^ p) (n ^ p) ⟩
      m * ((n * m ^ p) * n ^ p)
    ≡⟨ cong (λ e -> m * (e * n ^ p)) (*-commutative n (m ^ p)) ⟩
      m * (m ^ p * n * n ^ p)
    ≡⟨ cong (λ e -> m * e) (*-associative (m ^ p) n (n ^ p)) ⟩
      m * (m ^ p * (n * n ^ p))
    ≡⟨ symm (*-associative m (m ^ p) (n * n ^ p)) ⟩
      m * m ^ p * (n * n ^ p)
    ∎

  one^ : ∀ n -> 1 ^ n ≡ 1
  one^ zero = refl
  one^ (succ n) = trans (+zero (1 ^ n)) (one^ n)

  ^-tower : ∀ m n p -> m ^ n ^ p ≡ m ^ (n * p)
  ^-tower _ zero p = one^ p
  ^-tower m (succ n) p =
    begin
      (m * m ^ n) ^ p
    ≡⟨ *^-distributive m (m ^ n) p ⟩
      m ^ p * m ^ n ^ p
    ≡⟨ cong (λ e -> m ^ p * e) (^-tower m n p) ⟩
      m ^ p * m ^ (n * p)
    ≡⟨ symm (^+-distributive m p (n * p)) ⟩
      m ^ (p + n * p)
    ∎
