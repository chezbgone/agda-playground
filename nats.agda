module nats where

  open import equality

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  infix 10 _+_
  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (succ n) + m = succ (n + m)

  plus-zero : ∀ x → x ≡ (x + zero)
  plus-zero zero = refl
  plus-zero (succ x) = cong succ (plus-zero x)

  plus-succ : ∀ x y → succ (x + y) ≡ x + succ y
  plus-succ zero y = refl
  plus-succ (succ x) y = cong succ (plus-succ x y)

  +associative : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
  +associative zero y z = refl
  +associative (succ x) y z = cong succ (+associative x y z)

  +commutative : ∀ (x y : ℕ) → x + y ≡ y + x
  +commutative zero y = plus-zero y
  +commutative (succ x) y = trans (cong succ (+commutative x y)) (plus-succ y x)
