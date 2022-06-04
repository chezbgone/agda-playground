module bin where

  open import equality
  open import nats

  data bin : Set where
    ⟨⟩ : bin
    _O : bin -> bin
    _I : bin -> bin

  inc : bin -> bin
  inc ⟨⟩ = ⟨⟩ I
  inc (x O) = x I
  inc (x I) = (inc x) O

  double : ℕ -> ℕ
  double zero = zero
  double (succ x) = succ (succ (double x))

  from : bin → ℕ
  from ⟨⟩ = zero
  from (x O) = double (from x)
  from (x I) = succ (double (from x))

  to : ℕ -> bin
  to zero = ⟨⟩
  to (succ x) = inc (to x)

  x = from (⟨⟩ I O I I O)
  y = to 127

  inc-suc : ∀ b -> from (inc b) ≡ succ (from b)
  inc-suc ⟨⟩ = refl
  inc-suc (b O) = refl
  inc-suc (b I) rewrite inc-suc b = refl

  -- to-from: to (from b) ≡ b
  not-to-from-L = to (from (⟨⟩ O)) -- ⟨⟩
  not-to-from-R = (⟨⟩ O)           -- ⟨⟩ O

  from-to : ∀ n -> from (to n) ≡ n
  from-to zero = refl
  from-to (succ n) =
    begin
      from (inc (to n))
    ≡⟨ inc-suc (to n) ⟩
      succ (from (to n))
    ≡⟨ cong succ (from-to n) ⟩
      succ n
    ∎
