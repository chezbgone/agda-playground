module bin where

  open import equality
  open import nats
  open import natRels

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

  succ-inc : ∀ n -> (succ n) ≡ from (inc (to n))
  succ-inc zero = refl
  succ-inc (succ n) =
    begin
      succ (succ n)
    ≡⟨ cong succ (succ-inc n) ⟩
      succ (from (inc (to n)))
    ≡⟨ symm (inc-suc (inc (to n))) ⟩
      from (inc (inc (to n)))
    ∎

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

  -- starts with I
  data One : bin -> Set where
    one : One (⟨⟩ I)
    one-O : ∀ {o} -> One o -> One (o O)
    one-I : ∀ {o} -> One o -> One (o I)

  -- Canonical
  data Can : bin -> Set where
    can-zero : Can ⟨⟩
    can-one : ∀ {b} -> One b -> Can b

  inc-preserves-one : ∀ {b} -> One b -> One (inc b)
  inc-preserves-one one = one-O one
  inc-preserves-one (one-I ob) = one-O (inc-preserves-one ob)
  inc-preserves-one (one-O ob) = one-I ob

  inc-preserves-can : ∀ {b} -> Can b -> Can (inc b)
  inc-preserves-can can-zero = can-one one
  inc-preserves-can (can-one b) = can-one (inc-preserves-one b)

  can-to : ∀ n -> Can (to n)
  can-to zero = can-zero
  can-to (succ n) = inc-preserves-can (can-to n)

  positive-double : ∀ {n} -> 1 ≤ n -> 1 ≤ double n
  positive-double (s≤s 1≤n) = s≤s z≤n

  one-inc : ∀ {b} -> Can b -> One (inc b)
  one-inc can-zero = one
  one-inc (can-one ob) = one-inc' ob
    where
    one-inc' : ∀ {b} -> One b -> One (inc b)
    one-inc' one = one-O one
    one-inc' (one-I ob) = one-O (one-inc' ob)
    one-inc' (one-O ob) = one-I ob

  can-inc : ∀ {b} -> Can b -> Can (inc b)
  can-inc cb = can-one (one-inc cb)

  0≤-one : ∀ {n} -> 1 ≤ n -> One (to n)
  0≤-one {succ zero} 1len = one
  0≤-one {succ (succ n)} 1len = one-inc (can-one (0≤-one {succ n} (s≤s z≤n)))

  one-0≤ : ∀ {b} -> One b -> 1 ≤ from b
  one-0≤ one = s≤s z≤n
  one-0≤ (one-I ob) = s≤s z≤n
  one-0≤ (one-O ob) = positive-double (one-0≤ ob)

  double-one : ∀ {n} -> One (to n) -> One (to (double n))
  double-one {succ n} otn = one-inc (can-inc (can-to (double n)))

  double-one' : ∀ {b} -> One b -> One (to (double (from b)))
  double-one' {b} ob = double-one {from b} (0≤-one (one-0≤ ob))

  double-from : ∀ b -> One b -> to (double (from b)) ≡ b O
  double-from (b O) (one-O ob) =
    begin
      to (double (double (from b)))
    ≡⟨ cong (λ e -> to (double e)) (symm (from-to (double (from b)))) ⟩
      to (double (from (to (double (from b)))))
    --                 ----------------------
    ≡⟨ double-from (to (double (from b))) (double-one' ob) ⟩
      (to (double (from b)) O)
    ≡⟨ cong (λ e -> e O) (double-from b ob) ⟩
      ((b O) O)
    ∎
  double-from (b I) ob = {!!}

  one-from : ∀ {b} -> One b -> to (from b) ≡ b
  one-from {.(⟨⟩ I)} one = refl
  one-from {.(_ O)} (one-O ob) = {!!}
  one-from {.(_ I)} (one-I ob) = {!!}

  can-from : ∀ {b} -> Can b -> to (from b) ≡ b
  can-from can-zero = refl
  can-from (can-one ob) = one-from ob

