module boolean where

  open import equality

  data bool : Set where
    true : bool
    false : bool

  ¬ : bool → bool
  ¬ true = false
  ¬ false = true

  _∧_ : bool → bool → bool
  true  ∧ b = b
  false ∧ b = false

  _∨_ : bool → bool → bool
  true  ∨ b = true
  false ∨ b = b

  not-not-is-id : ∀ b -> ¬ (¬ b) ≡ b
  not-not-is-id true = refl
  not-not-is-id false = refl

  demorgan1 : ∀ a b → ¬ (a ∧ b) ≡ ¬ a ∨ ¬ b
  demorgan1 true b = refl
  demorgan1 false b = refl

  demorgan2 : ∀ a b → ¬ (a ∨ b) ≡ ¬ a ∧ ¬ b
  demorgan2 true b = refl
  demorgan2 false b = refl
