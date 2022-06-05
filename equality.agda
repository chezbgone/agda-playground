module equality where

  infix 4 _≡_
  data _≡_ {A : Set} (x : A) : A -> Set where
    refl : x ≡ x
  {-# BUILTIN EQUALITY _≡_ #-}

  cong : ∀ {A B} (f : A → B) {x y} →
         x ≡ y → f x ≡ f y
  cong f refl = refl

  symm : ∀ {A} {x y : A} → x ≡ y → y ≡ x
  symm refl = refl

  trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl refl = refl

  subst : ∀ {A : Set} {P : A → Set} {x y} -> x ≡ y -> P x -> P y
  subst refl px = px

  module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {A} {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ {A} (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ {A} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ {A} (x : A) → x ≡ x
  x ∎ = refl

  open ≡-Reasoning
