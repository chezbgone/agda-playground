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

  infixl 1 equational-reasoning_
  infixl 0 step-equational-reasoning

  equational-reasoning_ : ∀ {A} (x : A) → x ≡ x
  equational-reasoning x = refl
  
  step-equational-reasoning :
    ∀ {A} {x y : A} → (x ≡ y) → (u : A) → (y ≡ u) → (x ≡ u)
  step-equational-reasoning x≡y _ y≡u = trans x≡y y≡u

  syntax step-equational-reasoning p z q = p ≡ z by q
