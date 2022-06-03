module equality where

  infix 4 _≡_
  data _≡_ {A : Set} : (x y : A) -> Set where
    refl : {x : A} → x ≡ x

  cong : ∀ {A B} (f : A → B) {x y} →
         x ≡ y → f x ≡ f y
  cong f refl = refl

  symm : ∀ {A} {x y : A} → x ≡ y → y ≡ x
  symm refl = refl

  trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl refl = refl
