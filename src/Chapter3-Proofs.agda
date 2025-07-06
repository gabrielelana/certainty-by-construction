module Chapter3-Proofs where

open import Chapter1-Agda
  using (Bool; true; false; _∨_; _∧_; not)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_; _^_)

module Definition where
  infix 4 _≡_

  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  -- Alternative implementation as in standard library

  -- data _≡_ {A : Set} (x : A) : A → Set where
    -- refl : x ≡ x

module Playground where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)

  _ : suc (suc (suc zero)) ≡ suc (suc (suc zero))
  _ = refl

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  _ : three ≡ suc (suc (suc zero))
  _ = refl

  _ : three ≡ two + one
  _ = refl

  -- Easy, depends on how the `_+_` has been defined
  zero-is-+-identity₁ : ∀ (n : ℕ) → zero + n ≡ n
  zero-is-+-identity₁ _ = refl

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- Requires more work
  zero-is-+-identity : ∀ (n : ℕ) → n + zero ≡ n
  zero-is-+-identity zero = refl
  zero-is-+-identity (suc n) = {!!}
  -- zero-is-+-identity (suc n) = cong suc (zero-is-+-identity n)

  suc-+ : ∀ (n m : ℕ) → n + suc m ≡ suc (n + m)
  suc-+ zero m = refl
  suc-+ (suc n) m = cong suc (suc-+ n m)

  zero-+ : ∀ (n : ℕ) → n + zero ≡ n
  zero-+ zero = refl
  zero-+ (suc n) = cong suc (zero-+ n)

  -- With `rewrite` we can rewrite the next goal using a function. Basically it
  -- means to use something already proven to change the goal or if you want to
  -- use a theorem to prove another
  commutativity-+ : ∀ (n m : ℕ) → n + m ≡ m + n
  -- originally the goal on the right is `m ≡ m + zero` since by pattern matching we know that n is zero
  -- using `zero-+` applied to m, we can rewrite the hole from `m ≡ m + zero` to `m ≡ m` which is trivially provable
  commutativity-+ zero m rewrite zero-+ m = refl
  -- originally the goal on the right is `suc n + m ≡ m + suc n`
  -- using `suc-+` applied to m and n we can rewrite the hole to `suc (n + m) ≡ suc (m + n)`
  -- which is exactly what we need for a recursive call using `cong`
  commutativity-+ (suc n) m  rewrite suc-+ m n = cong suc (commutativity-+ n m)

  -- We can also use the commutativity of the sum to prove the identity of zero
  zero-is-+-identity₂ : ∀ (n : ℕ) → n + zero ≡ n
  zero-is-+-identity₂ zero = refl
  zero-is-+-identity₂ (suc n) rewrite commutativity-+ n zero = refl

  +-identityˡ : ∀ (x : ℕ) → zero + x ≡ x
  +-identityˡ = zero-is-+-identity₁

  +-identityʳ : ∀ (x : ℕ) → x + zero ≡ x
  +-identityʳ = zero-is-+-identity


  -- Exercise
  *-identityˡ : ∀ (x : ℕ) → one * x ≡ x
  *-identityˡ zero = refl
  *-identityˡ (suc x) = cong suc (*-identityˡ x)

  -- Exercise
  *-identityʳ : ∀ (x : ℕ) → x * one ≡ x
  *-identityʳ zero = refl
  *-identityʳ (suc x) = cong suc (*-identityʳ x)

  -- Exercise
  ^-identityʳ : ∀ (x : ℕ) → x ^ one ≡ x
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)

  -- Exercise
  ∧-identityˡ : ∀ (b : Bool) → true ∧ b ≡ b
  ∧-identityˡ _ = refl

  ∧-identityʳ : ∀ (b : Bool) → b ∧ true ≡ b
  ∧-identityʳ true = refl
  ∧-identityʳ false = refl

  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  ∨-zeroˡ : (x : Bool) → true ∨ x ≡ true
  ∨-zeroˡ _ = refl

  ∨-zeroʳ : (x : Bool) → x ∨ true ≡ true
  ∨-zeroʳ false = refl
  ∨-zeroʳ true = refl

  -- Exercise
  ∧-zeroˡ : (x : Bool) → false ∧ x ≡ false
  ∧-zeroˡ _ = refl

  -- Exercise
  ∧-zeroʳ : (x : Bool) → x ∧ false ≡ false
  ∧-zeroʳ false = refl
  ∧-zeroʳ true = refl
