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

  _ : three ≡ one + two
  _ = refl

  _ : one + two ≡ three
  _ = refl

  -- Easy, depends on how the `_+_` has been defined
  zero-is-+-identity₁ : ∀ (n : ℕ) → zero + n ≡ n
  zero-is-+-identity₁ _ = refl

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- With flipped arguments requires more work, and the use of `cong`
  zero-is-+-identity : ∀ (n : ℕ) → n + zero ≡ n
  zero-is-+-identity zero = refl
  zero-is-+-identity (suc m) = cong suc (zero-is-+-identity m)

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
  ^-identityʳ : (x : ℕ) → x ^ one ≡ x
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

  -- Cannot do that
  -- *-identityˡ′ : ∀ (x : ℕ) → x ≡ one * x
  -- *-identityˡ′ = *-identityˡ

  -- Equality is simmetrical
  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  -- Now we can do that
  *-identityˡ′ : ∀ (x : ℕ) → x ≡ one * x
  *-identityˡ′ x = sym (*-identityˡ x)

  -- For fun, is sym involutive?
  sym-involutive : {A : Set} → {x y : A} → (P : x ≡ y) → sym (sym P) ≡ P
  sym-involutive refl = refl

  -- Is not?
  not-involutive : (x : Bool) → not (not x) ≡ x
  not-involutive false = refl
  not-involutive true = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0 a b = trans (^-identityʳ a)
                        (trans (sym (+-identityʳ a))
                               (cong (λ φ → a + φ) (sym (*-zeroʳ b))))

  a^1≡a+b*0¹ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0¹ a b = trans (^-identityʳ a)
                         (trans (sym (+-identityʳ a))
                                -- `a +_` is `λ φ → a + φ`
                                (cong (a +_) (sym (*-zeroʳ b))))

  -- also using rewrite
  a^1≡a+b*0² : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0² a b rewrite ^-identityʳ a rewrite *-zeroʳ b rewrite +-identityʳ a = refl

  module ≡-Reasoning where

    -- series of right associative operators to chain equalities

    -- the end of our proof
    infixr 3 _∎
    _∎ : {A : Set} → (x : A) → x ≡ x
    _∎ x = refl


    -- step: moving along the proof we already got
    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
    x ≡⟨⟩ p = p

    _ : 4 ≡ suc (one + two)
    _ = 4
      ≡⟨⟩
        two + two
      ≡⟨⟩
        suc one + suc one
      ≡⟨⟩
        suc (suc zero) + suc (suc zero)
      ≡⟨⟩
        suc (suc (suc zero)) + (suc zero)
      ≡⟨⟩
        suc (suc (suc (suc zero)))
      ∎

    -- step: with justification, syntax sugar for trans
    infixr 2 _≡⟨_⟩_
    _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x ≡⟨ xy ⟩ yz = trans xy yz

    -- init of our proof
    infix 1 begin_
    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin p = p

    a^1≡a+b*0³ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
    a^1≡a+b*0³ a b =
      begin
        a ^ 1
      ≡⟨ ^-identityʳ a ⟩
        a
      ≡⟨ sym (+-identityʳ a) ⟩
        a + 0
      ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
        a + b * 0
      ∎

    -- NOTE: to solve it incrementtally

    -- a^1≡a+b*0⁴ : (a b : ℕ) → a ^ 1 ≡ a + b * 0
    -- a^1≡a+b*0⁴ a b =
    --   begin
    --     -- begin with the expression on the left of the equality
    --     a ^ 1
    --   ≡⟨ {!!} ⟩ -- leave a hole in the equality you *need* to use, in this case to show that `a ^ 1 ≡ a`
    --     a  -- state what you want to obtain
    --   ≡⟨ {!!} ⟩ -- leave room for what comes next
    --     {!!}

  open ≡-Reasoning

  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  -- Exercise
  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true b c = refl

  -- Show that addiction is associative
  +-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
  +-assoc zero b c = refl
  +-assoc (suc a) b c = begin
                          suc a + b + c
                        ≡⟨⟩
                          suc (a + b + c)
                        ≡⟨ cong suc (+-assoc a b c) ⟩
                          suc (a + (b + c))
                        ≡⟨⟩
                          suc a + (b + c)
                        ∎

  -- Exercise
  +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  -- Exercise
  +-com : (x y : ℕ) → x + y ≡ y + x
  +-com zero y = sym (+-identityʳ y)
  +-com (suc x) y = begin
                      suc (x + y)
                    ≡⟨ cong suc (+-com x y) ⟩
                      suc (y + x)
                    ≡⟨ sym (+-suc y x) ⟩
                      y + suc x
                    ∎

  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero y = refl
  *-suc (suc x) y = begin
                      suc x * suc y
                    ≡⟨⟩
                      suc y + x * suc y
                    ≡⟨ cong (λ φ → suc y + φ) (*-suc x y) ⟩
                      suc y + (x + x * y)
                    ≡⟨⟩
                      suc (y + (x + x * y))
                    ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
                      suc ((y + x) + x * y)
                    ≡⟨ cong (λ φ → suc (φ + x * y)) (+-com y x) ⟩
                      suc ((x + y) + x * y)
                    ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
                      suc (x + (y + x * y))
                    ≡⟨⟩
                      suc x + (y + x * y)
                    ≡⟨⟩
                      suc x + (suc x * y)
                    ∎

  -- Exercise
  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc x) y = begin
                       suc x * y
                     ≡⟨ refl ⟩
                       y + x * y
                     ≡⟨ cong (λ φ → y + φ) (*-comm x y) ⟩
                       y + y * x
                     ≡⟨ sym (*-suc y x) ⟩
                       y * suc x
                     ∎

  -- Exercise
  *-distribʳ-+ : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
  *-distribʳ-+ x zero z = refl
  *-distribʳ-+ x (suc y) z = begin
                               (suc y + z) * x
                             ≡⟨ refl ⟩
                               x + (y + z) * x
                             ≡⟨ cong (x +_) (*-distribʳ-+ x y z) ⟩
                               x + (y * x + z * x)
                             ≡⟨ sym (+-assoc x (y * x) (z * x)) ⟩
                               suc y * x + z * x
                             ∎

  -- Exercise
  *-distribˡ-+ : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
  *-distribˡ-+ x y z = begin
                         x * (y + z)
                       ≡⟨ *-comm x (y + z) ⟩
                         (y + z) * x
                       ≡⟨ *-distribʳ-+ x y z ⟩
                         y * x + z * x
                       ≡⟨ cong (λ φ → (y * x) + φ) (*-comm z x) ⟩
                         y * x + x * z
                       ≡⟨ cong (λ φ → φ + (x * z)) (*-comm y x) ⟩
                         x * y + x * z
                       ∎

  -- Exercise
  *-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z = begin
                          suc x * y * z
                        ≡⟨⟩
                          (y + x * y) * z
                        ≡⟨ *-distribʳ-+ z y (x * y) ⟩
                          y * z + (x * y) * z
                        ≡⟨ cong (λ φ → y * z + φ) (*-assoc x y z) ⟩
                          y * z + x * (y * z)
                        ≡⟨ refl ⟩
                          suc x * (y * z)
                        ∎

open import Relation.Binary.PropositionalEquality
  using (_≡_; module ≡-Reasoning)
  public

module PropEq where
  open Relation.Binary.PropositionalEquality
    using (refl; cong; sym; trans)
    public

open import Data.Bool
  using (if_then_else_)
  public

open import Function
  using (case_of_)
  public

open import Data.Bool.Properties
  using ( ∨-identityˡ ; ∨-identityʳ
        ; ∨-zeroˡ
        ; ∨-zeroʳ
        ; ∨-assoc
        ; ∧-assoc
        ; ∧-identityˡ ; ∧-identityʳ
        ; ∧-zeroˡ
        ; ∧-zeroʳ
        ; not-involutive
        )
  public

open import Data.Nat.Properties
  using ( +-identityˡ ; +-identityʳ
        ; *-identityˡ ; *-identityʳ
        ; *-zeroˡ
        ; *-zeroʳ
        ; +-assoc
        ; *-assoc
        ; +-comm
        ; *-comm
        ; ^-identityʳ
        ; +-suc
        ; suc-injective
        ; *-distribˡ-+ ; *-distribʳ-+
        )
  public
