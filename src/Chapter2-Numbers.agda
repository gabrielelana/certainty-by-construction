module Chapter2-Numbers where

open import Relation.Binary.PropositionalEquality

import Chapter1-Agda

module Sandbox-Naturals where
  data ℕ : Set where
    zero : ℕ                    -- 0 / base case
    suc : ℕ → ℕ                 -- x → x + 1 / inductive step

  -- Don't know why in the book he is importing naturals from stdlib at this
  -- point, but until necessary I'll use what we have

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three

  five : ℕ
  five = suc four

  six : ℕ
  six = suc five

  open Chapter1-Agda using (Bool; true; false)

  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false

  -- Exercise: implement `n=2?` (pp71)

  n=2? : ℕ → Bool
  n=2? (suc (suc zero)) = true
  n=2? n = false

  open import Relation.Binary.PropositionalEquality

  _ : n=2? one ≡ false
  _ = refl

  _ : n=2? two ≡ true
  _ = refl

  -- 2.4 Induction

  even? : ℕ → Bool
  even? zero = true
  even? (suc zero) = false
  even? (suc (suc x)) = even? x

  -- 2.5 Two Notions of Evenness

  module Sandbox-Usable where
    postulate
      Usable : Set
      Unusable : Set

    -- Would be nice to have a type to represent even numbers.
    -- We create a function that given a natural will return a type.
    -- We don't what the return should be, for now we "postulate" some types.
    -- Only to show that in Agda

    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  -- A more proper way to implement it is to use a data type

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four
  -- four-is-even = {!!}
  -- four-is-even = suc-suc-even {!!}
  -- four-is-even = suc-suc-even (suc-suc-even {!!})
  four-is-even = suc-suc-even (suc-suc-even zero-even)

  -- three-is-even : IsEven three
  -- three-is-even = {!!}
  -- three-is-even = suc-suc-even {!!}
  -- ERROR: No introduction forms found.
  -- Meaning: didn't found any constructor for type `one` therefore nothing can fit the last hole

  -- Exercise: build an index type for IsOdd (pp77)

  data IsOdd : ℕ → Set where
    one-odd : IsOdd (suc zero)
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  data IsOdd₁ : ℕ → Set where
    is-odd : {n : ℕ} -> IsEven n -> IsOdd₁ (suc n)

  -- Exercise: write an inductive function which witnesses the fact that every
  -- even number is followed by an odd number (pp77)

  even-then-odd : {n : ℕ} -> IsEven n → IsOdd (suc n)
  even-then-odd zero-even = one-odd
  even-then-odd (suc-suc-even x) = suc-suc-odd (even-then-odd x)

  even-then-odd₁ : {n : ℕ} -> IsEven n → IsOdd₁ (suc n)
  even-then-odd₁ x = is-odd x

  -- 2.6 Constructing Evidence

  data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  -- NOTE: the following will not work because `evenEv n` has type `Maybe (IsEven n)`
  --       when we need the type `Maybe (IsEven (suc (suc n)))`.
  --       Put in another way we need to prove that the original `n` is even,
  --       not that `n - 2` is even
  -- evenEv (suc (suc n)) = evenEv n

  -- We need to prove first that `n` is even, we do that recursively and then we
  -- can use `IsEven` constructor for `suc (suc n)` (which is under the
  -- assumption that `n` is even)
  evenEv (suc (suc n)) with evenEv n
  ... | just n = just (suc-suc-even n)
  ... | nothing = nothing

  -- 2.7 Addition

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc n) + m = suc (n + m)

  infixl 6 _+_

  _ : zero + one ≡ one
  _ = refl

  _ : two + one ≡ three
  _ = refl

  -- 2.9 Multiplication and Exponentiation

  _*_ : ℕ → ℕ → ℕ
  zero * n = zero
  (suc zero) * n = n
  (suc n) * m = m + (n * m)

  infixl 7 _*_

  _ : zero * one ≡ zero
  _ = refl

  _ : one * three ≡ three
  _ = refl

  _ : three * one ≡ three
  _ = refl

  _ : two * two ≡ four
  _ = refl

  _^_ : ℕ → ℕ → ℕ
  n ^ zero = one
  n ^ (suc m) = n * n ^ m

  infixl 8 _^_

  _ : two ^ two ≡ four
  _ = refl

  _ : two ^ three ≡ two * two * two
  _ = refl

  -- 2.10 Semi-subtration

  -- Exercise: implement monus ∸

  _∸_ : ℕ → ℕ → ℕ
  n ∸ zero = n
  zero ∸ (suc n) = zero
  (suc n) ∸ (suc m) = n ∸ m

  _ : three ∸ one ≡ two
  _ = refl

  _ : one ∸ three ≡ zero
  _ = refl

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  zero : ℤ
  zero = + ℕ.zero

  one : ℤ
  one = + 1

  -one : ℤ
  -one = -[1+ ℕ.zero ]

  suc : ℤ → ℤ
  suc (+ x) = + ℕ.suc x
  suc -[1+ ℕ.zero ] = zero
  suc -[1+ (ℕ.suc x) ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.suc x) = + x
  pred (+ ℕ.zero) = -one
  pred -[1+ x ] = -[1+ ℕ.suc x ]

  -- Not symmetric implementation of ~-~ 🤮
  -- -_ : ℤ → ℤ
  -- - (+ ℕ.zero) = + ℕ.zero
  -- - (+ ℕ.suc x) = -[1+ x ]
  -- - -[1+ x ] = + ℕ.suc x

  -- To make ℤ symmetric
  pattern +[1+_] n = + ℕ.suc n

  -- To make ℤ look prettier
  pattern +0 = + ℕ.zero

  -- After the definition of this "Pattern Synonyms"
  -_ : ℤ → ℤ
  - +0 = +0
  - +[1+ x ] = -[1+ x ]
  - -[1+ x ] = +[1+ x ]

  module Naive-Addition where

    -- Now we can subtract a natural from another natural and get back an integer
    _⊖_ : ℕ → ℕ → ℤ
    ℕ.zero ⊖ ℕ.zero = +0
    ℕ.zero ⊖ ℕ.suc y = -[1+ y ]
    ℕ.suc x ⊖ ℕ.zero = +[1+ x ]
    ℕ.suc x ⊖ ℕ.suc y = x ⊖ y

    infixl 5 _+_

    _+_ : ℤ → ℤ → ℤ
    + x + + y = + (x ℕ.+ y)
    + x + -[1+ y ] = x ⊖ ℕ.suc y
    -[1+ x ] + + y = y ⊖ ℕ.suc x
    -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

    _ : -[1+ 4 ] + +[1+ 4 ] ≡ +0
    _ = refl

    _ : -[1+ 4 ] + +[1+ 3 ] ≡ -one
    _ = refl

    _ : -[1+ 3 ] + +[1+ 4 ] ≡ one
    _ = refl

    -- We can implement general subtraction between integers
    _-_ : ℤ → ℤ → ℤ
    x - y = x + (- y)

    -- And multiplication
    _*_ : ℤ → ℤ → ℤ
    +0 * y = +0
    x * +0 = +0
    x * +[1+ ℕ.zero ] = x
    x * -[1+ ℕ.zero ] = - x
    x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
    x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x

    _ : (+ 2) * (+ 3) ≡ +[1+ 5 ]
    _ = refl

    _ : (- (+ 2)) * (+ 3) ≡ -[1+ 5 ]
    _ = refl

    _ : (- (+ 2)) * (- (+ 3)) ≡ +[1+ 5 ]
    _ = refl

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Sandbox-Naturals
  using (one; two; three; four; five; six)

open Sandbox-Naturals
  using (IsEven)
  renaming ( zero-even to z-even ; suc-suc-even to ss-even )
  public

open import Data.Maybe
  using (Maybe; just; nothing)
  public
