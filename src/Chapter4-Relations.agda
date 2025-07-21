{-# OPTIONS --large-indices #-}

module Chapter4-Relations where

open import Chapter1-Agda
  using (Bool; false; true; not; _×_)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs

-- Agda makes no distinctions between values and types

-- With indexed types we used values as indexes in types, but we can also use
-- types as values

_ : Set₀
_ = Bool

_ : Set₁
_ = Set

_ : Set₂
_ = Set₁

_ : Set₁₀₁
_ = Set₁₀₀

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)


module Playground-Level where
  data Maybe₀ (A : Set) : Set where
    just₀ : A → Maybe₀ A
    nothing₀ : Maybe₀ A

  -- Cannot do that because we are using `ℕ` as instance of `A` therefore `A` is
  -- the type of `ℕ` which is `Set₀` but `Set₀` is not of type `Set₀` like
  -- specified in the type Maybe₀ `(A : Set)`
  -- _ = just₀ ℕ

  -- This is ok because `1` is of type `ℕ` which is like saying that `A` is `ℕ`, and `ℕ : Set`
  _ = just₀ 1

  -- We can generalize abstracting over the universe level
  data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
    just₁ : A → Maybe₁ A
    nothing₁ : Maybe₁ A

  _ = just₁ ℕ
  _ = just₁ 1

private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Set a
  B : Set b
  C : Set c

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

_ : Set ≡ Set₀
_ = refl

_ : Set₀ ≡ Set lzero
_ = refl

_ : Set₁ ≡ Set (lsuc lzero)
_ = refl

-- Max between two levels
_ : (lsuc lzero) ⊔ lzero ≡ lsuc lzero
_ = refl

module Definition-DependentPair where
  -- open Chapter3-Proofs

  -- record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where -- according to the book
  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where -- according to the stdlib
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  -- The following is the proof that there exists an `ℕ` so that its successor
  -- is `5` and we prove that by supplying the pair made of that particular `ℕ`
  -- and a function that describe that property.
  ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , refl

  _ = Σ.proj₁ ∃n,n+1≡5 ≡ 4

open import Data.Product
  using (Σ; _,_)

module Sandbox-Relations where
  -- In standard library https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.Core.html#955

  -- Goal: we want a type to represent the general concept of relation.

  -- Solution: with are going to use the type `A → B → Set ℓ` which is saying
  -- that given two types `A` and `B` we will get back `Set ℓ` which is the type
  -- that represents the relation between `A` and `B`, that is a type which can
  -- be constructed with values from `A` and `B` only if those value have that
  -- relationship that we want to represent.

  -- We want to generalize the universe level of `A` and `B` therefore we are
  -- keeping their level as parameters `a` and `b`, plus we are asking for the
  -- universe level of the resulting type `ℓ`

  -- REL: is what in other languages you call a type alias, it's a convenient
  -- function that given two types `A` and `B` will give you back the type of a
  -- relation.

  -- NOTE: `Set (a ⊔ b ⊔ (lsuc ℓ))` is the type of `A → B → Set ℓ`, the level is
  -- `a ⊔ b ⊔ (lsuc ℓ)` because
  -- - `A` is of type `Set a`
  -- - `B` is of type `Set b`
  -- - `Set ℓ` is of type `Set (lsuc ℓ)`
  -- Therefore the level must be the max of all those levels

  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ (lsuc ℓ))
  REL A B ℓ = A → B → Set ℓ

  data Unrelated : REL A B lzero where
  -- NOTE: same as write `data Unrelated : A → B → Set lzero where`

  data Related : REL A B lzero where
    related : {a : A} {b : B} → Related a b

  -- Usage of Related type
  _ : Related ℕ Bool
  _ = related

  data Foo : Set where
    f1 f2 f3 : Foo

  data Bar : Set where
    b1 b2 b3 : Bar

  -- The following type doesn't make sense, is just a demonstration that two
  -- values can be related in many different ways.
  data FooBar : REL Foo Bar lzero where
    f2-b2 : FooBar f2 b2
    f2-b2′ : FooBar f2 b2
    f2-b : (b : Bar) → FooBar f2 b
    f3-b2 : FooBar f3 b2

  -- Functions as relations
  data _maps_↦_ (f : A → B) : REL A B lzero where
    app : {x : A} → f maps x ↦ f x

  _ : not maps true ↦ false
  _ = app

  _ : not maps false ↦ true
  _ = app

  -- Cannot refine: `false` is not related to `false` as far as `not` is concerned
  -- _ : not maps false ↦ false
  -- _ = {!!}

  -- NOTE: the `_~_` is going to pattern match on the REL type aka `A → B → Set
  -- ℓ` therefore it will become an infix operator with a value of type `A` on
  -- the left and a value of type `B` on the right and give back a value of type
  -- `Set ℓ` which is the proof of the relation between those values

  Functional : REL A B ℓ → Set _
  Functional {A = A} {B = B} _~_
    = ∀ {x : A} {y z : B}
    → x ~ y → x ~ z
    → y ≡ z

  Total : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_
    = ∀ (x : A) → Σ B (λ y → x ~ y)

  relToFn : (_~_ : REL A B ℓ) → Functional _~_ → Total _~_ → A → B
  relToFn _~_ _ total a = Σ.proj₁ (total a)

  -- Homogeneous relations
  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  -- Properties of relations to ask for

  -- NOTE: the following are again type aliases useful only to generate the type
  -- (`Set _`) which is in this case the mathematical statement of the property
  -- of a particular homogeneous relation

  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_ = ∀ {n : A} → n ~ n

  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_ = ∀ {n m : A} → n ~ m → m ~ n

  Anti-Symmetric : Rel A ℓ → Set _
  Anti-Symmetric {A = A} _~_ = ∀ {n m : A} → n ~ m → m ~ n → n ≡ m

  Transitive : Rel A ℓ → Set _
  Transitive {A = A} _~_ = ∀ {n m p : A} → n ~ m → m ~ p → n ~ p
