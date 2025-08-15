{-# OPTIONS --large-indices #-}

module Chapter4-Relations where

open import Chapter1-Agda using (Bool; false; true; not; _×_)
open import Chapter2-Numbers using (ℕ; zero; suc; _+_)
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

open import Agda.Primitive using (Level; _⊔_; lzero; lsuc)

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
    ℓ : Level

  data Maybe₂ (A : Set ℓ) : Set ℓ where
    just₂ : A → Maybe₂ A
    nothing₂ : Maybe₂ A

private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Set a
  B : Set b
  C : Set c

module Playgroun-Universe where
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
  open Chapter3-Proofs

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
  ∃n,n+1≡5 = 4 , PropEq.refl

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
  REL : Set a → Set b → (ℓ : Level)
      → Set (a ⊔ b ⊔ lsuc ℓ)
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

  data _maps_↦_ (f : A → B) : REL A B lzero where
    app : {x : A} → f maps x ↦ f x

  not-maps-false : not maps false ↦ true
  not-maps-false = app

  not-maps-true : not maps true ↦ false
  not-maps-true = app

  -- Cannot refine: `false` is not related to `false` as far as `not` is concerned
  -- _ : not maps false ↦ false
  -- _ = {!app!}

  -- NOTE: the `_~_` is going to pattern match on the REL type aka `A → B → Set
  -- ℓ` therefore it will become an infix operator with a value of type `A` on
  -- the left and a value of type `B` on the right and give back a value of type
  -- `Set ℓ` which is the proof of the relation between those values

  -- AKA: injectivity
  Functional : REL A B ℓ → Set _
  Functional {A = A} {B = B} _~_
    = {x : A} {y z : B}
    → x ~ y → x ~ z
    → y ≡ z

  -- _ : Functional Related
  -- _ : ∀ x y → Related x y → Related x z → y ≡ z
  -- _ = {!!}

  Total : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (λ y → x ~ y)


  relToFn : (_~_ : REL A B ℓ) → Functional _~_ → Total _~_ → A → B
  relToFn _~_ _ total a = Σ.proj₁ (total a)

  -- Homogeneous relations: the two elements have the same type
  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  -- Properties of relations to ask for

  -- NOTE: the following are again type aliases useful only to generate the type
  -- (`Set _`) which is in this case the mathematical statement of the property
  -- of a particular homogeneous relation

  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_ = {x : A} → x ~ x

  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_ = {x y : A} → x ~ y → y ~ x

  Anti-Symmetric : Rel A ℓ → Set _
  Anti-Symmetric {A = A} _~_ = ∀ {n m : A} → n ~ m → m ~ n → n ≡ m

  Transitive : Rel A ℓ → Set _
  Transitive {A = A} _~_ = {x y z : A} → x ~ y → y ~ z → x ~ z

open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric)

module Naive-≤₁ where
  -- First wrong representation
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  infix 4 _≤_

  -- Test if it works
  -- NOTE: the use of `lte` value constructor will give us the *type expression*
  -- `2 ≤ 2 + 3` which will compute to the final type `2 ≤ 5` but we could have
  -- also written `_ : 2 ≤ 2 + 3` it would have been the same
  _ : 2 ≤ 5
  _ = lte 2 3

  -- Prove that `suc` is monotonic
  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono (lte x y) = lte (suc x) y

  -- Prove that ≤ is Reflexive
  ≤-reflexive : Reflexive _≤_
  ≤-reflexive {zero} = lte zero zero
  ≤-reflexive {suc x} = suc-mono (≤-reflexive {x})

  -- ≤-reflexive₁ : Reflexive _≤_
  -- ≤-reflexive₁ {x} = {!lte x 0!}
  -- Cannot be filled because `x + 0` does not reduce automatically to `x` like we want

  -- Two ways to work around this:
  -- 1. `Naive-≤₂` swapping the addends of the sum
  -- 2. Using the `+-identityʳ` proof combined with `subst`

  open Chapter3-Proofs
    using (+-identityʳ)

  subst : {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
  -- since `x` is equal to `y` (by the use of `refl` in pattern matching of `x ≡
  -- y`) then Agda rewrites our original goal from `P y` to `P x` and we already
  -- have a `P x` which is `px`
  subst _ PropEq.refl px = px

  ≤-refl' : Reflexive _≤_
  ≤-refl' {x} = subst (λ φ → x ≤ φ) (+-identityʳ x) (lte x 0)

  suc-mono' : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono' {x} {.(x + b)} (lte .x b) = lte (suc x) b

module Naive-≤₂ where
  infix 4 _≤_
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ b + a

  -- Another way to prove it in a simpler way
  ≤-reflexive : Reflexive _≤_
  ≤-reflexive {x} = lte x 0

  open Naive-≤₁ using (subst)

  -- But, proving suc-mono will be more complicated
  suc-mono : ∀ {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono (lte a b) = subst (_≤_ (suc a)) (+-suc b a) (lte (suc a) b)

  ≤-reflexive₁ : Reflexive _≤_
  ≤-reflexive₁ {zero} = lte zero zero
  ≤-reflexive₁ {suc x} = suc-mono (lte x 0)

module Definition-LessThanOrEqualTo where
  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where
  -- Let's play a little bit with the relation
  _ : 2 ≤ 5
  -- We need to build a value of type `2 ≤ 5`
  -- _ = ?
  -- We have only 2 constructors `z≤n` and `s≤s`, `z≤n` is not good because on the left must have zero, therefore
  -- _ = s≤s ?
  -- Now we need to build an instance of something whose `suc` is `2 ≤ 5`,
  -- which is `1 ≤ 4` and for the same resoning as before the only suitable constructor is `s≤s`
  -- _ = s≤s (s≤s ?)
  -- Finally now we need to fill `0 ≤ 3` for which only one constructor fits
  _ = s≤s (s≤s z≤n)

  -- Proven by definition, we have a direct constructor
  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono = s≤s

  -- Trivial after making case
  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl

  -- Trivial after making case
  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n y = z≤n
  ≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

module Sandbox-Preorders where
  open Sandbox-≤

  record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl  : Reflexive _~_
      trans : Transitive _~_

  ≤-preorder : IsPreorder _≤_
  IsPreorder.refl ≤-preorder = ≤-refl
  IsPreorder.trans ≤-preorder = ≤-trans

  ≡-preorder : IsPreorder (_≡_ {A = A})
  IsPreorder.refl ≡-preorder = PropEq.refl
  IsPreorder.trans ≡-preorder = PropEq.trans

  -- Exercise: prove that Unrelated is a preorder. Unrelated is not a preorder, no elements are related with each other
  -- unrelated-preorder : IsPreorder {A = A} Sandbox-Relations.Unrelated
  -- unrelated-preorder .IsPreorder.reflexive = {!!}
  -- unrelated-preorder .IsPreorder.transitive = {!!}

  -- Exercise: prove that Related is a preorder
  related-preorder : IsPreorder {A = A} Sandbox-Relations.Related
  related-preorder .IsPreorder.refl = Sandbox-Relations.related
  related-preorder .IsPreorder.trans _ _ = Sandbox-Relations.related

  module Preorder-Reasoning
    -- NOTE: here the module is taking an implicit parameter `_~_` and an
    -- explicit parameter `~-preorder`, meaning that when we later will import
    -- `Preorder-Reasoning` we will need to provide the a specific relation with
    -- the proof that it's a preorder (aka an instance of `IsPreorder` for that
    -- relation)
    {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where

    -- Here now `~-preorder` is whatever the caller has given us as parameter

    open IsPreorder ~-preorder public

    -- By opening it public we have access on the `IsPreorder` fields which are
    -- `refl` and `trans`, conveniently they have the same name and signature as
    -- the well known functions.

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y
    infix 1 begin_

    _∎ : (x : A) → x ~ x
    _∎ x = refl
    infix 3 _∎

    _≈⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≈⟨⟩ p = p
    infixr 2 _≈⟨⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
    infixr 2 _≈⟨_⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z
    infixr 2 _≡⟨_⟩_

  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n = begin
    n
    ≈⟨ n≤1+n n ⟩
    1 + n
    ≡⟨ +-comm 1 n ⟩
    n + 1
    ∎
    where open Preorder-Reasoning ≤-preorder

  module ≤-Reasoning where
    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public


  n≤n+1' : (n : ℕ) → n ≤ n + 1
  n≤n+1' n = begin
    n
    ≤⟨ n≤1+n n ⟩
    1 + n
    ≡⟨ +-comm 1 n ⟩
    n + 1
    ∎
    where open ≤-Reasoning

  module Reachability {V : Set ℓ₁} (_⇒_ : Rel V ℓ₂) where
    private variable
      v v₁ v₂ v₃ : V

    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_ : v₁ ⇒ v₂ → Path v₁ v₂
      here : Path v v
      connect : Path v₁ v₂ → Path v₂ v₃ → Path v₁ v₃

    Path-preorder : IsPreorder Path
    IsPreorder.refl Path-preorder = here
    IsPreorder.trans Path-preorder = connect

  module Example-AboutABoy where
    -- Define a type Person with some constructors
    data Person : Set where
      ellie fiona marcus rachel susie will : Person

    -- Define variables of type Person to use implicitly
    private variable
      p₁ p₂ : Person

    -- Define a relation on Person with some constructors
    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will : marcus IsFriendsWith will
      marcus-fiona : marcus IsFriendsWith fiona
      fiona-susie  : fiona IsFriendsWith susie

    -- True by definition, don't need to prove
    postulate
      sym : p₁ IsFriendsWith p₂ → p₂ IsFriendsWith p₁

    -- Another relation on Person with some constructors
    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie : marcus IsInterestedIn ellie
      will-rachel  : will IsInterestedIn rachel
      rachel-will  : rachel IsInterestedIn will
      susie-will   : susie IsInterestedIn will

    -- Generalize two relations with another relation
    data SocialTie : Rel Person lzero where
      friendship : p₁ IsFriendsWith p₂ → SocialTie p₁ p₂
      interest : p₁ IsInterestedIn p₂ → SocialTie p₁ p₂

    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona = begin
      -- creates a path between will and marcus using the frenship between the two
      -- here with `_≈⟨_⟩_` we are using the transitivity proof of `Path`
      will ≈⟨ ↪ friendship (sym marcus-will) ⟩
      -- creates a path between marcus and fiona using the frenship between the two
      -- here with `_≈⟨_⟩_` we are using the transitivity proof of `Path`
      marcus ≈⟨ ↪ friendship marcus-fiona ⟩
      -- we reached fiona building a path between will and fiona building single
      -- paths and using path transitivity
      fiona ∎
      where open Preorder-Reasoning Path-preorder

    rachel-ellie : Path rachel ellie
    rachel-ellie = begin
      rachel ≈⟨ ↪ interest rachel-will ⟩
      will ≈⟨ ↪ friendship (sym marcus-will) ⟩
      marcus ≈⟨ ↪ interest marcus-ellie ⟩
      ellie ∎
      where open Preorder-Reasoning Path-preorder

  ≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s x) (s≤s y) = PropEq.cong suc (≤-antisym x y)

  Antisymmetric : Rel A ℓ₁ → Rel A ℓ₂ → Set _
  Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  _ : Antisymmetric _≡_ _≤_
  _ = ≤-antisym

  module _ {a ℓ : Level} {A : Set a} (_~_ : Rel A ℓ) where

    record IsEquivalence : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        sym        : Symmetric _~_

      open IsPreorder isPreorder public

    record IsPartialOrder : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        antisym : Antisymmetric _≡_ _~_
      open IsPreorder isPreorder public

  ≡-equiv : IsEquivalence (_≡_ {A = A})
  IsEquivalence.isPreorder ≡-equiv = ≡-preorder
  IsEquivalence.sym ≡-equiv = PropEq.sym

  ≤-poset : IsPartialOrder _≤_
  IsPartialOrder.isPreorder ≤-poset = ≤-preorder
  IsPartialOrder.antisym ≤-poset = ≤-antisym

  _<_ : Rel ℕ lzero
  m < n = m ≤ suc n
  infix 4 _<_

open import Agda.Primitive using (Level; _⊔_; lzero; lsuc) public
open import Data.Product using (Σ; _,_) public
open import Relation.Binary using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric) public
open import Relation.Binary.PropositionalEquality using (subst) public
open import Data.Nat using (_≤_; z≤n; s≤s; _<_) public
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning) public
open Sandbox-Preorders
  using ( IsPreorder
        ; IsEquivalence
        ; IsPartialOrder
        ; module Preorder-Reasoning
        ; ≡-preorder; ≡-equiv
        ; ≤-preorder; ≤-poset
        ) public
