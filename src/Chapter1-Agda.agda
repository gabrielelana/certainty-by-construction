module Chapter1-Agda where

module Example-Imports where
  -- With only import another module you must use fully qualified names
  -- >>>
  -- import Data.Bool
  -- _ : Data.Bool.Bool
  -- _ = Data.Bool.false

  -- To use simple names you have to "open" the imported module
  -- >>>
  -- import Data.Bool
  -- open Data.Bool
  -- _ : Bool
  -- _ = false

  -- So common that we have syntactic sugar for that
  open import Data.Bool
  _ : Bool
  _ = false

module Example-Judgments where
  -- Postulate that `Bool` is a type. `Set` is the type of all types.
  postulate
    Bool : Set
    false : Bool
    true : Bool

    -- We can postulate whatever we want about types and their values
    Foo : Set
    bar : Foo

-- Definition of booleans without postulate
module Booleans where
  data Bool : Set where
    false : Bool
    true : Bool

  -- typing judgment followed by the function definition
  -- `not` has a type "from Bool to Bool"
  not : Bool → Bool
  not false = true
  not true = false

  -- and : Bool → Bool → Bool
  -- and false false = false
  -- and false true = false
  -- and true false = false
  -- and true true = true

  _∧_ : Bool → Bool → Bool
  true ∧ other = other
  false ∧ _ = false

  -- true ∧ true = true
  -- _ ∧ _ = false

  _∨_ : Bool → Bool → Bool
  false ∨ other = other
  true ∨ _ = true

  -- false ∨ false = false
  -- _ ∨ _ = true

  -- false ∨ false = false
  -- false ∨ true = true
  -- true ∨ false = true
  -- true ∨ true = true

  _v₁_ : Bool → Bool → Bool
  true v₁ true = true
  true v₁ false = true
  false v₁ true = true
  false v₁ false = false

  _v₂_ : Bool → Bool → Bool
  false v₂ other = other
  true v₂ other = true

  open import Relation.Binary.PropositionalEquality

  _ : not (not false) ≡ false
  _ = refl

module Example-Employees where
  open Booleans
  open import Data.String using (String)

  -- Our company has 5 departments
  data Department : Set  where
    administrative : Department
    engineering : Department
    finance : Department
    marketing : Department
    sales : Department

  -- An employee belongs to one department
  record Employee : Set where
    field
      name : String
      department : Department
      is-new-hire : Bool

  -- Build a value of type Employee
  tillman : Employee
  tillman = record
    { name = "Tillman"
    ; department = engineering
    ; is-new-hire = false
    }

module Sandbox-Tuples where
  -- `A` and `B` are locally bound variables which are later instantiated as
  -- types. We can think to `_×_` as a function which takes two types and gives
  -- back another type
  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A -- "project" or "select" the first element
      proj₂ : B -- "project" or "select" the second element

  open Booleans

  -- Definition of a value of type `Bool × Bool`
  a-tuple : Bool × Bool
  a-tuple = record { proj₁ = true ∧ false ; proj₂ = not false }

  -- How to project fields out of a record?

  -- 1. Pattern matching
  first : Bool × Bool → Bool
  -- first = { }0
  -- first x = { }0
  -- first record { proj₁ = proj₁ ; proj₂ = proj₂ } = { }0
  -- first record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁
  -- first record { proj₁ = x ; proj₂ = y } = x
  first record { proj₁ = x } = x

  -- 2. Record access syntax (`._×_.proj₁` fully qualified name)
  a-tuple-first : Bool
  a-tuple-first = a-tuple ._×_.proj₁

  -- 3. Record selector (`_×_.proj₂` is an implicitly defined function defined
  -- when the record was defined)
  a-tuple-second : Bool
  a-tuple-second = _×_.proj₂ a-tuple

  -- We can get rid of the fully qualified name with
  open _×_

  a-tuple-first' : Bool
  a-tuple-first' = a-tuple .proj₁

  a-tuple-second' : Bool
  a-tuple-second' = proj₂ a-tuple

  -- TODO: didn't understand the copattern thing

  -- a-copattern : Bool × Bool
  -- proj₁ a-copattern = {!!}
  -- proj₂ a-copattern = {!!}

  -- nested-copattern : Bool × (Bool × Bool)
  -- nested-copattern .proj₁ = {!!}
  -- nested-copattern .proj₂ .proj₁ = {!!}
  -- nested-copattern .proj₂ .proj₂ = {!!}

  _,_ : {A B : Set} → A → B → A × B
  x , x₁ = record { proj₁ = x ; proj₂ = x₁ }

  a-tuple' : Bool × Bool
  a-tuple' = (true ∧ false) , (not false)


module Sandbox-Tuples₂ where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_ -- green, as other constructors
    field
      proj₁ : A
      proj₂ : B

  open _×_

  infixr 4 _,_

  a-tuple : Bool × Bool
  a-tuple = true ∧ false , not false

  associative-to-the-right : Bool × (Bool × Bool)
  associative-to-the-right = true , false , false

  infixr 2 _×_

  associative-to-the-right' : Bool × Bool × Bool
  associative-to-the-right' = true , false , false


module Coproduct where
  data _⊎_ (A : Set) (B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

module Example-Pets where
  open import Data.String using (String)

  data Species : Set where
    bird cat dog reptile : Species

  data Temperament : Set where
    anxious chill excitable grumpy : Temperament

  record Pet : Set where
    constructor makePet
    field
      species : Species
      temperament : Temperament
      name : String

  makeGrumpyCat : String → Pet
  makeGrumpyCat = makePet cat grumpy
  -- name can be remove from both sides -> eta reduction
  -- makeGrumpyCat name = makePet cat grumpy name

module CurryUncurry where
  open Booleans
  open Sandbox-Tuples₂

  -- We can require all the arguments using product types
  or : (Bool × Bool) → Bool
  or (false , other) = other
  or (true , other) = true

  -- With this we get almost the familiar syntax of function calling in other language
  _ : Bool
  _ = or (true , false)

  -- Are the curried and uncurried function equivalent?

  -- To be equivalent we should be able to show an isomorphism between the two,
  -- aka a pair of functions to transform back and forth between the two.

  curry : {A B C : Set} → (A × B → C) → (A → B → C)
  -- f : (A × B → C)
  -- a : A
  -- b : B
  curry f a b = f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
  -- f : (A → B → C)
  -- x : (A × B) destructured with pattern matching
  uncurry f (a , b) = f a b

  -- We have demostracted that curried and uncurried function are equivalent

  -- We can ask Agda to solve a type hole
  -- _ : ?
  -- C-c C-s is "solve"
  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)

  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming ( _,′_ to _,_
             ; curry′ to curry
             ; uncurry′ to uncurry
             )

  -- Try to make type parameters explicit
  make-tuple : (A : Set) → (B : Set) → A → B → A × B
  make-tuple A B = _,_

  _ : Bool × Bool
  -- _ = ?                                -- C-c C-l aka load
  -- _ = { }0
  -- _ = { make-tuple }0                  -- C-c C-r aka refine
  -- _ = make-tuple { }0 { }1 { }2 { }3   -- C-c C-s aka solve
  -- _ = make-tuple Bool { }1 { }2 { }3   -- C-c C-s aka solve
  -- _ = make-tuple Bool Bool { }2 { }3   -- C-c C-a aka proof search
  -- _ = make-tuple Bool Bool false { }3  -- C-c C-a aka proof search
  -- _ = make-tuple Bool Bool false false
  _ = make-tuple Bool Bool false false


  data PrimaryColor : Set where
    red green blue : PrimaryColor

  -- When explicit parameters can be completely deduced we can leave a hole and
  -- Agda will fill it, this is called "elaboration"

  -- By keeping type paramters implicit with curly braces we are asking Agda to
  -- elaborate them

  weird-tuple : PrimaryColor × Bool
  weird-tuple = make-tuple _ _ red false

  -- We can make implicit parameters explict by using curly braces
  another-weird-tuple : Bool × PrimaryColor
  another-weird-tuple = _,_ {A = Bool} {B = PrimaryColor} true green

-- Export for the future chapters some things of the Data.Bool standard module
open import Data.Bool
  using (Bool; false; true; not; _∨_; _∧_)
  public

-- Export for the future chapters some things of the Data.Product standard module
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; curry; uncurry)
  public

-- Export for the future chapters some things of the Data.Sum standard module
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public
