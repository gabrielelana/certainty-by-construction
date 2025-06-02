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

  open import Relation.Binary.PropositionalEquality

  _ : not (not false) ≡ false
  _ = refl
