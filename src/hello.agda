module hello where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# COMPILE GHC putStrLn = putStrLn . Data.Text.unpack #-}

main : IO ⊤
main = putStrLn "Hello world!"
