{-# OPTIONS --allow-unsolved-metas #-}

module Sequence where

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; reverse)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

data Alphabet : Set where
  X : Alphabet
  Y : Alphabet
  [+] : Alphabet
  [-] : Alphabet

data Op : Set where
  R : Op
  L : Op

L-help-R : List Alphabet → List Alphabet
L-help-R [] = []
L-help-R (X ∷ xs) = X ∷ [+] ∷ Y ∷ (L-help-R xs)
L-help-R (Y ∷ xs) = X ∷ [-] ∷ Y ∷ (L-help-R xs)
L-help-R (a ∷ xs) = a ∷ (L-help-R xs)

L-help-L : List Alphabet → List Alphabet
L-help-L [] = []
L-help-L (X ∷ xs) = X ∷ [-] ∷ Y ∷ (L-help-L xs)
L-help-L (Y ∷ xs) = X ∷ [+] ∷ Y ∷ (L-help-L xs)
L-help-L (a ∷ xs) = a ∷ (L-help-L xs)

strip : List Alphabet → List Alphabet
strip [] = []
strip ([+] ∷ xs) = [+] ∷ (strip xs)
strip ([-] ∷ xs) = [-] ∷ (strip xs)
strip (a ∷ xs) = strip xs

invert : List Alphabet → List Alphabet
invert [] = []
invert ([+] ∷ xs) = [-] ∷ (invert xs)
invert ([-] ∷ xs) = [+] ∷ (invert xs)
invert (a ∷ xs) = invert xs

dragonL : Alphabet → List Op → List Alphabet
dragonL a [] = a ∷ []
dragonL a (R ∷ ops) = L-help-R (dragonL a ops)
dragonL a (L ∷ ops) = L-help-L (dragonL a ops)

dragonC : List Op → List Alphabet
dragonC [] = []
dragonC (R ∷ ops) = (dragonC ops) ++ ([+] ∷ (invert (reverse (dragonC ops))))
dragonC (L ∷ ops) = (dragonC ops) ++ ([-] ∷ (invert (reverse (dragonC ops))))

LC-≡ : ∀ (ops : List Op) → strip (dragonL X ops) ≡ dragonC (reverse ops)
LC-≡ [] = refl
LC-≡ (x ∷ ops) = {!   !}











-- Tests

tmpList : List Op
tmpList = R ∷ R ∷ R ∷ L ∷ R ∷ L ∷ R ∷ R ∷ []

testEquiv : strip (dragonL X tmpList) ≡ dragonC (reverse tmpList)
testEquiv = refl
