{-# OPTIONS --allow-unsolved-metas #-}

module Sequence where

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; reverse)
open import Data.List.Properties using (unfold-reverse)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Alphabet : Set where
  X : Alphabet
  Y : Alphabet
  [+] : Alphabet
  [-] : Alphabet

data Op : Set where
  R : Op
  L : Op

choose : Op → Alphabet
choose R = [+]
choose L = [-]

L-help : Op → List Alphabet → List Alphabet
L-help _ [] = []
L-help R (X ∷ xs) = X ∷ [+] ∷ Y ∷ (L-help R xs)
L-help R (Y ∷ xs) = X ∷ [-] ∷ Y ∷ (L-help R xs)
L-help L (X ∷ xs) = X ∷ [-] ∷ Y ∷ (L-help L xs)
L-help L (Y ∷ xs) = X ∷ [+] ∷ Y ∷ (L-help L xs)
L-help op (a ∷ xs) = a ∷ (L-help op xs)

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
dragonL a (op ∷ ops) = L-help op (dragonL a ops)

dragonC : List Op → List Alphabet
dragonC [] = []
dragonC (op ∷ ops) = (dragonC ops) ++ ((choose op) ∷ (invert (reverse (dragonC ops))))

L-help-distrib : 
    ∀ (op : Op) 
  → ∀ (xs ys : List Alphabet) 
  → L-help op (xs ++ ys) ≡ (L-help op xs) ++ (L-help op ys)

L-help-distrib op [] ys = refl

L-help-distrib R (X ∷ xs) ys = cong (λ v → X ∷ [+] ∷ Y ∷ v) (L-help-distrib R xs ys)
L-help-distrib R (Y ∷ xs) ys = cong (λ v → X ∷ [-] ∷ Y ∷ v) (L-help-distrib R xs ys)
L-help-distrib R ([+] ∷ xs) ys = cong ([+] ∷_) (L-help-distrib R xs ys)
L-help-distrib R ([-] ∷ xs) ys = cong ([-] ∷_) (L-help-distrib R xs ys)

L-help-distrib L (X ∷ xs) ys = cong (λ v → X ∷ [-] ∷ Y ∷ v) (L-help-distrib L xs ys)
L-help-distrib L (Y ∷ xs) ys = cong (λ v → X ∷ [+] ∷ Y ∷ v) (L-help-distrib L xs ys)
L-help-distrib L ([+] ∷ xs) ys = cong ([+] ∷_) (L-help-distrib L xs ys)
L-help-distrib L ([-] ∷ xs) ys = cong ([-] ∷_) (L-help-distrib L xs ys)

strip-distrib : ∀ (xs ys : List Alphabet) → strip (xs ++ ys) ≡ strip xs ++ strip ys
strip-distrib [] ys = refl
strip-distrib ([+] ∷ xs) ys = cong ([+] ∷_) (strip-distrib xs ys)
strip-distrib ([-] ∷ xs) ys = cong ([-] ∷_) (strip-distrib xs ys)
strip-distrib (X ∷ xs) ys = strip-distrib xs ys
strip-distrib (Y ∷ xs) ys = strip-distrib xs ys

dragonL-X-compose : 
    ∀ (fst : Op) 
  → ∀ (ops : List Op)
  → dragonL X (ops ∷ʳ fst) ≡ (dragonL X ops) ++ ((choose fst) ∷ (dragonL Y ops))

dragonL-X-compose R [] = refl
dragonL-X-compose L [] = refl
dragonL-X-compose fst (op ∷ ops) =
  begin
    dragonL X ((op ∷ ops) ∷ʳ fst)
  ≡⟨⟩
    L-help op (dragonL X (ops ∷ʳ fst))
  ≡⟨ cong (L-help op) (dragonL-X-compose fst ops) ⟩
    L-help op ((dragonL X ops) ++ ((choose fst) ∷ (dragonL Y ops)))
  ≡⟨ L-help-distrib op (dragonL X ops) ((choose fst) ∷ (dragonL Y ops)) ⟩
    (L-help op (dragonL X ops)) ++ (L-help op ((choose fst) ∷ (dragonL Y ops)))
  ≡⟨⟩
    (dragonL X (op ∷ ops)) ++ (L-help op ((choose fst) ∷ (dragonL Y ops)))
  ≡⟨ cong (λ v → (dragonL X (op ∷ ops)) ++ v) (help1 op fst ops) ⟩
    (dragonL X (op ∷ ops)) ++ ((choose fst) ∷ L-help op (dragonL Y ops))
  ≡⟨⟩
    (dragonL X (op ∷ ops)) ++ ((choose fst) ∷ (dragonL Y (op ∷ ops)))
  ∎ 
  where
    help1 : ∀ (op fst : Op) → ∀ (ops : List Op) → L-help op ((choose fst) ∷ (dragonL Y ops)) ≡ (choose fst) ∷ L-help op (dragonL Y ops)
    help1 R R ops = refl
    help1 R L ops = refl
    help1 L R ops = refl
    help1 L L ops = refl

LC-≡ : ∀ (ops : List Op) → strip (dragonL X (reverse ops)) ≡ dragonC ops
LC-≡ [] = refl
LC-≡ (x ∷ ops) = 
  begin
    strip (dragonL X (reverse (x ∷ ops)))
  ≡⟨ cong (λ v → strip (dragonL X v)) (unfold-reverse x ops) ⟩ 
    strip (dragonL X ((reverse ops) ∷ʳ x))
  ≡⟨ cong strip (dragonL-X-compose x (reverse ops)) ⟩
    strip ( (dragonL X (reverse ops)) ++ ((choose x) ∷ (dragonL Y (reverse ops)))  )
  ≡⟨ strip-distrib (dragonL X (reverse ops)) ((choose x) ∷ (dragonL Y (reverse ops))) ⟩ 
    strip (dragonL X (reverse ops)) ++ strip ((choose x) ∷ (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → strip (dragonL X (reverse ops)) ++ v) (help-1 x (dragonL Y (reverse ops))) ⟩ 
    strip (dragonL X (reverse ops)) ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → v ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))) (LC-≡ ops) ⟩ 
    (dragonC ops) ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ {!   !} ⟩ 
    {!   !}
  ≡⟨ {!   !} ⟩ 
    (dragonC ops) ++ ((choose x) ∷ (invert (reverse (dragonC ops))))
  ≡⟨⟩ 
    dragonC (x ∷ ops)
  ∎ 
  where
    help-1 : ∀ x xs → strip ((choose x) ∷ xs) ≡ (choose x) ∷ strip xs
    help-1 R xs = refl
    help-1 L xs = refl


-- Tests

tmpList : List Op
tmpList = R ∷ R ∷ R ∷ L ∷ R ∷ L ∷ R ∷ R ∷ []

testEquiv : strip (dragonL X (reverse tmpList)) ≡ dragonC tmpList
testEquiv = refl
