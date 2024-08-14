module Sequence where

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; reverse)
open import Data.List.Properties using (unfold-reverse; reverse-involutive; reverse-++-commute)

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

-- try to combine these two
choose : Op → Alphabet
choose R = [+]
choose L = [-]

chooseY : Op → Alphabet
chooseY R = [-]
chooseY L = [+]

-- use choose to simplify
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
invert (a ∷ xs) = a ∷ (invert xs)

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

invert-distrib : ∀ (xs ys : List Alphabet) → invert (xs ++ ys) ≡ invert xs ++ invert ys
invert-distrib [] ys = refl
invert-distrib ([+] ∷ xs) ys = cong ([-] ∷_) (invert-distrib xs ys)
invert-distrib ([-] ∷ xs) ys = cong ([+] ∷_) (invert-distrib xs ys)
invert-distrib (X ∷ xs) ys = cong (X ∷_) (invert-distrib xs ys)
invert-distrib (Y ∷ xs) ys = cong (Y ∷_) (invert-distrib xs ys)

rev-involutive : ∀ {A : Set} → ∀ (xs : List A) → reverse (reverse xs) ≡ xs
rev-involutive xs = reverse-involutive xs

inv-involutive : ∀ (xs : List Alphabet) → invert (invert xs) ≡ xs
inv-involutive [] = refl
inv-involutive (X ∷ xs) = cong (X ∷_) (inv-involutive xs)
inv-involutive (Y ∷ xs) = cong (Y ∷_) (inv-involutive xs)
inv-involutive ([+] ∷ xs) = cong ([+] ∷_) (inv-involutive xs)
inv-involutive ([-] ∷ xs) = cong ([-] ∷_) (inv-involutive xs)

∷-assoc : ∀ {A : Set} → ∀ (xs ys : List A) → ∀ m → xs ++ (m ∷ ys) ≡ (xs ∷ʳ m) ++ ys
∷-assoc [] ys m = refl
∷-assoc (x ∷ xs) ys m = cong (x ∷_) (∷-assoc xs ys m)

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
  ≡⟨ cong (λ v → (dragonL X (op ∷ ops)) ++ v) (help op fst ops) ⟩
    (dragonL X (op ∷ ops)) ++ ((choose fst) ∷ L-help op (dragonL Y ops))
  ≡⟨⟩
    (dragonL X (op ∷ ops)) ++ ((choose fst) ∷ (dragonL Y (op ∷ ops)))
  ∎ 
  where
    help : ∀ (op fst : Op) → ∀ (ops : List Op) → L-help op ((choose fst) ∷ (dragonL Y ops)) ≡ (choose fst) ∷ L-help op (dragonL Y ops)
    help R R ops = refl
    help R L ops = refl
    help L R ops = refl
    help L L ops = refl

dragonL-Y-compose : 
    ∀ (fst : Op) 
  → ∀ (ops : List Op)
  → dragonL Y (ops ∷ʳ fst) ≡ (dragonL X ops) ++ ((chooseY fst) ∷ (dragonL Y ops))

dragonL-Y-compose R [] = refl
dragonL-Y-compose L [] = refl
dragonL-Y-compose fst (op ∷ ops) = 
  begin
    dragonL Y ((op ∷ ops) ∷ʳ fst)
  ≡⟨⟩
    L-help op (dragonL Y (ops ∷ʳ fst))
  ≡⟨ cong (L-help op) (dragonL-Y-compose fst ops) ⟩
    L-help op ((dragonL X ops) ++ ((chooseY fst) ∷ (dragonL Y ops)))
  ≡⟨ L-help-distrib op (dragonL X ops) ((chooseY fst) ∷ (dragonL Y ops)) ⟩
    (L-help op (dragonL X ops)) ++ (L-help op ((chooseY fst) ∷ (dragonL Y ops)))
  ≡⟨⟩
    (dragonL X (op ∷ ops)) ++ (L-help op ((chooseY fst) ∷ (dragonL Y ops)))
  ≡⟨ cong (λ v → (dragonL X (op ∷ ops)) ++ v) (help op fst ops) ⟩
    (dragonL X (op ∷ ops)) ++ ((chooseY fst) ∷ L-help op (dragonL Y ops))
  ≡⟨⟩
    (dragonL X (op ∷ ops)) ++ ((chooseY fst) ∷ (dragonL Y (op ∷ ops)))
  ∎ 
  where
    help : ∀ (op fst : Op) → ∀ (ops : List Op) → L-help op ((chooseY fst) ∷ (dragonL Y ops)) ≡ (chooseY fst) ∷ L-help op (dragonL Y ops)
    help R R ops = refl
    help R L ops = refl
    help L R ops = refl
    help L L ops = refl
  

LC[X]-≡ : ∀ (ops : List Op) → strip (dragonL X (reverse ops)) ≡ dragonC ops
LC[Y]-≡ : ∀ (ops : List Op) → strip (dragonL Y (reverse ops)) ≡ invert (reverse (dragonC ops))

LC[X]-≡ [] = refl
LC[X]-≡ (x ∷ ops) = 
  begin
    strip (dragonL X (reverse (x ∷ ops)))
  ≡⟨ cong (λ v → strip (dragonL X v)) (unfold-reverse x ops) ⟩ 
    strip (dragonL X ((reverse ops) ∷ʳ x))
  ≡⟨ cong strip (dragonL-X-compose x (reverse ops)) ⟩
    strip ( (dragonL X (reverse ops)) ++ ((choose x) ∷ (dragonL Y (reverse ops)))  )
  ≡⟨ strip-distrib (dragonL X (reverse ops)) ((choose x) ∷ (dragonL Y (reverse ops))) ⟩ 
    strip (dragonL X (reverse ops)) ++ strip ((choose x) ∷ (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → strip (dragonL X (reverse ops)) ++ v) (help x (dragonL Y (reverse ops))) ⟩ 
    strip (dragonL X (reverse ops)) ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → v ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))) (LC[X]-≡ ops) ⟩ 
    (dragonC ops) ++ ((choose x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → (dragonC ops) ++ ((choose x) ∷ v)) (LC[Y]-≡ ops) ⟩ 
    (dragonC ops) ++ ((choose x) ∷ (invert (reverse (dragonC ops))))
  ≡⟨⟩ 
    dragonC (x ∷ ops)
  ∎ 
  where
    help : ∀ x xs → strip ((choose x) ∷ xs) ≡ (choose x) ∷ strip xs
    help R xs = refl
    help L xs = refl

LC[Y]-≡ [] = refl
LC[Y]-≡ (x ∷ ops) = 
  begin
    strip (dragonL Y (reverse (x ∷ ops)))
  ≡⟨ cong (λ v → strip (dragonL Y v)) (unfold-reverse x ops) ⟩
    strip (dragonL Y ((reverse ops) ∷ʳ x))
  ≡⟨ cong strip (dragonL-Y-compose x (reverse ops)) ⟩
    strip ( (dragonL X (reverse ops)) ++ ((chooseY x) ∷ (dragonL Y (reverse ops)))  )
  ≡⟨ strip-distrib (dragonL X (reverse ops)) ((chooseY x) ∷ (dragonL Y (reverse ops))) ⟩
    strip (dragonL X (reverse ops)) ++ strip ((chooseY x) ∷ (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → strip (dragonL X (reverse ops)) ++ v) (help x (dragonL Y (reverse ops))) ⟩
    strip (dragonL X (reverse ops)) ++ ((chooseY x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ cong (λ v → v ++ ((chooseY x) ∷ strip (dragonL Y (reverse ops)))) (LC[X]-≡ ops) ⟩
    (dragonC ops) ++ ((chooseY x) ∷ strip (dragonL Y (reverse ops)))
  ≡⟨ ∷-assoc (dragonC ops) (strip (dragonL Y (reverse ops))) (chooseY x) ⟩
    ((dragonC ops) ∷ʳ (chooseY x)) ++ strip (dragonL Y (reverse ops))
  ≡⟨ sym (cong (λ v → (v ∷ʳ (chooseY x)) ++ strip (dragonL Y (reverse ops))) (help5 (dragonC ops))) ⟩
    (invert (reverse (invert (reverse (dragonC ops)))) ∷ʳ (chooseY x)) ++ strip (dragonL Y (reverse ops))
  ≡⟨ cong (λ v → (invert (reverse (invert (reverse (dragonC ops)))) ∷ʳ (chooseY x)) ++ v) (LC[Y]-≡ ops) ⟩
    invert (reverse (invert (reverse (dragonC ops)))) ∷ʳ (chooseY x) ++ invert (reverse (dragonC ops))
  ≡⟨ sym (cong (λ v → v ++ invert (reverse (dragonC ops))) (help2 (reverse (invert (reverse (dragonC ops)))) x)) ⟩
    invert ( (reverse (invert (reverse (dragonC ops))) ∷ʳ choose x)) ++ invert (reverse (dragonC ops)) 
  ≡⟨ sym (invert-distrib ((reverse (invert (reverse (dragonC ops))) ∷ʳ choose x)) (reverse (dragonC ops)) ) ⟩
    invert ( (reverse (invert (reverse (dragonC ops))) ∷ʳ choose x) ++ reverse (dragonC ops)) 
  ≡⟨ cong (λ v → invert (v ++ reverse (dragonC ops)) ) (sym (unfold-reverse (choose x) (invert (reverse (dragonC ops))))) ⟩
    invert (reverse ((choose x) ∷ invert (reverse (dragonC ops))) ++ reverse (dragonC ops)) 
  ≡⟨ cong (invert) (sym (reverse-++-commute (dragonC ops) ((choose x) ∷ invert (reverse (dragonC ops))))) ⟩
    invert (reverse ((dragonC ops) ++ ((choose x) ∷ invert (reverse (dragonC ops))))) 
  ≡⟨⟩
    invert (reverse (dragonC (x ∷ ops))) 
  ∎ 
  where
    help : ∀ x xs → strip ((chooseY x) ∷ xs) ≡ (chooseY x) ∷ strip xs
    help R xs = refl
    help L xs = refl

    help2 : ∀ xs x → invert (xs ∷ʳ (choose x)) ≡ invert xs ∷ʳ (chooseY x)
    help2 xs R = invert-distrib xs ([+] ∷ [])
    help2 xs L = invert-distrib xs ([-] ∷ [])

    help3 : ∀ x → invert (x ∷ []) ≡ reverse (invert (x ∷ [])) 
    help3 X = refl
    help3 Y = refl
    help3 [+] = refl
    help3 [-] = refl

    help4 : ∀ xs → invert (reverse xs) ≡ reverse (invert xs)
    help4 [] = refl
    help4 (x ∷ xs) = 
      begin
        invert (reverse (x ∷ xs))
      ≡⟨ cong invert (unfold-reverse x xs) ⟩ 
        invert (reverse xs ++ (x ∷ []))
      ≡⟨ invert-distrib (reverse xs) (x ∷ []) ⟩ 
        invert (reverse xs) ++ invert (x ∷ [])
      ≡⟨ cong (_++ invert (x ∷ [])) (help4 xs) ⟩
        reverse (invert xs) ++ invert (x ∷ [])
      ≡⟨ cong (λ v → reverse (invert xs) ++ v) (help3 x) ⟩
        reverse (invert xs) ++ reverse (invert (x ∷ [])) 
      ≡⟨ sym (reverse-++-commute (invert (x ∷ [])) (invert xs)) ⟩
        reverse (invert (x ∷ []) ++ invert xs) 
      ≡⟨ sym (cong reverse (invert-distrib (x ∷ []) xs)) ⟩
        reverse (invert (x ∷ xs)) 
      ∎ 

    help5 : ∀ xs → invert (reverse (invert (reverse xs))) ≡ xs
    help5 xs = 
      begin
        invert (reverse (invert (reverse xs)))
      ≡⟨ help4 (invert (reverse xs)) ⟩ 
        reverse (invert (invert (reverse xs)))
      ≡⟨ cong reverse (inv-involutive (reverse xs)) ⟩ 
        reverse (reverse xs)
      ≡⟨ rev-involutive xs ⟩ 
        xs
      ∎

-- Tests

tmpList : List Op
tmpList = R ∷ R ∷ R ∷ L ∷ R ∷ L ∷ R ∷ R ∷ []
 
testEquiv : strip (dragonL X (reverse tmpList)) ≡ dragonC tmpList
testEquiv = refl
  