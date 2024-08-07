open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; reverse)
open import Data.List.Properties using (reverse-++-commute; ++-assoc; unfold-reverse)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Alphabet : Set where
  X : Alphabet
  Y : Alphabet
  [+] : Alphabet
  [-] : Alphabet

dragon-L : List Alphabet → List Alphabet
dragon-L [] = []
dragon-L (X ∷ xs) = X ∷ [+] ∷ Y ∷ (dragon-L xs)
dragon-L (Y ∷ xs) = X ∷ [-] ∷ Y ∷ (dragon-L xs)
dragon-L (a ∷ xs) = a ∷ (dragon-L xs)

seq-strip : List Alphabet → List Alphabet
seq-strip [] = []
seq-strip ([+] ∷ xs) = [+] ∷ (seq-strip xs)
seq-strip ([-] ∷ xs) = [-] ∷ (seq-strip xs)
seq-strip (a ∷ xs) = seq-strip xs

seq-invert : List Alphabet → List Alphabet
seq-invert [] = []
seq-invert ([+] ∷ xs) = [-] ∷ (seq-invert xs)
seq-invert ([-] ∷ xs) = [+] ∷ (seq-invert xs)
seq-invert (a ∷ xs) = seq-invert xs

dragon-X : ℕ → List Alphabet
dragon-X zero = X ∷ []
dragon-X (suc n) = dragon-L (dragon-X n)

dragon-Y : ℕ → List Alphabet
dragon-Y zero = Y ∷ []
dragon-Y (suc n) = dragon-L (dragon-Y n)

dragon-2 : ℕ → List Alphabet
dragon-2 zero = []
dragon-2 (suc n) = (dragon-2 n) ++ ([+] ∷ (seq-invert (reverse (dragon-2 n))))

-- strip is distributive on concatenated lists
strip-distri : ∀ (xs ys : List Alphabet) → seq-strip (xs ++ ys) ≡ seq-strip xs ++ seq-strip ys
strip-distri [] ys = refl
strip-distri ([+] ∷ xs) ys = cong ([+] ∷_) (strip-distri xs ys)
strip-distri ([-] ∷ xs) ys = cong ([-] ∷_) (strip-distri xs ys)
strip-distri (X ∷ xs) ys = strip-distri xs ys
strip-distri (Y ∷ xs) ys = strip-distri xs ys

-- invert is distributive on concatenated lists
invert-distri : ∀ (xs ys : List Alphabet) → seq-invert (xs ++ ys) ≡ seq-invert xs ++ seq-invert ys
invert-distri [] ys = refl
invert-distri ([+] ∷ xs) ys = cong ([-] ∷_) (invert-distri xs ys)
invert-distri ([-] ∷ xs) ys = cong ([+] ∷_) (invert-distri xs ys)
invert-distri (X ∷ xs) ys = invert-distri xs ys
invert-distri (Y ∷ xs) ys = invert-distri xs ys

-- L is distributive on concatenated lists
L-distri : ∀ (xs ys : List Alphabet) → dragon-L (xs ++ ys) ≡ (dragon-L xs) ++ (dragon-L ys)
L-distri [] ys = refl
L-distri (X ∷ xs) ys = cong (λ v → X ∷ [+] ∷ Y ∷ v) (L-distri xs ys)
L-distri (Y ∷ xs) ys = cong (λ v → X ∷ [-] ∷ Y ∷ v) (L-distri xs ys)
L-distri ([+] ∷ xs) ys = cong ([+] ∷_) (L-distri xs ys)
L-distri ([-] ∷ xs) ys = cong ([-] ∷_) (L-distri xs ys)

-- Xn+1 is composed of Xn and Yn
dragon-X-compose : ∀ (n : ℕ) → dragon-X (suc n) ≡ dragon-X n ++ ([+] ∷ (dragon-Y n))
dragon-X-compose zero = refl
dragon-X-compose (suc n) =
  begin
    dragon-X (suc (suc n))
  ≡⟨⟩
    dragon-L (dragon-X (suc n))
  ≡⟨ cong dragon-L (dragon-X-compose n) ⟩
    dragon-L (dragon-X n ++ ([+] ∷ (dragon-Y n)))
  ≡⟨ L-distri (dragon-X n) ([+] ∷ (dragon-Y n)) ⟩
    dragon-L (dragon-X n) ++ dragon-L ([+] ∷ (dragon-Y n))
  ≡⟨⟩
    dragon-X (suc n) ++ ([+] ∷ dragon-Y (suc n))
  ∎

dragon-Y-compose : ∀ (n : ℕ) → dragon-Y (suc n) ≡ dragon-X n ++ ([-] ∷ (dragon-Y n))
dragon-Y-compose zero = refl
dragon-Y-compose (suc n) =
  begin
    dragon-Y (suc (suc n))
  ≡⟨⟩
    dragon-L (dragon-Y (suc n))
  ≡⟨ cong dragon-L (dragon-Y-compose n) ⟩
    dragon-L (dragon-X n ++ ([-] ∷ (dragon-Y n)))
  ≡⟨ L-distri (dragon-X n) ([-] ∷ (dragon-Y n)) ⟩
    dragon-L (dragon-X n) ++ dragon-L ([-] ∷ (dragon-Y n))
  ≡⟨⟩
    dragon-X (suc n) ++ ([-] ∷ dragon-Y (suc n))
  ∎

help1 : ∀ (n : ℕ) → seq-invert (seq-strip ([+] ∷ (dragon-Y n))) ≡ [-] ∷ seq-invert (seq-strip (dragon-Y n))
help1 n = refl

help2 : ∀ {A : Set} → ∀ (xs ys : List A) → ∀ (k : A) → reverse xs ++ (k ∷ ys) ≡ reverse (k ∷ xs) ++ ys
help2 [] ys k = refl
help2 (x ∷ xs) ys k =
  begin
    reverse (x ∷ xs) ++ (k ∷ ys)
  ≡⟨⟩
    reverse (x ∷ xs) ++ ((k ∷ []) ++ ys)
  ≡⟨ sym (++-assoc (reverse (x ∷ xs)) (k ∷ []) (ys)) ⟩
    (reverse (x ∷ xs) ++ (k ∷ [])) ++ ys
  ≡⟨⟩
    (reverse (x ∷ xs) ∷ʳ k) ++ ys
  ≡⟨ sym (cong (_++ ys) (unfold-reverse k (x ∷ xs))) ⟩
    reverse (k ∷ (x ∷ xs)) ++ ys
  ∎

XY-relation : ∀ (n : ℕ) → seq-invert (seq-strip (dragon-X n)) ≡ reverse (seq-strip (dragon-Y n))
YX-relation : ∀ (n : ℕ) → seq-invert (seq-strip (dragon-Y n)) ≡ reverse (seq-strip (dragon-X n))

XY-relation zero = refl
XY-relation (suc n) =
  begin
    seq-invert (seq-strip (dragon-X (suc n)))
  ≡⟨ cong (λ v → seq-invert (seq-strip v)) (dragon-X-compose n) ⟩
    seq-invert (seq-strip (dragon-X n ++ ([+] ∷ (dragon-Y n)) ))
  ≡⟨ cong (seq-invert) (strip-distri (dragon-X n) ([+] ∷ (dragon-Y n)) )⟩
    seq-invert (seq-strip (dragon-X n) ++ seq-strip ([+] ∷ (dragon-Y n)))
  ≡⟨ invert-distri (seq-strip (dragon-X n)) (seq-strip ([+] ∷ (dragon-Y n))) ⟩
    seq-invert (seq-strip (dragon-X n)) ++ seq-invert (seq-strip ([+] ∷ (dragon-Y n)))
  ≡⟨ cong (_++ seq-invert (seq-strip ([+] ∷ (dragon-Y n))) ) (XY-relation n) ⟩
    reverse (seq-strip (dragon-Y n)) ++ seq-invert (seq-strip ([+] ∷ (dragon-Y n)))
  ≡⟨ cong (reverse (seq-strip (dragon-Y n)) ++_) (help1 n) ⟩
    reverse (seq-strip (dragon-Y n)) ++ [-] ∷ seq-invert (seq-strip (dragon-Y n))
  ≡⟨ help2 (seq-strip (dragon-Y n)) ( seq-invert (seq-strip (dragon-Y n))) [-] ⟩
   reverse ([-] ∷ seq-strip (dragon-Y n)) ++ seq-invert (seq-strip (dragon-Y n))
  ≡⟨⟩
   reverse (seq-strip ([-] ∷ dragon-Y n)) ++ seq-invert (seq-strip (dragon-Y n))
  ≡⟨ cong (reverse (seq-strip ([-] ∷ dragon-Y n)) ++_) (YX-relation n) ⟩
   reverse (seq-strip ([-] ∷ dragon-Y n)) ++ reverse (seq-strip (dragon-X n))
  ≡⟨ sym (reverse-++-commute (seq-strip (dragon-X n)) (seq-strip ([-] ∷ (dragon-Y n)))) ⟩
   reverse (seq-strip (dragon-X n) ++ seq-strip ([-] ∷ (dragon-Y n)) )
  ≡⟨ sym (cong reverse (strip-distri (dragon-X n) ([-] ∷ (dragon-Y n)))) ⟩
   reverse (seq-strip ( dragon-X n ++ ([-] ∷ (dragon-Y n))))
  ≡⟨ sym (cong (λ v → reverse (seq-strip v)) (dragon-Y-compose n)) ⟩
   reverse (seq-strip (dragon-Y (suc n)))
  ∎

YX-relation zero = refl
YX-relation (suc n) =
  begin
    seq-invert (seq-strip (dragon-Y (suc n)))
  ≡⟨ cong (λ v → seq-invert (seq-strip v)) (dragon-Y-compose n) ⟩
    seq-invert (seq-strip (dragon-X n ++ ([-] ∷ (dragon-Y n)) ))
  ≡⟨ cong (seq-invert) (strip-distri (dragon-X n) ([-] ∷ (dragon-Y n)) )⟩
    seq-invert (seq-strip (dragon-X n) ++ seq-strip ([-] ∷ (dragon-Y n)))
  ≡⟨ invert-distri (seq-strip (dragon-X n)) (seq-strip ([-] ∷ (dragon-Y n))) ⟩
    seq-invert (seq-strip (dragon-X n)) ++ seq-invert (seq-strip ([-] ∷ (dragon-Y n)))
  ≡⟨⟩
    seq-invert (seq-strip (dragon-X n)) ++ seq-invert ([-] ∷ seq-strip (dragon-Y n))
  ≡⟨⟩
    seq-invert (seq-strip (dragon-X n)) ++ [+] ∷ seq-invert (seq-strip (dragon-Y n))
  ≡⟨ cong (λ v → seq-invert (seq-strip (dragon-X n)) ++ [+] ∷ v) (YX-relation n) ⟩
    seq-invert (seq-strip (dragon-X n)) ++ [+] ∷ reverse (seq-strip (dragon-X n))
  ≡⟨ cong (_++ [+] ∷ reverse (seq-strip (dragon-X n))) (XY-relation n) ⟩
    reverse (seq-strip (dragon-Y n)) ++ [+] ∷ reverse (seq-strip (dragon-X n))
  ≡⟨ help2 (seq-strip (dragon-Y n)) (reverse (seq-strip (dragon-X n))) [+]  ⟩
    reverse ([+] ∷ seq-strip (dragon-Y n)) ++ reverse (seq-strip (dragon-X n))
  ≡⟨ sym (reverse-++-commute (seq-strip (dragon-X n)) ([+] ∷ seq-strip (dragon-Y n)) ) ⟩
    reverse (seq-strip (dragon-X n) ++ ([+] ∷ seq-strip (dragon-Y n)))
  ≡⟨ sym (cong reverse (strip-distri (dragon-X n) ([+] ∷ (dragon-Y n)) ))⟩
    reverse (seq-strip (dragon-X n ++ ([+] ∷ (dragon-Y n))))
  ≡⟨ sym (cong (λ v → reverse (seq-strip v)) (dragon-X-compose n)) ⟩
    reverse (seq-strip (dragon-X (suc n)))
  ∎

invert² : ∀ (xs : List Alphabet) → seq-invert (seq-invert (seq-strip xs)) ≡ seq-strip xs
invert² [] = refl
invert² (X ∷ xs) = invert² xs
invert² (Y ∷ xs) = invert² xs
invert² ([+] ∷ xs) = cong ([+] ∷_) (invert² xs)
invert² ([-] ∷ xs) = cong ([-] ∷_) (invert² xs)

-- YX-relation : ∀ (n : ℕ) → seq-invert (seq-strip (dragon-Y n)) ≡ reverse (seq-strip (dragon-X n))

def-equality : ∀ (n : ℕ) → seq-strip (dragon-X n) ≡ dragon-2 n
def-equality zero = refl
def-equality (suc n) =
  begin
    seq-strip (dragon-X (suc n))
  ≡⟨ cong seq-strip (dragon-X-compose n) ⟩
    seq-strip (dragon-X n ++ ([+] ∷ (dragon-Y n)))
  ≡⟨ strip-distri (dragon-X n) ([+] ∷ (dragon-Y n)) ⟩
    seq-strip (dragon-X n) ++ seq-strip ([+] ∷ (dragon-Y n))
  ≡⟨ cong (_++ seq-strip ([+] ∷ (dragon-Y n))) (def-equality n) ⟩
    dragon-2 n ++ seq-strip ([+] ∷ (dragon-Y n))
  ≡⟨⟩
    dragon-2 n ++ [+] ∷ seq-strip (dragon-Y n)
  ≡⟨ sym (cong (λ v → dragon-2 n ++ [+] ∷ v) (invert² (dragon-Y n))) ⟩
    dragon-2 n ++ [+] ∷ seq-invert (seq-invert (seq-strip (dragon-Y n)))
  ≡⟨ cong (λ v → dragon-2 n ++ [+] ∷ seq-invert v) (YX-relation n) ⟩
    dragon-2 n ++ [+] ∷ seq-invert (reverse (seq-strip (dragon-X n)))
  ≡⟨ cong (λ v → dragon-2 n ++ [+] ∷ seq-invert (reverse v)) (def-equality n) ⟩
    dragon-2 n ++ [+] ∷ seq-invert (reverse (dragon-2 n))
  ≡⟨⟩
    dragon-2 (suc n)
  ∎

