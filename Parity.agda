open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -[1+_]; +[1+_]; _+_; _-_; _*_;  -_; ∣_∣)
open import Data.Integer.Properties using (+-comm; +-assoc; *-comm; *-assoc; *-distribˡ-+; -1*n≡-n)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

2ℤ : ℤ
2ℤ = + 2

Even : ℤ → Set
Even z = ∃[ k ] (z ≡ (+ 2) * k)

Odd : ℤ → Set
Odd z = ∃[ k ] (z ≡ (+ 2) * k + (+ 1))

e≡-e : ∀ {n : ℤ} → Even n → Even (- n)
e≡-e {n} ⟨ z , n≡2z ⟩ =  ⟨ - z , eq ⟩ where
  eq : - n ≡ 2ℤ * - z
  eq =
    begin
      - n
    ≡⟨ sym (-1*n≡-n n) ⟩
      -[1+ zero ] * n
    ≡⟨ cong (λ v →  -[1+ zero ] * v) n≡2z ⟩
       -[1+ zero ] * (2ℤ * z)
    ≡⟨ sym (*-assoc -[1+ zero ] 2ℤ z) ⟩
       (-[1+ zero ] * 2ℤ) * z
    ≡⟨ cong (λ v → v * z) (*-comm -[1+ zero ] 2ℤ) ⟩
       (2ℤ * -[1+ zero ]) * z
    ≡⟨ *-assoc 2ℤ -[1+ zero ] z ⟩
       2ℤ * (-[1+ zero ] * z)
    ≡⟨ cong (2ℤ *_) (-1*n≡-n z) ⟩
       2ℤ * - z
    ∎

o≡-o : ∀ {n : ℤ} → Odd n → Odd (- n)
o≡-o {n} ⟨ z , n≡2z+1 ⟩ =  ⟨ - (z + 1ℤ) , eq ⟩ where
  eq : - n ≡ 2ℤ * (- (z + 1ℤ)) + 1ℤ
  eq =
    begin
      - n
    ≡⟨ sym (-1*n≡-n n) ⟩
      -[1+ zero ] * n
    ≡⟨ cong (λ v →  -[1+ zero ] * v) n≡2z+1 ⟩
      -[1+ zero ] * (2ℤ * z + 1ℤ)
    ≡⟨ *-distribˡ-+ -[1+ zero ] (2ℤ * z) 1ℤ ⟩
      -[1+ zero ] * (2ℤ * z) + -[1+ zero ] * 1ℤ
    ≡⟨ cong (λ v → -[1+ zero ] * (2ℤ * z) + v) (-1*n≡-n 1ℤ) ⟩
      -[1+ zero ] * (2ℤ * z) + (- 1ℤ)
    ≡⟨⟩
      -[1+ zero ] * (2ℤ * z) + (- 2ℤ + 1ℤ)
    ≡⟨ sym (+-assoc (-[1+ zero ] * (2ℤ * z)) (- 2ℤ) 1ℤ) ⟩
      -[1+ zero ] * (2ℤ * z) + (- 2ℤ) + 1ℤ
    ≡⟨ cong (λ v → -[1+ zero ] * (2ℤ * z) + v + 1ℤ) (sym (-1*n≡-n 2ℤ)) ⟩
      -[1+ zero ] * (2ℤ * z) + -[1+ zero ] * 2ℤ + 1ℤ
    ≡⟨ cong (_+ 1ℤ) (sym (*-distribˡ-+ -[1+ zero ] (2ℤ * z) 2ℤ)) ⟩
      -[1+ zero ] * (2ℤ * z + 2ℤ) + 1ℤ
    ≡⟨ sym (cong (λ v → -[1+ zero ] * v + 1ℤ) (*-distribˡ-+ 2ℤ z 1ℤ)) ⟩
      -[1+ zero ] * (2ℤ * (z + 1ℤ)) + 1ℤ 
    ≡⟨ sym (cong (_+ 1ℤ) (*-assoc -[1+ zero ] 2ℤ (z + 1ℤ)))  ⟩
      (-[1+ zero ] * 2ℤ) * (z + 1ℤ) + 1ℤ 
    ≡⟨ cong (λ v → v * (z + 1ℤ) + 1ℤ) (*-comm -[1+ zero ] 2ℤ) ⟩
      (2ℤ * -[1+ zero ]) * (z + 1ℤ) + 1ℤ
    ≡⟨ cong (_+ 1ℤ) (*-assoc 2ℤ -[1+ zero ] (z + 1ℤ) ) ⟩
      2ℤ * (-[1+ zero ] * (z + 1ℤ)) + 1ℤ
    ≡⟨ cong (λ v → 2ℤ * v + 1ℤ) (-1*n≡-n (z + 1ℤ)) ⟩
      2ℤ * (- (z + 1ℤ)) + 1ℤ
    ∎

e+e≡e : ∀ {m n : ℤ} → Even m → Even n → Even (m + n)
e+e≡e {m} {n} ⟨ z1 , eq1 ⟩ ⟨ z2 , eq2 ⟩ = ⟨ (z1 + z2) , eq ⟩ where
  eq : m + n ≡ + 2 * (z1 + z2)
  eq =
    begin
      m + n
    ≡⟨ cong (λ v → v + n) eq1 ⟩
      (+ 2 * z1) + n
    ≡⟨ cong (λ v → (+ 2 * z1) + v ) eq2 ⟩
      (+ 2 * z1) + (+ 2 * z2)
    ≡⟨ sym (*-distribˡ-+ (+ 2) z1 z2) ⟩
       + 2 * (z1 + z2)
    ∎

e-e≡e : ∀ {m n : ℤ} → Even m → Even n → Even (m - n)
e-e≡e {m} {n} ⟨ z1 , eq1 ⟩ ⟨ z2 , eq2 ⟩ = e+e≡e ⟨ z1 , eq1 ⟩ (e≡-e ⟨ z2 , eq2 ⟩)

o+o≡e : ∀ {m n : ℤ} → Odd m → Odd n → Even (m + n)
o+o≡e {m} {n} ⟨ z1 , eq1 ⟩ ⟨ z2 , eq2 ⟩ = ⟨ z1 + z2 + 1ℤ , eq ⟩ where
  eq : m + n ≡ 2ℤ * (z1 + z2 + 1ℤ)
  eq =
    begin
      m + n
    ≡⟨ cong (λ v → v + n) eq1 ⟩
      (2ℤ * z1 + 1ℤ) + n
    ≡⟨ cong (λ v → (2ℤ * z1 + 1ℤ) + v ) eq2 ⟩
      (2ℤ * z1 + 1ℤ) + (2ℤ * z2 + 1ℤ)
    ≡⟨ +-assoc (2ℤ * z1) 1ℤ (2ℤ * z2 + 1ℤ)  ⟩
      2ℤ * z1 + (1ℤ + (2ℤ * z2 + 1ℤ))
    ≡⟨ cong (λ v → 2ℤ * z1 + v) (sym (+-assoc 1ℤ (2ℤ * z2) 1ℤ)) ⟩
      2ℤ * z1 + ((1ℤ + 2ℤ * z2) + 1ℤ)
    ≡⟨ cong (λ v → 2ℤ * z1 + (v + 1ℤ)) (+-comm 1ℤ (2ℤ * z2)) ⟩
      2ℤ * z1 + ((2ℤ * z2 + 1ℤ) + 1ℤ)
    ≡⟨ cong (λ v → 2ℤ * z1 + v) (+-assoc (2ℤ * z2) 1ℤ 1ℤ) ⟩
      2ℤ * z1 + (2ℤ * z2 + (1ℤ + 1ℤ))
    ≡⟨⟩
      2ℤ * z1 + (2ℤ * z2 + 2ℤ * 1ℤ)
    ≡⟨ sym (cong (λ v → 2ℤ * z1 + v) (*-distribˡ-+ 2ℤ z2 1ℤ)) ⟩
      2ℤ * z1 + 2ℤ * (z2 + 1ℤ)
    ≡⟨ sym (*-distribˡ-+ 2ℤ z1 (z2 + 1ℤ)) ⟩
      2ℤ * (z1 + (z2 + 1ℤ))
    ≡⟨ cong (λ v → 2ℤ * v) (sym (+-assoc z1 z2 1ℤ)) ⟩
       2ℤ * (z1 + z2 + 1ℤ)
    ∎
    
o-o≡e : ∀ {m n : ℤ} → Odd m → Odd n → Even (m - n)
o-o≡e {m} {n} ⟨ z1 , eq1 ⟩ ⟨ z2 , eq2 ⟩ = o+o≡e ⟨ z1 , eq1 ⟩ (o≡-o ⟨ z2 , eq2 ⟩)

data Same-Parity : ℤ → ℤ → Set where
  SP-e : ∀ {m n : ℤ}
    → Even m
    → Even n
    → Same-Parity m n
    
  SP-o : ∀ {m n : ℤ}
    → Odd m
    → Odd n
    → Same-Parity m n

sp→e[m-n] : ∀ {m n : ℤ} → Same-Parity m n → Even (m - n)
sp→e[m-n] (SP-e em en) = e-e≡e em en
sp→e[m-n] (SP-o om on) = o-o≡e om on

sp→e[n-m] : ∀ {m n : ℤ} → Same-Parity m n → Even (n - m)
sp→e[n-m] (SP-e em en) = e-e≡e en em
sp→e[n-m] (SP-o om on) = o-o≡e on om

sp→e[m+n] : ∀ {m n : ℤ} → Same-Parity m n → Even (m + n)
sp→e[m+n] (SP-e em en) = e+e≡e em en
sp→e[m+n] (SP-o om on) = o+o≡e om on


-- Tests

even[+8] : Even (+ 8)
even[+8] = ⟨ (+ 4) , refl ⟩

odd[-7] : Odd (-[1+ 6 ])
odd[-7] = ⟨ (-[1+ 3 ]) , refl ⟩
