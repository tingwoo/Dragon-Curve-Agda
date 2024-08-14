module Geometry where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -[1+_]; +[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (+-comm; +-assoc; +-identityʳ; +-identityˡ; *-assoc; *-comm; *-identityˡ; *-zeroʳ; *-distribˡ-+; *-distribʳ-+; +-minus-telescope; *-cancelˡ-≡; neg-involutive; neg-distrib-+; -1*n≡-n; +-inverseʳ)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Parity using (Even; Odd; Same-Parity; SP-o; sp→e[m+n]; sp→e[m-n]; sp→e[n-m])
open import Calculus using (2ℤ; 4ℤ; -2ℤ; _²; m+n≡m--n; n+n≡2n; *-distribʳ--; *-distribˡ--; ^-distrib-*; -a²≡a²; -a*b≡-ab; -a*-b≡ab; [a+b][c+d]; [a-b][c-d]; a-b²; a+b²)

record Coord : Set where
  field
    x : ℤ
    y : ℤ

half : ∀ {n : ℤ} → Even n → ℤ
half ⟨ z , _ ⟩ = z

45↑-clw : Coord → Coord
45↑-clw record { x = x ; y = y } =
  record
    { x = x + y
    ; y = (- x) + y
    }

45↑-ccw : Coord → Coord
45↑-ccw record { x = x ; y = y } =
  record
    { x = x - y
    ; y = x + y
    }

-- ∧-45-clw-arr : Arrow → Arrow
-- ∧-45-clw-arr record { type = type ; start = start ; end = end }
--   = record { type = type ; start = ∧-45-clw start ; end = ∧-45-clw end }

-- ∧-45-ccw-arr : Arrow → Arrow
-- ∧-45-ccw-arr record { type = type ; start = start ; end = end }
--   = record { type = type ; start = ∧-45-ccw start ; end = ∧-45-ccw end }

45↓-clw : ∀ ( ( record { x = x ; y = y } ) : Coord ) → Same-Parity x y → Coord
45↓-clw record { x = x ; y = y } same =
  record
    { x = half (sp→e[m+n] same)
    ; y = half (sp→e[n-m] same)
    }

45↓-ccw : ∀ ( ( record { x = x ; y = y } ) : Coord ) → Same-Parity x y → Coord
45↓-ccw record { x = x ; y = y } same =
  record
    { x = half (sp→e[m-n] same)
    ; y = half (sp→e[m+n] same)
    }

dist2 : Coord → Coord → ℤ
dist2 p1 p2 = (Coord.x p2 - Coord.x p1) ² + (Coord.y p2 - Coord.y p1) ²

45↑-clw-similar : ∀ {p1 p2 : Coord} → 2ℤ * (dist2 p1 p2) ≡ dist2 (45↑-clw p1) (45↑-clw p2)
45↑-clw-similar {p1} {p2} =
  begin
    2ℤ * (dist2 p1 p2)
  ≡⟨⟩
    2ℤ * ( (c - a) ² + (d - b) ² )
  ≡⟨ cong (λ v → 2ℤ * ( v + (d - b) ² )) (a-b² c a) ⟩
    2ℤ * (c ² - 2ℤ * (c * a) + a ² + (d - b) ²)
  ≡⟨ cong (λ v → 2ℤ * (c ² - 2ℤ * (c * a) + a ² + v)) (a-b² d b) ⟩
    2ℤ * (c ² - 2ℤ * (c * a) + a ² + (d ² - 2ℤ * (d * b) + b ²)) --
  ≡⟨ cong (2ℤ *_) (group3 (c ²) (- (2ℤ * (c * a))) (a ²) (d ²) (- (2ℤ * (d * b))) (b ²)) ⟩ 
    2ℤ * ((c ² + d ²) + (- (2ℤ * (c * a)) + - (2ℤ * (d * b))) + (a ² + b ²))
  ≡⟨ sym (cong (λ v → 2ℤ * ((c ² + d ²) + v + (a ² + b ²))) (neg-distrib-+ (2ℤ * (c * a)) (2ℤ * (d * b)))) ⟩ 
    2ℤ * ((c ² + d ²) - (2ℤ * (c * a) + 2ℤ * (d * b)) + (a ² + b ²))
  ≡⟨ sym (cong (λ v → 2ℤ * ((c ² + d ²) - v + (a ² + b ²))) (*-distribˡ-+ 2ℤ (c * a) (d * b))) ⟩ 
    2ℤ * ((c ² + d ²) - 2ℤ * (c * a + d * b) + (a ² + b ²))
  ≡⟨ sym (cong (λ v → 2ℤ * ((c ² + d ²) - v + (a ² + b ²))) (tmp3 c d a b)) ⟩ 
    2ℤ * ((c ² + d ²) - ((c + d) * (a + b) + (- c + d) * (- a + b)) + (a ² + b ²))
  ≡⟨ p[a-b+c] 2ℤ (c ² + d ²) ((c + d) * (a + b) + (- c + d) * (- a + b)) (a ² + b ²) ⟩ 
    2ℤ * (c ² + d ²) - 2ℤ * ((c + d) * (a + b) + (- c + d) * (- a + b)) + 2ℤ * (a ² + b ²)
  ≡⟨ cong (λ v → 2ℤ * (c ² + d ²) - v + 2ℤ * (a ² + b ²)) (*-distribˡ-+ 2ℤ ((c + d) * (a + b)) ((- c + d) * (- a + b))) ⟩ 
    2ℤ * (c ² + d ²) - (2ℤ * ((c + d) * (a + b)) + 2ℤ * ((- c + d) * (- a + b))) + 2ℤ * (a ² + b ²)
  ≡⟨ cong (λ v → 2ℤ * (c ² + d ²) + v + 2ℤ * (a ² + b ²)) (neg-distrib-+ (2ℤ * ((c + d) * (a + b))) (2ℤ * ((- c + d) * (- a + b)))) ⟩ 
    2ℤ * (c ² + d ²) + ((- (2ℤ * ((c + d) * (a + b)))) + (- (2ℤ * ((- c + d) * (- a + b))))) + 2ℤ * (a ² + b ²)
  ≡⟨ sym (cong (λ v → 2ℤ * (c ² + d ²) + ((- (2ℤ * ((c + d) * (a + b)))) + (- (2ℤ * ((- c + d) * (- a + b))))) + v) ([a+b]²+[-a+b]²≡2[a²+b²] a b)) ⟩ 
    2ℤ * (c ² + d ²) + ((- (2ℤ * ((c + d) * (a + b)))) + (- (2ℤ * ((- c + d) * (- a + b))))) + ((a + b) ² + (- a + b) ²)
  ≡⟨ sym (cong (λ v → v + ((- (2ℤ * ((c + d) * (a + b)))) + (- (2ℤ * ((- c + d) * (- a + b))))) + ((a + b) ² + (- a + b) ²)) ([a+b]²+[-a+b]²≡2[a²+b²] c d)) ⟩ 
    ((c + d) ² + (- c + d) ²) + ((- (2ℤ * ((c + d) * (a + b)))) + (- (2ℤ * ((- c + d) * (- a + b))))) + ((a + b) ² + (- a + b) ²)
  ≡⟨ sym (group3 ((c + d) ²) (- (2ℤ * ((c + d) * (a + b)))) ((a + b) ²) ((- c + d) ²) (- (2ℤ * ((- c + d) * (- a + b)))) ((- a + b) ²)) ⟩ 
     (c + d) ²   - 2ℤ * ((c + d)   * (a + b))   + (a + b) ² + 
    ((- c + d) ² - 2ℤ * ((- c + d) * (- a + b)) + (- a + b) ²) --
  ≡⟨ sym (cong (λ v → (c + d) ² - 2ℤ * ((c + d) * (a + b)) + (a + b) ² + v) (a-b² (- c + d) (- a + b))) ⟩
    (c + d) ² - 2ℤ * ((c + d) * (a + b)) + (a + b) ² + ((- c + d) - (- a + b)) ²
  ≡⟨ sym (cong (λ v → v + ( (- c + d) - (- a + b) ) ²) (a-b² (c + d) (a + b))) ⟩
    ((c + d) - (a + b)) ² + ((- c + d) - (- a + b)) ²
  ≡⟨⟩
    dist2
      record {x = a + b ; y = - a + b }
      record {x = c + d ; y = - c + d }
  ≡⟨⟩
    dist2 (45↑-clw p1) (45↑-clw p2)
  ∎ where
    a : ℤ
    a = Coord.x p1
    b : ℤ
    b = Coord.y p1
    c : ℤ
    c = Coord.x p2
    d : ℤ
    d = Coord.y p2

    group3 : ∀ (a b c d e f : ℤ) → a + b + c + (d + e + f) ≡ (a + d) + (b + e) + (c + f)
    group3 a b c d e f = 
      begin
        a + b + c + (d + e + f)
      ≡⟨ cong (λ v → (a + b + c) + v) (+-assoc d e f) ⟩ 
        a + b + c + (d + (e + f))
      ≡⟨ sym (+-assoc (a + b + c) d (e + f)) ⟩ 
        (a + b + c + d) + (e + f)
      ≡⟨ cong (λ v → v + (e + f)) (+-assoc (a + b) c d) ⟩ 
        (a + b + (c + d)) + (e + f)
      ≡⟨ cong (λ v → (a + b + v) + (e + f)) (+-comm c d) ⟩ 
        (a + b + (d + c)) + (e + f)
      ≡⟨ sym (cong (λ v → v + (e + f)) (+-assoc (a + b) d c)) ⟩ 
        ((a + b + d) + c) + (e + f)
      ≡⟨ cong (λ v → (v + c) + (e + f)) (+-assoc a b d) ⟩ 
        ((a + (b + d)) + c) + (e + f)
      ≡⟨ cong (λ v → ((a + v) + c) + (e + f)) (+-comm b d) ⟩ 
        ((a + (d + b)) + c) + (e + f)
      ≡⟨ sym (cong (λ v → (v + c) + (e + f)) (+-assoc a d b)) ⟩ 
        (((a + d) + b) + c) + (e + f)
      ≡⟨ sym (+-assoc (((a + d) + b) + c) e f) ⟩ 
        a + d + b + c + e + f
      ≡⟨ cong (λ v → v + f) (+-assoc (a + d + b) c e) ⟩ 
        a + d + b + (c + e) + f
      ≡⟨ cong (λ v → a + d + b + v + f ) (+-comm c e) ⟩ 
        a + d + b + (e + c) + f
      ≡⟨ sym (cong (λ v → v + f) (+-assoc (a + d + b) e c)) ⟩ 
        a + d + b + e + c + f
      ≡⟨ +-assoc (a + d + b + e) c f ⟩ 
        a + d + b + e + (c + f)
      ≡⟨ cong (λ v → v + (c + f)) (+-assoc (a + d) b e) ⟩ 
        (a + d) + (b + e) + (c + f)
      ∎ 

    [a+b]²+[a-b]²≡2[a²+b²] : ∀ (a b : ℤ) → (a + b) ² + (a - b) ² ≡ 2ℤ * (a ² + b ²)
    [a+b]²+[a-b]²≡2[a²+b²] a b = 
      begin 
        (a + b) ² + (a - b) ²
      ≡⟨ cong (λ v → v + (a - b) ²) (a+b² a b) ⟩ 
        (a ² + 2ℤ * (a * b) + b ²) + (a - b) ²
      ≡⟨ cong (λ v → (a ² + 2ℤ * (a * b) + b ²) + v) (a-b² a b) ⟩ 
        (a ² + 2ℤ * (a * b) + b ²) + (a ² - 2ℤ * (a * b) + b ²)
      ≡⟨ group3 (a ²) (2ℤ * (a * b)) (b ²) (a ²) (- (2ℤ * (a * b))) (b ²) ⟩
         (a ² + a ²) + (2ℤ * (a * b) + - (2ℤ * (a * b))) + (b ² + b ²)
      ≡⟨ cong (λ v → v + (2ℤ * (a * b) + - (2ℤ * (a * b))) + (b ² + b ²)) (n+n≡2n (a ²)) ⟩
        2ℤ * a ² + (2ℤ * (a * b) + - (2ℤ * (a * b))) + (b ² + b ²)
      ≡⟨ cong (λ v → 2ℤ * a ² + (2ℤ * (a * b) + - (2ℤ * (a * b))) + v) (n+n≡2n (b ²)) ⟩
        2ℤ * a ² + (2ℤ * (a * b) + - (2ℤ * (a * b))) + 2ℤ * b ²
      ≡⟨ cong (λ v → 2ℤ * a ² + v + 2ℤ * b ²) (+-inverseʳ (2ℤ * (a * b))) ⟩ 
        2ℤ * a ² + 0ℤ + 2ℤ * b ²
      ≡⟨ cong (λ v → v + 2ℤ * b ²) (+-identityʳ (2ℤ * a ²)) ⟩ 
        2ℤ * a ² + 2ℤ * b ²
      ≡⟨ sym (*-distribˡ-+ 2ℤ (a ²) (b ²)) ⟩ 
        2ℤ * (a ² + b ²)
      ∎  

    [a+b]²+[-a+b]²≡2[a²+b²] : ∀ (a b : ℤ) → (a + b) ² + (- a + b) ² ≡ 2ℤ * (a ² + b ²)
    [a+b]²+[-a+b]²≡2[a²+b²] a b = 
      begin
        (a + b) ² + (- a + b) ²
      ≡⟨ cong (λ v → v ² + (- a + b) ²) (+-comm a b) ⟩ 
        (b + a) ² + (- a + b) ²
      ≡⟨ cong (λ v → (b + a) ² + v ²) (+-comm (- a) b) ⟩ 
        (b + a) ² + (b + (- a)) ²
      ≡⟨ [a+b]²+[a-b]²≡2[a²+b²] b a ⟩ 
        2ℤ * (b ² + a ²)
      ≡⟨ cong (2ℤ *_) (+-comm (b ²) (a ²)) ⟩ 
        2ℤ * (a ² + b ²)
      ∎ 

    group2 : ∀ (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    group2 a b c d = 
      begin
        (a + b) + (c + d)
      ≡⟨ sym (+-assoc (a + b) c d) ⟩
        ((a + b) + c) + d
      ≡⟨ cong (_+ d) (+-assoc a b c) ⟩
        (a + (b + c)) + d
      ≡⟨ cong (λ x → (a + x) + d) (+-comm b c) ⟩
        (a + (c + b)) + d
      ≡⟨ cong (_+ d) (sym (+-assoc a c b)) ⟩
        ((a + c) + b) + d
      ≡⟨ +-assoc (a + c) b d ⟩
        (a + c) + (b + d)
      ∎

    tmp : ∀ (a b c : ℤ) → a * (b + c) + (- a) * (- b + c) ≡ 2ℤ * (a * b)
    tmp a b c = 
      begin
        a * (b + c) + (- a) * (- b + c)
      ≡⟨ cong (λ v → v + (- a) * (- b + c)) (*-distribˡ-+ a b c) ⟩
        a * b + a * c + (- a) * (- b + c)
      ≡⟨ cong (λ v → a * b + a * c + v) (*-distribˡ-+ (- a) (- b) c) ⟩ 
        a * b + a * c + ((- a) * (- b) + (- a) * c)
      ≡⟨ cong (λ v → a * b + a * c + (v + (- a) * c)) (-a*-b≡ab a b) ⟩
        a * b + a * c + (a * b + (- a) * c)
      ≡⟨ cong (λ v → a * b + a * c + (a * b + v)) (-a*b≡-ab a c) ⟩
        a * b + a * c + (a * b + - (a * c))
      ≡⟨ group2 (a * b) (a * c) (a * b) (- (a * c)) ⟩ 
        (a * b + a * b) + ((a * c) - (a * c))
      ≡⟨ cong (λ v → v + ((a * c) - (a * c))) (n+n≡2n (a * b)) ⟩ 
        2ℤ * (a * b) + ((a * c) - (a * c))
      ≡⟨ cong (λ v → 2ℤ * (a * b) + v) (+-inverseʳ (a * c)) ⟩ 
        2ℤ * (a * b) + 0ℤ
      ≡⟨ +-identityʳ (2ℤ * (a * b)) ⟩ 
        2ℤ * (a * b)
      ∎  

    tmp2 : ∀ (a b c : ℤ) → a * (b + c) + a * (- b + c) ≡ 2ℤ * (a * c)
    tmp2 a b c = 
      begin
        a * (b + c) + a * (- b + c)
      ≡⟨ cong (λ v → v + a * (- b + c)) (*-distribˡ-+ a b c) ⟩
        a * b + a * c + a * (- b + c)
      ≡⟨ cong (λ v → a * b + a * c + v) (*-distribˡ-+ a (- b) c) ⟩ 
        a * b + a * c + (a * (- b) + a * c)
      ≡⟨ group2 (a * b) (a * c) (a * (- b)) (a * c) ⟩
        a * b + a * (- b) + (a * c + a * c)
      ≡⟨ sym (cong (λ v → v + (a * c + a * c)) (*-distribˡ-+ a b (- b))) ⟩
        a * (b - b) + (a * c + a * c)
      ≡⟨ cong (λ v → a * (b - b) + v) (n+n≡2n (a * c)) ⟩
        a * (b - b) + (2ℤ * (a * c))
      ≡⟨ cong (λ v → a * v + (2ℤ * (a * c))) (+-inverseʳ b) ⟩
        a * 0ℤ + (2ℤ * (a * c))
      ≡⟨ cong (λ v → v + (2ℤ * (a * c))) (*-zeroʳ a) ⟩
        0ℤ + (2ℤ * (a * c))
      ≡⟨ +-identityˡ (2ℤ * (a * c)) ⟩
        2ℤ * (a * c)
      ∎  
    
    tmp3 : ∀ (a b c d : ℤ) → (a + b) * (c + d) + (- a + b) * (- c + d) ≡ 2ℤ * (a * c + b * d)
    tmp3 a b c d = 
      begin
        (a + b) * (c + d) + (- a + b) * (- c + d)
      ≡⟨ cong (λ v → v + (- a + b) * (- c + d)) (*-distribʳ-+ (c + d) a b) ⟩
        (a * (c + d) + b * (c + d)) + (- a + b) * (- c + d)
      ≡⟨ cong (λ v → (a * (c + d) + b * (c + d)) + v) (*-distribʳ-+ (- c + d) (- a) b) ⟩
        (a * (c + d) + b * (c + d)) + ((- a) * (- c + d) + b * (- c + d))
      ≡⟨ sym (+-assoc (a * (c + d) + b * (c + d)) ((- a) * (- c + d)) (b * (- c + d))) ⟩
        ((a * (c + d) + b * (c + d)) + (- a) * (- c + d)) + b * (- c + d)
      ≡⟨ cong (λ v → v + b * (- c + d)) (+-assoc (a * (c + d)) (b * (c + d)) ((- a) * (- c + d))) ⟩
        (a * (c + d) + (b * (c + d) + (- a) * (- c + d))) + b * (- c + d)
      ≡⟨ cong (λ v → (a * (c + d) + v) + b * (- c + d)) (+-comm (b * (c + d)) ((- a) * (- c + d))) ⟩
        (a * (c + d) + ((- a) * (- c + d) + b * (c + d))) + b * (- c + d)
      ≡⟨ sym (cong (λ v → v + b * (- c + d)) (+-assoc (a * (c + d)) ((- a) * (- c + d)) (b * (c + d)))) ⟩
        (a * (c + d) + (- a) * (- c + d) + b * (c + d)) + b * (- c + d)
      ≡⟨ cong (λ v → (v + b * (c + d)) + b * (- c + d)) (tmp a c d) ⟩
        (2ℤ * (a * c) + b * (c + d)) + b * (- c + d)
      ≡⟨ +-assoc (2ℤ * (a * c)) (b * (c + d)) (b * (- c + d)) ⟩
        2ℤ * (a * c) + (b * (c + d) + b * (- c + d))
      ≡⟨ cong (λ v → 2ℤ * (a * c) + v) (tmp2 b c d) ⟩
        2ℤ * (a * c) + 2ℤ * (b * d)
      ≡⟨ sym (*-distribˡ-+ 2ℤ (a * c) (b * d)) ⟩
        2ℤ * (a * c + b * d)
      ∎ 

    p[a-b+c] : ∀ (p a b c : ℤ) → p * (a - b + c) ≡ p * a - p * b + p * c
    p[a-b+c] p a b c = 
      begin
        p * (a - b + c)
      ≡⟨ *-distribˡ-+ p (a - b) c ⟩ 
        p * (a - b) + p * c
      ≡⟨ cong (λ v → v + p * c) (*-distribˡ-- p a b) ⟩ 
        p * a - p * b + p * c
      ∎

45↑-ccw-similar : ∀ {p1 p2 : Coord} → 2ℤ * (dist2 p1 p2) ≡ dist2 (45↑-ccw p1) (45↑-ccw p2)
45↑-ccw-similar {p1} {p2} = sym (half-eq (dist2 (45↑-ccw p1) (45↑-ccw p2)) (dist2 p1 p2) (
    begin
      2ℤ * (dist2 (45↑-ccw p1) (45↑-ccw p2))
    ≡⟨ 45↑-clw-similar {45↑-ccw p1} {45↑-ccw p2} ⟩
      dist2 (45↑-clw (45↑-ccw p1)) (45↑-clw (45↑-ccw p2))
    ≡⟨ cong (λ v → dist2 v (45↑-clw (45↑-ccw p2))) (clw∘ccw p1) ⟩
      dist2 (scale 2ℤ p1) (45↑-clw (45↑-ccw p2))
    ≡⟨ cong (λ v → dist2 (scale 2ℤ p1) v) (clw∘ccw p2) ⟩
      dist2 (scale 2ℤ p1) (scale 2ℤ p2)
    ≡⟨ dist∘scale 2ℤ p1 p2 ⟩
      4ℤ * dist2 p1 p2
    ∎
    )) where
  half-eq : ∀ (a b : ℤ) → 2ℤ * a ≡ 4ℤ * b → a ≡ 2ℤ * b
  half-eq a b eq = *-cancelˡ-≡ 2ℤ a (2ℤ * b) (λ())
    (begin (2ℤ * a) ≡⟨ eq ⟩ ((2ℤ * 2ℤ) * b) ≡⟨ *-assoc 2ℤ 2ℤ b ⟩ (2ℤ * (2ℤ * b)) ∎)

  scale : ℤ → Coord → Coord
  scale n record {x = x ; y = y} = record {x = n * x ; y = n * y}

  clw∘ccw : ∀ (p : Coord) → 45↑-clw (45↑-ccw p) ≡ scale 2ℤ p
  clw∘ccw record {x = x ; y = y} =
    begin
      record {x = (x - y) + (x + y) ; y = - (x - y) + (x + y)}
    ≡⟨ cong (λ v → record {x = (x - y) + v ; y = - (x - y) + (x + y)}) (+-comm x y) ⟩
      record {x = (x - y) + (y + x) ; y = - (x - y) + (x + y)}
    ≡⟨ cong (λ v → record {x = (x - y) + v ; y = - (x - y) + (x + y)}) (m+n≡m--n y x) ⟩
      record {x = (x - y) + (y - (- x)) ; y = - (x - y) + (x + y)}
    ≡⟨ cong (λ v → record {x = v ; y = - (x - y) + (x + y)}) (+-minus-telescope x y (- x)) ⟩
      record {x = x - (- x) ; y = - (x - y) + (x + y)}
    ≡⟨ sym (cong (λ v → record {x = v ; y = - (x - y) + (x + y)}) (m+n≡m--n x x)) ⟩
      record {x = x + x ; y = - (x - y) + (x + y)}
    ≡⟨ cong (λ v → record {x = v ; y = - (x - y) + (x + y)} ) (n+n≡2n x) ⟩
      record {x = 2ℤ * x ; y = - (x - y) + (x + y)}
    ≡⟨⟩
      record {x = 2ℤ * x ; y = - (x + - y) + (x + y)}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = - v + (x + y)}) (+-comm x (- y)) ⟩
      record {x = 2ℤ * x ; y = - (- y + x) + (x + y)}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = v + (x + y)}) (neg-distrib-+ (- y) x) ⟩
      record {x = 2ℤ * x ; y = (- - y - x) + (x + y)}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = (v - x) + (x + y)}) (neg-involutive y) ⟩
      record {x = 2ℤ * x ; y = (y - x) + (x + y)}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = (y - x) + v}) (m+n≡m--n x y) ⟩
      record {x = 2ℤ * x ; y = (y - x) + (x - (- y))}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = v}) (+-minus-telescope y x (- y)) ⟩
      record {x = 2ℤ * x ; y = y - (- y)}
    ≡⟨ sym (cong (λ v → record {x = 2ℤ * x ; y = v}) (m+n≡m--n y y)) ⟩
      record {x = 2ℤ * x ; y = y + y}
    ≡⟨ cong (λ v → record {x = 2ℤ * x ; y = v}) (n+n≡2n y) ⟩
      record {x = 2ℤ * x ; y = 2ℤ * y}
    ≡⟨⟩
      scale 2ℤ record {x = x ; y = y} 
    ∎
  
  dist∘scale : ∀ (n : ℤ) → ∀ (p3 p4 : Coord) → dist2 (scale n p3) (scale n p4) ≡ (n * n) * dist2 p3 p4
  dist∘scale n record {x = x1 ; y = y1} record {x = x2 ; y = y2} =
    begin
      dist2 record {x = n * x1 ; y = n * y1} record {x = n * x2 ; y = n * y2}
    ≡⟨⟩
      (n * x2 - n * x1) ² + (n * y2 - n * y1) ²
    ≡⟨ sym (cong (λ v → v ² + (n * y2 - (n * y1)) ²) (*-distribˡ-- n x2 x1)) ⟩
      (n * (x2 - x1)) ² + (n * y2 - (n * y1)) ²
    ≡⟨ sym (cong (λ v → (n * (x2 - x1)) ² + v ²) (*-distribˡ-- n y2 y1)) ⟩
      (n * (x2 - x1)) ² + (n * (y2 - y1)) ²
    ≡⟨ cong (λ v → v + (n * (y2 - y1)) ²) (^-distrib-* 2ℤ n (x2 - x1)) ⟩
      n ² * (x2 - x1) ² + (n * (y2 - y1)) ²
    ≡⟨ cong (λ v → n ² * (x2 - x1) ² + v) (^-distrib-* 2ℤ n (y2 - y1)) ⟩
      n ² * (x2 - x1) ² + n ² * (y2 - y1) ²
    ≡⟨ sym (*-distribˡ-+ (n ²) ((x2 - x1) ²) ((y2 - y1) ²)) ⟩
      n ² * ((x2 - x1) ² + (y2 - y1) ²)
    ∎
