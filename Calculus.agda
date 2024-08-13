open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -[1+_]; +[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (neg-involutive; +-assoc; *-comm; *-assoc; *-distribʳ-+; *-distribˡ-+; *-identityˡ; -1*n≡-n)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

2ℤ : ℤ
2ℤ = + 2

4ℤ : ℤ
4ℤ = + 4

-2ℤ : ℤ
-2ℤ = -[1+ 1 ]

_² : ℤ → ℤ
z ² = z * z

_ : ∀ (x y : ℤ) → x - y ≡ x + (- y)
_ = λ x y → refl

m+n≡m--n : ∀ (x y : ℤ) → x + y ≡ x - (- y)
m+n≡m--n x y = sym (begin
    x - (- y)
  ≡⟨⟩
    x + (- - y)
  ≡⟨ cong (λ v → x + v) (neg-involutive y) ⟩
    x + y
  ∎)

n+n≡2n : ∀ (x : ℤ) → x + x ≡ 2ℤ * x
n+n≡2n x =
  begin
    x + x
  ≡⟨ sym (cong (λ v → v + x) (*-identityˡ x)) ⟩
    1ℤ * x + x
  ≡⟨ sym (cong (λ v → 1ℤ * x + v) (*-identityˡ x)) ⟩
    1ℤ * x + 1ℤ * x
  ≡⟨ sym (*-distribʳ-+ x 1ℤ 1ℤ) ⟩
    2ℤ * x
  ∎

*-distribˡ-- : ∀ (p m n : ℤ) → p * (m - n) ≡ p * m - p * n
*-distribˡ-- p m n =
  begin
     p * (m - n)
  ≡⟨⟩
     p * (m + - n)
  ≡⟨ *-distribˡ-+ p m (- n) ⟩
    p * m + p * - n
  ≡⟨ sym (cong (λ v → p * m + p * v) (-1*n≡-n n)) ⟩
    p * m + p * (-1ℤ * n)
  ≡⟨ sym (cong (λ v → p * m + v) (*-assoc p -1ℤ n)) ⟩
    p * m + (p * -1ℤ) * n
  ≡⟨ cong (λ v → p * m + v * n) (*-comm p -1ℤ) ⟩
    p * m + -1ℤ * p * n
  ≡⟨ cong (λ v → p * m + v) (*-assoc -1ℤ p n) ⟩
    p * m + -1ℤ * (p * n)
  ≡⟨ cong (λ v → p * m + v) (-1*n≡-n (p * n)) ⟩
    p * m + - (p * n)
  ≡⟨⟩
    p * m - p * n
  ∎

*-distribʳ-- : ∀ (p m n : ℤ) → (m - n) * p ≡ m * p - n * p
*-distribʳ-- p m n =
  begin
     (m - n) * p
  ≡⟨⟩
     (m + - n) * p
  ≡⟨ *-distribʳ-+ p m (- n) ⟩
    m * p + (- n) * p
  ≡⟨ sym (cong (λ v → m * p + v * p) (-1*n≡-n n)) ⟩
    m * p + -1ℤ * n * p
  ≡⟨ cong (λ v → m * p + v) (*-assoc -1ℤ n p) ⟩
    m * p + -1ℤ * (n * p)
  ≡⟨ cong (λ v → m * p + v) (-1*n≡-n (n * p)) ⟩
    m * p - (n * p)
  ∎

^-distrib-* : ∀ (p m n : ℤ) → (m * n) ² ≡ m ² * n ²
^-distrib-* p m n =
  begin
    (m * n) ²
  ≡⟨⟩
    m * n * (m * n)
  ≡⟨ *-assoc m n (m * n) ⟩
    m * (n * (m * n))
  ≡⟨ sym (cong (m *_) (*-assoc n m n)) ⟩
    m * (n * m * n)
  ≡⟨ cong (λ v → m * (v * n)) (*-comm n m) ⟩
    m * (m * n * n)
  ≡⟨ cong (λ v → m * v) (*-assoc m n n) ⟩
    m * (m * (n * n))
  ≡⟨ sym (*-assoc m m (n * n)) ⟩
    (m * m) * (n * n)
  ∎

-a²≡a² : ∀ (a : ℤ) → (- a) ² ≡ a ²
-a²≡a² a = begin
    (- a) ² 
  ≡⟨ sym (cong (λ v → v ²) (-1*n≡-n a)) ⟩
    (-1ℤ * a) ²
  ≡⟨ ^-distrib-* 2ℤ -1ℤ a ⟩
    (-1ℤ) ² * a ²
  ≡⟨ *-identityˡ (a ²) ⟩
    a ²
  ∎ 

-a*b≡-ab : ∀ (a b : ℤ) → (- a) * b ≡ - (a * b)
-a*b≡-ab a b = 
  begin 
    (- a) * b
  ≡⟨ sym (cong (λ v → v * b) (-1*n≡-n a)) ⟩ 
    (-1ℤ * a) * b
  ≡⟨ *-assoc -1ℤ a b ⟩ 
    -1ℤ * (a * b)
  ≡⟨ -1*n≡-n (a * b) ⟩ 
    - (a * b)
  ∎

-a*-b≡ab : ∀ (a b : ℤ) → (- a) * (- b) ≡ a * b
-a*-b≡ab a b = 
  begin 
    (- a) * (- b)
  ≡⟨ -a*b≡-ab a (- b) ⟩ 
    - (a * (- b))
  ≡⟨ cong (-_) (*-comm a (- b)) ⟩ 
    - ((- b) * a)
  ≡⟨ cong (-_) (-a*b≡-ab b a) ⟩ 
    - - (b * a)
  ≡⟨ neg-involutive (b * a) ⟩ 
    b * a
  ≡⟨ *-comm b a ⟩ 
    a * b
  ∎

[a+b][c+d] : ∀ (a b c d : ℤ) → (a + b) * (c + d) ≡ a * c + a * d + b * c + b * d
[a+b][c+d] a b c d =
    begin
      (a + b) * (c + d)
    ≡⟨ *-distribʳ-+ (c + d) a b ⟩ 
      a * (c + d) + b * (c + d)
    ≡⟨ cong (λ v → v + b * (c + d)) (*-distribˡ-+ a c d) ⟩
      a * c + a * d + b * (c + d)
    ≡⟨ cong (λ v → a * c + a * d + v) (*-distribˡ-+ b c d) ⟩
      a * c + a * d + (b * c + b * d)
    ≡⟨ sym (+-assoc (a * c + a * d) (b * c) (b * d)) ⟩
      a * c + a * d + b * c + b * d
    ∎ 

[a-b][c-d] : ∀ (a b c d : ℤ) → (a - b) * (c - d) ≡ a * c - a * d - b * c + b * d
[a-b][c-d] a b c d =
    begin
      (a - b) * (c - d)
    ≡⟨ *-distribʳ-+ (c - d) a (- b) ⟩ 
      a * (c - d) + (- b) * (c - d)
    ≡⟨ cong (λ v → v + (- b) * (c - d)) (*-distribˡ-- a c d) ⟩
      a * c - a * d + (- b) * (c - d)
    ≡⟨ cong (λ v → a * c - a * d + v) (*-distribˡ-- (- b) c d) ⟩
      a * c - a * d + ((- b) * c + - ((- b) * d))
    ≡⟨ sym (+-assoc (a * c - a * d) ((- b) * c) (- ((- b) * d))) ⟩
      a * c - a * d + (- b) * c + - ((- b) * d)
    ≡⟨ cong (λ v → a * c - a * d + v + - ((- b) * d)) (-a*b≡-ab b c) ⟩
      a * c - a * d - (b * c) + - ((- b) * d)
    ≡⟨ cong (λ v → a * c - a * d - (b * c) - v ) (-a*b≡-ab b d) ⟩
      a * c - a * d - b * c + - (- (b * d))
    ≡⟨ cong (λ v → a * c - a * d - b * c + v) (neg-involutive (b * d)) ⟩
      a * c - a * d - b * c + b * d
    ∎ 

a-b² : ∀ (a b : ℤ) → (a - b) ² ≡ a ² - 2ℤ * (a * b) + b ²
a-b² a b =
  begin 
    (a - b) ² 
  ≡⟨ [a-b][c-d] a b a b ⟩ 
    a * a - a * b - b * a + b * b 
  ≡⟨ cong (λ v → a * a - a * b - v + b * b ) (*-comm b a)⟩ 
    a * a + (- (a * b)) + (- (a * b)) + b * b 
  ≡⟨ cong (λ v → v + b ²) (+-assoc (a ²) (- (a * b)) (- (a * b))) ⟩ 
    a ² + (- (a * b) + - (a * b)) + b ²
  ≡⟨ cong (λ v → a ² + v + b ²) (n+n≡2n (- (a * b))) ⟩ 
    a ² + 2ℤ * (- (a * b)) + b ² 
  ≡⟨ cong (λ v → a ² + v + b ²) (*-comm 2ℤ (- (a * b))) ⟩
    a ² + (- (a * b)) * 2ℤ + b ² 
  ≡⟨ cong (λ v → a ² + v + b ²) (-a*b≡-ab (a * b) 2ℤ) ⟩
    a ² + - ((a * b) * 2ℤ) + b ² 
  ≡⟨ cong (λ v → a ² - v + b ²) (*-comm (a * b) 2ℤ) ⟩
    a ² + - (2ℤ * (a * b)) + b ² 
  ∎

a+b² : ∀ (a b : ℤ) → (a + b) ² ≡ a ² + 2ℤ * (a * b) + b ²
a+b² a b = 
  begin 
    (a + b) ² 
  ≡⟨ [a+b][c+d] a b a b ⟩ 
    a * a + a * b + b * a + b * b 
  ≡⟨ cong (λ v → a * a + a * b + v + b * b ) (*-comm b a)⟩ 
    a * a + a * b + a * b + b * b 
  ≡⟨ cong (λ v → v + b ²) (+-assoc (a ²) (a * b) (a * b)) ⟩ 
    a ² + (a * b + a * b) + b ²
  ≡⟨ cong (λ v → a ² + v + b ²) (n+n≡2n (a * b)) ⟩ 
    a ² + 2ℤ * (a * b) + b ² 
  ∎