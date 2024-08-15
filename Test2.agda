open import Geometry using (Coord; Arrow)
open import Sequence using (Op; R; L)

open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (¬_)

open import Data.Fin

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)

Shape = List Arrow

Overlap : Arrow → Arrow → Set
Overlap a1 a2 = 
  ((Arrow.s a1 ≡ Arrow.s a2) × (Arrow.e a1 ≡ Arrow.e a2)) ⊎
  ((Arrow.s a1 ≡ Arrow.e a2) × (Arrow.e a1 ≡ Arrow.s a2))

data No-Overlap-Shape : Shape → Set where
  NOS-zero : No-Overlap-Shape []

  NOS-suc : ∀ {arr : Arrow} → ∀ {sha : Shape}
    → All (λ v → ¬ Overlap arr v) sha
    → No-Overlap-Shape sha
    → No-Overlap-Shape (arr ∷ sha)

No-Overlap-Shape-Any : Shape → Set
No-Overlap-Shape-Any sha = ∀ (i j : Fin (length sha)) → i ≢ j → ¬ Overlap (lookup sha i) (lookup sha j)

remove-one : ∀ {arr} → ∀ {sha} → No-Overlap-Shape-Any (arr ∷ sha) → No-Overlap-Shape-Any sha
remove-one = {!   !}

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-NOS : ∀ sha → No-Overlap-Shape sha ⇔ No-Overlap-Shape-Any sha
⇔-NOS [] = record { to = λ _ → λ() ; from = λ _ → NOS-zero }
⇔-NOS (x ∷ sha) = record { to = help1 ; from = help2 } where 
  
  help1 : No-Overlap-Shape (x ∷ sha) → No-Overlap-Shape-Any (x ∷ sha)
  help1 pf = {!   !}
  
  help2-1 : ∀ {arr} → ∀ {sha} → No-Overlap-Shape-Any (arr ∷ sha) → All (λ v → ¬ Overlap arr v) sha
  help2-1 {arr} {[]} pf = []
  help2-1 {arr} {x ∷ sha} pf = (pf zero (suc zero) λ()) ∷ (help2-1 {! !})

  help2 : No-Overlap-Shape-Any (x ∷ sha) → No-Overlap-Shape (x ∷ sha)
  help2 pf = NOS-suc {!   !} (_⇔_.from (⇔-NOS sha) (remove-one pf))

stub : Shape
stub = record {
  s = record {x = 0ℤ ; y = 0ℤ} ;
  e = record {x = 0ℤ ; y = 1ℤ}
  } ∷ []

rotate-shape : Op → Shape → Shape
rotate-shape op sha = {!   !}

expand-shape : Op → Shape → Shape
expand-shape op sha = {!   !}

data DragonG : Shape → Set where
  DG-zero : DragonG stub

  DG-suc-R : ∀ {sha : Shape}
    → DragonG sha
    → DragonG (expand-shape R (rotate-shape R sha))

  DG-suc-L : ∀ {sha : Shape}
    → DragonG sha
    → DragonG (expand-shape L (rotate-shape L sha))

-- For now, it's horizontal and vertical
Grid-Pattern : Arrow → Set
Grid-Pattern arr = {!   !}

GP-preserve : ∀ {sha} → ∀ op → All Grid-Pattern sha → All Grid-Pattern (expand-shape op (rotate-shape op sha))
GP-preserve = {!   !}

NOS-preserve : ∀ {sha} → ∀ op → No-Overlap-Shape sha → All Grid-Pattern sha → No-Overlap-Shape (expand-shape op (rotate-shape op sha))
NOS-preserve = {!   !}

dragon-on-grid : ∀ {sha} → DragonG sha → All Grid-Pattern sha
dragon-on-grid DG-zero = {!   !}
dragon-on-grid (DG-suc-R dra) = GP-preserve R (dragon-on-grid dra)
dragon-on-grid (DG-suc-L dra) = GP-preserve L (dragon-on-grid dra)

-- "Any" version would be easier?

no-overlap-in-dragonG : ∀ {sha : Shape} → DragonG sha → No-Overlap-Shape sha
no-overlap-in-dragonG DG-zero = NOS-suc [] NOS-zero
no-overlap-in-dragonG (DG-suc-R dra) = NOS-preserve R (no-overlap-in-dragonG dra) (dragon-on-grid dra) 
no-overlap-in-dragonG (DG-suc-L dra) = NOS-preserve L (no-overlap-in-dragonG dra) (dragon-on-grid dra) 

-- no-overlap-in-dragonG : ∀ {sha : Shape} → DragonG sha → No-Overlap-Shape-Any sha
-- no-overlap-in-dragonG DG-zero = λ i j → (λ())
-- no-overlap-in-dragonG (DG-suc dra) = {!   !}



-- Tests

arr1 : Arrow
arr1 = record {
  s = record {x = 0ℤ ; y = 1ℤ} ;
  e = record {x = 1ℤ ; y = 1ℤ}
  }

arr2 : Arrow
arr2 = record {
  s = record {x = 1ℤ ; y = 1ℤ} ;
  e = record {x = 0ℤ ; y = 1ℤ}
  }

_ : Overlap arr1 arr2
_ = inj₂ ⟨ refl , refl ⟩
 
  