-- open import Parity using (Same-Parity)
open import Parity using (Even; Odd)
open import Geometry using (Coord; Arrow; _+ᶜ_; arrow-vec; Same-Parity-Coord; 45↑-clw-arr; 45↑-ccw-arr; 45↓-clw; 45↓-ccw; 45↑-ccw-arr-parity; 45↑-clw-arr-parity)
open import Sequence using (Op; R; L)

open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.List using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookup-all)
open import Relation.Nullary using (¬_)

open import Data.Fin using (Fin; zero; suc; pred)
open import Data.Fin.Properties using (<-cmp)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)

Shape = List Arrow

Overlap : Arrow → Arrow → Set
Overlap a1 a2 = 
  ((Arrow.s a1 ≡ Arrow.s a2) × (Arrow.e a1 ≡ Arrow.e a2)) ⊎
  ((Arrow.s a1 ≡ Arrow.e a2) × (Arrow.e a1 ≡ Arrow.s a2))

OL-trans : ∀ {a1 a2 : Arrow} → Overlap a1 a2 → Overlap a2 a1 
OL-trans (inj₁ cis-pf) = inj₁ ⟨ sym (proj₁ cis-pf) , sym (proj₂ cis-pf) ⟩
OL-trans (inj₂ tra-pf) = inj₂ ⟨ sym (proj₂ tra-pf) , sym (proj₁ tra-pf) ⟩

data No-Overlap-Shape : Shape → Set where
  NOS-zero : No-Overlap-Shape []

  NOS-suc : ∀ {arr : Arrow} → ∀ {sha : Shape}
    → All (λ v → ¬ Overlap arr v) sha
    → No-Overlap-Shape sha
    → No-Overlap-Shape (arr ∷ sha)

No-Overlap-Shape-Any : Shape → Set
No-Overlap-Shape-Any sha = ∀ i j → i ≢ j → ¬ Overlap (lookup sha i) (lookup sha j)

remove-one : ∀ {arr} → ∀ {sha} → No-Overlap-Shape-Any (arr ∷ sha) → No-Overlap-Shape-Any sha
remove-one {arr} {sha} pf = λ i j i≢j → pf (suc i) (suc j) (λ si≡sj → i≢j (finSucInj si≡sj))
  where
    finSucInj : ∀ {n} {i j : Fin n} → suc i ≡ suc j → i ≡ j
    finSucInj refl = refl

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open import Relation.Binary using (Tri)

⇔-NOS : ∀ sha → No-Overlap-Shape sha ⇔ No-Overlap-Shape-Any sha
⇔-NOS [] = record { to = λ _ → λ() ; from = λ _ → NOS-zero }
⇔-NOS (x ∷ sha) = record { to = help1 ; from = help2 } where 
  
  help1 : No-Overlap-Shape (x ∷ sha) → No-Overlap-Shape-Any (x ∷ sha)
  -- help1 pf = λ i j i≢j → {!   !}
  help1 pf i j i≢j ol-ij with <-cmp i j
  ... | Tri.tri< a ¬b ¬c = {! pf !} 
  ... | Tri.tri≈ ¬a b ¬c = i≢j b
  ... | Tri.tri> ¬a ¬b c = {! case for i > j !}
  
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

expand-arrow : Op → Arrow → Arrow × Arrow
expand-arrow R arr = ⟨ arr1 , arr2 ⟩ where
  
  slanted-arr : Arrow
  slanted-arr = 45↑-ccw-arr arr

  vec : Coord
  vec = arrow-vec slanted-arr

  rotated-vec = 45↓-clw vec (45↑-ccw-arr-parity arr) 

  mid : Coord
  mid = (Arrow.s slanted-arr) +ᶜ rotated-vec

  arr1 : Arrow
  arr1 = record {s = Arrow.s slanted-arr ; e = mid}

  arr2 : Arrow
  arr2 = record {s = Arrow.e slanted-arr ; e = mid}

expand-arrow L arr = ⟨ arr1 , arr2 ⟩ where
  
  slanted-arr : Arrow
  slanted-arr = 45↑-clw-arr arr

  vec : Coord
  vec = arrow-vec slanted-arr

  rotated-vec = 45↓-ccw vec (45↑-clw-arr-parity arr) 

  mid : Coord
  mid = (Arrow.s slanted-arr) +ᶜ rotated-vec

  arr1 : Arrow
  arr1 = record {s = Arrow.s slanted-arr ; e = mid}

  arr2 : Arrow
  arr2 = record {s = Arrow.e slanted-arr ; e = mid}

expand-shape : Op → Shape → Shape
expand-shape op [] = []
expand-shape op (x ∷ sha) = proj₁ arrs ∷ proj₂ arrs ∷ (expand-shape op sha) where 
  arrs : Arrow × Arrow
  arrs = expand-arrow op x

data DragonG : Shape → Set where
  DG-zero : DragonG stub

  DG-suc-R : ∀ {sha : Shape}
    → DragonG sha
    → DragonG (expand-shape R sha)

  DG-suc-L : ∀ {sha : Shape}
    → DragonG sha
    → DragonG (expand-shape L sha)

-- For now, it's horizontal and vertical
Grid-Pattern : Arrow → Set
Grid-Pattern record { s = record { x = sx ; y = sy } ; e = record { x = ex ; y = ey } } 
  = Even (sx + sy) × Odd (ex + ey)

GP-NOL2 : ∀ (a1 a2 : Arrow) → ∀ op 
  → Grid-Pattern a1 
  → Grid-Pattern a2 
  → ¬ Overlap a1 a2 
  → No-Overlap-Shape (expand-shape op (a1 ∷ a2 ∷ []))
GP-NOL2 = {!   !}

GP-preserve : ∀ {sha} → ∀ op → All Grid-Pattern sha → All Grid-Pattern (expand-shape op sha)
GP-preserve = {!   !}

NOS-preserve : ∀ {sha} → ∀ op → No-Overlap-Shape sha → All Grid-Pattern sha → No-Overlap-Shape (expand-shape op sha)
NOS-preserve op NOS-zero [] = NOS-zero
NOS-preserve {arr ∷ sha} op (NOS-suc x nos) (gp ∷ gps) = NOS-suc {!   !} (NOS-suc help1 (NOS-preserve op nos gps)) where
  help1 : All (λ v → ¬ Overlap (proj₂ (expand-arrow op arr)) v) (expand-shape op sha) 
  help1 = {!   !}

dragon-on-grid : ∀ {sha} → DragonG sha → All Grid-Pattern sha
dragon-on-grid DG-zero = {!   !}
dragon-on-grid (DG-suc-R dra) = GP-preserve R (dragon-on-grid dra)
dragon-on-grid (DG-suc-L dra) = GP-preserve L (dragon-on-grid dra)

-- "Any" version would be easier?

no-overlap-in-dragonG : ∀ {sha : Shape} → DragonG sha → No-Overlap-Shape sha
no-overlap-in-dragonG DG-zero = NOS-suc [] NOS-zero
no-overlap-in-dragonG (DG-suc-R dra) = NOS-preserve R (no-overlap-in-dragonG dra) (dragon-on-grid dra) 
no-overlap-in-dragonG (DG-suc-L dra) = NOS-preserve L (no-overlap-in-dragonG dra) (dragon-on-grid dra) 

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

dragon1 : expand-shape R stub ≡ 
  record {
    s = record { x = + 0 ; y = + 0 } ;
    e = record { x = + 0 ; y = + 1 }
  } ∷ record {
    s = record { x = -[1+ 0 ] ; y = + 1 } ;
    e = record { x = + 0 ; y = + 1 }
  } ∷ []
dragon1 = refl 

dragon3 : expand-shape L (expand-shape R stub) ≡ 
  record {
    s = record { x = + 0 ; y = + 0 } ;
    e = record { x = + 0 ; y = + 1 }
  } ∷ record {
    s = record { x = + 1 ; y = + 1 } ;
    e = record { x = + 0 ; y = + 1 }
  } ∷ record {
    s = record { x = + 0 ; y = + 2 } ;
    e = record { x = + 1 ; y = + 2 }
  } ∷ record {
    s = record { x = + 1 ; y = + 1 } ;
    e = record { x = + 1 ; y = + 2 }
  } ∷ []
dragon3 = refl 
  
     