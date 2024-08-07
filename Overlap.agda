open import Figure using (Arrow; Shape; DragonF)

open import Data.List using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Fin

open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym; trans)

data Overlap : Arrow → Arrow → Set where
  OL-nor : ∀ {a1 a2 : Arrow}
    → Arrow.start a1 ≡ Arrow.start a2
    → Arrow.end   a1 ≡ Arrow.end   a2
    → Overlap a1 a2
    
  OL-rev : ∀ {a1 a2 : Arrow}
    → Arrow.start a1 ≡ Arrow.end   a2
    → Arrow.end   a1 ≡ Arrow.start a2
    → Overlap a1 a2

ol-trans : ∀ {a1 a2 a3 : Arrow}
  → Overlap a1 a2
  → Overlap a2 a3
  → Overlap a1 a3

ol-trans (OL-nor s1≡s2 e1≡e2) (OL-nor s2≡s3 e2≡e3) = OL-nor (trans s1≡s2 s2≡s3) (trans e1≡e2 e2≡e3)
ol-trans (OL-nor s1≡s2 e1≡e2) (OL-rev s2≡e3 e2≡s3) = OL-rev (trans s1≡s2 s2≡e3) (trans e1≡e2 e2≡s3)
ol-trans (OL-rev s1≡e2 e1≡s2) (OL-nor s2≡s3 e2≡e3) = OL-rev (trans s1≡e2 e2≡e3) (trans e1≡s2 s2≡s3)
ol-trans (OL-rev s1≡e2 e1≡s2) (OL-rev s2≡e3 e2≡s3) = OL-nor (trans s1≡e2 e2≡s3) (trans e1≡s2 s2≡e3)

data No-Overlap : Shape → Set where
  no-overlap : ∀ {shape : Shape}
    → (∀ (i j : Fin (length shape)) → i ≢ j → ¬ Overlap (lookup shape i) (lookup shape j))
    → No-Overlap shape

no-overlap-in-dragon : ∀ {shape : Shape}
  → DragonF shape
  → No-Overlap shape

no-overlap-in-dragon {shape} dragonF-pf = {!!}

-- data No-Overlap : Shape → Set where
--   NO1-base : No-Overlap []
    
--   NO1-suc : ∀ {arr : Arrow} → ∀ {shape : Shape}
--     → No-Overlap shape
--     → All (λ v → ¬ (Overlap arr v)) shape
--     → No-Overlap (arr ∷ shape)

-- no-two-arrows-overlap : ∀ {shape : Shape}
--   → No-Overlap shape
--   → (∀ (i j : Fin (length shape)) → i ≢ j → ¬ Overlap (lookup shape i) (lookup shape j))

-- no-two-arrows-overlap shape-not-ol = {!!}


-- open import Data.Nat using (ℕ; zero; suc)
   
-- data Fin : ℕ → Set where
--   fin-zero : ∀ {n : ℕ} → Fin (suc n)
--   fin-suc  : ∀ {n : ℕ} → (i : Fin n) → Fin (suc n)
  
-- exampleFin : Fin 3
-- exampleFin = fin-suc {2} (fin-zero {1})

