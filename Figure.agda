{-# OPTIONS --allow-unsolved-metas #-}

module Figure where

open import Sequence using (Op; R; L; Alphabet; X; Y; [+]; [-]; dragonL)
-- open import Parity using (Even; Odd; Same-Parity; SP-o; sp→e[m+n]; sp→e[m-n]; sp→e[n-m])

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -[1+_]; +[1+_]; _+_; _-_; _*_;  -_)
open import Data.Integer.Properties using (+-comm; +-assoc; *-comm; *-assoc; *-distribˡ-+; -1*n≡-n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
-- open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-- data even : ℤ → Set
-- data odd  : ℤ → Set

-- data even where

--   even-zero : even 0ℤ

--   even-suc : ∀ {n : ℕ}
--     → odd  (+ n)
--     ----------------
--     → even (+ (suc n))

--   even-inv : ∀ {n : ℕ}
--     → odd  (+ n)
--     ---------------
--     → even (-[1+ n ])

-- data odd where

--   odd-suc  : ∀ {n : ℕ}
--     → even (+ n)
--     ----------------
--     → odd  (+ (suc n))

--   odd-inv : ∀ {n : ℕ}
--     → even (+ n)
--     ---------------
--     → odd  (-[1+ n ])

-1ℤ : ℤ
-1ℤ = -[1+ 0 ]

-- record Coord : Set where
--   field
--     x : ℤ
--     y : ℤ

data ArrowType : Set where
  forw : ArrowType
  back : ArrowType
  
record Arrow : Set where
  field
    type  : ArrowType
    start : Coord
    end   : Coord

-- Transform : Set
-- Transform = Coord → Coord

Shape : Set
Shape = List Arrow

-- ∧-45-clw : Transform
-- ∧-45-clw record { x = x ; y = y } =
--   record
--     { x = x + y
--     ; y = (- x) + y
--     }

-- ∧-45-ccw : Transform
-- ∧-45-ccw record { x = x ; y = y } =
--   record
--     { x = x - y
--     ; y = x + y
--     }

-- ∧-45-clw-arr : Arrow → Arrow
-- ∧-45-clw-arr record { type = type ; start = start ; end = end }
--   = record { type = type ; start = ∧-45-clw start ; end = ∧-45-clw end }

-- ∧-45-ccw-arr : Arrow → Arrow
-- ∧-45-ccw-arr record { type = type ; start = start ; end = end }
--   = record { type = type ; start = ∧-45-ccw start ; end = ∧-45-ccw end }

-- half : ∀ {n : ℤ} → Even n → ℤ
-- half ⟨ z , _ ⟩ = z 

-- ∨-45-clw : ∀ ( ( record { x = x ; y = y } ) : Coord ) → Same-Parity x y → Coord
-- ∨-45-clw record { x = x ; y = y } same =
--   record
--     { x = half (sp→e[m+n] same)
--     ; y = half (sp→e[n-m] same)
--     }

-- ∨-45-ccw : ∀ ( ( record { x = x ; y = y } ) : Coord ) → Same-Parity x y → Coord
-- ∨-45-ccw record { x = x ; y = y } same =
--   record
--     { x = half (sp→e[m-n] same)
--     ; y = half (sp→e[m+n] same)
--     }
    
data Expandable : Arrow → Set where
  expandable : ∀ {arr : Arrow}
    → Same-Parity
      (Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr))
      (Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr))
    → Expandable arr
  
expand-arrow[R] : ∀ (arr : Arrow) → Expandable arr → Arrow × Arrow
expand-arrow[R] arr (expandable vec-sp) = ⟨ a1 , a2 ⟩ where
  vec : Coord
  vec = record { x = Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ;
                 y = Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) }
  
  tfVec : Coord
  tfVec = ∨-45-clw vec vec-sp
  
  mp : Coord
  mp = record { x = Coord.x (Arrow.start arr) + Coord.x tfVec ;
                y = Coord.y (Arrow.start arr) + Coord.y tfVec }
                
  a1 : Arrow
  a1 with Arrow.type arr
  ...    | forw = record { type = forw ; start = Arrow.start arr ; end = mp }
  ...    | back = record { type = back ; start = Arrow.end arr   ; end = mp }
  
  a2 : Arrow
  a2 with Arrow.type arr
  ...    | forw = record { type = back ; start = Arrow.end arr   ; end = mp }
  ...    | back = record { type = forw ; start = Arrow.start arr ; end = mp }

expand-arrow[L] : ∀ (arr : Arrow) → Expandable arr → Arrow × Arrow
expand-arrow[L] arr (expandable vec-sp) = ⟨ a1 , a2 ⟩ where
  vec : Coord
  vec = record { x = Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ;
                 y = Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) }

  tfVec : Coord
  tfVec = ∨-45-ccw vec vec-sp
  
  mp : Coord
  mp = record { x = Coord.x (Arrow.start arr) + Coord.x tfVec ;
                y = Coord.y (Arrow.start arr) + Coord.y tfVec }
                
  a1 : Arrow
  a1 with Arrow.type arr
  ...    | forw = record { type = forw ; start = Arrow.start arr ; end = mp }
  ...    | back = record { type = back ; start = Arrow.end arr   ; end = mp }
  
  a2 : Arrow
  a2 with Arrow.type arr
  ...    | forw = record { type = back ; start = Arrow.end arr   ; end = mp }
  ...    | back = record { type = forw ; start = Arrow.start arr ; end = mp }

stub : Shape
stub =
  record
    { type  = forw
    ; start = record { x = 0ℤ ; y = 0ℤ }
    ; end   = record { x = 0ℤ ; y = 1ℤ }
    }
  ∷ []

data DragonF    : Shape → Set
data DragonF[/] : Shape → Set
data DragonF[\] : Shape → Set

dragon-exp[/] : ∀ { dragon : Shape } → DragonF[/] dragon → All Expandable dragon
dragon-exp[\] : ∀ { dragon : Shape } → DragonF[\] dragon → All Expandable dragon

tilt-dragon[/] : Shape → Shape
tilt-dragon[\] : Shape → Shape

expand-dragon[R]  : ∀ { dragon : Shape } → DragonF[\] dragon → Shape
expand-dragon[L]  : ∀ { dragon : Shape } → DragonF[/] dragon → Shape

data DragonF where
  df-base : DragonF stub
  
  df-suc[R]  : ∀ {d : Shape}
    → ∀ (pf : DragonF[\] d)
    → DragonF (expand-dragon[R] pf)

  df-suc[L]  : ∀ {d : Shape}
    → ∀ (pf : DragonF[/] d)
    → DragonF (expand-dragon[L] pf)
    
data DragonF[\] where
  df-suc[\] : ∀ {d : Shape}
    → DragonF d
    → DragonF[\] (tilt-dragon[\] d)

data DragonF[/] where
  df-suc[/] : ∀ {d : Shape}
    → DragonF d
    → DragonF[/] (tilt-dragon[/] d)

tilt-dragon[/] [] = []
tilt-dragon[/] (arr ∷ sha) =
  record
    { type  = Arrow.type arr
    ; start = ∧-45-clw (Arrow.start arr)
    ; end   = ∧-45-clw (Arrow.end arr)
    } ∷ (tilt-dragon[/] sha)

tilt-dragon[\] [] = []
tilt-dragon[\] (arr ∷ sha) =
  record
    { type  = Arrow.type arr
    ; start = ∧-45-ccw (Arrow.start arr)
    ; end   = ∧-45-ccw (Arrow.end arr)
    } ∷ (tilt-dragon[\] sha)

expand-dragon[R] {dragon} pf[\] = helper (dragon-exp[\] pf[\]) where
  helper : ∀ {sha : Shape} →  All Expandable sha → Shape
  helper [] = []
  helper ((expandable {arr} sp) ∷ all-pfs) = (proj₁ prod) ∷ (proj₂ prod) ∷ (helper all-pfs) where
    prod : Arrow × Arrow
    prod = expand-arrow[R] arr (expandable sp)

expand-dragon[L] {dragon} pf[/] = helper (dragon-exp[/] pf[/]) where
  helper : ∀ {sha : Shape} →  All Expandable sha → Shape
  helper [] = []
  helper ((expandable {arr} sp) ∷ all-pfs) = (proj₁ prod) ∷ (proj₂ prod) ∷ (helper all-pfs) where
    prod : Arrow × Arrow
    prod = expand-arrow[L] arr (expandable sp) 

-- define unit
data Unit : Arrow → Set where
  U-U : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ 0ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ 1ℤ
    → Unit arr

  U-D : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ 0ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ -1ℤ
    → Unit arr

  U-L : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ -1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ 0ℤ
    → Unit arr

  U-R : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ 1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ 0ℤ
    → Unit arr
    
-- define unit-diagonal
data Unit-Diagonal : Arrow → Set where
  UR : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ 1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ 1ℤ
    → Unit-Diagonal arr

  UL : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ -1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ 1ℤ
    → Unit-Diagonal arr

  DR : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ 1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ -1ℤ
    → Unit-Diagonal arr

  DL : ∀ {arr : Arrow}
    → Coord.x (Arrow.end arr) - Coord.x (Arrow.start arr) ≡ -1ℤ
    → Coord.y (Arrow.end arr) - Coord.y (Arrow.start arr) ≡ -1ℤ
    → Unit-Diagonal arr

-- Unit after transformation → Unit-Diagonal
unit→unit-diag : ∀ {arr : Arrow} → Unit arr → Unit-Diagonal (∧-45-clw-arr arr)
unit→unit-diag {arr} (U-U dx≡0 dy≡1)
  = UR {!!} {!!}
unit→unit-diag (U-D x x₁) = {!!}
unit→unit-diag (U-L x x₁) = {!!}
unit→unit-diag (U-R x x₁) = {!!}

-- Unit-Diagonal after expansion → two Units
-- unit-diag→unit :


-- all arrows in DragonF[/] are unit-diagonal
a∈dra→unit : ∀ {shape : Shape} → DragonF shape → All Unit shape
a∈dra→unit df = {!!}

a∈[/]→unit-diag : ∀ {shape : Shape} → DragonF[/] shape → All Unit-Diagonal shape
a∈[/]→unit-diag (df-suc[/] x) = {!!}

a∈[\]→unit-diag : ∀ {shape : Shape} → DragonF[\] shape → All Unit-Diagonal shape
a∈[\]→unit-diag (df-suc[\] x) = {!!}

-- unit-diagonal arrows are expandable
unit-diag→exp : ∀ {arr : Arrow} → Unit-Diagonal arr → Expandable arr
unit-diag→exp (UR dx≡1  dy≡1 ) = expandable (SP-o ⟨ 0ℤ  , dx≡1  ⟩ ⟨ 0ℤ  , dy≡1  ⟩)
unit-diag→exp (UL dx≡-1 dy≡1 ) = expandable (SP-o ⟨ -1ℤ , dx≡-1 ⟩ ⟨ 0ℤ  , dy≡1  ⟩)
unit-diag→exp (DR dx≡1  dy≡-1) = expandable (SP-o ⟨ 0ℤ  , dx≡1  ⟩ ⟨ -1ℤ , dy≡-1 ⟩)
unit-diag→exp (DL dx≡-1 dy≡-1) = expandable (SP-o ⟨ -1ℤ , dx≡-1 ⟩ ⟨ -1ℤ , dy≡-1 ⟩)

-- all arrows in DragonF[/] and DragonF[\] are expandable
dragon-exp[/] {shape} df = helper (a∈[/]→unit-diag df) where
  helper : ∀ {sha : Shape} → All Unit-Diagonal sha → All Expandable sha
  helper [] = []
  helper (px ∷ ud) = (unit-diag→exp px) ∷ helper ud

dragon-exp[\] {shape} df = helper (a∈[\]→unit-diag df) where
  helper : ∀ {sha : Shape} → All Unit-Diagonal sha → All Expandable sha
  helper [] = []
  helper (px ∷ ud) = (unit-diag→exp px) ∷ helper ud


-- main
origin : Coord
origin = record { x = 0ℤ ; y = 0ℤ }

unit : Coord
unit = record { x = 0ℤ ; y = 1ℤ }

90[/] : Transform
90[/] record { x = x ; y = y } = record { x = y ; y = - x }

90[\] : Transform
90[\] record { x = x ; y = y } = record { x = - y ; y = x }

_⊕_ : Coord → Coord → Coord
c1 ⊕ c2 = record { x = Coord.x c1 + Coord.x c2 ; y = Coord.y c1 + Coord.y c2 }

dragonL-to-F : List Alphabet → Shape
dragonL-to-F list = helper list origin unit where
  helper : List Alphabet → Coord → Coord → Shape
  helper [] _ _ = []
  helper (X ∷ list) coord dir =
    record
      { type = forw
      ; start = coord
      ; end = coord ⊕ dir
      } ∷ (helper list (coord ⊕ dir) dir)
      
  helper (Y ∷ list) coord dir =
    record
      { type = back
      ; start = coord ⊕ dir
      ; end = coord
      } ∷ (helper list (coord ⊕ dir) dir)
      
  helper ([+] ∷ list) coord dir = helper list coord (90[\] dir)
  helper ([-] ∷ list) coord dir = helper list coord (90[/] dir)

LF-≡ : ∀ (list : List Op) → DragonF (dragonL-to-F (dragonL X list))
LF-≡ = {!!}
    
_ : DragonF (dragonL-to-F (dragonL X ([])))
_ = df-base

-- _ : DragonF (dragonL-to-F (dragonL X (L ∷ [])))
-- _ = df-suc[L] (df-suc[/] df-base)

-- _ : DragonF (dragonL-to-F (dragonL X (L ∷ [])))
-- _ = LF-≡ (L ∷ [])




-- Tests

even[-6] : Even (-[1+ 5 ])
even[-6] = ⟨ (-[1+ 2 ]) , refl ⟩

half[-6] : half even[-6] ≡ -[1+ 2 ]
half[-6] = refl

-- stubArr : Arrow
-- stubArr =
--   record
--     { start = record { x = + 2 ; y = -[1+ 1 ] }
--     ; end   = record { x = + 4 ; y = -[1+ 7 ] }
--     }
    
-- expansionTest1 : expand-arrow[R] stubArr (arrExp (even-suc (odd-suc even-zero)) (even-inv (odd-suc (even-suc (odd-suc (even-suc (odd-suc even-zero)))))) ) ≡
--   ⟨
--     record
--       { start = record { x = + 2 ; y = -[1+ 1 ] }
--       ; end =   record { x = + 0 ; y = -[1+ 5 ] }
--       }
--   ,
--     record
--       { start = record { x = + 4 ; y = -[1+ 7 ] }
--       ; end =   record { x = + 0 ; y = -[1+ 5 ] }
--       }
--   ⟩
-- expansionTest1 = refl

-- expansionTest2 : expand-arrow[L] stubArr (arrExp (even-suc (odd-suc even-zero)) (even-inv (odd-suc (even-suc (odd-suc (even-suc (odd-suc even-zero)))))) ) ≡
--   ⟨
--     record
--       { start = record { x = + 2 ; y = -[1+ 1 ] }
--       ; end =   record { x = + 6 ; y = -[1+ 3 ] }
--       }
--   ,
--     record
--       { start = record { x = + 4 ; y = -[1+ 7 ] }
--       ; end =   record { x = + 6 ; y = -[1+ 3 ] }
--       }
--   ⟩
-- expansionTest2 = refl
