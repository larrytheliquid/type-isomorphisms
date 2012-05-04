module Examples where
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Bij

twoR : ⊤ ⊎ (⊤ ⊎ ⊤)
twoR = inj₂ (inj₁ tt)

twoL : (⊤ ⊎ ⊤) ⊎ ⊤
twoL = inj₁ (inj₂ tt)

middleR : ⊤ ⊎ (⊤ ⊎ ⊤) → Bool
middleR (inj₂ (inj₁ tt)) = true
middleR _ = false

middleL : (⊤ ⊎ ⊤) ⊎ ⊤ → Bool
-- middleL = ⟪ middleR ⟫
middleL (inj₁ (inj₂ tt)) = true
middleL _ = false


