{-# OPTIONS --safe --without-K #-}
module Shape where

open import Function using (_↔_)
open import Data.Product as × using (_×_)
open import Data.Empty using (⊥)
open import Data.Unit  using (⊤)
open import Data.Sum using (_⊎_)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties renaming (Fin0↔⊥ to 0↔⊥)
open import Data.Vec using (Vec)

open import Misc

-- Most of the content below will be moved into other top-level modules and
-- shared with FFT and other algorithm families.

infix 6 _`⊎_
infix 7 _`×_
data Shape : Set where
  `⊥ `⊤ : Shape
  _`⊎_ _`×_  : Shape → Shape → Shape

# : Shape → ℕ
#    `⊥    =     0
#    `⊤    =     1
# (s `⊎ t) = # s + # t
# (s `× t) = # s * # t

Index : Shape → Set
Index    `⊥    =         ⊥
Index    `⊤    =         ⊤
Index (s `⊎ t) = Index s ⊎ Index t
Index (s `× t) = Index s × Index t

-- TODO: Generalize # and Index to Semiring

open import Function.Construct.Product using () renaming (_⊗-↔_ to _⊗̇_)
open import Function.Construct.Sum     using () renaming (_⊕-↔_ to _⊕̇_)

fin↔index : (s : Shape) → Fin (# s) ↔ Index s
fin↔index    `⊥    = 0↔⊥
fin↔index    `⊤    = 1↔⊤
fin↔index (s `⊎ t) = (fin↔index s ⊕̇ fin↔index t) ∘̇ +↔⊎
fin↔index (s `× t) = (fin↔index s ⊗̇ fin↔index t) ∘̇ *↔×
