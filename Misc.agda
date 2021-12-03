{-# OPTIONS --safe --without-K #-}
-- Miscellaneous definitions to go elsewhere, especially agda-std

module Misc where

open import Level
open import Function using (id; _∘_; _↔_; mk↔′; Inverse)
open import Data.Product as × using (_,_; _×_; proj₁; proj₂)
open import Data.Unit
open import Data.Nat
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec as V using (Vec)
import Data.Vec.Properties as V
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Bundles using (Setoid)

private variable
  a ℓ : Level
  A B C D : Set a
  Q R S : Setoid a ℓ
  n : ℕ

infixr 9 _∘̇_
_∘̇_ : Inverse R S → Inverse Q R → Inverse Q S
g ∘̇ f = inverse f g where open import Function.Construct.Composition

-- In agda-std-2.0
1↔⊤ : Fin 1 ↔ ⊤
1↔⊤ = mk↔′ (λ { 0F → tt }) (λ { tt → 0F }) (λ { tt → refl }) λ { 0F → refl }

-- Does this operation live anywhere?
_⁻¹ : Inverse R S → Inverse S R
inv ⁻¹ = record
  { f = inv.f⁻¹
  ; f⁻¹ = inv.f
  ; cong₁ = inv.cong₂
  ; cong₂ = inv.cong₁
  ; inverse = ×.swap inv.inverse
  } where module inv = Inverse inv

dom : A ↔ B → Inverse (A →-setoid C) (B →-setoid C)
dom A↔B = record
  { f = _∘ f⁻¹
  ; f⁻¹ = _∘ f
  ; cong₁ = _∘ f⁻¹
  ; cong₂ = _∘ f
  ; inverse = (λ g → cong g ∘ proj₁ inverse)
            , (λ g → cong g ∘ proj₂ inverse)
  } where open Inverse A↔B


-- TODO: propose for agda-stdlib
vec-fun-inverse : Inverse (≡.setoid (Vec A n)) (Fin n →-setoid A)
vec-fun-inverse = record
  { f       = V.lookup
  ; f⁻¹     = V.tabulate
  ; cong₁   = λ { refl i → refl }
  ; cong₂   = V.tabulate-cong
  ; inverse = V.lookup∘tabulate , V.tabulate∘lookup
  }

-- Alternatively
fun-vec-inverse : Inverse (Fin n →-setoid A) (≡.setoid (Vec A n))
fun-vec-inverse = vec-fun-inverse ⁻¹
