module Scan where

infix 6 _`+_
infix 7 _`×_
data Shape : Set where
  `⊥ `⊤ : Shape
  _`+_ _`×_  : Shape → Shape → Shape

open import Level

private variable
  s t : Shape
  ℓ : Level
  A B C : Set ℓ

open import Data.Nat

# : Shape → ℕ
# `⊥ = 0
# `⊤ = 1
# (s `+ t) = # s + # t
# (s `× t) = # s * # t

infix 7 _⊗_

data T {a} (A : Set a) : Shape → Set a where
  1̇ : T A `⊥
  I : A → T A `⊤
  _⊗_ : T A s → T A t → T A (s `+ t)
  ◎ : T (T A t) s → T A (s `× t)

map : (A → B) → T A s → T B s
map f 1̇       = 1̇
map f (I x)   = I (f x)
map f (u ⊗ v) = map f u ⊗ map f v
map f (◎ us)  = ◎ (map (map f) us)
-- Synthesized by Agda

zipWith : (A → B → C) → T A s → T B s → T C s
zipWith f 1̇ 1̇ = 1̇
zipWith f (I x) (I y) = I (f x y)
zipWith f (u₁ ⊗ u₂) (v₁ ⊗ v₂) = zipWith f u₁ v₁ ⊗ zipWith f u₂ v₂
zipWith f (◎ u) (◎ v) = ◎ (zipWith (zipWith f) u v)
-- Synthesized by Agda

open import Data.Product hiding (map)

unzip : T (A × B) s → T A s × T B s
unzip 1̇ = 1̇ , 1̇
unzip (I (x , y)) = I x , I y
unzip (u ⊗ v) = let u₁ , u₂ = unzip u
                    v₁ , v₂ = unzip v
                in
                  u₁ ⊗ v₁ , u₂ ⊗ v₂
unzip (◎ w) = {!w!}

open import Algebra.Bundles

module _ {c ℓ} (M : Monoid c ℓ) where

  open Monoid M renaming (Carrier to X)

  scanˡ : ∀ s → T X s → T X s × X
  scanˡ `⊥ 1̇ = 1̇ , ε
  scanˡ `⊤ (I x) = I ε , x
  scanˡ (s `+ t) (u ⊗ v) =
    let u′ , x = scanˡ s u
        v′ , y = scanˡ t v
    in
      u′ ⊗ map (x ∙_) v′ , (x ∙ y)
  scanˡ (s `× t) (◎ w) =
    let w′ , zs = unzip (map (scanˡ t) w)
        zs′ , z′ = scanˡ s zs
        tweak t = map (t ∙_)
    in
      ◎ (zipWith tweak zs′ w′) , z′

-- TODO: Make s parameter implicit

