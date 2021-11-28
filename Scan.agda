module Scan where

open import Level

open import Function using (_∘_)
open import Data.Product renaming (map to map×)

infix 6 _`+_
infix 7 _`×_
data Shape : Set where
  `⊥ `⊤ : Shape
  _`+_ _`×_  : Shape → Shape → Shape

private variable
  s t : Shape
  A B C D : Set

open import Data.Nat

# : Shape → ℕ
# `⊥ = 0
# `⊤ = 1
# (s `+ t) = # s + # t
# (s `× t) = # s * # t

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (map to map⊎)

Index : Shape → Set
Index `⊥ = ⊥
Index `⊤ = ⊤
Index (s `+ t) = Index s ⊎ Index t
Index (s `× t) = Index s × Index t

-- Tries (Naperian functors) as inductive type family. We can then pattern-match
-- over tries and leave shape arguments implicit.
module InductiveTrie where

  infix 7 _⊗_
  data T (A : Set) : Shape → Set where
    1̇ : T A `⊥
    I : A → T A `⊤
    _⊗_ : T A s → T A t → T A (s `+ t)
    ◎ : T (T A t) s → T A (s `× t)

  infixl 1 _!_

  at _!_ : T A s → Index s → A
  at (I x)   = λ { tt → x }
  at (u ⊗ v) = [ at u , at v ]
  at (◎ w)   = uncurry (at ∘ at w)

  _!_ = at

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

  transpose : (T A s × T B s) → (T A t × T B t) → (T A (s `+ t) × T B (s `+ t))
  transpose (u₁ , u₂) (v₁ , v₂) = u₁ ⊗ v₁ , u₂ ⊗ v₂  -- synthesized

  unzip : T (A × B) s → T A s × T B s
  unzip 1̇ = 1̇ , 1̇
  unzip (I (x , y)) = I x , I y
  unzip (u ⊗ v) = transpose (unzip u) (unzip v)
  unzip (◎ w) = map× ◎ ◎ (unzip (map unzip w))

  -- T (A × B) (s `× t)
  -- T (T (A × B) t) s
  -- T (T A t × T B t) s
  -- T (T A t) s × T (T B t) s
  -- T A (s × t) × T B (s × t)

  open import Algebra.Bundles

  module _ {ℓ} (M : Monoid 0ℓ ℓ) where

    open Monoid M renaming (Carrier to X)

    scanˡ : T X s → T X s × X
    scanˡ {`⊥} 1̇ = 1̇ , ε
    scanˡ {`⊤} (I x) = I ε , x
    scanˡ {s `+ t} (u ⊗ v) =
      let u′ , x = scanˡ u
          v′ , y = scanˡ v
      in
        u′ ⊗ map (x ∙_) v′ , x ∙ y
    scanˡ {s `× t} (◎ w) =
      let w′ , zs = unzip (map scanˡ w)
          zs′ , z′ = scanˡ zs
          tweak z = map (z ∙_)
      in
        ◎ (zipWith tweak zs′ w′) , z′

-- Tries as recursive type family. This choice avoids a new data type, but we
-- can no longer pattern-match over tries, and shapes arguments must be
-- explicit.
module RecursiveTrie where

  T : Set → Shape → Set
  T A `⊥ = ⊤
  T A `⊤ = A
  T A (s `+ t) = T A s × T A t
  T A (s `× t) = T (T A t) s

  infixl 1 _!_

  at _!_ : ∀ s → T A s → Index s → A
  at `⊤ x = λ { tt → x }
  at (s `+ t) (u , v) = [ at s u , at t v ]
  at (s `× t) w = uncurry (at t ∘ at s w)

  _!_ = at

  map : ∀ s → (A → B) → T A s → T B s
  map `⊥ f tt = tt
  map `⊤ f u = f u
  map (s `+ t) f (u , v) = map s f u , map t f v
  map (s `× t) f w = map s (map t f) w

  zipWith : ∀ s → (A → B → C) → T A s → T B s → T C s
  zipWith `⊥ f tt tt = tt
  zipWith `⊤ f x y = f x y
  zipWith (s `+ t) f (u₁ , u₂) (v₁ , v₂) =
    zipWith s f u₁ v₁ , zipWith t f u₂ v₂
  zipWith (s `× t) f u v = zipWith s (zipWith t f) u v

  transpose : (A × B) × (C × D) → (A × C) × (B × D)
  transpose ((a , b) , (c , d)) = (a , c) , (b , d)

  unzip : ∀ s → T (A × B) s → T A s × T B s
  unzip `⊥ tt = tt , tt
  unzip `⊤ (x , y) = x , y
  unzip (s `+ t) (u , v) = transpose (unzip s u , unzip t v)
  unzip (s `× t) w = unzip s (map s (unzip t) w)

  -- T (A × B) (s `× t)
  -- T (T (A × B) t) s
  -- T (T A t × T B t) s
  -- T (T A t) s × T (T B t) s
  -- T A (s × t) × T B (s × t)

  open import Algebra.Bundles

  module _ {ℓ} (M : Monoid 0ℓ ℓ) where

    open Monoid M renaming (Carrier to X)

    scanˡ : ∀ s → T X s → T X s × X
    scanˡ `⊥ tt = tt , ε
    scanˡ `⊤ x = ε , x
    scanˡ (s `+ t) (u , v) =
      let u′ , x = scanˡ s u
          v′ , y = scanˡ t v
      in
        (u′ , (map t (x ∙_) v′)) , x ∙ y

    scanˡ (s `× t) w =
      let w′ , zs = unzip s (map s (scanˡ t) w)
          zs′ , z′ = scanˡ s zs
          tweak z = map t (z ∙_)
      in
        zipWith s tweak zs′ w′ , z′
