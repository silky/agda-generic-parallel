{-# OPTIONS --safe --without-K #-}

-- Tries as recursive type family. This choice avoids a new data type, but we
-- can no longer pattern-match over tries, and shapes arguments must be
-- explicit.

module Trie.Recursive where

open import Level
open import Function using (_∘_)
open import Data.Product as × using (_,_; _×_; uncurry)
open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_; [_,_])

open import Misc
open import Shape

-- Most of the content below will be moved into other top-level modules and
-- shared with FFT and other algorithm families.

private variable
  ℓ : Level
  A B C D : Set ℓ
  s t : Shape

T : Set → Shape → Set
T A `⊥ = ⊤
T A `⊤ = A
T A (s `⊎ t) = T A s × T A t
T A (s `× t) = T (T A t) s

lookup : ∀ s → T A s → Index s → A
lookup `⊤ x = λ { tt → x }
lookup (s `⊎ t) (u , v) = [ lookup s u , lookup t v ]
lookup (s `× t) w = uncurry (lookup t ∘ lookup s w)

map : ∀ s → (A → B) → T A s → T B s
map `⊥ f tt = tt
map `⊤ f u = f u
map (s `⊎ t) f (u , v) = map s f u , map t f v
map (s `× t) f w = map s (map t f) w

zipWith : ∀ s → (A → B → C) → T A s → T B s → T C s
zipWith `⊥ f tt tt = tt
zipWith `⊤ f x y = f x y
zipWith (s `⊎ t) f (u₁ , u₂) (v₁ , v₂) =
  zipWith s f u₁ v₁ , zipWith t f u₂ v₂
zipWith (s `× t) f u v = zipWith s (zipWith t f) u v

transpose : (A × B) × (C × D) → (A × C) × (B × D)
transpose ((a , b) , (c , d)) = (a , c) , (b , d)

unzip : ∀ s → T (A × B) s → T A s × T B s
unzip `⊥ tt = tt , tt
unzip `⊤ (x , y) = x , y
unzip (s `⊎ t) (u , v) = transpose (unzip s u , unzip t v)
unzip (s `× t) w = unzip s (map s (unzip t) w)
