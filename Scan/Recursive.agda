{-# OPTIONS --safe --without-K #-}

-- Tries as recursive type family. This choice avoids a new data type, but we
-- can no longer pattern-match over tries, and shapes arguments must be
-- explicit.

open import Level
open import Algebra.Bundles using (Monoid)

module Scan.Recursive {ℓ} (M : Monoid 0ℓ ℓ) where

open import Data.Product using (_,_; _×_)

open import Misc
open import Shape
open import Trie.Recursive

private variable
  a b c : Level
  A B C D : Set a
  s t : Shape

open Monoid M renaming (Carrier to X)

-- scanˡ : ∀ s → T X s → T X s × X
scanˡ : ∀ s → T X s → T X (s `⊎ `⊤)
scanˡ `⊥ tt = tt , ε
scanˡ `⊤ x = ε , x
scanˡ (s `⊎ t) (u , v) =
  let u′ , x = scanˡ s u
      v′ , y = scanˡ t v
  in
    (u′ , (map t (x ∙_) v′)) , x ∙ y
scanˡ (s `× t) w =
  let w′ , zs  = unzip s (map s (scanˡ t) w)
      zs′ , z′ = scanˡ s zs
      tweak z  = map t (z ∙_)
  in
    zipWith s tweak zs′ w′ , z′

-- Note that the signature variants now agree in meaning.
