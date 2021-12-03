{-# OPTIONS --safe --without-K #-}

-- Tries (Naperian functors) as inductive type family. We can then pattern-match
-- over tries and leave shape arguments implicit.

open import Level
open import Algebra.Bundles using (Monoid)

module Scan.Inductive {ℓ} (M : Monoid 0ℓ ℓ) where

-- TODO: Generalize beyond 0ℓ

open import Function using (_∘_)
open import Data.Product as × using (_,_; _×_)

open import Misc
open import Shape
open import Trie.Inductive

private variable
  a b c : Level
  A B C D : Set a
  s t : Shape

open Monoid M renaming (Carrier to X)

scanˡ : T X s → T X s × X
scanˡ 1̇ = 1̇ , ε
scanˡ (I x) = I ε , x
scanˡ (u ⊗ v) =
  let u′ , x = scanˡ u
      v′ , y = scanˡ v
  in
    u′ ⊗ map (x ∙_) v′ , x ∙ y
scanˡ (◎ w) =
  let w′ , zs = unzip (map scanˡ w)
      zs′ , z′ = scanˡ zs
      tweak z = map (z ∙_)
  in
    ◎ (zipWith tweak zs′ w′) , z′

-- Experiment: return type as a single trie. I think we'll need it for the
-- categorical version in which objects are shapes.

unzip′ : T (T A (t `⊎ `⊤)) s → T (T A t) s × T A s
unzip′ = ×.map₂ (map unI) ∘ unzip ∘ map un⊗

-- T (T A (t `⊎ `⊤)) s         -- map un⊗
-- T (T A t × T A `⊤) s        -- unzip
-- T (T A t) s × T (T A `⊤) s  -- ×.map₂ (map unI)
-- T (T A t) s × T A s

infix 7 _⊗̂_
pattern _⊗̂_ u x = u ⊗ I x

scanˡ′ : T X s → T X (s `⊎ `⊤)
scanˡ′ 1̇ = 1̇ ⊗ I ε
scanˡ′ (I x) = I ε ⊗̂ x
scanˡ′ (u ⊗ v) with u′ ⊗̂ x ← scanˡ′ u
                  | v′ ⊗̂ y ← scanˡ′ v =
  (u′ ⊗ map (x ∙_) v′) ⊗̂ (x ∙ y)
scanˡ′ (◎ w) with w′ , zs  ← unzip′ (map scanˡ′ w)
             with zs′ ⊗̂ z′ ← scanˡ′ zs =
  let tweak z = map (z ∙_) in
    ◎ (zipWith tweak zs′ w′) ⊗̂ z′
