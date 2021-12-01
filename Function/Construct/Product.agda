------------------------------------------------------------------------
-- The Agda standard library (intended)
--
-- Product-monoidal combination of functional properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Construct.Product where

open import Data.Product
open import Function
open import Level using (Level)
open import Relation.Binary as B hiding (_⇔_; IsEquivalence)

open import Data.Product.Relation.Binary.Pointwise.NonDependent
-- TODO: Dependent

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Properties

private

  transpose : {B : A → Set b} {D : C → Set d} →
    Σ A B × Σ C D → Σ (A × C) λ (x , y) → B x × D y
  transpose ((x , y) , (w , z)) = ((x , w) , (y , z))

module PW  (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈₃ : Rel C ℓ₃) (≈₄ : Rel D ℓ₄) where

  ≈₁₂ : Rel (A × B) _
  ≈₁₂ = Pointwise ≈₁ ≈₂

  ≈₃₄ : Rel (C × D) _
  ≈₃₄ = Pointwise ≈₃ ≈₄

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈₃ : Rel C ℓ₃) (≈₄ : Rel D ℓ₄)
         {f : A → C} {g : B → D}
         where

  open PW ≈₁ ≈₂ ≈₃ ≈₄

  congruent : Congruent ≈₁ ≈₃ f → Congruent ≈₂ ≈₄ g →
              Congruent ≈₁₂ ≈₃₄ (map f g)
  congruent f-cong g-cong = map f-cong g-cong

  injective : Injective ≈₁ ≈₃ f → Injective ≈₂ ≈₄ g →
              Injective ≈₁₂ ≈₃₄ (map f g)
  injective f-inj g-inj = map f-inj g-inj

  surjective : Surjective ≈₁ ≈₃ f → Surjective ≈₂ ≈₄ g →
               Surjective ≈₁₂ ≈₃₄ (map f g)
  surjective f-sur g-sur = transpose ∘ dmap f-sur g-sur

  -- surjective f-sur g-sur (w , z) with f-sur w | g-sur z
  -- ... | x , fx≈w | y , gy≈z = (x , y) , (fx≈w , gy≈z)

  bijective : Bijective ≈₁ ≈₃ f → Bijective ≈₂ ≈₄ g →
              Bijective ≈₁₂ ≈₃₄ (map f g)
  bijective (f-inj , f-sur) (g-inj , g-sur) =
    injective f-inj g-inj , surjective f-sur g-sur

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) (≈₃ : Rel C ℓ₃) (≈₄ : Rel D ℓ₄)
         {f : A → C} {f⁻¹ : C → A} {g : B → D} {g⁻¹ : D → B}
         where

  open PW ≈₁ ≈₂ ≈₃ ≈₄

  inverseˡ : Inverseˡ ≈₁ ≈₃ f f⁻¹ → Inverseˡ ≈₂ ≈₄ g g⁻¹ →
             Inverseˡ ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  inverseˡ f-inv g-inv = dmap f-inv g-inv

  inverseʳ : Inverseʳ ≈₁ ≈₃ f f⁻¹ → Inverseʳ ≈₂ ≈₄ g g⁻¹ →
             Inverseʳ ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  inverseʳ f-inv g-inv = dmap f-inv g-inv

  inverseᵇ : Inverseᵇ ≈₁ ≈₃ f f⁻¹ → Inverseᵇ ≈₂ ≈₄ g g⁻¹ →
             Inverseᵇ ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  inverseᵇ (f-invˡ , f-invʳ) (g-invˡ , g-invʳ) =
    inverseˡ f-invˡ g-invˡ , inverseʳ f-invʳ g-invʳ

------------------------------------------------------------------------
-- Structures

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {≈₃ : Rel C ℓ₃} {≈₄ : Rel D ℓ₄}
         {f : A → C} {g : B → D}
         where

  open PW ≈₁ ≈₂ ≈₃ ≈₄

  isCongruent : IsCongruent ≈₁ ≈₃ f → IsCongruent ≈₂ ≈₄ g →
                IsCongruent ≈₁₂ ≈₃₄ (map f g)
  isCongruent f-cong g-cong = record
    { cong           = map F.cong G.cong
    ; isEquivalence₁ = ×-isEquivalence F.isEquivalence₁ G.isEquivalence₁
    ; isEquivalence₂ = ×-isEquivalence F.isEquivalence₂ G.isEquivalence₂
    } where module F = IsCongruent f-cong; module G = IsCongruent g-cong

  isInjection : IsInjection ≈₁ ≈₃ f → IsInjection ≈₂ ≈₄ g →
                IsInjection ≈₁₂ ≈₃₄ (map f g)
  isInjection f-inj g-inj = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; injective   = injective ≈₁ ≈₂ ≈₃ ≈₄ F.injective G.injective
    } where module F = IsInjection f-inj; module G = IsInjection g-inj

  isSurjection : IsSurjection ≈₁ ≈₃ f → IsSurjection ≈₂ ≈₄ g →
                 IsSurjection ≈₁₂ ≈₃₄ (map f g)
  isSurjection f-surj g-surj = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; surjective  = surjective ≈₁ ≈₂ ≈₃ ≈₄ F.surjective G.surjective
    } where module F = IsSurjection f-surj; module G = IsSurjection g-surj

  isBijection : IsBijection ≈₁ ≈₃ f → IsBijection ≈₂ ≈₄ g →
                IsBijection ≈₁₂ ≈₃₄ (map f g)
  isBijection f-bij g-bij = record
    { isInjection = isInjection F.isInjection G.isInjection
    ; surjective  = surjective ≈₁ ≈₂ ≈₃ ≈₄ F.surjective G.surjective
    } where module F = IsBijection f-bij; module G = IsBijection g-bij

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {≈₃ : Rel C ℓ₃} (≈₄ : Rel D ℓ₄)
         {f : A → C} {f⁻¹ : C → A} {g : B → D} {g⁻¹ : D → B}
         where

  open PW ≈₁ ≈₂ ≈₃ ≈₄

  isLeftInverse : IsLeftInverse ≈₁ ≈₃ f f⁻¹ → IsLeftInverse ≈₂ ≈₄ g g⁻¹ →
                  IsLeftInverse ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  isLeftInverse f-invˡ g-invˡ = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; cong₂       = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    ; inverseˡ    = inverseˡ ≈₁ ≈₂ ≈₃ ≈₄ {f = f} {g = g} F.inverseˡ G.inverseˡ
    } where module F = IsLeftInverse f-invˡ; module G = IsLeftInverse g-invˡ

  isRightInverse : IsRightInverse ≈₁ ≈₃ f f⁻¹ → IsRightInverse ≈₂ ≈₄ g g⁻¹ →
                   IsRightInverse ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  isRightInverse f-invʳ g-invʳ = record
    { isCongruent = isCongruent F.isCongruent G.isCongruent
    ; cong₂       = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    ; inverseʳ    = inverseʳ ≈₁ ≈₂ ≈₃ ≈₄ {f⁻¹ = f⁻¹} {g⁻¹ = g⁻¹}
                      F.inverseʳ G.inverseʳ
    } where module F = IsRightInverse f-invʳ; module G = IsRightInverse g-invʳ

  isInverse : IsInverse ≈₁ ≈₃ f f⁻¹ → IsInverse ≈₂ ≈₄ g g⁻¹ →
              IsInverse ≈₁₂ ≈₃₄ (map f g) (map f⁻¹ g⁻¹)
  isInverse f-inv g-inv = record
    { isLeftInverse = isLeftInverse F.isLeftInverse G.isLeftInverse
    ; inverseʳ      = inverseʳ ≈₁ ≈₂ ≈₃ ≈₄ {f⁻¹ = f⁻¹} {g⁻¹ = g⁻¹}
                        F.inverseʳ G.inverseʳ
    } where module F = IsInverse f-inv; module G = IsInverse g-inv

------------------------------------------------------------------------
-- Setoid bundles

module _ {R : Setoid a ℓ₁} {S : Setoid b ℓ₂} {T : Setoid c ℓ₃} {U : Setoid d ℓ₄} where

  open Setoid renaming (_≈_ to ≈)

  private
    RS = ×-setoid R S
    TU = ×-setoid T U

    ≈₁ = ≈ R
    ≈₂ = ≈ S
    ≈₃ = ≈ T
    ≈₄ = ≈ U

    cong≈ = congruent ≈₁ ≈₂ ≈₃ ≈₄

  function : Func R T → Func S U → Func RS TU
  function f g = record
    { f    = map F.f G.f
    ; cong = cong≈ F.cong G.cong
    } where module F = Func f; module G = Func g

  injection : Injection R T → Injection S U → Injection RS TU
  injection inj₁ inj₂ = record
    { f         = map F.f G.f
    ; cong      = cong≈ F.cong G.cong
    ; injective = injective ≈₁ ≈₂ ≈₃ ≈₄ F.injective G.injective
    } where module F = Injection inj₁; module G = Injection inj₂

  surjection : Surjection R T → Surjection S U → Surjection RS TU
  surjection surj₁ surj₂ = record
    { f          = map F.f G.f
    ; cong       = cong≈ F.cong G.cong
    ; surjective = surjective ≈₁ ≈₂ ≈₃ ≈₄ F.surjective G.surjective
    } where module F = Surjection surj₁; module G = Surjection surj₂

  bijection : Bijection R T → Bijection S U → Bijection RS TU
  bijection bij₁ bij₂ = record
    { f         = map F.f G.f
    ; cong      = cong≈ F.cong G.cong
    ; bijective = bijective ≈₁ ≈₂ ≈₃ ≈₄ F.bijective G.bijective
    } where module F = Bijection bij₁; module G = Bijection bij₂

  equivalence : Equivalence R T → Equivalence S U → Equivalence RS TU
  equivalence equiv₁ equiv₂ = record
    { f     = map F.f G.f
    ; g     = map F.g G.g
    ; cong₁ = cong≈ F.cong₁ G.cong₁
    ; cong₂ = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    } where module F = Equivalence equiv₁; module G = Equivalence equiv₂

  leftInverse : LeftInverse R T → LeftInverse S U → LeftInverse RS TU
  leftInverse invˡ₁ invˡ₂ = record
    { f        = map F.f G.f
    ; g        = map F.g G.g
    ; cong₁    = cong≈ F.cong₁ G.cong₁
    ; cong₂    = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    ; inverseˡ = inverseˡ  ≈₁ ≈₂ ≈₃ ≈₄ {f = F.f} {g = G.f}
                   F.inverseˡ G.inverseˡ
    } where module F = LeftInverse invˡ₁; module G = LeftInverse invˡ₂

  rightInverse : RightInverse R T → RightInverse S U → RightInverse RS TU
  rightInverse invʳ₁ invʳ₂ = record
    { f        = map F.f G.f
    ; g        = map F.g G.g
    ; cong₁    = cong≈ F.cong₁ G.cong₁
    ; cong₂    = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    ; inverseʳ = inverseʳ  ≈₁ ≈₂ ≈₃ ≈₄ {f⁻¹ = F.g} {g⁻¹ = G.g}
                   F.inverseʳ G.inverseʳ
    } where module F = RightInverse invʳ₁; module G = RightInverse invʳ₂

  inverse : Inverse R T → Inverse S U → Inverse RS TU
  inverse inv₁ inv₂ = record
    { f       = map F.f   G.f
    ; f⁻¹     = map F.f⁻¹ G.f⁻¹
    ; cong₁   = cong≈ F.cong₁ G.cong₁
    ; cong₂   = congruent ≈₃ ≈₄ ≈₁ ≈₂ F.cong₂ G.cong₂
    ; inverse = inverseᵇ  ≈₁ ≈₂ ≈₃ ≈₄ {f = F.f} {g = G.f}
                  F.inverse G.inverse
    } where module F = Inverse inv₁; module G = Inverse inv₂

------------------------------------------------------------------------
-- Propositional bundles

open import Relation.Binary.PropositionalEquality

private
  pattern refl² = refl , refl

  pw : Rel (A × B) _
  pw = Pointwise _≡_ _≡_

  ⇊ : ∀ {p q : A × B} → pw p q → p ≡ q
  ⇊ refl² = refl

  ⇈ : ∀ {p q : A × B} → p ≡ q → pw p q
  ⇈ refl = refl²

import Function.Construct.Composition as •

infixr 7 _⊗-⟶_ _⊗-↣_ _⊗-↠_ _⊗-⤖_ _⊗-⇔_ _⊗-↩_ _⊗-↪_ _⊗-↔_

_⊗-⟶_ : (A ⟶ C) → (B ⟶ D) → (A × B) ⟶ (C × D)
f ⊗-⟶ g = record { cong = ⇈ }
         • function f g
         • record { cong = ⇊ }
 where infixr 9 _•_ ; _•_ = •.function

_⊗-↣_ : A ↣ C → B ↣ D → (A × B) ↣ (C × D)
f ⊗-↣ g = record { cong = ⇈ ; injective = ⇊ }
        • injection f g
        • record { cong = ⇊ ; injective = ⇈ }
 where infixr 9 _•_ ; _•_ = •.injection

_⊗-↠_ : A ↠ C → B ↠ D → (A × B) ↠ (C × D)
f ⊗-↠ g = record { cong = ⇈ ; surjective = _, refl² }
        • surjection f g
        • record { cong = ⇊ ; surjective = _, refl }
 where infixr 9 _•_ ; _•_ = •.surjection

_⊗-⤖_ : A ⤖ C → B ⤖ D → (A × B) ⤖ (C × D)
f ⊗-⤖ g = record { cong = ⇈ ; bijective = ⇊ , _, refl² }
        • bijection f g
        • record { cong = ⇊ ; bijective = ⇈ , _, refl }
 where infixr 9 _•_ ; _•_ = •.bijection

_⊗-⇔_ : A ⇔ C → B ⇔ D → (A × B) ⇔ (C × D)
f ⊗-⇔ g = record { cong₁ = ⇈ ; cong₂ = ⇊ }
        • equivalence f g
        • record { cong₁ = ⇊ ; cong₂ = ⇈ }
 where infixr 9 _•_ ; _•_ = •.equivalence

_⊗-↩_ : A ↩ C → B ↩ D → (A × B) ↩ (C × D)
f ⊗-↩ g = record { cong₁ = ⇈ ; cong₂ = ⇊ ; inverseˡ = λ _ → refl² }
        • leftInverse f g
        • record { cong₁ = ⇊ ; cong₂ = ⇈ ; inverseˡ = λ _ → refl }
 where infixr 9 _•_ ; _•_ = •.leftInverse

_⊗-↪_ : A ↪ C → B ↪ D → (A × B) ↪ (C × D)
f ⊗-↪ g = record { cong₁ = ⇈ ; cong₂ = ⇊ ; inverseʳ = λ _ → refl }
        • rightInverse f g
        • record { cong₁ = ⇊ ; cong₂ = ⇈ ; inverseʳ = λ _ → refl² }
 where infixr 9 _•_ ; _•_ = •.rightInverse

_⊗-↔_ : A ↔ C → B ↔ D → (A × B) ↔ (C × D)
f ⊗-↔ g = record { cong₁ = ⇈ ; cong₂ = ⇊ ; inverse = (λ _ → refl²) , (λ _ → refl) }
        • inverse f g
        • record { cong₁ = ⇊ ; cong₂ = ⇈ ; inverse = (λ _ → refl) , (λ _ → refl²) }
 where infixr 9 _•_ ; _•_ = •.inverse
