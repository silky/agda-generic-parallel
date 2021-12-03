{-# OPTIONS --safe --without-K #-}

-- Tries (Naperian functors) as inductive type family. We can then pattern-match
-- over tries and leave shape arguments implicit.

module Trie.Inductive where

open import Level
open import Function using (id; _∘_; flip; _$_; _↔_; Inverse)
open import Data.Product as × using (_,_; _×_; uncurry; curry)
open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (map to map⊎)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡
  hiding ([_]) renaming (trans to _;_)
open ≡-Reasoning

open import Misc
open import Shape

-- Most of the content below will be moved into other top-level modules and
-- shared with FFT and other algorithm families.

private variable
  ℓ : Level
  A B C D : Set ℓ
  s t : Shape

infix 7 _⊗_
data T (A : Set) : Shape → Set where   -- TODO: Generalize from Set
  1̇ : T A `⊥
  I : A → T A `⊤
  _⊗_ : T A s → T A t → T A (s `⊎ t)
  ◎ : T (T A t) s → T A (s `× t)

un1̇ : T A `⊥ → ⊤
un1̇ 1̇ = tt

unI : T A `⊤ → A
unI (I x) = x

un⊗ : T A (s `⊎ t) → T A s × T A t
un⊗ (u ⊗ v) = u , v

un◎ : T A (s `× t) → T (T A t) s
un◎ (◎ w) = w

lookup : ∀ {s A} → T A s → (Index s → A)
lookup ( I x ) = λ { tt → x }
lookup (u ⊗ v) = [ lookup u , lookup v ]
lookup ( ◎ w ) = uncurry (lookup ∘ lookup w)

tabulate : ∀ {s A} → (Index s → A) → T A s
tabulate {  `⊥  } f = 1̇
tabulate {  `⊤  } f = I (f tt)
tabulate {s `⊎ t} f = tabulate (f ∘ inj₁) ⊗ tabulate (f ∘ inj₂)
tabulate {s `× t} f = ◎ (tabulate (tabulate ∘ curry f))

tabulate-cong : {f g : Index s → A} → f ≗ g → tabulate f ≡ tabulate g
tabulate-cong {  `⊥  } f≗g = refl
tabulate-cong {  `⊤  } f≗g = cong I (f≗g tt)
tabulate-cong {s `⊎ t} f≗g =
   cong₂ _⊗_ (tabulate-cong (f≗g ∘ inj₁)) (tabulate-cong (f≗g ∘ inj₂))
tabulate-cong {s `× t} f≗g =
   cong ◎ (tabulate-cong (tabulate-cong ∘ curry f≗g))

tabulate∘lookup : ∀ {s A} → tabulate ∘ lookup {s} {A} ≗ id
tabulate∘lookup 1̇ = refl
tabulate∘lookup (I x) = refl
tabulate∘lookup (u ⊗ v) = cong₂ _⊗_ (tabulate∘lookup u) (tabulate∘lookup v)
tabulate∘lookup (◎ w) = cong ◎ $
  begin
    tabulate (λ x → tabulate (lookup (lookup w x)))
  ≡⟨⟩
    tabulate (tabulate ∘ lookup ∘ lookup w)
  ≡⟨ tabulate-cong (tabulate∘lookup ∘ lookup w) ⟩
    tabulate (lookup w)
  ≡⟨ tabulate∘lookup w ⟩
    w
  ∎

lookup∘tabulate : ∀ {s A} (f : Index s → A) → lookup (tabulate f) ≗ f
lookup∘tabulate {`⊤} f = λ { tt → refl }
lookup∘tabulate {s `⊎ t} f =
  [ lookup∘tabulate (f ∘ inj₁) , lookup∘tabulate (f ∘ inj₂) ]
lookup∘tabulate {s `× t} f = λ p@(i , j) →
  begin
    lookup (tabulate f) (i , j)
  ≡⟨⟩
    lookup (lookup (tabulate (tabulate ∘ curry f)) i) j
  ≡⟨ cong (flip lookup j) (lookup∘tabulate (tabulate ∘ curry f) i) ⟩
    lookup ((tabulate ∘ curry f) i) j
  ≡⟨⟩
    lookup (tabulate (curry f i)) j
  ≡⟨ lookup∘tabulate (curry f i) j ⟩
    curry f i j
  ≡⟨⟩
    f (i , j)
  ∎

T↔fun : Inverse (≡.setoid (T A s)) (Index s →-setoid A)
T↔fun = record
  { f       = lookup
  ; f⁻¹     = tabulate
  ; cong₁   = λ { refl i → refl }
  ; cong₂   = tabulate-cong
  ; inverse = lookup∘tabulate , tabulate∘lookup
  }

T↔Vec : ∀ {s A} → T A s ↔ Vec A (# s)
T↔Vec {s} = fun-vec-inverse ∘̇ dom (fin↔index s ⁻¹) ∘̇ T↔fun

map : ∀ {s A B} → (A → B) → T A s → T B s
map f 1̇       = 1̇
map f (I x)   = I (f x)
map f (u ⊗ v) = map f u ⊗ map f v
map f (◎ us)  = ◎ (map (map f) us)
-- Synthesized by Agda

map-cong : ∀ {s A B} → {f g : A → B} → f ≗ g → map {s} f ≗ map g
map-cong {`⊥} f≗g 1̇ = refl
map-cong {`⊤} f≗g (I x) = cong I (f≗g x)
map-cong {s `⊎ t} f≗g (u ⊗ v) = cong₂ _⊗_ (map-cong f≗g u) (map-cong f≗g v)
map-cong {s `× t} f≗g (◎ w) = cong ◎ (map-cong (map-cong f≗g) w)
-- We could probably prove map-cong via tabulate-cong.

map-id : map {s} {A} id ≗ id
map-id 1̇       = refl
map-id (I _)   = refl
map-id (u ⊗ v) = cong₂ _⊗_ (map-id u) (map-id v)
map-id (◎ w)   = cong ◎ (map-cong map-id w ; map-id w)
-- Synthesized by Agda with hints

map-∘ : ∀ {s A B C} → {f : A → B} {g : B → C} → map {s} g ∘ map f ≗ map (g ∘ f)
map-∘ {`⊥} 1̇ = refl
map-∘ {`⊤} (I _) = refl
map-∘ {s `⊎ t} (u ⊗ v) = cong₂ _⊗_ (map-∘ u) (map-∘ v)
map-∘ {s `× t} (◎ w) = cong ◎ (map-∘ w ; map-cong map-∘ w)

zipWith : (A → B → C) → T A s → T B s → T C s
zipWith f 1̇ 1̇ = 1̇
zipWith f (I x) (I y) = I (f x y)
zipWith f (u₁ ⊗ u₂) (v₁ ⊗ v₂) = zipWith f u₁ v₁ ⊗ zipWith f u₂ v₂
zipWith f (◎ u) (◎ v) = ◎ (zipWith (zipWith f) u v)
-- Synthesized by Agda

transpose : (T A s × T B s) → (T A t × T B t) → (T A (s `⊎ t) × T B (s `⊎ t))
transpose (u₁ , u₂) (v₁ , v₂) = u₁ ⊗ v₁ , u₂ ⊗ v₂  -- synthesized

unzip : T (A × B) s → T A s × T B s
unzip 1̇ = 1̇ , 1̇
unzip (I (x , y)) = I x , I y
unzip (u ⊗ v) = transpose (unzip u) (unzip v)
unzip (◎ w) = ×.map ◎ ◎ (unzip (map unzip w))
