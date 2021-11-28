module Scan where

open import Level using (0ℓ)

open import Function using (id; _∘_; _↔_; mk↔′)
open import Data.Product renaming (map to map×; map₁ to map×₁)
open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (map to map⊎)
open import Data.Nat
open import Data.Fin as F hiding (_+_; #_; splitAt)
open import Data.Fin.Properties
open import Data.Fin.Patterns
open import Data.Vec hiding ([_]; zipWith; transpose; unzip)
                     renaming (map to mapv)
open import Data.Vec.Properties using (++-injective; unfold-take; unfold-drop)
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (trans to _;_)
open ≡-Reasoning

infix 6 _`+_
infix 7 _`×_
data Shape : Set where
  `⊥ `⊤ : Shape
  _`+_ _`×_  : Shape → Shape → Shape

private variable
  s t : Shape
  A B C D : Set

# : Shape → ℕ
# `⊥ = 0
# `⊤ = 1
# (s `+ t) = # s + # t
# (s `× t) = # s * # t

Index : Shape → Set
Index `⊥ = ⊥
Index `⊤ = ⊤
Index (s `+ t) = Index s ⊎ Index t
Index (s `× t) = Index s × Index t

↔Fin : (s : Shape) → Index s ↔ Fin (# s)
↔Fin s = mk↔′ (to s) (from s) (to∘from s) (from∘to s)
 where
   to : (s : Shape) → Index s → Fin (# s)
   to `⊥ = λ ()
   to `⊤ = λ { tt → zero }
   to (s `+ t) = join _ _ ∘ map⊎ (to s) (to t)
   to (s `× t) = uncurry combine ∘ map× (to s) (to t)

   from : (s : Shape) → Fin (# s) → Index s
   from `⊥ = λ ()
   from `⊤ = λ { 0F → tt }
   from (s `+ t) = map⊎ (from s) (from t) ∘ F.splitAt _
   from (s `× t) = map× (from s) (from t) ∘ remQuot _

   to∘from : (s : Shape) → to s ∘ from s ≗ id
   to∘from `⊥ = λ ()
   to∘from `⊤ = λ { 0F → refl }
   to∘from (s `+ t) = {!!}
   to∘from (s `× t) = {!!}

   from∘to : (s : Shape) → from s ∘ to s ≗ id
   from∘to s = {!!}

-- TODO: invert the structure of this definition, writing one mk↔′ call per
-- Index constructor. Use the isomorphisms from Data.Fin.Properties. Construct
-- isomorphisms compositionally.

{-
-- In agda-std-2.0
1↔⊤ : Fin 1 ↔ ⊤
1↔⊤ = mk↔′ (λ { 0F → tt }) (λ { tt → 0F }) (λ { tt → refl }) λ { 0F → refl }

Fin↔ : (s : Shape) → Fin (# s) ↔ Index s
Fin↔ `⊥ = Fin0↔⊥
Fin↔ `⊤ = 1↔⊤
Fin↔ (s `+ t) = {!!}
Fin↔ (s `× t) = {!*↔×!}

-- TODO: Find or define compositional building blocks. See [(1623) Composing Inverses etc - Agda - Zulip](https://agda.zulipchat.com/#narrow/stream/238741-general/topic/Composing.20Inverses.20etc/near/262943635).

-}


-- I suspect these next few can be proved more directly or avoided.

take-++ : ∀ {m n a} {A : Set a} (xs : Vec A m) (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ [] ys = refl
take-++ {suc m} (x ∷ xs) ys =
 unfold-take m x (xs ++ ys) ; cong (x ∷_) (take-++ xs ys)

drop-++ : ∀ {m n a} {A : Set a} (xs : Vec A m) (ys : Vec A n) → drop m (xs ++ ys) ≡ ys
drop-++ [] ys = refl
drop-++ {suc m} (x ∷ xs) ys = unfold-drop m x (xs ++ ys) ; drop-++ xs ys

group′ : ∀ m n (xs : Vec A (m * n)) → Vec (Vec A n) m
group′ m n xs with group m n xs
group′ m n .(concat xss) | xss , refl = xss

-- group′-[] : ∀ n → group′ {A = A} zero n [] ≡ []
-- group′-[] n = refl

concat-injective : ∀ {m n} {a} {A : Set a} {xss yss : Vec (Vec A n) m} → concat xss ≡ concat yss → xss ≡ yss
concat-injective {zero} {xss = []} {[]} refl = refl
concat-injective {suc m} {xss = xs ∷ xss} {ys ∷ yss} eq with ++-injective xs ys eq
concat-injective {suc m} {xss = xs ∷ xss} {ys ∷ yss} _ | refl , eq′ =
  cong (xs ∷_) (concat-injective eq′)

unfold-group′ : ∀ m n xs (xss : Vec (Vec A n) m) →
  group′ (suc m) n (concat (xs ∷ xss)) ≡ xs ∷ group′ m n (concat xss)

unfold-group′ m n xs xss with group m n (concat xss)
unfold-group′ m n xs xss | fst , snd = {!!}

-- unfold-group′ m n xs xss with group (suc m) n (concat (xs ∷ xss))
-- unfold-group′ m n xs xss | ys ∷ yss , eq with ++-injective xs ys eq
-- unfold-group′ m n xs xss | .xs ∷ yss , _ | refl , eq =
--   -- Goal: (group′ (suc m) n (xs ++ concat xss) | xs ∷ yss , eq₁) ≡
--   --     xs ∷ (group′ m n (concat xss) | group m n (concat xss))
--   begin
--     {!group′ (suc m) n (xs ++ concat xss)!}
--   ≡⟨⟩
--     {!!}
--   ≡⟨ {!!} ⟩
--     {!!}
--   ≡⟨⟩
--     {!!}
--   ∎

-- unfold-group′ m n xs xss with group (suc m) n (concat (xs ∷ xss))
-- ... | ys ∷ yss , eq with ++-injective xs ys eq
-- ...   | fst , snd = {!!}

-- unfold-group′ m n xs xss with splitAt n (concat (xs ∷ xss))
-- unfold-group′ m n xs xss | ys , zs , eq with ++-injective xs ys eq
-- unfold-group′ m n xs xss | .xs , .(concat xss) , eq | refl , refl = {!!}

-- unfold-group′ m n xs xss with splitAt n (concat (xs ∷ xss))
-- ... | ys , zs , eq with ++-injective xs ys eq
-- ... |    refl , refl = {!!}

-- group : ∀ m n (xs : Vec A (m * n)) →
--         ∃ λ (xss : Vec (Vec A n) m) → xs ≡ concat xss
-- group zero    n []                  = ([] , refl)
-- group (suc m) n xs                  with splitAt n xs
-- group (suc m) n .(ys ++ zs)         | (ys , zs , refl) with group m n zs
-- group (suc m) n .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
--   ((ys ∷ zss) , refl)

-- unfold-group′ : ∀ m n xs (xss : Vec (Vec A n) m) →
--   group′ (suc m) n (concat (xs ∷ xss)) ≡ xs ∷ group′ m n (concat xss)
-- unfold-group′ zero n xs [] =
--   -- group′ 1 n (xs ++ []) ≡ xs ∷ group′ zero n []
--   begin
--     group′ 1 n (xs ++ [])
--   ≡⟨ {!!} ⟩
--     xs ∷ group′ 0 n []
--   ∎
-- unfold-group′ (suc m) n xs xss =
--   begin
--     group′ (suc (suc m)) n (concat (xs ∷ xss))
--   ≡⟨⟩
--     {!!}
--   ≡⟨ {!!} ⟩
--     {!!}
--   ≡⟨⟩
--     xs ∷ group′ (suc m) n (concat xss)
--   ∎

group′-concat : ∀ m n (xss : Vec (Vec A n) m) → group′ m n (concat xss) ≡ xss
group′-concat zero n [] = refl
group′-concat (suc m) n (xs ∷ xss) =
  begin
    group′ (suc m) n (xs ++ concat xss)
  ≡⟨ unfold-group′ m n xs xss ⟩
    xs ∷ group′ m n (concat xss)
  ≡⟨ cong (xs ∷_) (group′-concat m n xss) ⟩
    xs ∷ xss
  ∎



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

  map : ∀ {s A B} → (A → B) → T A s → T B s
  map f 1̇       = 1̇
  map f (I x)   = I (f x)
  map f (u ⊗ v) = map f u ⊗ map f v
  map f (◎ us)  = ◎ (map (map f) us)
  -- Synthesized by Agda

  map-cong : ∀ {s A B} → {f g : A → B} → f ≗ g → map {s} f ≗ map g
  map-cong {`⊥} f≗g 1̇ = refl
  map-cong {`⊤} f≗g (I x) = cong I (f≗g x)
  map-cong {s `+ t} f≗g (u ⊗ v) = cong₂ _⊗_ (map-cong f≗g u) (map-cong f≗g v)
  map-cong {s `× t} f≗g (◎ w) = cong ◎ (map-cong (map-cong f≗g) w)

  map-id : map {s} {A} id ≗ id
  map-id 1̇       = refl
  map-id (I _)   = refl
  map-id (u ⊗ v) = cong₂ _⊗_ (map-id u) (map-id v)
  map-id (◎ w)   = cong ◎ (map-cong map-id w ; map-id w)
  -- Synthesized by Agda with hints

  map-∘ : ∀ {s A B C} → {f : A → B} {g : B → C} → map {s} g ∘ map f ≗ map (g ∘ f)
  map-∘ {`⊥} 1̇ = refl
  map-∘ {`⊤} (I _) = refl
  map-∘ {s `+ t} (u ⊗ v) = cong₂ _⊗_ (map-∘ u) (map-∘ v)
  map-∘ {s `× t} (◎ w) = cong ◎ (map-∘ w ; map-cong map-∘ w)

{-

Goal: map (map g) (map (map f) w) ≡ map (map (g ∘ f)) w

w : T (T A t) s

map (map g) (map (map f) w)
map (map g ∘ map f) w
map (map (g ∘ f)) w

-}

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

  T↔ : ∀ {s A} → T A s ↔ Vec A (# s)
  T↔ {s} = mk↔′ to from (to∘from s) from∘to
   where
     to : ∀ {s A} → T A s → Vec A (# s)
     to 1̇ = []
     to (I x) = x ∷ []
     to (u ⊗ v) = to u ++ to v
     to (◎ w) = concat (to (map to w))

     from : ∀ {s A} → Vec A (# s) → T A s
     from {`⊥} [] = 1̇
     from {`⊤} (x ∷ []) = I x
     from {s `+ t} zs = from (take (# s) zs) ⊗ from (drop (# s) zs)
     -- from {s `+ t} zs with splitAt (# s) {# t} zs
     -- ... | xs , ys , refl = from xs ⊗ from ys
     from {s `× t} xs = ◎ (map from (from (group′ (# s) (# t) xs)))
     -- from {s `× t} xs with group (# s) (# t) xs
     -- ... | xss , refl = ◎ (map from (from xss))

     to∘from : ∀ s → to ∘ from {s} {A} ≗ id

     to∘from `⊥ [] = refl
     to∘from `⊤ (_ ∷ []) = refl
     to∘from (s `+ t) zs with splitAt (# s) {# t} zs ; ... | xs , ys , refl =
       cong₂ _++_ (to∘from s xs) (to∘from t ys)
     to∘from (s `× t) xs with group (# s) (# t) xs
     ... | xss , refl =
       begin
         concat (to (map to (map from (from {s} xss))))
       ≡⟨ cong (λ ○ → concat (to ○)) (map-∘ (from {s} xss)) ⟩
         concat (to (map (to {t} ∘ from) (from {s} xss)))
       ≡⟨ cong (concat ∘ to) (map-cong (to∘from t) (from {s} xss)) ⟩
         concat (to (map id (from {s} xss)))
       ≡⟨ cong (concat ∘ to) (map-id (from {s} xss)) ⟩
         concat (to (from {s} xss))
       ≡⟨ cong concat (to∘from s xss) ⟩
         concat xss
       ∎

     from∘to : ∀ {s A} → from ∘ to {s} {A} ≗ id
     from∘to 1̇ = refl
     from∘to (I _) = refl
     from∘to {s `+ t} (u ⊗ v) =
       begin
         from (to (u ⊗ v))
       ≡⟨⟩
         from (to u ++ to v)
       ≡⟨⟩
         from (take (# s) (to u ++ to v)) ⊗ from (drop (# s) (to u ++ to v))
       ≡⟨ cong₂ (λ ○ ● → from ○ ⊗ from ●)
            (take-++ (to u) (to v)) (drop-++ (to u) (to v)) ⟩
         from (to u) ⊗ from (to v)
       ≡⟨ cong₂ _⊗_ (from∘to u) (from∘to v) ⟩
         u ⊗ v
       ∎
     from∘to {s `× t} (◎ w) =
       begin
         from (concat (to (map to w)))
       ≡⟨⟩
         ◎ (map from (from (group′ (# s) (# t) (concat (to (map to w))))))
       ≡⟨ cong (λ ○ → ◎ (map from (from ○)))
            (group′-concat (# s) (# t) (to (map to w))) ⟩
         ◎ (map from (from (to (map to w))))
       ≡⟨ cong (λ ○ → ◎ (map from ○)) (from∘to (map to w)) ⟩
         ◎ (map from (map to w))
       ≡⟨ cong ◎ (map-∘ w) ⟩
         ◎ (map (from ∘ to) w)
       ≡⟨ cong ◎ (map-cong from∘to w) ⟩
         ◎ (map id w)
       ≡⟨ cong ◎ (map-id w) ⟩
         ◎ w
       ∎

-- group′-concat : ∀ m n (xss : Vec (Vec A n) m) → group′ m n (concat xss) ≡ xss


     -- from {s `× t} xs = ◎ (map from (from (group′ (# s) (# t) xs)))


-- Goal: (from (concat (to (map to w)))
--        | group (# s) (# t) (concat (to (map to w))))
--       ≡ ◎ w


     -- from {s `× t} xs with group (# s) (# t) xs
     -- ... | xss , refl = ◎ (map from (from xss))


  open import Algebra.Bundles

  module scanˡ {ℓ} (M : Monoid 0ℓ ℓ) where

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

    vscanˡ : ∀ {n} → Vec X n → Vec X n × X
    vscanˡ = go ε
     where
       go : ∀ (x : X) {n} → Vec X n → Vec X n × X
       go acc [] = [] , acc
       go acc (x ∷ xs) = map×₁ (acc ∷_) (go acc xs)

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

  open import Algebra.Bundles

  module scanˡ {ℓ} (M : Monoid 0ℓ ℓ) where

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
