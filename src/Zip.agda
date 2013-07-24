module Zip where

open import Data.List as L
  using (List; []; _∷_)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec as V
  using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

Func : ∀ {n} (σs : Vec Set n) (τ : Set) → Set
Func []       τ = τ
Func (σ ∷ σs) τ = σ → Func σs τ

ZipWith-type : ∀ {n} (σs : Vec Set n) (τ : Set) → Set
ZipWith-type σs τ = Func σs τ → Func (V.map List σs) (List τ)

zipWith : ∀ {n} (σs : Vec Set n) (τ : Set) → ZipWith-type σs τ
zipWith []       τ   x  = L.[ x ]  -- should be repeat (as pure of ZipList applicative)
zipWith (σ ∷ σs) τ f xs = go σs τ (L.map f xs)
  where
  go : ∀ {n} (σs : Vec Set n) (τ : Set) → List (Func σs τ) → Func (V.map List σs) (List τ)
  go []       τ    xs = xs
  go (σ ∷ σs) τ fs xs = go σs τ (L.zipWith (λ x → x) fs xs)

ZipWith-poly-type : ℕ → List Set → Set₁
ZipWith-poly-type zero    σs = {τ : Set} → ZipWith-type (V.fromList σs) τ
ZipWith-poly-type (suc n) σs = {σ : Set} → ZipWith-poly-type n (σ ∷ σs)

zipWith-p : ∀ n → ZipWith-poly-type n []
zipWith-p n = go n []
  where
  go : ∀ n σs → ZipWith-poly-type n σs
  go zero    = λ σs {τ} → zipWith (V.fromList σs) τ
  go (suc n) = λ σs {σ} → go n (σ ∷ σs)


test₁ : zipWith-p 2 _+_ (1 ∷ 4 ∷ []) (2 ∷ 7 ∷ 9 ∷ []) ≡ 3 ∷ 11 ∷ []
test₁ = refl

f : ℕ → ℕ → ℕ → ℕ
f a b c = a + b * c

test₂ : zipWith-p 3 f (3 ∷ 2 ∷ []) (4 ∷ []) (5 ∷ 8 ∷ 10 ∷ []) ≡ 23 ∷ []
test₂ = refl
