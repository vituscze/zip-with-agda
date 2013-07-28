module Zip where

open import Data.List as L
  using (List; []; _∷_)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_)
open import Data.Vec as V
  using (Vec; []; _∷_)
open import Function
  using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

Func : ∀ {n} (σs : Vec Set n) (τ : Set) → Set
Func []       τ = τ
Func (σ ∷ σs) τ = σ → Func σs τ

ZipWith-type : ∀ {n} (σs : Vec Set n) (τ : Set) → Set
ZipWith-type σs τ = Func σs τ → Func (V.map List σs) (List τ)

zipWith : ∀ {n} (σs : Vec Set n) (τ : Set) → ZipWith-type σs τ
zipWith []       τ   x  = L.[ x ]
zipWith (σ ∷ σs) τ f xs = go σs τ (L.map f xs)
  where
  go : ∀ {n} (σs : Vec Set n) (τ : Set) → List (Func σs τ) → Func (V.map List σs) (List τ)
  go []       τ    xs = xs
  go (σ ∷ σs) τ fs xs = go σs τ (L.zipWith (λ x → x) fs xs)

-- Alternatively:
--
-- {-# NO_TERMINATION_CHECK #-}
-- repeat : {A : Set} → A → List A
-- repeat x = x ∷ repeat x
--
-- zipWith : ∀ {n} (σs : Vec Set n) (τ : Set) → ZipWith-type σs τ
-- zipWith σs τ f = go σs τ (repeat f)
--   where
--   go : ∀ {n} (σs : Vec Set n) (τ : Set) → List (Func σs τ) → Func (V.map List σs) (List τ)
--   go []       τ    xs = xs
--   go (σ ∷ σs) τ fs xs = go σs τ (L.zipWith (λ x → x) fs xs)
--
-- Which matches Haskell's ZipList applicative. We could also use CoLists for everything.

ZipWith-poly-type : ℕ → (List Set → List Set) → Set₁
ZipWith-poly-type zero    k = {τ : Set} → ZipWith-type (V.fromList (k [])) τ
ZipWith-poly-type (suc n) k = {σ : Set} → ZipWith-poly-type n (k ∘ _∷_ σ)

zipWith-p : ∀ n → ZipWith-poly-type n id
zipWith-p n = go n id
  where
  go : ∀ n k → ZipWith-poly-type n k
  go zero    k = λ {τ} → zipWith (V.fromList (k [])) τ
  go (suc n) k = λ {σ} → go n (k ∘ _∷_ σ)


test₁ : zipWith-p 2 _+_ (1 ∷ 4 ∷ []) (2 ∷ 7 ∷ 9 ∷ []) ≡ 3 ∷ 11 ∷ []
test₁ = refl

f : ℕ → ℕ → ℕ → ℕ
f a b c = a + b * c

test₂ : zipWith-p 3 f (3 ∷ 2 ∷ []) (4 ∷ []) (5 ∷ 8 ∷ 10 ∷ []) ≡ 23 ∷ []
test₂ = refl
