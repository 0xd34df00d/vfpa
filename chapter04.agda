module chapter04 where

open import bool
open import nat
open import nat-thms
open import product
open import product-thms
open import eq

{-
data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) → (xs : 𝕃 A) → 𝕃 A
  -}

{-
data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 𝔹 -- not gonna work due to mismatched ℓ
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A
  -}

open import list
open import maybe

length-++' : ∀ {ℓ} {A : Set ℓ}
           → (l₁ l₂ : 𝕃 A)
           → length (l₁ ++ l₂) ≡ length l₁ + length l₂
length-++' [] l₂ = refl
length-++' (x :: l₁) l₂ = cong suc (length-++' l₁ l₂)

length-filter' : ∀ {ℓ} {A : Set ℓ}
               → (p : A → 𝔹) 
               → (l : 𝕃 A)
               → length (filter p l) ≤ length l ≡ tt
length-filter' p [] = refl
length-filter' p (x :: l) with p x
length-filter' p (x :: l) | tt = length-filter' p l
length-filter' p (x :: l) | ff = ≤-trans {length (filter p l)} (length-filter' p l) (≤-suc (length l))

filter-idem' : ∀ {ℓ} {A : Set ℓ}
             → (p : A → 𝔹)
             → (l : 𝕃 A)
             → filter p (filter p l) ≡ filter p l
filter-idem' p [] = refl
filter-idem' p (x :: l) with keep (p x)
filter-idem' p (x :: l) | tt , p' rewrite p' | p' | filter-idem' p l = refl
filter-idem' p (x :: l) | ff , p' rewrite p' = filter-idem' p l
