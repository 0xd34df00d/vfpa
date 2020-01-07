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

-- 4.1
-- a, b, d are obviously false
-- c:
repeat-filter-[] : ∀ {ℓ} {A : Set ℓ} {p : A → 𝔹} {a : A}
                 → (n : ℕ)
                 → p a ≡ ff
                 → filter p (repeat n a) ≡ []
repeat-filter-[] zero _ = refl
repeat-filter-[] (suc n) prf rewrite prf = repeat-filter-[] n prf
-- e:
filter-cons : ∀ {ℓ} {A : Set ℓ}
            → (p : A → 𝔹)
            → (l₁ l₂ : 𝕃 A)
            → filter p (l₁ ++ l₂) ≡ filter p l₁ ++ filter p l₂
filter-cons p [] l₂ = refl
filter-cons p (x :: l₁) l₂ with p x
filter-cons p (x :: l₁) l₂ | tt rewrite sym (filter-cons p l₁ l₂) = refl
filter-cons p (x :: l₁) l₂ | ff = filter-cons p l₁ l₂

-- 4.3
takeWhile : ∀ {ℓ} {A : Set ℓ}
          → (p : A → 𝔹)
          → 𝕃 A
          → 𝕃 A
takeWhile p [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

-- 4.4
takeWhile-tt-repeat : ∀ {ℓ} {A : Set ℓ}
                    → (p : A → 𝔹)
                    → (a : A)
                    → (n : ℕ)
                    → p a ≡ tt
                    → filter p (repeat n a) ≡ repeat n a
takeWhile-tt-repeat p a zero prf = refl
takeWhile-tt-repeat p a (suc n) prf rewrite prf | takeWhile-tt-repeat p a n prf = refl

-- 4.5
take : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → 𝕃 A → 𝕃 A
take zero _ = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs

-- 4.6
take++nthTail : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → (xs : 𝕃 A)
              → take n xs ++ nthTail n xs ≡ xs
take++nthTail zero xs = refl
take++nthTail (suc n) [] = refl
take++nthTail (suc n) (x :: xs) rewrite take++nthTail n xs = refl
