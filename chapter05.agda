module chapter05 where

open import vector
open import nat
open import bool
open import eq

-- 5.1

_by_matrix : ℕ → ℕ → Set
n by m matrix = 𝕍 (𝕍 ℕ m) n

-- n columns and m rows

-- 5.2

zero-matrix : (m n : ℕ) → n by m matrix
zero-matrix m n = repeat𝕍 (repeat𝕍 0 m) n

matrix-elt : {m n : ℕ}
           → n by m matrix
           → (i j : ℕ)
           → i < n ≡ tt → j < m ≡ tt
           → ℕ
matrix-elt mat i j p₁ p₂ = nth𝕍 j p₂ (nth𝕍 i p₁ mat)

diagonal-matrix : (d n : ℕ) → n by n matrix
diagonal-matrix d = go
  where
    go : (n : ℕ) → n by n matrix
    go zero = []
    go (suc n) = let fstRow = d :: repeat𝕍 0 n
                     rec = map𝕍 (_::_ 0) (go n)
                 in fstRow :: rec

identity-matrix : (n : ℕ) → n by n matrix
identity-matrix = diagonal-matrix 1

transpose : {m n : ℕ} → n by m matrix -> m by n matrix
transpose {m} [] = repeat𝕍 [] m
transpose (row :: mat) = zipWith𝕍 _::_ row (transpose mat)

_∙_ : {n : ℕ} → 𝕍 ℕ n → 𝕍 ℕ n → ℕ
[] ∙ [] = 0
(x₁ :: v₁) ∙ (x₂ :: v₂) = x₁ * x₂ + v₁ ∙ v₂

_*matrix_ : {n k m : ℕ} → n by k matrix → k by m matrix → n by m matrix
[] *matrix m2 = []
(row :: m1) *matrix m2 = let rec = m1 *matrix m2
                             row' = map𝕍 (_∙_ row) (transpose m2)
                         in row' :: rec
