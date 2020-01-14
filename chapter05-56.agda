open import bool

module chapter05-56 (A : Set) (ord : A → A → 𝔹) where

open import braun-tree A ord
open import list-merge-sort A ord
open import list
open import eq
open import nat
open import nat-thms

merge-+-len : (l₁ l₂ : 𝕃 A)
            → length (merge l₁ l₂) ≡ length l₁ + length l₂
merge-+-len [] l₂ = refl
merge-+-len (x₁ :: l₁) [] rewrite +0 (length l₁) = refl
merge-+-len (x₁ :: l₁) (x₂ :: l₂) with ord x₁ x₂
... | tt rewrite merge-+-len l₁ (x₂ :: l₂) = refl
... | ff rewrite merge-+-len (x₁ :: l₁) l₂ | +suc (length l₁) (length l₂) = refl

merge-sort-h-lemma : ∀ {n} (t : braun-tree' n)
                   → length (merge-sort-h t) ≡ n
merge-sort-h-lemma (bt'-leaf x) = refl
merge-sort-h-lemma (bt'-node l r x) rewrite merge-+-len (merge-sort-h l) (merge-sort-h r)
                                          | merge-sort-h-lemma l
                                          | merge-sort-h-lemma r = refl

merge-sort-len : ∀ (xs : 𝕃 A)
               → length (merge-sort xs) ≡ length xs
merge-sort-len [] = refl
merge-sort-len (x :: xs) with 𝕃-to-braun-tree' x xs
... | t rewrite merge-sort-h-lemma t = refl
