module chapter06 where

open import eq
open import bool
open import bool-thms
open import nat
open import nat-thms
open import sum
open import unit
open import product
open import integer

-- 6.1

ℤneg : ℤ → ℤ
ℤneg (mkℤ zero t) = mkℤ zero t
ℤneg (mkℤ (suc n) s) = mkℤ (suc n) (~ s)

ℤneg-elim : ∀ z → ℤneg (ℤneg z) ≡ z
ℤneg-elim (mkℤ zero x) = refl
ℤneg-elim (mkℤ (suc n) x) rewrite ~~-elim x = refl

_-ℤ_ : ℤ → ℤ → ℤ
z -ℤ mkℤ zero ss = z
mkℤ zero ms -ℤ mkℤ (suc s) ss = mkℤ (suc s) (~ ss)
mkℤ (suc m) ms -ℤ mkℤ (suc s) ss with ms xor ss
... | tt = mkℤ (suc m + suc s) ms
... | ff = if ms then diffℤ m s else diffℤ s m

ℤ-0 : ∀ z → z -ℤ 0ℤ ≡ z
ℤ-0 z = refl

0-ℤ : ∀ z → 0ℤ -ℤ z ≡ ℤneg z
0-ℤ (mkℤ zero triv) = refl
0-ℤ (mkℤ (suc n) x) = refl

+ℤneg : ∀ z₁ z₂ → z₁ +ℤ (ℤneg z₂) ≡ z₁ -ℤ z₂
+ℤneg (mkℤ zero triv) z₂ rewrite 0-ℤ z₂ = refl
+ℤneg (mkℤ (suc n) tt) (mkℤ zero x) = refl
+ℤneg (mkℤ (suc n) tt) (mkℤ (suc n₁) tt) with ℕ-trichotomy n n₁
... | inj₁ p = refl
... | inj₂ (inj₁ x) = refl
... | inj₂ (inj₂ y) = refl
+ℤneg (mkℤ (suc n) tt) (mkℤ (suc n₁) ff) = refl
+ℤneg (mkℤ (suc n) ff) (mkℤ zero triv) = refl
+ℤneg (mkℤ (suc n) ff) (mkℤ (suc n₁) tt) = refl
+ℤneg (mkℤ (suc n) ff) (mkℤ (suc n₁) ff) = refl

ℤ+ℤ-ℤ : ∀ z₁ z₂ z₃ → (z₁ +ℤ z₂) -ℤ z₃ ≡ z₁ +ℤ (z₂ -ℤ z₃)
ℤ+ℤ-ℤ (mkℤ zero x) z₂ z₃ = refl
ℤ+ℤ-ℤ (mkℤ (suc n) x) (mkℤ zero triv) (mkℤ n₁ x₂) rewrite 0-ℤ (mkℤ n₁ x₂) = sym (+ℤneg (mkℤ (suc n) x) (mkℤ n₁ x₂))
ℤ+ℤ-ℤ (mkℤ (suc n) x) (mkℤ (suc n₁) x₁) (mkℤ zero triv) = refl
ℤ+ℤ-ℤ (mkℤ (suc n) x) (mkℤ (suc n₁) tt) (mkℤ (suc n₂) tt) = {!   !}
ℤ+ℤ-ℤ (mkℤ (suc n) x) (mkℤ (suc n₁) ff) (mkℤ (suc n₂) tt) = {!   !}
ℤ+ℤ-ℤ (mkℤ (suc n) x) (mkℤ (suc n₁) x₁) (mkℤ (suc n₂) ff) = {!   !}
