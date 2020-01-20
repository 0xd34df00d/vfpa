module chapter09 where

open import termination
open import nat
open import nat-thms
open import sum
open import eq
open import bool

↓->' : ∀ x → ↓𝔹 _>_ x
↓->' x₀ = pf↓ (h x₀)
  where
    h : ∀ x → ∀ {y} → y < x ≡ tt → ↓𝔹 _>_ y
    h zero {zero} ()
    h zero {suc y} ()
    h (suc x) {y} prf with <-drop {y} {x} prf
    ... | inj₁ prf' rewrite prf' = ↓->' x
    ... | inj₂ prf' = h x prf'
