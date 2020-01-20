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

module measure' {ℓ ℓ' ℓ₁ ℓ₂}
                {A : Set ℓ} {B : Set ℓ'}
                (_>A_ : A → A → Set ℓ₁)
                (_>B_ : B → B → Set ℓ₂)
                (m : A → B)
                (decreasem : ∀ {a a'} → a >A a' → m a >B m a')
      where

  measure-↓ : ∀ {a} → ↓ _>B_ (m a) → ↓ _>A_ a
  measure-↓ {a} (pf↓ fm) = pf↓ f
    where
      f : {y : A} → a >A y → ↓ _>A_ y
      f prf = measure-↓ (fm (decreasem prf))
