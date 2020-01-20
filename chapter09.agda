module chapter09 where

open import termination
open import nat
open import nat-thms
open import sum
open import eq
open import bool
open import bool-thms
open import product
open import product-thms

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

div-result : ℕ → ℕ → Set
div-result x d = Σ ℕ (λ q →
                 Σ ℕ (λ r →
                    q * d + r ≡ x
                  ∧ r < d ≡ tt
                  ))

div-helper : (x : ℕ)
           → (↓x : ↓𝔹 _>_ x)
           → (d : ℕ)
           → (nz : d =ℕ 0 ≡ ff)
           → div-result x d
div-helper zero _ (suc d) _ = zero , zero , refl , refl
div-helper (suc x) (pf↓ fx) (suc d) _ with keep (x < d)
... | tt , p = zero , suc x , refl , p
... | ff , p with div-helper (x ∸ d) (fx (∸<1 {x} {d})) (suc d) refl
... | q , r , p₁ , p₂ = suc q , r , lemma {q * suc d} {r} {d} (∸eq-swap {x} {d} (<ff {x} p) p₁) , p₂
  where
    lemma : ∀ {a b c} → a + b + c ≡ x → suc (c + a + b) ≡ suc x
    lemma {a} {b} {c} prf rewrite +comm c a
                                | sym (+assoc a c b)
                                | +comm c b
                                | +assoc a b c
                                | prf = refl
