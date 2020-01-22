module chapter09 where

open import termination
open import nat
open import nat-thms
open import sum
open import eq
open import bool
open import bool-thms
open import bool-thms2
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

module meas {ℓ ℓ' ℓ₁ ℓ₂}
            {A : Set ℓ} {B : Set ℓ'}
            (_>A_ : A → A → Set ℓ₁)
            (_>B_ : B → B → Set ℓ₂)
            (m : A → B)
            (decreasem : ∀ {a a'} → a >A a' → m a >B m a')
      where

  measure-↓' : ∀ {a} → ↓ _>B_ (m a) → ↓ _>A_ a
  measure-↓' {a} (pf↓ fm) = pf↓ f
    where
      f : {y : A} → a >A y → ↓ _>A_ y
      f prf = measure-↓' (fm (decreasem prf))

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



infixl 7 _∘_
infix 6 _⇝_

data comb : Set where
  S : comb
  K : comb
  _∘_ : comb → comb → comb

data _⇝_ : comb → comb → Set where
  ⇝K : (a b : comb) → K ∘ a ∘ b ⇝ a
  ⇝S : (a b c : comb) → S ∘ a ∘ b ∘ c ⇝ (a ∘ c) ∘ (b ∘ c)
  ⇝Cong1 : {a a' : comb} → (b : comb) → a ⇝ a' → a ∘ b ⇝ a' ∘ b
  ⇝Cong2 : (a : comb) → {b b' : comb} → b ⇝ b' → a ∘ b ⇝ a ∘ b'

size : comb → ℕ
size S = 1
size K = 1
size (a ∘ b) = suc (size a + size b)

-- S-free combinators

Sfree : comb → 𝔹
Sfree S = ff
Sfree K = tt
Sfree (a ∘ b) = Sfree a && Sfree b

Sfree-⇝-size> : ∀ {a a' : comb}
              → Sfree a ≡ tt
              → a ⇝ a'
              → size a > size a' ≡ tt
Sfree-⇝-size> prf (⇝K a b) = ≤<-trans {size a}
                                (≤+1 (size a) (size b))
                                (<+2 {size a + size b} {2})
Sfree-⇝-size> prf (⇝Cong1 {a} {a'} b r) with &&-elim {Sfree a} prf
... | prf' , _ = <+mono2 {size a'} (Sfree-⇝-size> prf' r)
Sfree-⇝-size> prf (⇝Cong2 a r) with &&-elim{Sfree a} prf
... | _ , prf' = <+mono1 {size a} (Sfree-⇝-size> prf' r)

⇝-preserves-Sfree : ∀ {a a' : comb}
                  → Sfree a ≡ tt
                  → a ⇝ a'
                  → Sfree a' ≡ tt
⇝-preserves-Sfree prf (⇝K a b) = fst (&&-elim {Sfree a} prf)
⇝-preserves-Sfree prf (⇝Cong1 {a} {a'} b r) with &&-elim {Sfree a} prf
... | prf_a , prf_b = let rec = ⇝-preserves-Sfree prf_a r
                      in &&-intro rec prf_b
⇝-preserves-Sfree prf (⇝Cong2 a r) with &&-elim {Sfree a} prf
... | prf_a , prf_b = let rec = ⇝-preserves-Sfree prf_b r
                      in &&-intro prf_a rec
