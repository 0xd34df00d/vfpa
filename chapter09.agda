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
open import string

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

Sfree-comb : Set
Sfree-comb = Σ comb (λ a → Sfree a ≡ tt)

_⇝̇_ : Sfree-comb → Sfree-comb → Set
(a , _) ⇝̇ (b , _) = a ⇝ b

size-Sfree-comb : Sfree-comb → ℕ
size-Sfree-comb (a , _) = size a

decrease-size : ∀ {a a' : Sfree-comb}
              → a ⇝̇ a'
              → size-Sfree-comb a > size-Sfree-comb a' ≡ tt
decrease-size {a , p} {a' , p'} prf = Sfree-⇝-size> p prf

open meas {A = Sfree-comb}
          _⇝̇_
          (λ a b → a > b ≡ tt)
          size-Sfree-comb
          decrease-size

measure-decreases : ∀ a → ↓ _⇝̇_ a
measure-decreases a = measure-↓' (↓->' (size-Sfree-comb a))


-- λ-abtractions with combinators

data varcomb : Set where
  S : varcomb
  K : varcomb
  _∘_ : (a : varcomb) → (b : varcomb) → varcomb
  var : (s : string) → varcomb

λ* : (s : string) → varcomb → varcomb
λ* s S = K ∘ S
λ* s K = K ∘ K
λ* s (a ∘ b) = S ∘ λ* s a ∘ λ* s b
λ* s (var s') = if s =string s' then S ∘ K ∘ K else K ∘ var s'

contains-var : string → varcomb → 𝔹
contains-var _ S = ff
contains-var _ K = ff
contains-var s (a ∘ b) = contains-var s a || contains-var s b
contains-var s (var s') = s =string s'

λ*-binds : ∀ s v → contains-var s (λ* s v) ≡ ff
λ*-binds s S = refl
λ*-binds s K = refl
λ*-binds s (a ∘ b) rewrite λ*-binds s a | λ*-binds s b = refl
λ*-binds s (var s') with keep (s =string s')
... | tt , prf rewrite prf = refl
... | ff , prf rewrite prf = prf

subst : varcomb → string → varcomb → varcomb
subst c s S = S
subst c s K = K
subst c s (c₁ ∘ c₂) = subst c s c₁ ∘ subst c s c₂
subst c s (var s₁) = if s =string s₁ then c else var s₁

infix 6 _⇒_
data _⇒_ : varcomb → varcomb → Set where
  ⇒K : ∀ (a b) → K ∘ a ∘ b ⇒ a
  ⇒S : ∀ (a b c) → S ∘ a ∘ b ∘ c ⇒ (a ∘ c) ∘ (b ∘ c)
  ⇒Cong₁ : ∀ {a a'} b → a ⇒ a' → a ∘ b ⇒ a' ∘ b
  ⇒Cong₂ : ∀ a {b b'} → b ⇒ b' → a ∘ b ⇒ a ∘ b'

open import closures
open closures.basics _⇒_

infix 6 _⇒+_
_⇒+_ : varcomb → varcomb → Set
_⇒+_ = tc

Cong₁+ : ∀ {a a'} b → a ⇒+ a' → a ∘ b ⇒+ a' ∘ b
Cong₁+ b (tc-step a) = tc-step (⇒Cong₁ b a)
Cong₁+ b (tc-trans a₁ a₂) = tc-trans (Cong₁+ b a₁) (Cong₁+ b a₂)

Cong₂+ : ∀ a {b b'} → b ⇒+ b' → a ∘ b ⇒+ a ∘ b'
Cong₂+ a (tc-step b) = tc-step (⇒Cong₂ a b)
Cong₂+ a (tc-trans b₁ b₂) = tc-trans (Cong₂+ a b₁) (Cong₂+ a b₂)

λ*-⇒ : ∀ v₁ v₂ s
     → λ* s v₁ ∘ v₂ ⇒+ subst v₂ s v₁
λ*-⇒ S v₂ s = tc-step (⇒K S v₂)
λ*-⇒ K v₂ s = tc-step (⇒K K v₂)
λ*-⇒ (a ∘ b) v₂ s = let sDef = tc-step (⇒S (λ* s a) (λ* s b) v₂)
                        ₁cng = Cong₁+ (λ* s b ∘ v₂) (λ*-⇒ a v₂ s)
                        ₂cng = Cong₂+ (subst v₂ s a) (λ*-⇒ b v₂ s)
                    in tc-trans sDef (tc-trans ₁cng ₂cng)
λ*-⇒ (var s') v₂ s with s =string s'
... | tt = tc-trans (tc-step (⇒S K K v₂)) (tc-step (⇒K v₂ (K ∘ v₂)))
... | ff = tc-step (⇒K (var s') v₂)

-- Exercises
--
module exercises where

  -- 9.1

  term1 = λ* "x" (λ* "y" (var "x"))
  term2 = λ* "x" (λ* "y" (var "y"))
  term3 = λ* "s" (λ* "z" (var "s" ∘ var "z"))
  term4 = λ* "x" (var "x" ∘ var "x")

  -- 9.2

  c : comb
  c = (K ∘ K) ∘ ((K ∘ K) ∘ K)

  red1 : c ⇝ K
  red1 = ⇝K K (K ∘ K ∘ K)

  red2 : c ⇝ (K ∘ K) ∘ K
  red2 = ⇝Cong2 (K ∘ K) (⇝K K K)

  -- 9.3

  open closures.basics _⇝_ renaming ( tc to tc⇝
                                    ; tc-step to tc-step⇝
                                    )

  infix 6 _⇝+_
  _⇝+_ : comb → comb → Set
  _⇝+_ = tc⇝

  mred : (K ∘ K) ∘ ((K ∘ K) ∘ K) ⇝+ K
  mred = tc-step⇝ red1
