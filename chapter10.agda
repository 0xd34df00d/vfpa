module chapter10 where

open import list
open import nat
open import product
open import relations
open import string
open import unit

infixr 6 _⇒_
infixr 7 _&_

data formula : Set where
  $ : string → formula
  True : formula
  _⇒_ : formula → formula → formula
  _&_ : formula → formula → formula

p q : formula
p = $ "p"
q = $ "q"

ctxt : Set
ctxt = 𝕃 formula

infix 5 _⊢_

data _⊢_ : ctxt → formula → Set where
  assume   : ∀ {Γ f}      {- none   -}
                          → f :: Γ ⊢ f
  weaken   : ∀ {Γ f f'}   → Γ ⊢ f
                          → f' :: Γ ⊢ f
  TrueI    : ∀ {Γ}        {- none   -}
                          → Γ ⊢ True
  ImpliesI : ∀ {Γ f₁ f₂}  → f₁ :: Γ ⊢ f₂
                          → Γ ⊢ f₁ ⇒ f₂
  ImpliesE : ∀ {Γ f₁ f₂}  → Γ ⊢ f₁ ⇒ f₂ → Γ ⊢ f₁
                          → Γ ⊢ f₂
  AndI     : ∀ {Γ f₁ f₂}  → Γ ⊢ f₁ → Γ ⊢ f₂
                          → Γ ⊢ f₁ & f₂
  AndE₁    : ∀ {Γ f₁ f₂}  → Γ ⊢ f₁ & f₂
                          → Γ ⊢ f₁
  AndE₂    : ∀ {Γ f₁ f₂}  → Γ ⊢ f₁ & f₂
                          → Γ ⊢ f₂

exTerm1 : [] ⊢ p ⇒ p & p
exTerm1 = ImpliesI (AndI assume assume)

record struct : Set₁ where
  field W         : Set
        R         : W → W → Set
        preorderR : preorder R
        V         : W → string → Set
        monoV     : ∀ {w w'} → R w w' → ∀ {s} → V w s → V w' s
  reflR : reflexive R
  reflR = fst preorderR
  transR : transitive R
  transR = snd preorderR

open struct

_,_⊨_ : (k : struct) → W k → formula → Set
k , w ⊨ $ x = V k w x
k , w ⊨ True = ⊤
k , w ⊨ (f₁ ⇒ f₂) = ∀ {w'} → R k w w' → k , w' ⊨ f₁ → k , w' ⊨ f₂
k , w ⊨ (f₁ & f₂) = (k , w ⊨ f₁) ∧ (k , w ⊨ f₂)

_,_⊨ctxt_ : (k : struct) → W k → ctxt → Set
k , w ⊨ctxt [] = ⊤
k , w ⊨ctxt (f :: fs) = (k , w ⊨ f) ∧ (k , w ⊨ctxt fs)

mono⊨ : ∀ {k f w₁ w₂} → R k w₁ w₂ → k , w₁ ⊨ f → k , w₂ ⊨ f
mono⊨ {k} {$ x} r p = monoV k r p
mono⊨ {k} {True} r p = triv
mono⊨ {k} {f₁ ⇒ f₂} r p r' p' = p (transR k r r') p'
mono⊨ {k} {f₁ & f₂} r (p₁ , p₂) = mono⊨ {f = f₁} r p₁ , mono⊨ {f = f₂} r p₂

mono⊨ctxt : ∀ {k Γ w₁ w₂} → R k w₁ w₂ → k , w₁ ⊨ctxt Γ → k , w₂ ⊨ctxt Γ
mono⊨ctxt {Γ = []} r p = triv
mono⊨ctxt {Γ = f :: Γ} r (p₁ , p₂) = mono⊨ {f = f} r p₁ , mono⊨ctxt r p₂

_⊩_ : ctxt → formula → Set₁
Γ ⊩ f = ∀ {k} {w : W k} → k , w ⊨ctxt Γ → k , w ⊨ f

Soundness : ∀ {Γ f} → Γ ⊢ f → Γ ⊩ f
Soundness assume ctx = fst ctx
Soundness (weaken deriv) ctx = Soundness deriv (snd ctx)
Soundness TrueI _ = triv
Soundness (ImpliesI deriv) ctx rel f₁ent = Soundness deriv (f₁ent , mono⊨ctxt rel ctx)
Soundness (ImpliesE d_f₁ d_impl) {k} ctx = Soundness d_f₁ ctx (reflR k) (Soundness d_impl ctx)
Soundness (AndI deriv₁ deriv₂) ctx = Soundness deriv₁ ctx , Soundness deriv₂ ctx
Soundness (AndE₁ deriv) ctx = fst (Soundness deriv ctx)
Soundness (AndE₂ deriv) ctx = snd (Soundness deriv ctx)
