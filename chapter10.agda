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

record struct : Set1 where
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
