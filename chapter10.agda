module chapter10 where

open import list
open import nat
open import product
open import relations
open import nat
open import unit

infixr 6 _⇒_
infixr 7 _&_

data formula : Set where
  $ : nat → formula
  True : formula
  _⇒_ : formula → formula → formula
  _&_ : formula → formula → formula

p q r : formula
p = $ 0
q = $ 1
r = $ 2

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
        V         : W → nat → Set
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

data _≼_ : 𝕃 formula → 𝕃 formula → Set where
  ≼-refl : ∀ {Γ} → Γ ≼ Γ
  ≼-cons : ∀ {Γ Γ' f} → Γ ≼ Γ' → Γ ≼ (f :: Γ')

≼-trans : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≼ Γ₂ → Γ₂ ≼ Γ₃ → Γ₁ ≼ Γ₃
≼-trans r ≼-refl = r
≼-trans r (≼-cons r') = ≼-cons (≼-trans r r')

weaken≼ : ∀{Γ Γ' f} → Γ ≼ Γ' → Γ ⊢ f → Γ' ⊢ f
weaken≼ ≼-refl prov = prov
weaken≼ (≼-cons ext) prov = weaken (weaken≼ ext prov)

U : struct
U = record
    { W = ctxt
    ; R = _≼_
    ; preorderR = ≼-refl , ≼-trans
    ; V = λ Γ v → Γ ⊢ $ v
    ; monoV = λ rel → weaken≼ rel
    }

CompletenessU : ∀ {f Γ} → U , Γ ⊨ f → Γ ⊢ f
SoundnessU : ∀ {f Γ} → Γ ⊢ f → U , Γ ⊨ f
CompletenessU {$ x} truthPrf = truthPrf
CompletenessU {True} _ = TrueI
CompletenessU {f₁ ⇒ f₂} truthPrf = ImpliesI (CompletenessU (truthPrf (≼-cons ≼-refl) (SoundnessU {f₁} assume)))
CompletenessU {f₁ & f₂} (p₁ , p₂) = AndI (CompletenessU p₁) (CompletenessU p₂)
SoundnessU {$ x} derivPrf = derivPrf
SoundnessU {True} _ = triv
SoundnessU {f₁ & f₂} derivPrf = SoundnessU (AndE₁ derivPrf) , SoundnessU (AndE₂ derivPrf)
SoundnessU {f₁ ⇒ f₂} derivPrf rel f₁prf = SoundnessU (ImpliesE (weaken≼ rel derivPrf) (CompletenessU f₁prf))

ctxt-id : ∀ Γ → U , Γ ⊨ctxt Γ
ctxt-id [] = triv
ctxt-id (f :: Γ) = SoundnessU {f} assume , mono⊨ctxt (≼-cons ≼-refl) (ctxt-id Γ)

Completeness : ∀ {f Γ} → Γ ⊩ f → Γ ⊢ f
Completeness {Γ = Γ} p = CompletenessU (p (ctxt-id Γ))

Universality₁ : ∀ {f Γ} → Γ ⊩ f → U , Γ ⊨ f
Universality₁ {f} {Γ} prf = SoundnessU (Completeness {f} {Γ} prf)

Universality₂ : ∀ {f Γ} → U , Γ ⊨ f → Γ ⊩ f
Universality₂ {f} {Γ} prf = Soundness (CompletenessU {f} {Γ} prf)

nbe : ∀ {Γ f} → Γ ⊢ f → Γ ⊢ f
nbe p = Completeness (Soundness p)

-- It's also instructive to look at the normalized form of just Soundness applied to these examples

a : [] ⊢ True
a = AndE₁ (AndI TrueI TrueI)

b : [] ⊢ True
b = ImpliesE (ImpliesE (ImpliesI (ImpliesI assume)) TrueI) TrueI

c : [] ⊢ p ⇒ p
c = ImpliesI (ImpliesE (ImpliesI assume) assume)

d : [ q ] ⊢ p ⇒ q
d = ImpliesI (ImpliesE (ImpliesI (weaken (weaken assume))) assume)

e : [] ⊢ (p & q) ⇒ (p & q)
e = ImpliesI assume

-- Exercises
--
-- 10.1

prf1 : [] ⊢ p & (q & r) ⇒ (p & q) & r
prf1 = ImpliesI (AndI (AndI (AndE₁ assume) (AndE₁ (AndE₂ assume))) (AndE₂ (AndE₂ assume)))

prf2 : [] ⊢ p & q ⇒ q & p
prf2 = ImpliesI (AndI (AndE₂ assume) (AndE₁ assume))

prf3 : [] ⊢ (p ⇒ q) ⇒ p ⇒ q
prf3 = ImpliesI assume

prf4 : [] ⊢ p ⇒ (p ⇒ q) ⇒ q
prf4 = ImpliesI (ImpliesI (ImpliesE assume (weaken assume)))

prf5 : [] ⊢ p ⇒ (p ⇒ q ⇒ r) ⇒ q ⇒ r
prf5 = ImpliesI (ImpliesI (ImpliesE assume (weaken assume)))

prf6 : [] ⊢ p ⇒ q ⇒ (p ⇒ q ⇒ r) ⇒ r
prf6 = ImpliesI (ImpliesI (ImpliesI (ImpliesE (ImpliesE assume (weaken (weaken assume))) (weaken assume))))

prf7 : [] ⊢ (p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r
prf7 = ImpliesI (ImpliesI (ImpliesI (ImpliesE (ImpliesE (weaken (weaken assume)) assume) (ImpliesE (weaken assume) assume))))
