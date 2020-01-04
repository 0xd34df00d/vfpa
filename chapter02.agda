module chapter02 where

open import bool
open import level
open import eq

open import product

~~tt : ~ ~ tt ≡ tt
~~tt = refl

~~-elim : ∀ b → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl

{-
~~-elim' : ∀ b → ~ ~ b ≡ b
~~-elim' tt = ?
~~-elim' ff = ~~tt
-}

||≡ff₁ : ∀ {b₁ b₂} → b₁ || b₂ ≡ ff → b₁ ≡ ff
||≡ff₁ {ff} _ = refl
--||≡ff₁ {tt} ()
--||≡ff₁ {tt} p = p

||-cong₂ : ∀ {b₁ b₂ b₂'} → b₂ ≡ b₂' → b₁ || b₂ ≡ b₁ || b₂'
||-cong₂ p rewrite p = refl

-- 2.2

&&-decomp : ∀ {b₁ b₂} → b₁ && b₂ ≡ tt → b₁ ≡ tt × b₂ ≡ tt
&&-decomp{tt}{tt} _ = refl , refl

-- 2.3

th1 : tt ≡ tt
th1 = refl

th2 : ff ≡ ff
th2 = refl

--th3 : ff ≡ tt

th4 : ff && ff ≡ ~ tt
th4 = refl

th5 : ∀ {x} → tt && x ≡ x
th5 = refl

th6 : ∀ {x} → x && tt ≡ x
th6 {tt} = refl
th6 {ff} = refl
-- so nope, requires case split and two refls
