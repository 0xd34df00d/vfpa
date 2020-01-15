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

_-ℤ_ : ℤ → ℤ → ℤ
z -ℤ mkℤ zero ss = z
mkℤ zero ms -ℤ mkℤ (suc s) ss = mkℤ (suc s) (~ ss)
mkℤ (suc m) ms -ℤ mkℤ (suc s) ss with ms xor ss
... | tt = mkℤ (suc m + suc s) ms
... | ff = if ms then diffℤ m s else diffℤ s m
