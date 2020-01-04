module chapter03 where

open import nat
open import eq

+0 : ∀ x → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
-- +assoc (suc x) y z rewrite +assoc x y z = refl
+assoc (suc x) y z = cong suc (+assoc x y z)

+succ : ∀ x y → suc (x + y) ≡ x + suc y
+succ zero y = refl
+succ (suc x) y rewrite +succ x y = refl

+comm : ∀ x y → x + y ≡ y + x
+comm zero y = sym (+0 y)
+comm (suc x) y rewrite +comm x y = +succ y x
