module chapter01 where

open import bool hiding ( _xor_ )

-- 1.3

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor b = ~ b
ff xor b = b

-- 1.4

data day : Set where
  mon : day
  tue : day
  wed : day
  thu : day
  fri : day
  sat : day
  sun : day

-- 1.5

nextday : day → day
nextday mon = tue
nextday tue = wed
nextday wed = thu
nextday thu = fri
nextday fri = sat
nextday sat = sun
nextday sun = mon

-- 1.6

data suit : Set where
  hearts : suit
  spades : suit
  diamonds : suit
  clubs : suit

-- 1.7

is-red : suit → 𝔹
is-red hearts = tt
is-red diamonds = tt
is-red _ = ff
