import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- open import plfa.part1.Naturals
-- Natural number datatype
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    suc (suc (suc (suc (suc 0))))
  ∎

_ : 2 + 3 ≡ 5
_ = refl

infixl 6 _+_ _∸_
infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ n = zero
(suc n) ∸ (suc m) = n ∸ m
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (suc (suc 0)) + suc (suc (suc (suc 0)))
  ≡⟨⟩
    suc ((suc (suc 0)) + (suc (suc (suc (suc 0)))))
  ≡⟨⟩
    suc (suc ((suc 0) + (suc (suc (suc (suc 0))))))
  ≡⟨⟩
    suc (suc (suc (0 + (suc (suc (suc (suc 0)))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc 0))))))
  ∎


_ : 4 ∸ 3 ≡ 1
_ = refl

-- Does not terminate for n / m case
-- _̇/_ : ℕ → ℕ → ℕ
-- zero ̇/ m = zero
-- n ̇/ m = suc ((n ∸ m) ̇/ m)

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)

data Bin : Set where
  <> : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- Increment binary number by I
inc : Bin → Bin
inc (t O)  = t I
inc (<> I) = <> I O
inc (t I)  = inc t O
inc <> = <>

to : ℕ → Bin
to zero = <> O
to (suc m) = inc (to m)

from : Bin -> ℕ
from <> = zero
from (t O) = 2 * from(t)
from (t I) = 1 + 2 * from(t)
