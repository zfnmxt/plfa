import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


-- --------------------------------
-- (zero + n)  + p ≡ zero + (n + p)

-- (m + n) + p ≡ m + (n + p)
-- -------------------------
-- (suc m + n) + p ≡ suc m + (n + p)
+assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+assoc m n p) ⟩
    suc ( m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎



-- lemma: m + zero ≡ m
+identityᴿ : ∀(m : ℕ) → m + zero ≡ m
+identityᴿ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+identityᴿ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+identityᴿ m) ⟩
    suc m
  ∎


-- lemma: m + suc n ≡ suc (m + n)
+suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+suc m n ) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- proposition: ∀ (m n : ℕ) → m + n ≡ n + m
+comm : ∀ (m n : ℕ) → m + n ≡ n + m
+comm m zero =
  begin
     m + zero
   ≡⟨ +identityᴿ m ⟩
     m
   ≡⟨⟩
     zero + m
   ∎
+comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- corollary: rearranging
+rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎

-- sym : if e provides evidence that a≡b then sym e provides evidence that b≡a.
+swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+swap zero n  p = refl
+swap (suc m) n p  rewrite +assoc m n p | +comm m (n + p) | +comm p m | sym (+suc n (m + p))= refl


