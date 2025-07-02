\begin{code}

open import MLTT.Id
open import MLTT.NaturalNumbers
open import MLTT.Pi
open import MLTT.Plus
open import MLTT.Sigma
open import UF.Hedberg
open import UF.Sets using (is-set)
open import UF.Subsingletons using (is-prop)
open import UF.Subsingletons-Properties using (props-are-sets)
open import Naturals.Properties using (pred)

module Various.NatSet where

reduce : (n : ℕ) → 0 ＝ succ n → 0 ＝ 1
reduce zero = id
reduce (succ n) eq = reduce n (ap pred eq)

expand : (n : ℕ) → 0 ＝ 1 → 0 ＝ n
expand zero _ = refl
expand (succ n) eq = eq ∙ ap succ (expand n eq)

explode : (n : ℕ) → 0 ＝ succ n → is-prop ℕ
explode n eq m k = (expand m (reduce n eq)) ⁻¹ ∙ expand k (reduce n eq)

decide : (m n : ℕ) → (m ＝ n) + ((m ＝ n) → is-prop ℕ)
decide zero zero = inl refl
decide zero (succ n) = inr (explode n)
decide (succ m) zero = inr (explode m ∘ _⁻¹)
decide (succ m) (succ n) = bump (decide m n)
 where
  bump : ((m ＝ n) + ((m ＝ n) → is-prop ℕ)) → (succ m ＝ succ n) + ((succ m ＝ succ n) → is-prop ℕ)
  bump (inl eq) = inl (ap succ eq)
  bump (inr neq) = inr (neq ∘ ap pred)

dne-lemma : (m n : ℕ)
 → ((m ＝ n) + ((m ＝ n) → is-prop ℕ))
 → (((m ＝ n) → is-prop ℕ) → is-prop ℕ) → m ＝ n
dne-lemma m n (inl eq) _ = eq
dne-lemma m n (inr neq) nneq = nneq neq m n

dne : (m n : ℕ) → (((m ＝ n) → is-prop ℕ) → is-prop ℕ) → m ＝ n
dne m n = dne-lemma m n (decide m n)

dne-wconstant : (m n : ℕ)
 → (nneq nneq' : ((m ＝ n) → is-prop ℕ) → is-prop ℕ)
 → dne m n nneq ＝ dne m n nneq'
dne-wconstant m n nneq nneq' = dne-lemma-wconstant (decide m n)
 where
  dne-lemma-wconstant : (dec : (m ＝ n) + ((m ＝ n) → is-prop ℕ))
   → dne-lemma m n dec nneq ＝ dne-lemma m n dec nneq'
  dne-lemma-wconstant (inl eq) = refl
  dne-lemma-wconstant (inr neq) = props-are-sets (nneq neq) (nneq neq m n) (nneq' neq m n)

-- A Hedberg-style theorem that does not require the relation to be prop-valued
-- but instead requires the map from R to equality to be weakly constant.
-- If we had funext we could just prove that ((m ＝ n) → is-prop ℕ) → is-prop ℕ)
-- is a proposition instead.

reflexive-relation-that-wconstantly-implies-equality-gives-set
 : {X : 𝓤 ̇ }
 → (_R_ : X → X → 𝓥 ̇ )
 → ((x : X) → x R x)
 → (e : (x y : X) → x R y → x ＝ y)
 → ((x y : X) → wconstant (e x y))
 → is-set X
reflexive-relation-that-wconstantly-implies-equality-gives-set
 {𝓤} {𝓥} {X} _R_ r e ec = γ
 where
  f : {x y :  X} → x ＝ y → x ＝ y
  f {x} {y} p = e x y (transport (x R_) p (r x))

  κ : {x y : X} → wconstant (f {x} {y})
  κ p q = ec _ _ _ _

  γ : is-set X
  γ = Id-collapsibles-are-sets (f , κ)

ℕ-is-set : is-set ℕ
ℕ-is-set =
 reflexive-relation-that-wconstantly-implies-equality-gives-set
  (λ m n → ((m ＝ n) → is-prop ℕ) → is-prop ℕ)
  (λ n neq → neq refl)
  dne
  dne-wconstant

\end{code}
