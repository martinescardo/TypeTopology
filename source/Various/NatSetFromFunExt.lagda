\begin{code}

open import MLTT.Id
open import MLTT.NaturalNumbers
open import MLTT.Pi
open import MLTT.Plus
open import MLTT.Universes using (𝓤₀)
open import UF.HedbergApplications
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Naturals.Properties using (pred)

module Various.NatSetFromFunExt where

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

dne : (m n : ℕ) → (((m ＝ n) → is-prop ℕ) → is-prop ℕ) → m ＝ n
dne m n nneq = lemma (decide m n)
  where
  lemma : ((m ＝ n) + ((m ＝ n) → is-prop ℕ)) → m ＝ n
  lemma (inl eq) = eq
  lemma (inr neq) = nneq neq m n

ℕ-is-set : funext 𝓤₀ 𝓤₀ → is-set ℕ
ℕ-is-set fe =
 reflexive-prop-valued-relation-that-implies-equality-gives-set
  (λ m n → ((m ＝ n) → is-prop ℕ) → is-prop ℕ)
  (λ m n → Π-is-prop fe (λ _ → being-prop-is-prop fe))
  (λ n neq → neq refl)
  dne

\end{code}
