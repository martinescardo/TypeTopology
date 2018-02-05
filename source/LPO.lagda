Martin Escardo, December 2017 (but done much earlier on paper)

As discussed in the module Omniscience, Bishop's "limited principle of
omniscience" amount to the omniscience of the type ℕ, that is,

  Π \(p : ℕ → 𝟚) → (Σ \(n : ℕ) → p n ≡ ₀) + (Π \(n : ℕ) → p n ≡ ₁).

This is in general not a univalent proposition, because there may be
many n:ℕ with p n ≡ ₀. In univalent mathematics, we may get a
proposition by truncating the Σ to get the existential quantifier ∃
(see the Homotopy Type Theory book). Here instead we construct the
truncation directly, and call it LPO.

Using this and the module Prop-Tychonoff, we show that the function
type LPO→ℕ is searchable and hence omniscient, despite the fact that
LPO is undecided in our type theory.

(We needed to add new helper lemmas in the module
GenericConvergentSequence)

\begin{code}

open import UF

module LPO (fe : {U V : Universe} → FunExt U V) where

open import Naturals
open import Two
open import GenericConvergentSequence
open import DecidableAndDetachable
open import OmniscientTypes

LPO : U₀ ̇
LPO = (x : ℕ∞) → decidable(Σ \(n : ℕ) → x ≡ under n)

LPO-isProp : isProp LPO
LPO-isProp = isProp-exponential-ideal fe f
 where
  a : (x : ℕ∞) → isProp(Σ \n → x ≡ under n)
  a x (n , p) (m , q) = Σ-≡ n m p q (under-lc (p ⁻¹ ∙ q)) (ℕ∞-set fe _ _)
  
  f : (x : ℕ∞) → isProp (decidable (Σ \n → x ≡ under n))
  f x = sum-of-contradictory-props (a x) (neg-isProp fe) (λ u φ → φ u)

LPO-implies-omniscient-ℕ : LPO → omniscient ℕ
LPO-implies-omniscient-ℕ lpo β = cases a b d
  where
    A = (Σ \(n : ℕ) → β n ≡ ₀) + (Π \(n : ℕ) → β n ≡ ₁)
    
    α : ℕ → 𝟚
    α = force-decreasing β
    
    x : ℕ∞
    x = (α , force-decreasing-is-decreasing β)
    
    d : decidable(Σ \(n : ℕ) → x ≡ under n)
    d = lpo x
    
    a : (Σ \(n : ℕ) → x ≡ under n) → A
    a (n , p) = inl (force-decreasing-is-not-much-smaller β n c) 
      where
        c : α n ≡ ₀
        c = ap (λ x → incl x n) p ∙ under-diagonal₀ n
        
    b : (¬ Σ \(n : ℕ) → x ≡ under n) → A
    b u = inr g
      where
        v : (n : ℕ) → x ≡ under n → 𝟘
        v = curry u
        
        g : (n : ℕ) → β n ≡ ₁
        g n = force-decreasing-is-smaller β n e
          where
            c : x ≡ under n → 𝟘
            c = v n
            
            l : x ≡ ∞
            l = not-ℕ-is-∞ fe v
            
            e : α n ≡ ₁
            e = ap (λ x → incl x n) l

omniscient-ℕ→LPO : omniscient ℕ → LPO
omniscient-ℕ→LPO chlpo x = cases a b d
  where
    A = decidable (Σ \(n : ℕ) → x ≡ under n)
    
    β : ℕ → 𝟚
    β = incl x
    
    d : (Σ \(n : ℕ) → β n ≡ ₀) + (Π \(n : ℕ) → β n ≡ ₁)
    d = chlpo β
    
    a : (Σ \(n : ℕ) → β n ≡ ₀) → A
    a (n , p) = inl g
      where
        g : Σ \(n : ℕ) → x ≡ under n
        g = under-lemma fe x n p
        
    b : (Π \(n : ℕ) → β n ≡ ₁) → A
    b φ = inr g
      where
        ψ : ¬ Σ \(n : ℕ) → β n ≡ ₀
        ψ = uncurry (λ n → Lemma[b≡₁→b≢₀](φ n))
        
        f : (Σ \(n : ℕ) → x ≡ under n) → Σ \(n : ℕ) → β n ≡ ₀
        f (n , p) = (n , (ap (λ x → incl x n) p ∙ under-diagonal₀ n))
          where
           l : incl x n ≡ incl (under n) n
           l = ap (λ x → incl x n) p
        
        g : ¬ Σ \(n : ℕ) → x ≡ under n
        g = contrapositive f ψ

\end{code}

Now, if LPO is false, that is, an empty type, then the function type

  LPO → ℕ
  
is isomorphic to the unit type 𝟙, and hence is searchable and
omniscient. If LPO holds, that is, LPO is isomorphic to 𝟙 because it
is a univalent proposition, then the function type LPO → ℕ is
isomorphic to ℕ, and hence the type LPO → ℕ is again searchable by
LPO. So in any case we have that the type LPO → ℕ is
searchable. However, LPO is an undecided proposition in our type
theory, so that the nature of the function type LPO → ℕ is
undecided. Nevertheless, we can show that it is searchable, without
knowing whether LPO holds or not!

\begin{code}

open import SearchableTypes
open import PropTychonoff

LPO→ℕ-searchable : searchable(LPO → ℕ)
LPO→ℕ-searchable = prop-tychonoff-corollary' fe LPO-isProp f
 where
   f : LPO → searchable ℕ
   f = inhabited-omniscient-implies-searchable 0 ∘ LPO-implies-omniscient-ℕ

LPO→ℕ-omniscient : omniscient(LPO → ℕ)
LPO→ℕ-omniscient = searchable-implies-omniscient LPO→ℕ-searchable

\end{code}
