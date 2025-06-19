Martin Escardo, 3rd Feb 2025.

Does the type ℕ∞₂ have a tight apartness? I don't think so. Here is an
illustrative failed attempt, which satisfies all conditions except
cotransitivity.

We use the standard apartness relation _♯_ on the Cantor type ℕ → 𝟚 to
define our attempted apartness relation _#_ on ℕ∞₂.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module gist.not-an-apartness
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import CoNaturals.Type
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Taboos.LPO
open import TypeTopology.Cantor
open import TypeTopology.FailureOfTotalSeparatedness fe
open import UF.Base
open import UF.DiscreteAndSeparated hiding (_♯_)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt
open Apartness pt

module failed-attempt where

 _#_  : ℕ∞₂ → ℕ∞₂ → 𝓤₀ ̇
 (x@(α , _) , f) # (y@(β , _) , g) =
  (α ♯ β) + (Σ p ꞉ x ＝ ∞ , Σ q ꞉ y ＝ ∞ , f p ≠ g q)

 s : is-strong-apartness _♯_
 s = ♯-is-strong-apartness fe

 I : is-prop-valued _#_
 I (x , f) (y , g) (inl a) (inl a') =
  ap inl (strong-apartness-is-prop-valued _♯_ s (ι x) (ι y) a a')
 I (x , f) (y , g) (inl a) (inr (p , q , _)) =
  𝟘-elim (strong-apartness-is-irreflexive' _♯_ s (ι x) (ι y) a
           (ap ι (p ∙ q ⁻¹)))
 I (x , f) (y , g) (inr (p , q , _)) (inl a) =
  𝟘-elim (strong-apartness-is-irreflexive' _♯_ s (ι x) (ι y) a
           (ap ι (p ∙ q ⁻¹)))
 I (x , f) (y , g) (inr b) (inr b') =
  ap inr
     (Σ-is-prop
       (ℕ∞-is-set fe)
       (λ p → Σ-is-prop (ℕ∞-is-set fe) (λ q → negations-are-props fe)) b b')

 II : is-irreflexive _#_
 II (x , f) (inl a) =
  strong-apartness-is-irreflexive _♯_ s (ι x) a
 II (x , f) (inr (p , q , d)) = 𝟘-elim (d (ap f (ℕ∞-is-set fe p q)))

 III : is-symmetric _#_
 III (x , f) (y , g) (inl a) =
  inl (strong-apartness-is-symmetric _♯_ s (ι x) (ι y) a)
 III (x , f) (y , g) (inr (p , q , d)) =
  inr (q , p , (≠-sym d))

 IV : is-tight _#_
 IV (x , f) (y , g) ν = to-Σ-＝ (IV₂ , IV₄)
  where
   IV₀ : ¬ ((ι x) ♯ (ι y))
   IV₀ a = ν (inl a)

   IV₁ : (p : x ＝ ∞) (q : y ＝ ∞) → f p ＝ g q
   IV₁ p q = 𝟚-is-¬¬-separated (f p) (g q) (λ d → ν (inr (p , q , d)))

   IV₂ : x ＝ y
   IV₂ = to-subtype-＝
        (being-decreasing-is-prop fe)
        (♯-is-tight fe (ι x) (ι y) IV₀)

   IV₃ : (r : x ＝ y) → transport (λ - → - ＝ ∞ → 𝟚) r f ＝ g
   IV₃ refl = dfunext fe (λ u → IV₁ u u)

   IV₄ : transport (λ - → - ＝ ∞ → 𝟚) IV₂ f ＝ g
   IV₄ = IV₃ IV₂

 V : is-cotransitive _#_ → LPO
 V sc = LPO-criterion fe V₆
  where
   module _ (x : ℕ∞) where

    α : 𝟚ᴺ
    α = ι x

    u : ℕ∞₂
    u = (x , λ _ → ₀)

    a : ∞₀ # ∞₁
    a = inr (refl , refl , zero-is-not-one)

    V₀ : (∞₀ # u) ∨ (∞₁ # u)
    V₀ = sc ∞₀ ∞₁ u a

    V₁ : ((𝟏 ♯ α) + (Σ p ꞉ ∞ ＝ ∞ , Σ q ꞉ x ＝ ∞ , ₀ ≠ ₀))
       ∨ ((𝟏 ♯ α) + (Σ p ꞉ ∞ ＝ ∞ , Σ q ꞉ x ＝ ∞ , ₁ ≠ ₀))
    V₁ = V₀

    V₂ : ((𝟏 ♯ α) + (Σ p ꞉ ∞ ＝ ∞ , Σ q ꞉ x ＝ ∞ , ₀ ≠ ₀))
       + ((𝟏 ♯ α) + (Σ p ꞉ ∞ ＝ ∞ , Σ q ꞉ x ＝ ∞ , ₁ ≠ ₀))
       → (𝟏 ♯ α) + (α ＝ 𝟏)
    V₂ (inl (inl a)) = inl a
    V₂ (inl (inr (p , q , d))) = 𝟘-elim (d refl)
    V₂ (inr (inl a)) = inl a
    V₂ (inr (inr (p , q , d))) = inr (ap ι q)

    V₃ : is-prop ((𝟏 ♯ α) + (α ＝ 𝟏))
    V₃ = sum-of-contradictory-props
          (♯-is-prop-valued fe 𝟏 α)
          (Cantor-is-set fe)
          V₃-₀
     where
      V₃-₀ : (𝟏 ♯ α) → (α ＝ 𝟏) → 𝟘 {𝓤₀}
      V₃-₀ (n , d , _) refl = d refl

    V₄ : (𝟏 ♯ α) + (α ＝ 𝟏)
    V₄ = ∥∥-rec V₃ V₂ V₁

    V₅ : type-of V₄ → is-decidable (Σ n ꞉ ℕ , α n ＝ ₀)
    V₅ (inl (n , d , _)) = inl (n , different-from-₁-equal-₀ (≠-sym d))
    V₅ (inr p) = inr (λ (n , q) → equal-₁-different-from-₀ (happly p n) q)

    V₆ : is-decidable (Σ n ꞉ ℕ , x ⊑ n)
    V₆ = V₅ V₄

\end{code}

Experiment (9th Feb 2025). Characterization of wconstant endomaps of
the type P + Q, where P and Q are propositions, and hence of when we
have a map ∥ P + Q ∥ → P + Q (by generalized Hedberg). This is to be
moved elsewhere when it is tidied up and completed.

We show that there is a wconstant endomap of P + Q if and only there
are functions

          g₀ : P → 𝟚
          g₁ : (p : P) → g₀ p ＝ ₁ → Q
          h₀ : Q → 𝟚
          h₁ : (q : Q) → h₀ q ＝ ₀ → P
          w :  (p : P) (q : Q) → g₀ p ＝ h₀ q

The idea is to get rid of "+", with only the type 𝟚 left as its
shadow.

\begin{code}

open import UF.Hedberg

module _ (P : 𝓤 ̇ )
         (Q : 𝓥 ̇ )
         (P-is-prop : is-prop P)
         (Q-is-prop : is-prop Q)
       where

 module _ (g₀ : P → 𝟚)
          (g₁ : (p : P) → g₀ p ＝ ₁ → Q)
          (h₀ : Q → 𝟚)
          (h₁ : (q : Q) → h₀ q ＝ ₀ → P)
          (w :  (p : P) (q : Q) → g₀ p ＝ h₀ q)
       where

  private
   f₀ : (p : P) (m : 𝟚) → g₀ p ＝ m → P + Q
   f₀ p ₀ r = inl p
   f₀ p ₁ r = inr (g₁ p r)

   f₁ : (q : Q) (n : 𝟚) → h₀ q ＝ n → P + Q
   f₁ q ₀ s = inl (h₁ q s)
   f₁ q ₁ s = inr q

  f : P + Q → P + Q
  f (inl p) = f₀ p (g₀ p) refl
  f (inr q) = f₁ q (h₀ q) refl

  private
   wc : (p : P) (q : Q) (m n : 𝟚) (r : g₀ p ＝ m) (s : h₀ q ＝ n)
      → f₀ p m r ＝ f₁ q n s
   wc p q ₀ ₀ r s = ap inl (P-is-prop p (h₁ q s))
   wc p q ₀ ₁ r s = 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ w p q ∙ s))
   wc p q ₁ ₀ r s = 𝟘-elim (one-is-not-zero (r ⁻¹ ∙ w p q ∙ s))
   wc p q ₁ ₁ r s = ap inr (Q-is-prop (g₁ p r) q)

  f-is-wconstant : wconstant f
  f-is-wconstant (inl p) (inl p') = ap (λ - →  f₀ - (g₀ -) refl) (P-is-prop p p')
  f-is-wconstant (inl p) (inr q)  = wc p q (g₀ p) (h₀ q) refl refl
  f-is-wconstant (inr q) (inl p)  = (wc p q (g₀ p) (h₀ q) refl refl)⁻¹
  f-is-wconstant (inr q) (inr q') = ap (λ - →  f₁ - (h₀ -) refl) (Q-is-prop q q')

 module _ (f : P + Q → P + Q)
          (f-is-wconstant : wconstant f)
        where

  private
   ϕ : P + Q → 𝟚
   ϕ (inl p) = ₀
   ϕ (inr q) = ₁

   ϕ₀ : (z t : P + Q) → f z ＝ t → ϕ t ＝ ₁ → Q
   ϕ₀ (inl p) (inr q)  r s = q
   ϕ₀ (inr q) (inr q') r s = q'

   ϕ₁ : (z t : P + Q) → f z ＝ t → ϕ t ＝ ₀ → P
   ϕ₁ (inl p) (inl p') r s = p'
   ϕ₁ (inr q) (inl p)  r s = p

  g₀ : P → 𝟚
  g₀ p = ϕ (f (inl p))

  g₁ : (p : P) → g₀ p ＝ ₁ → Q
  g₁ p = ϕ₀ (inl p) (f (inl p)) refl

  h₀ : Q → 𝟚
  h₀ q = ϕ (f (inr q))

  h₁ : (q : Q) → h₀ q ＝ ₀ → P
  h₁ q = ϕ₁ (inr q) (f (inr q)) refl

  private
   wc :  (p : P) (q : Q) (m n : 𝟚) → g₀ p ＝ m → h₀ q ＝ n → m ＝ n
   wc p q ₀ ₀ r s = refl
   wc p q ₀ ₁ r s = r ⁻¹ ∙ ap ϕ (f-is-wconstant (inl p) (inr q)) ∙ s
   wc p q ₁ ₀ r s = r ⁻¹ ∙ ap ϕ (f-is-wconstant (inl p) (inr q)) ∙ s
   wc p q ₁ ₁ r s = refl

  w :  (p : P) (q : Q) → g₀ p ＝ h₀ q
  w p q = wc p q (g₀ p) (h₀ q) refl refl

\end{code}

Notice that the second direction doesn't use the fact that P and Q are
propositions. But notice also that g₀ and h₀ are wconstant because f
is. So maybe, using this fact, we can instead add the additional
requirement that these two functions are wconstant. Of course, if we
assume that P and Q are propositions, they are wconstant.

In any case, the above two constructions should give a type
equivalence, rather than merely a logical equivalence, when P and Q
are propositions.
