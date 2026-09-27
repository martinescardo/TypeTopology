Martin Escardo

Sets (0-types).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Sets where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons

\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

is-h-isolated : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-h-isolated x = ∀ {y} → is-prop (x ＝ y)

h-isolatedness-criterion : {X : 𝓤 ̇ } {x : X}
                         → is-prop (x ＝ x)
                         → is-h-isolated x
h-isolatedness-criterion {𝓤} {X} {x} i {y} = γ
 where
  γ : is-prop (x ＝ y)
  γ refl = i refl

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = {x : X} → is-h-isolated x

hSet : (𝓤 : Universe) → 𝓤 ⁺ ̇
hSet 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A

underlying-set : hSet 𝓤 → 𝓤 ̇
underlying-set = pr₁

underlying-set-is-set : (𝓐 : hSet 𝓤) → is-set (underlying-set 𝓐)
underlying-set-is-set = pr₂

𝟘-is-set : is-set (𝟘 {𝓤})
𝟘-is-set {𝓤} {x} = 𝟘-elim x

refl-is-set : (X : 𝓤 ̇ )
            → ((x : X) (p : x ＝ x) → p ＝ refl)
            → is-set X
refl-is-set X r {x} p refl = r x p

refl-is-set' : (X : 𝓤 ̇ )
             → ((x : X) (p : x ＝ x) → refl ＝ p)
             → is-set X
refl-is-set' X r {x} refl p = r x p

+-is-set : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
         → is-set X
         → is-set Y
         → is-set (X + Y)
+-is-set X Y i j {inl x} {inl x'} p q = γ
 where
  r : ap inl (inl-lc p) ＝ ap inl (inl-lc q)
  r = ap (ap inl) (i (inl-lc p) (inl-lc q))

  γ : p ＝ q
  γ = inl-lc-is-section p ∙ r ∙ (inl-lc-is-section q)⁻¹

+-is-set X Y i j {inl x} {inr y} p q = 𝟘-elim (+disjoint  p)

+-is-set X Y i j {inr y} {inl x} p q = 𝟘-elim (+disjoint' p)

+-is-set X Y i j {inr y} {inr y'} p q = γ
 where
  r : ap inr (inr-lc p) ＝ ap inr (inr-lc q)
  r = ap (ap inr) (j (inr-lc p) (inr-lc q))

  γ : p ＝ q
  γ = inr-lc-is-section p ∙ r ∙ (inr-lc-is-section q)⁻¹

×-is-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-set X → is-set Y → is-set (X × Y)
×-is-set i j {(x , y)} {(x' , y')} p q =
 p            ＝⟨ tofrom-×-＝ p ⟩
 to-×-＝ p₀ p₁ ＝⟨ ap₂ (λ -₀ -₁ → to-×-＝ -₀ -₁) (i p₀ q₀) (j p₁ q₁) ⟩
 to-×-＝ q₀ q₁ ＝⟨ (tofrom-×-＝ q)⁻¹ ⟩
 q            ∎
  where
   p₀ : x ＝ x'
   p₀ = pr₁ (from-×-＝' p)

   p₁ : y ＝ y'
   p₁ = pr₂ (from-×-＝' p)

   q₀ : x ＝ x'
   q₀ = pr₁ (from-×-＝' q)

   q₁ : y ＝ y'
   q₁ = pr₂ (from-×-＝' q)

\end{code}

Formulation of the K axiom for a universe 𝓤.

\begin{code}

K-axiom : ∀ 𝓤 → 𝓤 ⁺ ̇
K-axiom 𝓤 = (X : 𝓤 ̇ ) → is-set X

K-Axiom : 𝓤ω
K-Axiom = (𝓤 : Universe) → K-axiom 𝓤

\end{code}
