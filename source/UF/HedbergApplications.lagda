Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.HedbergApplications where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

𝟘-is-collapsible : collapsible (𝟘 {𝓤})
𝟘-is-collapsible {𝓤} = id , (λ x y → 𝟘-elim y)

pointed-types-are-collapsible : {X : 𝓤 ̇ } → X → collapsible X
pointed-types-are-collapsible x = (λ y → x) , (λ y y' → refl)

\end{code}

Under Curry-Howard, the function type X → 𝟘 is understood as the
negation of X when X is viewed as a proposition. But when X is
understood as a mathematical object, inhabiting the type X → 𝟘 amounts
to showing that X is empty. (In fact, assuming univalence, defined
below, the type X → 𝟘 is equivalent to the type X ＝ 𝟘
(written (X → 𝟘) ≃ (X ＝ 𝟘)).)

\begin{code}

empty-types-are-collapsible : {X : 𝓤 ̇ } → is-empty X → collapsible X
empty-types-are-collapsible u = (id , (λ x x' → unique-from-𝟘 (u x)))

𝟘-is-collapsible' : collapsible 𝟘
𝟘-is-collapsible' = empty-types-are-collapsible id

\end{code}

Added 30 Jul 2023.

\begin{code}

constant-maps-are-h-isolated : funext 𝓤 𝓥
                             → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y₀ : Y)
                             → is-h-isolated y₀
                             → is-h-isolated (λ (x : X) → y₀)
constant-maps-are-h-isolated fe y₀ y₀-iso {f} = II
 where
  I = ((λ x → y₀) ＝ f) ≃⟨ ≃-funext fe (λ x → y₀) f ⟩
       (λ x → y₀) ∼ f   ■

  II : is-prop ((λ x → y₀) ＝ f)
  II = equiv-to-prop I (Π-is-prop fe (λ _ → y₀-iso))

\end{code}
