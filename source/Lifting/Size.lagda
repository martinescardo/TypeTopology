Martin Escardo 24th January 2019

Size matters.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Size (𝓣 : Universe) where

open import Lifting.IdentityViaSIP
open import Lifting.Lifting 𝓣
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Size
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

As one can see from the definition of 𝓛, we have that 𝓛 lives in a
universe strictly higher than that of X in general:

\begin{code}

private
 the-universe-of-𝓛 : (X : 𝓤 ̇ ) → 𝓣 ⁺ ⊔ 𝓤 ̇
 the-universe-of-𝓛 = 𝓛

\end{code}

However, if the argument is in 𝓣 ⁺ ⊔ 𝓤, then the size doesn't
increase:

\begin{code}

private
 𝓛-universe-preservation : (X : 𝓣 ⁺ ⊔ 𝓤 ̇ ) → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓛-universe-preservation = 𝓛

\end{code}

In particular, after the first application of 𝓛, further applications
don't increase the size:

\begin{code}

private
 the-universe-of-𝓛𝓛 : (X : 𝓤 ̇ ) → 𝓣 ⁺ ⊔ 𝓤 ̇
 the-universe-of-𝓛𝓛 X = 𝓛 (𝓛 X)

\end{code}

As a particular case of the above, if 𝓣 and 𝓤 are the same universe,
then the first application of 𝓛 has its result in the next universe 𝓣⁺.

\begin{code}

private
 the-universe-of-𝓛' : (X : 𝓣 ̇ ) → 𝓣 ⁺ ̇
 the-universe-of-𝓛' = 𝓛

\end{code}

But if 𝓤 is taken to be the successor 𝓣 ⁺ of 𝓣 then it is preserved by 𝓛:

\begin{code}

private
 the-universe-of-𝓛⁺ : (X : 𝓣 ⁺ ̇ ) → 𝓣 ⁺ ̇
 the-universe-of-𝓛⁺ = 𝓛

\end{code}

With weak propositional resizing (any proposition of any universe has
a logically equivalent copy in any universe), 𝓛 preserves all
universes except the first, i.e., all successor universes 𝓤 ⁺.

\begin{code}

𝓛-resize : is-univalent 𝓣
         → is-univalent 𝓤
         → Propositional-resizing
         → (X : 𝓤 ⁺ ̇ ) → 𝓛 X is (𝓤 ⁺) small
𝓛-resize {𝓤} ua ua' ρ X = L , e
 where
  L : 𝓤 ⁺ ̇
  L = Σ P ꞉ 𝓤 ̇ , (P → X) × is-prop P

  e : L ≃ 𝓛 X
  e = qinveq φ (γ , γφ , φγ)
   where
    φ : L → 𝓛 X
    φ (P , f , i) = resize ρ P i , f ∘ from-resize ρ P i , resize-is-prop ρ P i

    γ : 𝓛 X → L
    γ (Q , g , j) = resize ρ Q j , g ∘ from-resize ρ Q j , resize-is-prop ρ Q j

    φγ : (l : 𝓛 X) → φ (γ l) ＝ l
    φγ (Q , g , j) = ⋍-gives-＝ 𝓣 ua (a , b)
     where
      a : resize ρ (resize ρ Q j) (resize-is-prop ρ Q j) ≃ Q
      a = qinveq
           (from-resize ρ Q j ∘ from-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j))
           (to-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j) ∘ to-resize ρ Q j ,
           (λ r → resize-is-prop ρ (resize ρ Q j) (resize-is-prop ρ Q j) _ r) ,
           (λ q → j _ q))

      b : g ∘ from-resize ρ Q j ∘ from-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j) ＝ g ∘ ⌜ a ⌝
      b = ap (g ∘_) (dfunext (univalence-gives-funext ua) (λ r → j _ (⌜ a ⌝ r)))

    γφ : (m : L) → γ (φ m) ＝ m
    γφ (P , f , i) = ⋍-gives-＝ 𝓤 ua' (a , b)
     where
      a : resize ρ (resize ρ P i) (resize-is-prop ρ P i) ≃ P
      a = qinveq
           (from-resize ρ P i ∘ from-resize ρ (resize ρ P i) (resize-is-prop ρ P i))
           (to-resize ρ (resize ρ P i) (resize-is-prop ρ P i) ∘ to-resize ρ P i ,
           (λ r → resize-is-prop ρ (resize ρ P i) (resize-is-prop ρ P i) _ r) ,
           (λ q → i _ q))

      b : f ∘ from-resize ρ P i ∘ from-resize ρ (resize ρ P i) (resize-is-prop ρ P i)
        ＝ f ∘ ⌜ a ⌝
      b = ap (f ∘_) (dfunext (univalence-gives-funext ua') (λ r → i _ (⌜ a ⌝ r)))

\end{code}

TODO. The above proof can be simplified.

NB. With a more careful treatment everywhere (including the structure
identity principle), we can relax the assumption that 𝓣 and 𝓤 are
univalent to the assumption that 𝓣 satisfies propositional and
functional extensionality. But this is probably not worth the trouble,
as it would imply developing a copy of the SIP with this different
assumption.

Added 14t Feb 2022. Actually, function extensionality and
propositional extensionality together give univalence for
propositions, as proved in the module UF.Equiv-FunExt.

Added 8th Feb 2019.

\begin{code}

𝓛-resizing₀ : Ω-resizing₀ 𝓣
            → (X : 𝓣 ̇ ) → 𝓛 X is 𝓣 small
𝓛-resizing₀ (Ω₀ , e₀) X = (Σ p ꞉ Ω₀ , (up p holds → X)) , ≃-comp d e
 where
  up : Ω₀ → Ω 𝓣
  up = ⌜ e₀ ⌝

  up-is-equiv : is-equiv up
  up-is-equiv = ⌜⌝-is-equiv e₀

  d : (Σ p ꞉ Ω₀ , (up p holds → X)) ≃ (Σ p ꞉ Ω 𝓣 , (p holds → X))
  d = Σ-change-of-variable (λ p → p holds → X) up up-is-equiv

  e : (Σ p ꞉ Ω 𝓣 , (p holds → X)) ≃ 𝓛 X
  e = qinveq (λ ((P , i) , f) →  P , f ,  i)
             ((λ (P , f  , i) → (P , i) , f) ,
             (λ _ → refl) ,
             (λ _ → refl))

\end{code}

Added 15th Feb 2019. The proof is literally the same, the assumption is
more parsimonious.

\begin{code}

𝓛-resizing : Ω-resizing 𝓣
           → (X : 𝓣 ̇ ) → 𝓛 X is 𝓣 small
𝓛-resizing (O , ε) X = (Σ p ꞉ O , (up p holds → X)) , ≃-comp d e
 where
  up : O → Ω 𝓣
  up = ⌜ ε ⌝

  up-is-equiv : is-equiv up
  up-is-equiv = ⌜⌝-is-equiv ε

  d : (Σ p ꞉ O , (up p holds → X)) ≃ (Σ p ꞉ Ω 𝓣 , (p holds → X))
  d = Σ-change-of-variable (λ p → p holds → X) up up-is-equiv

  e : (Σ p ꞉ Ω 𝓣 , (p holds → X)) ≃ 𝓛 X
  e = qinveq (λ ((P , i) , f) →  P , f  , i)
             ((λ (P , f ,  i) → (P , i) , f) ,
             (λ _ → refl) ,
             (λ _ → refl))

\end{code}
