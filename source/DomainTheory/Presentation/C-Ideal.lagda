

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module DomainTheory.Presentation.C-Ideal
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        {𝓤 𝓥 𝓦 : Universe}
       where

open import UF.Powerset
open import UF.ImageAndSurjection pt
open import Posets.Poset fe
open PosetAxioms

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Presentation.Presentation pt fe {𝓤} {𝓥} {𝓦}

module C-Ideal
  (G : 𝓤 ̇)
  (_≲_ : G → G → 𝓣 ̇)
  (_◃_ : Cover-set G _≲_)
  (ℑ : G → Ω 𝓣')
  where

  is-C-ideal : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
  is-C-ideal = downward-closed × cover-closed
    where
      downward-closed = ∀ x y → x ≲ y
        → ℑ x holds → ℑ y holds
      cover-closed = ∀ I x (U : I → G) → (x ◃ U) holds
        → (∀ y → y ∈image U → ℑ y holds)
        → ℑ x holds

  being-C-ideal-is-prop : is-prop is-C-ideal
  being-C-ideal-is-prop = ×-is-prop
    (Π₄-is-prop fe λ _ _ _ _ → holds-is-prop (ℑ _))
    (Π₅-is-prop fe λ _ _ _ _ _ → holds-is-prop (ℑ _))

\end{code}
