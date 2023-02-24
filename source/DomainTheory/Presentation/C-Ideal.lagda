

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

module C-Ideal {𝓣'}
  (G : 𝓤 ̇)
  (_≲_ : G → G → 𝓣 ̇)
  (_◃_ : Cover-set G _≲_)
  (ℑ : G → Ω 𝓣')
  where

  is-C-ideal : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
  is-C-ideal = downward-closed × cover-closed
    where
      downward-closed = ∀ x y → x ≲ y
        → x ∈ ℑ → y ∈ ℑ
      cover-closed = ∀ I x (U : I → G) → (x ◃ U) holds
        → (∀ y → y ∈image U → y ∈ ℑ)
        → x ∈ ℑ

  being-C-ideal-is-prop : is-prop is-C-ideal
  being-C-ideal-is-prop = ×-is-prop
    (Π₄-is-prop fe λ _ _ _ _ → ∈-is-prop ℑ _)
    (Π₅-is-prop fe λ _ _ _ _ _ → ∈-is-prop ℑ _)

module _ {𝓣'}
  (G : 𝓤 ̇)
  (_≲_ : G → G → 𝓣 ̇)
  (_◃_ : Cover-set G _≲_) where
  open C-Ideal {𝓣' = 𝓣'} G _≲_ _◃_

  C-Idl = Σ is-C-ideal

  carrier : C-Idl → G → Ω 𝓣'
  carrier (ℑ , _) = ℑ

  C-ideality : (𝓘 : C-Idl) → is-C-ideal (carrier 𝓘)
  C-ideality (_ , i) = i

  _⊑_ : C-Idl → C-Idl → 𝓤 ⊔ 𝓣' ̇
  (ℑ , ℑ-is-ideal) ⊑ (𝔍 , 𝔍-is-ideal) = ℑ ⊆ 𝔍

\end{code}
