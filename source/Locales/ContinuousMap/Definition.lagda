--------------------------------------------------------------------------------
title:          Continuous maps of locales
author:         Ayberk Tosun
date-started:   2024-04-10
--------------------------------------------------------------------------------

Originally written as part of the `Locales.Frame` module on 2022-04-23.

Factored out from the `Locales.Frame` module into this module on 2024-04-10.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Slice.Family
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We work in a module parameterized by two locales `X` and `Y`.

\begin{code}

module ContinuousMaps (X : Locale 𝓤 𝓥 𝓦) (Y : Locale 𝓤' 𝓥' 𝓦) where

 open Locale
 open FrameHomomorphisms hiding (fun)

\end{code}

We denote the type of continuous maps by `X ─c→ Y`.

\begin{code}

 _─c→_ : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ⊔ 𝓤' ̇
 _─c→_ = 𝒪 Y ─f→ 𝒪 X

\end{code}

\begin{code}

 continuity-of : (f : _─c→_) → (S : Fam 𝓦 ⟨ 𝒪 Y ⟩)
               → f .pr₁ (⋁[ 𝒪 Y ] S) ＝ ⋁[ 𝒪 X ] ⁅ f .pr₁ V ∣ V ε S ⁆
 continuity-of f S = ⋁[ 𝒪 X ]-unique ⁅ f $ V ∣ V ε S ⁆ (f $ (⋁[ 𝒪 Y ] S)) ((pr₂ (pr₂ (pr₂ f)) S))
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    infixr 25 _$_
    _$_ = pr₁

\end{code}

\begin{code}

module ContinuousMapNotation (X : Locale 𝓤 𝓥 𝓦) (Y : Locale 𝓤' 𝓥' 𝓦) where

 infix  9 _⋆
 infixl 9 _⋆∙_

 open Locale

 open ContinuousMaps
 open FrameHomomorphisms (𝒪 Y) (𝒪 X) using (fun)
 open FrameHomomorphisms hiding (fun)

\end{code}

We denote by `f⋆` the defining frame homomorphism of a continuous map `f`.

\begin{code}

 _⋆ : (X ─c→ Y) → 𝒪 Y ─f→ 𝒪 X
 _⋆ f = f

\end{code}

\begin{code}

 _⋆∙_ : (X ─c→ Y) → ⟨ 𝒪 Y ⟩ → ⟨ 𝒪 X ⟩
 _⋆∙_ f = fun (_⋆ f)

\end{code}

\begin{code}

open ContinuousMaps using (_─c→_)
open Locale
open FrameHomomorphisms using (is-a-frame-homomorphism)

cont-comp : {𝓤'' 𝓥'' : Universe}
          → (X : Locale 𝓤   𝓥   𝓦)
          → (Y : Locale 𝓤'  𝓥'  𝓦)
          → (Z : Locale 𝓤'' 𝓥'' 𝓦)
          → (Y ─c→ Z) → (X ─c→ Y) → X ─c→ Z
cont-comp {𝓦 = 𝓦} X Y Z ℊ@(g , α₁ , α₂ , α₃) 𝒻@(f , β₁ , β₂ , β₃) = h , †
 where
  open ContinuousMapNotation X Y using () renaming (_⋆∙_ to _⋆₁∙_)
  open ContinuousMapNotation Y Z using () renaming (_⋆∙_ to _⋆₂∙_)

  h : ⟨ 𝒪 Z ⟩ → ⟨ 𝒪 X ⟩
  h W = 𝒻 ⋆₁∙ (ℊ ⋆₂∙ W)

  † : is-a-frame-homomorphism (𝒪 Z) (𝒪 X) h holds
  † = †₁ , †₂ , †₃
   where
    †₁ : 𝒻 ⋆₁∙ (ℊ ⋆₂∙ 𝟏[ 𝒪 Z ]) ＝ 𝟏[ 𝒪 X ]
    †₁ = 𝒻 ⋆₁∙ (ℊ ⋆₂∙ 𝟏[ 𝒪 Z ])     ＝⟨ Ⅰ ⟩
         𝒻 ⋆₁∙ 𝟏[ 𝒪 Y ]             ＝⟨ Ⅱ ⟩
         𝟏[ 𝒪 X ]                   ∎
          where
           Ⅰ = ap (λ - → 𝒻 ⋆₁∙ -) α₁
           Ⅱ = β₁

    †₂ : (U V : ⟨ 𝒪 Z ⟩)
       → 𝒻 ⋆₁∙ (ℊ ⋆₂∙ (U ∧[ 𝒪 Z ] V))
       ＝ (𝒻 ⋆₁∙ (ℊ ⋆₂∙ U)) ∧[ 𝒪 X ] (𝒻 ⋆₁∙ (ℊ ⋆₂∙ V))
    †₂ U V = 𝒻 ⋆₁∙ (ℊ ⋆₂∙ (U ∧[ 𝒪 Z ] V))                   ＝⟨ Ⅰ ⟩
             𝒻 ⋆₁∙ ((ℊ ⋆₂∙ U) ∧[ 𝒪 Y ] (ℊ ⋆₂∙ V))           ＝⟨ Ⅱ ⟩
             (𝒻 ⋆₁∙ (ℊ ⋆₂∙ U)) ∧[ 𝒪 X ] (𝒻 ⋆₁∙ (ℊ ⋆₂∙ V))   ∎
              where
               Ⅰ = ap (λ - → 𝒻 ⋆₁∙ -) (α₂ U V)
               Ⅱ = β₂ (ℊ ⋆₂∙ U) (ℊ ⋆₂∙ V)

    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    †₃ : (U : Fam 𝓦 ⟨ 𝒪 Z ⟩) → ((h (⋁[ 𝒪 Z ] U)) is-lub-of ⁅ h x ∣ x ε U ⁆) holds
    †₃ U = transport
            (λ - → (- is-lub-of ⁅ h x ∣ x ε U ⁆) holds)
            (†₄ ⁻¹)
            (⋁[ 𝒪 X ]-upper ⁅ h x ∣ x ε U ⁆ , ⋁[ 𝒪 X ]-least ⁅ h x ∣ x ε U ⁆)
     where
      open PosetReasoning (poset-of (𝒪 X))

      †₄ : h (⋁[ 𝒪 Z ] U) ＝ ⋁[ 𝒪 X ] ⁅ h x ∣ x ε U ⁆
      †₄ = 𝒻 ⋆₁∙ (ℊ ⋆₂∙ (⋁[ 𝒪 Z ] U))              ＝⟨ I  ⟩
           𝒻 ⋆₁∙ (⋁[ 𝒪 Y ] ⁅ ℊ ⋆₂∙ x ∣ x ε U ⁆)    ＝⟨ II ⟩
           ⋁[ 𝒪 X ] ⁅ h x ∣ x ε U ⁆                ∎
            where
             I  = ap (λ - → 𝒻 ⋆₁∙ -) (⋁[ 𝒪 Y ]-unique ⁅ ℊ ⋆₂∙ x ∣ x ε U ⁆ _ (α₃ _))
             II = ⋁[ 𝒪 X ]-unique ⁅ h x ∣ x ε U ⁆ _ (β₃ _)

\end{code}
