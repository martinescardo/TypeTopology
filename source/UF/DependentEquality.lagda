Martin Escardo, 31st October 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.DependentEquality where

open import UF.Base
open import MLTT.Spartan

dependent-Id : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
               {x₀ x₁ : X}
             → x₀ ＝ x₁
             → Y x₀
             → Y x₁
             → 𝓥 ̇
dependent-Id Y refl y₀ y₁ = (y₀ ＝ y₁)

infix -1 dependent-Id

syntax dependent-Id Y e y₀ y₁ = y₀ ＝⟦ Y , e ⟧ y₁

dependent-Id-via-transport : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                             {x₀ x₁ : X}
                             (e : x₀ ＝ x₁)
                             {y₀ : Y x₀}
                             {y₁ : Y x₁}
                           → (y₀ ＝⟦ Y , e ⟧ y₁) ＝ (transport Y e y₀ ＝ y₁)
dependent-Id-via-transport Y refl = refl

\end{code}
