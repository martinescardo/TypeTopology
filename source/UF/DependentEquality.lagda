Martin Escardo, 31st October 2025.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.DependentEquality where

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

Added by Anna Williams, 17th March 2026.

Chaining of equalities.

\begin{code}

cong-e : {X : 𝓤 ̇ }
         {Y : X → 𝓥 ̇ }
         {x₀ x₁ x₂ : X}
         {e : x₀ ＝ x₁}
         {e' : x₁ ＝ x₂}
         {a : Y x₀}
         {b : Y x₁}
         {c : Y x₂}
       → a ＝⟦ Y , e ⟧ b
       → b ＝⟦ Y , e' ⟧ c
       → a ＝⟦ Y , e ∙ e' ⟧ c
cong-e {_} {_} {_} {_} {_} {_} {_} {refl} {refl} {_} E E' = E ∙ E'


_＝⟦⟧⟨_⟩_ : {X : 𝓤 ̇ }
               {Y : X → 𝓥 ̇ }
               {x₀ x₁ x₂ : X}
               {e : x₀ ＝ x₁}
               {e' : x₁ ＝ x₂}
               (a : Y x₀)
               {b : Y x₁}
               {c : Y x₂}
             → a ＝⟦ Y , e ⟧ b
             → b ＝⟦ Y , e' ⟧ c
             → a ＝⟦ Y , e ∙ e' ⟧ c
_＝⟦⟧⟨_⟩_ _ = cong-e

_⟦⟧∎ : {X : 𝓤 ̇ }
       (a : X)
     → a ＝⟦ id , refl ⟧ a
_⟦⟧∎ _ = refl

_⁻¹' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x₀ x₁ : X} {e : x₀ ＝ x₁} {a : Y x₀} {b : Y x₁}
     → a ＝⟦ Y , e ⟧ b
     → b ＝⟦ Y , e ⁻¹ ⟧ a
_⁻¹' {_} {_} {_} {_} {_} {_} {refl} refl = refl


dep-ap : {X : 𝓤' ̇ }
         {Y : X → 𝓥' ̇ }
         {Z : 𝓦' ̇ }
         {A : Z → 𝓣' ̇ }
         {x₀ x₁ : X}
         {e : x₀ ＝ x₁}
         {E : X → Z}
         {a : Y x₀}
         {b : Y x₁}
         (f : {x : X} → Y x → A (E x))
       → a ＝⟦ Y , e ⟧ b
       → f a ＝⟦ A , ap E e ⟧ f b
dep-ap {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {refl} f eq = ap f eq

to-dep-＝ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
            {x₀ x₁ : X}
            {e : x₀ ＝ x₁} {a : Y x₀}
            {b : Y x₁}
          → ((i j : transport Y e a ＝ b) → i ＝ j)
          → (p q : a ＝⟦ Y , e ⟧ b)
          → p ＝ q
to-dep-＝ {_} {_} {_} {_} {_} {_} {refl} l = l

infix  3  _⁻¹'
infix  1 _⟦⟧∎
infixr 0 _＝⟦⟧⟨_⟩_
