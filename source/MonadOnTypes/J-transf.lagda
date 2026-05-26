Martin Escardo, Paulo Oliva, 2023

A J monad transformer that given a monad T and a type R produces a new
monad JT X := (X → T R) → T X.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.J-transf where

open import UF.FunExt
open import MonadOnTypes.Definition

𝕁-transf : Fun-Ext
         → {ℓ : Universe → Universe}
         → Monad {ℓ}
         → 𝓦₀ ̇
         → Monad {λ 𝓤 → ℓ 𝓦₀ ⊔ ℓ 𝓤 ⊔ 𝓤}
𝕁-transf {𝓦₀} fe {ℓ} 𝕋 R = monad JT ηᴶᵀ extᴶᵀ extᴶᵀ-η unitᴶᵀ assocᴶᵀ
 where
  open T-definitions 𝕋

  JT : {𝓤 : Universe} → 𝓤 ̇ →  ℓ 𝓦₀ ⊔ ℓ 𝓤 ⊔ 𝓤 ̇
  JT X = (X → T R) → T X

  ηᴶᵀ : {X : 𝓤 ̇ } → X → JT X
  ηᴶᵀ x p = ηᵀ x

  extᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → JT Y) → JT X → JT Y
  extᴶᵀ f ε p = extᵀ (λ x → f x p) (ε (λ x → extᵀ p (f x p)))

  extᴶᵀ-η : {X : 𝓤 ̇ } → extᴶᵀ (ηᴶᵀ {𝓤} {X}) ∼ 𝑖𝑑 (JT X)
  extᴶᵀ-η ε = dfunext fe λ p →
   extᵀ ηᵀ (ε (λ x → extᵀ p (ηᵀ x))) ＝⟨ extᵀ-η _ ⟩
   ε (λ x → extᵀ p (ηᵀ x))           ＝⟨ ap ε (dfunext fe (unitᵀ _)) ⟩
   ε p                               ∎

  unitᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → JT Y) (x : X)
         → extᴶᵀ f (ηᴶᵀ x) ＝ f x
  unitᴶᵀ f x = dfunext fe (λ p → unitᵀ (λ x → f x p) x)

  assocᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
            (g : Y → JT Z) (f : X → JT Y)
            (ε : JT X)
          → extᴶᵀ (λ x → extᴶᵀ g (f x)) ε ＝ extᴶᵀ g (extᴶᵀ f ε)
  assocᴶᵀ g f ε = dfunext fe γ
   where
    γ : ∀ p → extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p ＝ extᴶᵀ g (extᴶᵀ f ε) p
    γ p =
     extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p                ＝⟨refl⟩
     𝕖 (λ x → 𝕖 𝕘 (𝕗 x)) (ε (λ x → 𝕖 p (𝕖 𝕘 (𝕗 x)))) ＝⟨ assocᵀ _ _ _ ⟩
     𝕖 𝕘 (𝕖 𝕗 (ε (λ x → 𝕖 p (𝕖 𝕘 (𝕗 x)))))           ＝⟨ again-by-assoc ⟩
     𝕖 𝕘 (𝕖 𝕗 (ε (λ x → 𝕖 (λ y → 𝕖 p (𝕘 y)) (𝕗 x)))) ＝⟨refl⟩
     extᴶᵀ g (extᴶᵀ f ε) p ∎
      where
       𝕖 = extᵀ
       𝕘 = λ y → g y p
       𝕗 = λ x → f x (λ y → 𝕖 p (𝕘 y))
       again-by-assoc = ap (λ - → 𝕖 𝕘 (𝕖 𝕗 (ε -)))
                           (dfunext fe (λ x → (assocᵀ _ _ _)⁻¹))

𝕁' : Fun-Ext → 𝓦 ̇ → Monad
𝕁' fe = 𝕁-transf fe 𝕀𝕕

module JT-definitions
        {ℓ : Universe → Universe}
        (𝕋 : Monad {ℓ})
        (R : 𝓦 ̇ )
        (𝓐 : Algebra 𝕋 R)
        (fe : Fun-Ext)
       where

 open import MonadOnTypes.K

 open T-definitions 𝕋
 open α-definitions 𝕋 R 𝓐
 open K-definitions {𝓦} {R}

 𝕁𝕋 : Monad
 𝕁𝕋 = 𝕁-transf fe 𝕋 R

 JT : 𝓤 ̇ → ℓ 𝓦 ⊔ ℓ 𝓤 ⊔ 𝓤 ̇
 JT = functor 𝕁𝕋

 KT : 𝓤 ̇ → 𝓦 ⊔ ℓ 𝓦 ⊔ 𝓤 ̇
 KT X = (X → T R) → R

 ηᴶᵀ : {X : 𝓤 ̇ } → X → JT X
 ηᴶᵀ = η 𝕁𝕋

 extᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → JT Y) → JT X → JT Y
 extᴶᵀ = ext 𝕁𝕋

 mapᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → JT X → JT Y
 mapᴶᵀ = map 𝕁𝕋

 _⊗ᴶᵀ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
       → JT X
       → ((x : X) → JT (Y x))
       → JT (Σ x ꞉ X , Y x)
 _⊗ᴶᵀ_ = _⊗_ 𝕁𝕋

module JT-algebra-definitions
        {ℓ : Universe → Universe}
        (𝕋 : Monad {ℓ})
        (R : 𝓦₀ ̇ )
        (𝓐 : Algebra 𝕋 R)
        (fe : Fun-Ext)
       where

 open import MonadOnTypes.K

 open T-definitions 𝕋
 open K-definitions {𝓦₀} {R}
 open JT-definitions 𝕋 R 𝓐 fe
 open α-definitions 𝕋 R 𝓐

 α-overlineᵀ : {X : 𝓤 ̇ } → JT X → KT X
 α-overlineᵀ ε = λ p → α (extᵀ p (ε p))

 _α-attainsᵀ_ : {X : 𝓤 ̇ } → JT X → K X → 𝓦₀ ⊔ ℓ 𝓦₀ ⊔ 𝓤 ̇
 _α-attainsᵀ_ {𝓤} {X} ε ϕ = (p : X → T R) → α-overlineᵀ ε p ＝ ϕ (α ∘ p)

\end{code}

Is the following variation of α-overlineᵀ useful?

\begin{code}

 -α-overlineᵀ : {X : 𝓤 ̇ } → JT X → K X
 -α-overlineᵀ ε = λ p → α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

\end{code}
