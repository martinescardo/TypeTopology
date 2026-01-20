Martin Escardo, Paulo Oliva, 2023

A J monad transformer that give a monad T and a type R produces a new
monad JT X := (X → T R) → T X.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.J-transf where

open import UF.FunExt
open import MonadOnTypes.Construction

𝕁-transf : Fun-Ext → Monad → Type → Monad
𝕁-transf fe 𝕋 R = monad JT ηᴶᵀ extᴶᵀ extᴶᵀ-η unitᴶᵀ assocᴶᵀ
 where
  open T-definitions 𝕋

  JT : Type → Type
  JT X = (X → T R) → T X

  ηᴶᵀ : {X : Type} → X → JT X
  ηᴶᵀ = λ x p → ηᵀ x

  extᴶᵀ : {X Y : Type} → (X → JT Y) → JT X → JT Y
  extᴶᵀ f ε p = extᵀ (λ x → f x p) (ε (λ x → extᵀ p (f x p)))

  extᴶᵀ-η : {X : Type} → extᴶᵀ (ηᴶᵀ {X}) ∼ 𝑖𝑑 (JT X)
  extᴶᵀ-η ε = dfunext fe λ p →
   extᵀ ηᵀ (ε (λ x → extᵀ p (ηᵀ x))) ＝⟨ extᵀ-η _ ⟩
   ε (λ x → extᵀ p (ηᵀ x))           ＝⟨ ap ε (dfunext fe (unitᵀ _)) ⟩
   ε p                               ∎

  unitᴶᵀ : {X Y : Type} (f : X → JT Y) (x : X)
         → extᴶᵀ f (ηᴶᵀ x) ＝ f x
  unitᴶᵀ f x = dfunext fe (λ p → unitᵀ (λ x → f x p) x)

  assocᴶᵀ : {X Y Z : Type}
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

𝕁' : Fun-Ext → Type → Monad
𝕁' fe = 𝕁-transf fe 𝕀𝕕

module JT-definitions
        (𝕋 : Monad)
        (R : Type)
        (fe : Fun-Ext)
       where

 open import MonadOnTypes.K

 open T-definitions 𝕋
 open K-definitions R

 𝕁𝕋 : Monad
 𝕁𝕋 = 𝕁-transf fe 𝕋 R

 JT : Type → Type
 JT = functor 𝕁𝕋

 KT : Type → Type
 KT X = (X → T R) → R

 ηᴶᵀ : {X : Type} → X → JT X
 ηᴶᵀ = η 𝕁𝕋

 extᴶᵀ : {X Y : Type} → (X → JT Y) → JT X → JT Y
 extᴶᵀ = ext 𝕁𝕋

 mapᴶᵀ : {X Y : Type} → (X → Y) → JT X → JT Y
 mapᴶᵀ = map 𝕁𝕋

 _⊗ᴶᵀ_ : {X : Type} {Y : X → Type}
       → JT X
       → ((x : X) → JT (Y x))
       → JT (Σ x ꞉ X , Y x)
 _⊗ᴶᵀ_ = _⊗_ 𝕁𝕋

module JT-algebra-definitions
        (𝕋 : Monad)
        (R : Type)
        (𝓐 : Algebra 𝕋 R)
        (fe : Fun-Ext)
       where

 open import MonadOnTypes.K

 open T-definitions 𝕋
 open K-definitions R
 open JT-definitions 𝕋 R fe
 open α-definitions 𝕋 R 𝓐

 α-overlineᵀ : {X : Type} → JT X → KT X
 α-overlineᵀ ε = λ p → α (extᵀ p (ε p))

 _α-attainsᵀ_ : {X : Type} → JT X → K X → Type
 _α-attainsᵀ_ {X} ε ϕ = (p : X → T R) → α-overlineᵀ ε p ＝ ϕ (α ∘ p)

\end{code}

Is the following variation of α-overlineᵀ useful?

\begin{code}

 -α-overlineᵀ : {X : Type} → JT X → K X
 -α-overlineᵀ ε = λ p → α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

\end{code}
