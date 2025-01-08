Martin Escardo, Paulo Oliva, December 2024, modified from a 2023 file.

A variation of the J monad transformer. Starting with a monad T and an
algebra α : T R → R, we define a new monad JT X := (X → R) → T X.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.J-transf-variation where

open import UF.FunExt
open import Games.Monad

𝕁-transf : Fun-Ext
         → (𝓣 : Monad)
           (R : Type)
           (𝓐 : Algebra 𝓣 R)
         → Monad
𝕁-transf fe 𝓣 R 𝓐 = monad JT ηᴶᵀ extᴶᵀ extᴶᵀ-η unitᴶᵀ assocᴶᵀ
 where
  open α-definitions 𝓣 R 𝓐
  open T-definitions 𝓣

  JT : Type → Type
  JT X = (X → R) → T X

  ηᴶᵀ : {X : Type} → X → JT X
  ηᴶᵀ = λ x p → ηᵀ x

  extᴶᵀ : {X Y : Type} → (X → JT Y) → JT X → JT Y
  extᴶᵀ f ε p = extᵀ (λ x → f x p) (ε (λ x → α-extᵀ p (f x p)))

  extᴶᵀ-η : {X : Type} → extᴶᵀ (ηᴶᵀ {X}) ∼ 𝑖𝑑 (JT X)
  extᴶᵀ-η ε = dfunext fe (λ p →
   extᵀ ηᵀ (ε (λ x → α-extᵀ p (ηᵀ x))) ＝⟨ extᵀ-η _ ⟩
   ε (λ x → α-extᵀ p (ηᵀ x))           ＝⟨ ap ε (dfunext fe (α-extᵀ-unit p)) ⟩
   ε p                                 ∎)

  unitᴶᵀ : {X Y : Type} (f : X → JT Y) (x : X) → extᴶᵀ f (ηᴶᵀ x) ＝ f x
  unitᴶᵀ f x = dfunext fe (λ p → unit 𝓣 (λ x → f x p) x)

  assocᴶᵀ : {X Y Z : Type} (g : Y → JT Z) (f : X → JT Y) (ε : JT X)
          → extᴶᵀ (extᴶᵀ g ∘ f) ε ＝ extᴶᵀ g (extᴶᵀ f ε)
  assocᴶᵀ {X} {Y} {Z} g f ε = dfunext fe γ
   where
    γ : extᴶᵀ (extᴶᵀ g ∘ f) ε ∼ extᴶᵀ g (extᴶᵀ f ε)
    γ p =
     extᴶᵀ (extᴶᵀ g ∘ f) ε p                         ＝⟨ refl ⟩
     extᵀ (extᵀ 𝕘 ∘ 𝕗) (ε (α-extᵀ p ∘ extᵀ 𝕘 ∘ 𝕗))   ＝⟨ assoc 𝓣 _ _ _ ⟩
     extᵀ 𝕘 (extᵀ 𝕗 (ε (α-extᵀ p ∘ extᵀ 𝕘 ∘ 𝕗)))     ＝⟨ by-α-extᵀ-assoc ⁻¹ ⟩
     extᵀ 𝕘 (extᵀ 𝕗 (ε (α-extᵀ (α-extᵀ p ∘ 𝕘) ∘ 𝕗))) ＝⟨ refl ⟩
     extᴶᵀ g (extᴶᵀ f ε) p                           ∎
      where
       𝕘 : Y → T Z
       𝕘 = λ y → g y p
       𝕗 : X → T Y
       𝕗 = λ x → f x (α-extᵀ p ∘ 𝕘)
       by-α-extᵀ-assoc = ap (λ - → extᵀ 𝕘 (extᵀ 𝕗 (ε (- ∘ 𝕗))))
                            (dfunext fe (α-extᵀ-assoc fe p 𝕘))

𝕁' : Fun-Ext → Type → Monad
𝕁' fe R = 𝕁-transf fe 𝕀𝕕 R 𝓘
 where
  𝓘 = record {
       structure-map = id ;
       aunit         = λ r → refl ;
       aassoc        = λ r → refl }

module JT-definitions
        (𝓣 : Monad)
        (R : Type)
        (𝓐 : Algebra 𝓣 R)
        (fe : Fun-Ext)
       where

 open import Games.K

 open T-definitions 𝓣
 open K-definitions R

 𝕁𝕋 : Monad
 𝕁𝕋 = 𝕁-transf fe 𝓣 R 𝓐

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

\end{code}
