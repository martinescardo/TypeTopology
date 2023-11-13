Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.J where

open import UF.FunExt
open import Games.Monad

𝕁 : Type → Monad
𝕁 R = record {
 functor = λ X → (X → R) → X ;
 η       = λ x p → x ;
 ext     = λ f ε p → f (ε (λ x → p (f x p))) p ;
 ext-η   = λ ε → refl ;
 unit    = λ f x → refl ;
 assoc   = λ g f x → refl
 }

𝕁-transf : Fun-Ext → Monad → Type → Monad
𝕁-transf fe 𝓣 R = monad JT ηᴶᵀ extᴶᵀ extᴶᵀ-η unitᴶᵀ assocᴶᵀ
 where
 T = functor 𝓣

 JT : Type → Type
 JT X = (X → T R) → T X

 ηᴶᵀ : {X : Type} → X → JT X
 ηᴶᵀ = λ x p → η 𝓣 x

 extᴶᵀ : {X Y : Type} → (X → JT Y) → JT X → JT Y
 extᴶᵀ f ε p = ext 𝓣 (λ x → f x p) (ε (λ x → ext 𝓣 p (f x p)))

 extᴶᵀ-η : {X : Set} → extᴶᵀ (ηᴶᵀ {X}) ∼ 𝑖𝑑 (JT X)
 extᴶᵀ-η ε = dfunext fe λ p →
  ext 𝓣 (η 𝓣) (ε (λ x → ext 𝓣 p (η 𝓣 x))) ＝⟨ ext-η 𝓣 _ ⟩
  ε (λ x → ext 𝓣 p (η 𝓣 x))               ＝⟨ ap ε (dfunext fe (unit 𝓣 _)) ⟩
  ε p                                     ∎

 unitᴶᵀ : {X Y : Type} (f : X → JT Y) (x : X) → extᴶᵀ f (ηᴶᵀ x) ＝ f x
 unitᴶᵀ f x = dfunext fe (λ p → unit 𝓣 (λ x → f x p) x)

 assocᴶᵀ : {X Y Z : Type} (g : Y → JT Z) (f : X → JT Y) (ε : JT X)
        → extᴶᵀ (λ x → extᴶᵀ g (f x)) ε ＝ extᴶᵀ g (extᴶᵀ f ε)
 assocᴶᵀ g f ε = dfunext fe γ
  where
   γ : ∀ p → extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p ＝ extᴶᵀ g (extᴶᵀ f ε) p
   γ p =
    extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p                 ＝⟨ refl ⟩
    𝕖 (λ x → 𝕖 𝕘 (𝕗 x)) (ε (λ x → 𝕖 p (𝕖 𝕘 (𝕗 x)))) ＝⟨ assoc 𝓣 _ _ _ ⟩
    𝕖 𝕘 (𝕖 𝕗 (ε (λ x → 𝕖 p (𝕖 𝕘 (𝕗 x)))))           ＝⟨ again-by-assoc ⟩
    𝕖 𝕘 (𝕖 𝕗 (ε (λ x → 𝕖 (λ y → 𝕖 p (𝕘 y)) (𝕗 x)))) ＝⟨ refl ⟩
    extᴶᵀ g (extᴶᵀ f ε) p ∎
     where
      𝕖 = ext 𝓣
      𝕘 = λ y → g y p
      𝕗 = λ x → f x (λ y → 𝕖 p (𝕘 y))
      again-by-assoc = ap (λ - → 𝕖 𝕘 (𝕖 𝕗 (ε -)))
                          (dfunext fe (λ x → (assoc 𝓣 _ _ _)⁻¹))

𝕁' : Fun-Ext → Type → Monad
𝕁' fe = 𝕁-transf fe 𝕀𝕕

module J-definitions (R : Type) where

 J : Type → Type
 J = functor (𝕁 R)

 _⊗ᴶ_ : {X : Type} {Y : X → Type}
      → J X
      → ((x : X) → J (Y x))
      → J (Σ x ꞉ X , Y x)
 _⊗ᴶ_ = _⊗_ (𝕁 R)

 ⊗ᴶ-direct-definition : {X : Type} {Y : X → Type}
                        (ε : J X)
                        (δ : (x : X) → J (Y x))
                      → ε ⊗ᴶ δ ∼ (λ q → let
                                         ν  = λ x → δ x (curry q x)
                                         x₀ = ε (λ x → curry q x (ν x))
                                        in (x₀ , ν x₀))
 ⊗ᴶ-direct-definition ε δ q = refl

 ηᴶ : {X : Type} → X → J X
 ηᴶ = η (𝕁 R)

 extᴶ : {X Y : Type} → (X → J Y) → J X → J Y
 extᴶ = ext (𝕁 R)

 mapᴶ : {X Y : Type} → (X → Y) → J X → J Y
 mapᴶ = map (𝕁 R)

module JT-definitions
        (𝓣 : Monad)
        (R : Type)
        (𝓐 : Algebra 𝓣 R)
        (fe : Fun-Ext)
       where

 open import Games.K

 open T-definitions 𝓣
 open α-definitions 𝓣 R 𝓐
 open K-definitions R

 𝕁𝕋 : Monad
 𝕁𝕋 = 𝕁-transf fe 𝓣 R

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

Is -α-overlineᵀ useful?

\begin{code}

 α-overlineᵀ : {X : Type} → JT X → KT X
 α-overlineᵀ ε = λ p → α (extᵀ p (ε p))

 -α-overlineᵀ : {X : Type} → JT X → K X
 -α-overlineᵀ ε = λ p → α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

 _α-attainsᵀ_ : {X : Type} → JT X → K X → Type
 _α-attainsᵀ_ {X} ε ϕ = (p : X → T R) → α-overlineᵀ ε p ＝ ϕ (α ∘ p)

\end{code}
