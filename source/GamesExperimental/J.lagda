Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

open import MLTT.Spartan hiding (J)

module GamesExperimental.J where

open import UF.FunExt
open import GamesExperimental.Monad

private
 variable
  𝓦₀ : Universe

𝕁 : 𝓦₀  ̇ → Monad
𝕁 {𝓦₀} R = record {
 ℓ       = λ 𝓤 → 𝓦₀ ⊔ 𝓤 ;
 functor = λ X → (X → R) → X ;
 η       = λ x p → x ;
 ext     = λ f ε p → f (ε (λ x → p (f x p))) p ;
 ext-η   = λ ε → refl ;
 unit    = λ f x → refl ;
 assoc   = λ g f x → refl
 }

𝕁-transf : Fun-Ext → Monad → 𝓦₀  ̇ → Monad
𝕁-transf {𝓦₀} fe 𝓣 R = monad ℓᴶᵀ JT ηᴶᵀ extᴶᵀ extᴶᵀ-η unitᴶᵀ assocᴶᵀ
 where
 T = functor 𝓣

 ℓᴶᵀ : Universe → Universe
 ℓᴶᵀ 𝓤 = ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤

 JT : {𝓤 : Universe} → 𝓤  ̇ →  ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤 ̇
 JT {𝓤} X = (X → T R) → T X

 ηᴶᵀ : {X : 𝓤  ̇ } → X → JT X
 ηᴶᵀ x p = η 𝓣 x

 extᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → JT Y) → JT X → JT Y
 extᴶᵀ f ε p = ext 𝓣 (λ x → f x p) (ε (λ x → ext 𝓣 p (f x p)))

 extᴶᵀ-η : {X : 𝓤 ̇ } → extᴶᵀ (ηᴶᵀ {𝓤} {X}) ∼ 𝑖𝑑 (JT X) -- extᴶᵀ (ηᴶᵀ {?} {?}) ∼ 𝑖𝑑 (JT X)
 extᴶᵀ-η ε = dfunext fe λ p →
  ext 𝓣 (η 𝓣) (ε (λ x → ext 𝓣 p (η 𝓣 x))) ＝⟨ ext-η 𝓣 _ ⟩
  ε (λ x → ext 𝓣 p (η 𝓣 x))                ＝⟨ ap ε (dfunext fe (unit 𝓣 _)) ⟩
  ε p                                       ∎

 unitᴶᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → JT Y) (x : X) → extᴶᵀ f (ηᴶᵀ x) ＝ f x
 unitᴶᵀ f x = dfunext fe (λ p → unit 𝓣 (λ x → f x p) x)

 assocᴶᵀ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (g : Y → JT Z) (f : X → JT Y) (t : JT X) →
      extᴶᵀ (λ x → extᴶᵀ g (f x)) t ＝ extᴶᵀ g (extᴶᵀ f t)
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

𝕁' : Fun-Ext → 𝓦₀  ̇  → Monad
𝕁' fe = 𝕁-transf fe 𝕀𝕕

module J-definitions (R : 𝓦₀ ̇ ) where

 J : 𝓤 ̇  → 𝓦₀ ⊔ 𝓤  ̇
 J = functor (𝕁 R)

 _⊗ᴶ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → J X
      → ((x : X) → J (Y x))
      → J (Σ x ꞉ X , Y x)
 _⊗ᴶ_ = _⊗_ (𝕁 R)

 ⊗ᴶ-direct-definition : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                        (ε : J X)
                        (δ : (x : X) → J (Y x))
                      → ε ⊗ᴶ δ ∼ (λ q → let
                                         ν  = λ x → δ x (curry q x)
                                         x₀ = ε (λ x → curry q x (ν x))
                                        in (x₀ , ν x₀))
 ⊗ᴶ-direct-definition ε δ q = refl

 ηᴶ : {X : 𝓤 ̇ } → X → J X
 ηᴶ = η (𝕁 R)

 extᴶ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → J Y) → J X → J Y
 extᴶ = ext (𝕁 R)

 mapᴶ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → J X → J Y
 mapᴶ = map (𝕁 R)

module JT-definitions
        (𝓣 : Monad)
        (R : 𝓦₀ ̇ )
        (𝓐 : Algebra 𝓣 R)
        (fe : Fun-Ext)
       where

 open import GamesExperimental.K

 open T-definitions 𝓣
 open α-definitions 𝓣 R 𝓐
 open K-definitions R

 𝕁𝕋 : Monad
 𝕁𝕋 = 𝕁-transf fe 𝓣 R

 JT : 𝓤 ̇  → ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤  ̇
 JT = functor 𝕁𝕋

 KT : 𝓤 ̇  → 𝓦₀ ⊔ ℓ 𝓣 𝓦₀ ⊔ 𝓤  ̇
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

\end{code}

Is -α-overlineᵀ useful?

\begin{code}

 α-overlineᵀ : {X : 𝓤 ̇ } → JT X → KT X
 α-overlineᵀ ε = λ p → α (extᵀ p (ε p))

 -α-overlineᵀ : {X : 𝓤 ̇ } → JT X → K X
 -α-overlineᵀ ε = λ p → α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

 _α-attainsᵀ_ : {X : 𝓤 ̇ } → JT X → K X → 𝓦₀ ⊔ ℓ 𝓣 𝓦₀ ⊔ 𝓤  ̇
 _α-attainsᵀ_ {𝓤} {X} ε ϕ = (p : X → T R) → α-overlineᵀ ε p ＝ ϕ (α ∘ p)

\end{code}
