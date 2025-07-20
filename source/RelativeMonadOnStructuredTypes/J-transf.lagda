Martin Escardo, Paulo Oliva, originally 2023, modified in 2024 for
relative monads on structured types.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

open import MLTT.Spartan hiding (J)

open import RelativeMonadOnStructuredTypes.OneSigmaStructure

module RelativeMonadOnStructuredTypes.J-transf
        {{ρ : 𝟙-Σ-structure}}
       where

open 𝟙-Σ-structure ρ

open import UF.FunExt
open import RelativeMonadOnStructuredTypes.Monad

private
 variable
  𝓦₀ : Universe

𝕁-transf : Fun-Ext → Relative-Monad → 𝕊 𝓦₀ → Relative-Monad
𝕁-transf {𝓦₀} fe 𝓣 𝓡 =
 record
  { ℓ = ℓᴶᵀ
  ; functor = JT
  ; η = ηᴶᵀ
  ; ext = extᴶᵀ
  ; ext-η = extᴶᵀ-η
  ; unit = unitᴶᵀ
  ; assoc = assocᴶᵀ
  }
 where
 T : {𝓤 : Universe} → 𝕊 𝓤 → ℓ 𝓣 𝓤 ̇
 T = functor 𝓣

 ℓᴶᵀ : Universe → Universe
 ℓᴶᵀ 𝓤 = ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤

 JT : {𝓤 : Universe} → 𝕊 𝓤 → ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤 ̇
 JT 𝓧 = (⟨ 𝓧 ⟩ → T 𝓡) → T 𝓧

 ηᴶᵀ : {𝓧 : 𝕊 𝓤} → ⟨ 𝓧 ⟩ → JT 𝓧
 ηᴶᵀ x p = η 𝓣 x

 extᴶᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → JT 𝓨) → JT 𝓧 → JT 𝓨
 extᴶᵀ f ε p = ext 𝓣 (λ x → f x p) (ε (λ x → ext 𝓣 p (f x p)))

 extᴶᵀ-η : {𝓧 : 𝕊 𝓤} → extᴶᵀ (ηᴶᵀ {𝓤} {𝓧}) ∼ 𝑖𝑑 (JT 𝓧)
 extᴶᵀ-η ε = dfunext fe (λ p →
  ext 𝓣 (η 𝓣) (ε (λ x → ext 𝓣 p (η 𝓣 x))) ＝⟨ ext-η 𝓣 _ ⟩
  ε (λ x → ext 𝓣 p (η 𝓣 x))                ＝⟨ ap ε (dfunext fe (unit 𝓣 _)) ⟩
  ε p                                       ∎)

 unitᴶᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} (f : ⟨ 𝓧 ⟩ → JT 𝓨) (x : ⟨ 𝓧 ⟩)
        → extᴶᵀ {𝓤} {𝓥} {𝓧} {𝓨} f (ηᴶᵀ x) ＝ f x
 unitᴶᵀ f x = dfunext fe (λ p → unit 𝓣 (λ x → f x p) x)

 assocᴶᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} {𝓩 : 𝕊 𝓦} (g : ⟨ 𝓨 ⟩
         → JT 𝓩) (f : ⟨ 𝓧 ⟩ → JT 𝓨) (t : JT 𝓧)
         → extᴶᵀ (λ x → extᴶᵀ g (f x)) t ＝ extᴶᵀ g (extᴶᵀ f t)
 assocᴶᵀ g f ε = dfunext fe γ
  where
   γ : ∀ p → extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p ＝ extᴶᵀ g (extᴶᵀ f ε) p
   γ p =
    extᴶᵀ (λ x → extᴶᵀ g (f x)) ε p                ＝⟨ refl ⟩
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

module relative-JT-definitions
        (𝓣 : Relative-Monad)
        (𝓡 : 𝕊 𝓦₀)
        (𝓐 : Relative-Algebra 𝓣 ⟨ 𝓡 ⟩)
        (fe : Fun-Ext)
       where

 open import MonadOnTypesMGU.K

 open relative-T-definitions 𝓣
 open relative-α-definitions 𝓣 𝓡 𝓐
 open K-definitions ⟨ 𝓡 ⟩

 𝕁𝕋 : Relative-Monad
 𝕁𝕋 = 𝕁-transf fe 𝓣 𝓡

 JT : 𝕊 𝓤 → (ℓ 𝓣 𝓦₀ ⊔ ℓ 𝓣 𝓤 ⊔ 𝓤) ̇
 JT = functor 𝕁𝕋

 KT : 𝕊 𝓤 → (𝓦₀ ⊔ ℓ 𝓣 𝓦₀ ⊔ 𝓤) ̇
 KT 𝓧 = (⟨ 𝓧 ⟩ → T 𝓡) → ⟨ 𝓡 ⟩

 ηᴶᵀ : {𝓧 : 𝕊 𝓤} → ⟨ 𝓧 ⟩ → JT 𝓧
 ηᴶᵀ = η 𝕁𝕋

 extᴶᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → JT 𝓨) → JT 𝓧 → JT 𝓨
 extᴶᵀ = ext 𝕁𝕋

 mapᴶᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ 𝓨 ⟩) → JT 𝓧 → JT 𝓨
 mapᴶᵀ = map 𝕁𝕋

 _⊗ᴶᵀ_ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
       → JT 𝓧
       → ((x : ⟨ 𝓧 ⟩) → JT (𝓨 x))
       → JT (Σₛ x ꞉ 𝓧 , 𝓨 x)
 _⊗ᴶᵀ_ = _⊗ᵣ_ 𝕁𝕋

 overlineᴬ : {𝓧 : 𝕊 𝓤} → JT 𝓧 → KT 𝓧
 overlineᴬ ε = λ p → α (extᵀ p (ε p))

 -overlineᴬ : {𝓧 : 𝕊 𝓤} → JT 𝓧 → K ⟨ 𝓧 ⟩
 -overlineᴬ ε = λ p → α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

 _attainsᴬ_ : {𝓧 : 𝕊 𝓤} → JT 𝓧 → K ⟨ 𝓧 ⟩ → 𝓦₀ ⊔ ℓ 𝓣 𝓦₀ ⊔ 𝓤 ̇
 _attainsᴬ_ {𝓤} {𝓧} ε ϕ = (p : ⟨ 𝓧 ⟩ → T 𝓡) → overlineᴬ ε p ＝ ϕ (α ∘ p)

\end{code}
