Martin Escardo, 2018, April 2022.

The type of ordinals is (algebraically) injective.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module OrdinalsType-Injectivity (fe : FunExt) where

open import SpartanMLTT

open import UF-Base
open import UF-Equiv
open import UF-Embeddings

open import OrdinalsType
open import OrdinalsWellOrderArithmetic
open import InjectiveTypes fe

module ordinals-injectivity where

 _↗_ : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
     → (I → Ordinal 𝓦)
     → (I ↪ J)
     → (J → Ordinal (𝓤 ⊔ 𝓥 ⊔ 𝓦))
 α ↗ (e , e-is-embedding) = λ j → ((a / e) j  ,
                                   Extension.order j ,
                                   Extension.well-order j (λ i → is-well-ordered (α i)))
  where
   a = λ i → ⟨ α i ⟩
   module Extension = extension fe a e e-is-embedding (λ {i} → underlying-order (α i))

 ↗-property : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
              (α : I → Ordinal 𝓤)
              (𝓮@(e , e-is-embedding) : I ↪ J)
              (i : I)
            → (α ↗ 𝓮) (e i) ≃ₒ α i
 ↗-property {𝓤} {𝓥} {I} {J} α 𝓮@(e , e-is-embedding) i = γ
  where
   ϕ : ⟨ (α ↗ 𝓮) (e i) ⟩ ≃ ⟨ α i ⟩
   ϕ = Π-extension-property (λ i → ⟨ α i ⟩) e e-is-embedding i

   g : ⟨ (α ↗ 𝓮) (e i) ⟩ → ⟨ α i ⟩
   g = ⌜ ϕ ⌝

   g-is-equiv : is-equiv g
   g-is-equiv = ⌜⌝-is-equiv ϕ

   g-is-order-preserving : is-order-preserving ((α ↗ 𝓮) (e i)) (α i) g
   g-is-order-preserving u v ((i' , p) , l) = m
    where
     q : (i' , p) ≡ (i , refl)
     q = e-is-embedding (e i) (i' , p) (i , refl)

     m : u (i , refl) ≺⟨ α i ⟩ v (i , refl)
     m = transport (λ (i' , p) → u (i' , p) ≺⟨ α i' ⟩ v (i' , p)) q l

   g⁻¹ : ⟨ α i ⟩ → ⟨ (α ↗ 𝓮) (e i) ⟩
   g⁻¹ = ⌜ ϕ ⌝⁻¹

   g⁻¹-is-order-preserving : is-order-preserving (α i) ((α ↗ 𝓮) (e i)) g⁻¹
   g⁻¹-is-order-preserving x y l = (i , refl) , r
     where
      p : g⁻¹ x (i , refl) ≡ x
      p = inverses-are-sections g g-is-equiv x

      q : g⁻¹ y (i , refl) ≡ y
      q = inverses-are-sections g g-is-equiv y

      r : g⁻¹ x (i , refl) ≺⟨ α i ⟩ g⁻¹ y (i , refl)
      r = transport₂ (λ x y → x ≺⟨ α  i ⟩ y) (p ⁻¹) (q ⁻¹) l

   γ : (α ↗ 𝓮) (e i) ≃ₒ α i
   γ = g , g-is-order-preserving , g-is-equiv , g⁻¹-is-order-preserving


module topped-ordinals-injectivity where

 open import ToppedOrdinalsType fe

 _↗_ : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
     → (I → Ordinalᵀ 𝓦)
     → (I ↪ J)
     → (J → Ordinalᵀ (𝓤 ⊔ 𝓥 ⊔ 𝓦))
 τ ↗ (e , e-is-embedding) = λ j → ((t / e) j ,
                                   Extension.order j ,
                                   Extension.well-order j (λ i → tis-well-ordered (τ i))) ,
                                   Extension.top-preservation j (λ i → topped (τ i))
  where
   t = λ x → ⟪ τ x ⟫
   module Extension = extension fe t e e-is-embedding (λ {i} → tunderlying-order (τ i))

 ↗-property : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
              (α : I → Ordinalᵀ 𝓤)
              (𝓮@(e , e-is-embedding) : I ↪ J)
              (i : I)
            → [ (α ↗ 𝓮) (e i) ] ≃ₒ [ α i ]
 ↗-property α = ordinals-injectivity.↗-property (λ i → [ α i ])

\end{code}

TODO. The type of compact∙ ordinals is injective. The type of ordinals
that have infs of complemented subsets is injective. These two results
are already proved in other modules, but these results are not
explicitly stated. We should refactor that code.
