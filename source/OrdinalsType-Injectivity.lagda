Martin Escardo, 2018, April 2022.

The type of ordinals is (algebraically) injective.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module OrdinalsType-Injectivity where

open import SpartanMLTT

open import UF-Base
open import UF-Equiv
open import UF-Embeddings

open import OrdinalsType
open import OrdinalsWellOrderArithmetic

module ordinals-injectivity (fe : FunExt) where

 open import InjectiveTypes fe

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


module topped-ordinals-injectivity (fe : FunExt) where

 open import InjectiveTypes fe
 open import OrdinalsToppedType fe

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
 ↗-property α = ordinals-injectivity.↗-property fe (λ i → [ α i ])

\end{code}

TODO. The type of compact∙ ordinals is injective. The type of ordinals
that have infs of complemented subsets is injective. These two results
are already proved in other modules, but these results are not
explicitly stated. We should refactor that code.

Added 11th May 2022. But we still need to clean it up.

\begin{code}

open import UF-Univalence

module ordinals-injectivity-order (ua : Univalence) where

 open import OrdinalOfOrdinals ua
 open import UF-UA-FunExt
 open import UF-Subsingletons

 fe : FunExt
 fe = Univalence-gives-FunExt ua

 open ordinals-injectivity fe

 ↗-preserves-⊴ : {I J : 𝓤  ̇ } (𝓮 : I ↪ J)
                 (α β : I → Ordinal 𝓤)
               → ((i : I) → α i ⊴ β i)
               → (j : J) → (α ↗ 𝓮) j ⊴ (β ↗ 𝓮) j
 ↗-preserves-⊴ {𝓤} {I} {J} 𝓮@(e , e-is-embedding) α β ℓ j = f , fi , fop
  where
   h : (i : I) → ⟨ α i ⟩ → ⟨ β i ⟩
   h i = pr₁ (ℓ i)

   hi : (i : I) → is-initial-segment (α i) (β i) (h i)
   hi i = pr₁ (pr₂ (ℓ i))

   hop : (i : I) → is-order-preserving (α i) (β i) (h i)
   hop i = pr₂ (pr₂ (ℓ i))

   f : ⟨ (α ↗ 𝓮) j ⟩ → ⟨ (β ↗ 𝓮) j ⟩
   f ϕ (i , refl) = h i (ϕ (i , refl))

   fi : is-initial-segment ((α ↗ 𝓮) j) ((β ↗ 𝓮) j) f
   fi ϕ γ ((i , refl) , m) = ⦅b⦆ ⦅a⦆
    where
     g⁻¹ : ⟨ α i ⟩ → ⟨ (α ↗ 𝓮) (e i) ⟩
     g⁻¹ = case (↗-property α 𝓮 i) of (λ (g , gop , geq , g⁻¹op) → inverse g geq)

     w : fiber e (e i)
     w = (i , refl)

     u : w ≡ w
     u = e-is-embedding (e i) w w

     v : u ≡ 𝓻𝓮𝒻𝓵 w
     v = props-are-sets (e-is-embedding (e i)) _ _

     ⦅a⦆ : Σ x ꞉ ⟨ α i ⟩ , (x ≺⟨ α i ⟩ ϕ (i , refl)) × (h i x ≡ γ (i , refl))
     ⦅a⦆ = hi i (ϕ (i , refl)) (γ (i , refl)) m

     ⦅b⦆ : type-of ⦅a⦆
         → Σ ϕ' ꞉ ⟨ (α ↗ 𝓮) (e i) ⟩ , (ϕ' ≺⟨ (α ↗ 𝓮) (e i) ⟩ ϕ) × (f ϕ' ≡ γ)
     ⦅b⦆ (x , n , t) = g⁻¹ x , (w , l) , dfunext (fe 𝓤 𝓤) H
      where
       p : g⁻¹ x w ≡ x
       p = g⁻¹ x w                                     ≡⟨ refl ⟩
           transport (λ - → ⟨ α (pr₁ -) ⟩) u x         ≡⟨ ⦅0⦆ ⟩
           transport (λ - → ⟨ α (pr₁ -) ⟩) (𝓻𝓮𝒻𝓵 w) x ≡⟨ refl ⟩
           x                                           ∎
        where
         ⦅0⦆ = ap (λ - → transport (λ - → ⟨ α (pr₁ -) ⟩) - x) v

       l : g⁻¹ x w ≺⟨ α i ⟩ ϕ w
       l = transport (λ - → - ≺⟨ α i ⟩ ϕ w) (p ⁻¹) n

       H : f (g⁻¹ x) ∼ γ
       H (i' , r) =
         f (g⁻¹ x) (i' , r)                              ≡⟨ ⦅1⦆ ⟩
         transport (λ - → ⟨ β (pr₁ -) ⟩) q (f (g⁻¹ x) w) ≡⟨ ⦅3⦆ ⟩
         transport (λ - → ⟨ β (pr₁ -) ⟩) q (γ w)         ≡⟨ ⦅4⦆ ⟩
         γ (i' , r)                                      ∎
         where
          q : w ≡ (i' , r)
          q = e-is-embedding (e i) w (i' , r)

          ⦅1⦆ = (apd ( f (g⁻¹ x)) q)⁻¹

          ⦅2⦆ = f (g⁻¹ x) w   ≡⟨ refl ⟩
                h i (g⁻¹ x w) ≡⟨ ap (h i) p ⟩
                h i x         ≡⟨ t ⟩
                γ w           ∎

          ⦅3⦆ = ap (transport (λ - → ⟨ β (pr₁ -) ⟩) q) ⦅2⦆

          ⦅4⦆ = apd γ q

   fop : is-order-preserving ((α ↗ 𝓮) j) ((β ↗ 𝓮) j) f
   fop ϕ γ ((i , refl) , m) = (i , refl) , hop i (ϕ (i , refl)) (γ (i , refl)) m


module topped-ordinals-injectivity-order (ua : Univalence) where

 open import UF-UA-FunExt

 fe : FunExt
 fe = Univalence-gives-FunExt ua

 open import OrdinalsToppedType fe
 open import OrdinalOfOrdinals ua
 open import UF-Subsingletons

 open topped-ordinals-injectivity fe

 ↗-preserves-⊴ : {I J : 𝓤  ̇ } (𝓮 : I ↪ J)
                 (α β : I → Ordinalᵀ 𝓤)
               → ((i : I) → [ α i ] ⊴ [ β i ])
               → (j : J) → [ (α ↗ 𝓮) j ] ⊴ [ (β ↗ 𝓮) j ]
 ↗-preserves-⊴ 𝓮 α β =
   ordinals-injectivity-order.↗-preserves-⊴ ua 𝓮 (λ i → [ α i ]) (λ i → [ β i ])

\end{code}
