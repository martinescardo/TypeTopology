--------------------------------------------------------------------------------
title:          SIP for frames
author:         Ayberk Tosun
date-started:   2024-04-14
--------------------------------------------------------------------------------

Originally proved in `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.SIP.Frame
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale
open import Slice.Family
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Retracts
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open sip hiding (⟨_⟩)

\end{code}

\begin{code}

module SIP-For-Frames {A : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 A) where

\end{code}

\begin{code}

 open FrameIsomorphisms

 F : Frame (𝓤 ⁺) 𝓤 𝓤
 F = A , str₁

 G : Frame (𝓤 ⁺) 𝓤 𝓤
 G = A , str₂

 frame-data-of-F : frame-data 𝓤 𝓤 A
 frame-data-of-F = pr₁ str₁

 frame-data-of-G : frame-data 𝓤 𝓤 A
 frame-data-of-G = pr₁ str₂

 _≤₁_ : ⟨ F ⟩ → ⟨ F ⟩ → Ω 𝓤
 _≤₁_ = λ x y → x ≤[ poset-of F ] y

 _≤₂_ : ⟨ G ⟩ → ⟨ G ⟩ → Ω 𝓤
 _≤₂_ = λ x y → x ≤[ poset-of G ] y

 𝟏₁ : ⟨ F ⟩
 𝟏₁ = 𝟏[ F ]

 𝟏₂ : ⟨ G ⟩
 𝟏₂ = 𝟏[ G ]

 _∧₁_ : ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
 _∧₁_ = λ x y → x ∧[ F ] y

 _∧₂_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
 _∧₂_ = λ x y → x ∧[ G ] y

 ⋁₁_ : Fam 𝓤 ⟨ F ⟩ → ⟨ F ⟩
 ⋁₁_ = join-of F

 ⋁₂_ : Fam 𝓤 ⟨ G ⟩ → ⟨ G ⟩
 ⋁₂_ = join-of G

 homomorphic-identity-equivalence-gives-order-agreement
  : is-homomorphic F G (≃-refl A) holds
  → _≤₁_ ＝ _≤₂_
 homomorphic-identity-equivalence-gives-order-agreement h =
  dfunext fe λ x → dfunext fe λ y → † x y
   where
    iso : Isomorphismᵣ F G
    iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , h)

    open Isomorphismᵣ iso

    † : (x y : A) → x ≤₁ y ＝ x ≤₂ y
    † x y = ⇔-gives-＝ pe (x ≤₁ y) (x ≤₂ y) ‡
     where
      ‡ : (x ≤₁ y) ⇔ (x ≤₂ y) ＝ ⊤
      ‡ = holds-gives-equal-⊤ pe fe (x ≤₁ y ⇔ x ≤₂ y) (β , γ)
       where
        β : (x ≤₁ y ⇒ x ≤₂ y) holds
        β = frame-morphisms-are-monotonic F G id s-is-homomorphism (x , y)

        γ : (x ≤₂ y ⇒ x ≤₁ y) holds
        γ = frame-morphisms-are-monotonic G F id r-is-homomorphism (x , y)

 structural-equality-top-lemma : is-homomorphic F G (≃-refl A) holds
                               → 𝟏[ F ] ＝ 𝟏[ G ]
 structural-equality-top-lemma η = id-preserves-top
  where
   iso : Isomorphismᵣ F G
   iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , η)

   open Isomorphismᵣ iso using (forward; backward)

   φ : F ─f·→ G
   φ = frame-homomorphism-to-frame-homomorphismᵣ F G forward

   open _─f·→_ φ using () renaming (h-preserves-top to id-preserves-top)

 homomorphic-identity-equivalence-gives-meet-agreement
  : is-homomorphic F G (≃-refl A) holds
  → meet-of F ＝ meet-of G
 homomorphic-identity-equivalence-gives-meet-agreement h =
  dfunext fe λ x → dfunext fe λ y → id-preserves-meets x y
   where
    iso : Isomorphismᵣ F G
    iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , h)

    open Isomorphismᵣ iso using (forward; backward)

    φ : F ─f·→ G
    φ = frame-homomorphism-to-frame-homomorphismᵣ F G forward

    open _─f·→_ φ using () renaming (h-preserves-meets to id-preserves-meets)

 homomorphic-identity-equivalence-gives-join-agreement
  : is-homomorphic F G (≃-refl A) holds
  → join-of F ＝ join-of G
 homomorphic-identity-equivalence-gives-join-agreement h =
  dfunext fe λ S → frame-homomorphisms-preserve-all-joins′ F G (id , {!!}) S
  where
   iso : Isomorphismᵣ F G
   iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , h)

   open Isomorphismᵣ iso using (forward; backward)

   φ : F ─f·→ G
   φ = frame-homomorphism-to-frame-homomorphismᵣ F G forward

   open _─f·→_ φ using () renaming (h-preserves-joins to id-preserves-joins)

 frame-data-agreement : is-homomorphic F G (≃-refl A) holds → frame-data-of-F ＝ frame-data-of-G
 frame-data-agreement η =
  transport
   (λ - → _≤₁_ , 𝟏₁ , _∧₁_ , ⋁₁_ ＝ - , 𝟏₂ , _∧₂_ , ⋁₂_)
   (homomorphic-identity-equivalence-gives-order-agreement η)
   (to-Σ-＝' β)
   where
    δ : ⋁₁_ ＝ ⋁₂_
    δ = {!!}

    γ : _∧₁_ , ⋁₁_ ＝ _∧₂_ , ⋁₂_
    γ = transport
         (λ - → _∧₁_ , ⋁₁_ ＝ - , ⋁₂_)
         (homomorphic-identity-equivalence-gives-meet-agreement η)
         (to-Σ-＝' δ)

    β : 𝟏₁ , _∧₁_ , ⋁₁_ ＝ 𝟏₂ , _∧₂_ , ⋁₂_
    β = transport
         (λ - → 𝟏₁ , _∧₁_ , ⋁₁_ ＝ - , _∧₂_ , ⋁₂_)
         (structural-equality-top-lemma η)
         (to-Σ-＝' γ)


 structural-equality-lemma : is-homomorphic F G (≃-refl A) holds → str₁ ＝ str₂
 structural-equality-lemma =
  to-subtype-＝ satisfying-frame-laws-is-prop ∘ frame-data-agreement

 -- frame-sns-data : SNS (frame-structure 𝓤 𝓤) (𝓤 ⁺)
 -- frame-sns-data = ι , ρ , θ
 --  where
 --   ι : (F′ G′ : Frame (𝓤 ⁺) 𝓤 𝓤) → sip.⟨ F′ ⟩ ≃ sip.⟨ G′ ⟩ → 𝓤 ⁺  ̇
 --   ι F′ G′ e = is-homomorphic F′ G′ e holds

 --   ρ : (L : Frame (𝓤 ⁺) 𝓤 𝓤) → ι L L (≃-refl sip.⟨ L ⟩)
 --   ρ L = 𝔦𝔡-is-frame-homomorphism L , 𝔦𝔡-is-frame-homomorphism L

 --   β : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --     → is-homomorphic (X , str₁) (X , str₂) (≃-refl X) holds
 --     → (λ x y → x ≤[ poset-of (X , str₁) ] y) ＝ (λ x y → x ≤[ poset-of (X , str₂) ] y)
 --   β {X = X} str₁ str₂ p = dfunext fe λ x → dfunext fe λ y → † x y
 --    where
 --     _≤₁_ : X → X → Ω 𝓤
 --     _≤₁_ = λ x y → x ≤[ poset-of (X , str₁) ] y

 --     _≤₂_ : X → X → Ω 𝓤
 --     _≤₂_ = λ x y → x ≤[ poset-of (X , str₂) ] y

 --     iso : Isomorphismᵣ (X , str₁) (X , str₂)
 --     iso = isomorphism₀-to-isomorphismᵣ (X , str₁) (X , str₂) (≃-refl X , p)

 --     open Isomorphismᵣ

 --     † : (x y : X) → x ≤₁ y ＝ x ≤₂ y
 --     † x y = ⇔-gives-＝
 --              pe
 --              (x ≤₁ y)
 --              (x ≤₂ y)
 --              (holds-gives-equal-⊤ pe fe ((x ≤₁ y) ⇔ (x ≤₂ y)) (♣ , ♠))
 --      where
 --       ♣ : (x ≤₁ y ⇒ x ≤₂ y) holds
 --       ♣ = frame-morphisms-are-monotonic
 --            (X , str₁)
 --            (X , str₂)
 --            id
 --            (s-is-homomorphism iso)
 --            (x , y)

 --       ♠ : (x ≤₂ y ⇒ x ≤₁ y) holds
 --       ♠ = frame-morphisms-are-monotonic
 --            (X , str₂)
 --            (X , str₁)
 --            id
 --            (r-is-homomorphism iso)
 --            (x , y)

 --   γ : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --     → ι (X , str₁) (X , str₂) (≃-refl X) → 𝟏[ (X , str₁) ] ＝ 𝟏[ (X , str₂) ]
 --   γ {X} str₁ str₂ p = id-preserves-top
 --    where
 --     iso : Isomorphismᵣ (X , str₁) (X , str₂)
 --     iso = isomorphism₀-to-isomorphismᵣ (X , str₁) (X , str₂) (≃-refl X , p)

 --     open Isomorphismᵣ iso using (forward; backward)

 --     φ : (X , str₁) ─f·→ (X , str₂)
 --     φ = frame-homomorphism-to-frame-homomorphismᵣ (X , str₁) (X , str₂) forward

 --     open _─f·→_ φ using () renaming (h-preserves-top to id-preserves-top)

 --   δ : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --     → ι (X , str₁) (X , str₂) (≃-refl X)
 --     → meet-of (X , str₁) ＝ meet-of (X , str₂)
 --   δ = {!!}

 --   ε : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --     → ι (X , str₁) (X , str₂) (≃-refl X)
 --     → join-of (X , str₁) ＝ join-of (X , str₂)
 --   ε = {!!}

 --   foo : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --       → ι (X , str₁) (X , str₂) (≃-refl X)
 --       → str₁ ＝ str₂
 --   foo str₁@((a₁ , b₁ , c₁ , d₁) , laws₁) str₂@((a₂ , b₂ , c₂ , d₂) , laws₂) p =
 --    to-subtype-＝
 --     satisfying-frame-laws-is-prop
 --     (transport
 --       (λ - → - , b₁ , c₁ , d₁ ＝ a₂ , b₂ , c₂ , d₂)
 --       (q ⁻¹)
 --       (to-Σ-＝'
 --         (transport
 --           (λ - → - , c₁ , d₁ ＝ b₂ , c₂ , d₂)
 --           (r ⁻¹)
 --           (to-Σ-＝' (transport (λ - → - , d₁ ＝ c₂ , d₂) (s ⁻¹) (to-Σ-＝' t))))))
 --     where
 --      q : a₁ ＝ a₂
 --      q = β str₁ str₂ p

 --      r : b₁ ＝ b₂
 --      r = γ str₁ str₂ p

 --      s : c₁ ＝ c₂
 --      s = δ str₁ str₂ p

 --      t : d₁ ＝ d₂
 --      t = ε str₁ str₂ p

 --   θ : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
 --     → is-equiv (canonical-map ι ρ str₁ str₂)
 --   θ {X} str₁ str₂ = (foo str₁ str₂  , {!refl!}) , {!!} , {!!}

\end{code}
