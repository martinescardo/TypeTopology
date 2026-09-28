--------------------------------------------------------------------------------
title:          SIP for frames
author:         Ayberk Tosun
date-started:   2024-04-14
date-completed: 2024-04-18
--------------------------------------------------------------------------------

Originally proved on 2020-02-03 by Ayberk Tosun (j.w.w. Thierry Coquand) in
`ayberkt/formal-topology-in-UF` which is the Agda formalization accompanying
Ayberk Tosun's MSc thesis.

Ported to TypeTopology on 2024-04-17.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.SIP.FrameSIP
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
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.SIP
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open sip hiding (⟨_⟩)

\end{code}

We work in a module parameterized by two frame structures that we call `str₁`
and `str₂`.

\begin{code}

module SIP-For-Frames {A : 𝓤 ⁺ ̇ } (str₁ str₂ : frame-structure 𝓤 𝓤 A) where

 open FrameIsomorphisms

\end{code}

We denote by `F` and `G` the frames `(A , str₁)` and `(B , str₂)`.

\begin{code}

 F : Frame (𝓤 ⁺) 𝓤 𝓤
 F = A , str₁

 G : Frame (𝓤 ⁺) 𝓤 𝓤
 G = A , str₂

\end{code}

We define a bunch of other abbreviations that we will use throughout this
module.

\begin{code}

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

\end{code}

We now prove some lemmas showing that, if the identity equivalence between frames
`F` and `G` is homomorphic, then the frame structures must be equal.

\begin{code}

 abstract
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

  homomorphic-identity-equivalence-gives-top-agreement
   : is-homomorphic F G (≃-refl A) holds
   → 𝟏[ F ] ＝ 𝟏[ G ]
  homomorphic-identity-equivalence-gives-top-agreement η = id-preserves-top
   where
    iso : Isomorphismᵣ F G
    iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , η)

    open Isomorphismᵣ iso using (𝓈; 𝓇)

    φ : F ─f·→ G
    φ = frame-homomorphism-to-frame-homomorphismᵣ F G 𝓈

    open _─f·→_ φ using () renaming (h-preserves-top to id-preserves-top)

  homomorphic-identity-equivalence-gives-meet-agreement
   : is-homomorphic F G (≃-refl A) holds
   → meet-of F ＝ meet-of G
  homomorphic-identity-equivalence-gives-meet-agreement h =
   dfunext fe λ x → dfunext fe λ y → id-preserves-meets x y
    where
     iso : Isomorphismᵣ F G
     iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , h)

     open Isomorphismᵣ iso using (𝓈; 𝓇)

     φ : F ─f·→ G
     φ = frame-homomorphism-to-frame-homomorphismᵣ F G 𝓈

     open _─f·→_ φ using () renaming (h-preserves-meets to id-preserves-meets)

  homomorphic-identity-equivalence-gives-join-agreement
   : is-homomorphic F G (≃-refl A) holds
   → join-of F ＝ join-of G
  homomorphic-identity-equivalence-gives-join-agreement h =
   dfunext fe (frame-homomorphisms-preserve-all-joins′ F G (id , s-is-homomorphism))
   where
    iso : Isomorphismᵣ F G
    iso = isomorphism₀-to-isomorphismᵣ F G (≃-refl A , h)

    open Isomorphismᵣ iso using (𝓈; 𝓇; s-is-homomorphism)

    φ : F ─f·→ G
    φ = frame-homomorphism-to-frame-homomorphismᵣ F G 𝓈

    open _─f·→_ φ using () renaming (h-preserves-joins to id-preserves-joins)

 homomorphic-identity-equivalence-gives-frame-data-agreement
  : is-homomorphic F G (≃-refl A) holds
  → frame-data-of-F ＝ frame-data-of-G
 homomorphic-identity-equivalence-gives-frame-data-agreement η =
  transport
   (λ - → _≤₁_ , 𝟏₁ , _∧₁_ , ⋁₁_ ＝ - , 𝟏₂ , _∧₂_ , ⋁₂_)
   (homomorphic-identity-equivalence-gives-order-agreement η)
   (to-Σ-＝' β)
   where
    δ : ⋁₁_ ＝ ⋁₂_
    δ = homomorphic-identity-equivalence-gives-join-agreement η

    γ : _∧₁_ , ⋁₁_ ＝ _∧₂_ , ⋁₂_
    γ = transport
         (λ - → _∧₁_ , ⋁₁_ ＝ - , ⋁₂_)
         (homomorphic-identity-equivalence-gives-meet-agreement η)
         (to-Σ-＝' δ)

    β : 𝟏₁ , _∧₁_ , ⋁₁_ ＝ 𝟏₂ , _∧₂_ , ⋁₂_
    β = transport
         (λ - → 𝟏₁ , _∧₁_ , ⋁₁_ ＝ - , _∧₂_ , ⋁₂_)
         (homomorphic-identity-equivalence-gives-top-agreement η)
         (to-Σ-＝' γ)

\end{code}

We use the lemmas that we proved above to conclude that the identity equivalence
on `A` being homomorphic gives the equality of `str₁` and `str₂`.

\begin{code}

 abstract
  homomorphic-equivalence-gives-structural-equality
   : is-homomorphic F G (≃-refl A) holds
   → str₁ ＝ str₂
  homomorphic-equivalence-gives-structural-equality =
     to-subtype-＝ satisfying-frame-laws-is-prop
   ∘ homomorphic-identity-equivalence-gives-frame-data-agreement

open FrameIsomorphisms

\end{code}

The fact that `frame-structure` is a standard notion of structure is then
an easy corollary.

\begin{code}

frame-sns-data : SNS (frame-structure 𝓤 𝓤) (𝓤 ⁺)
frame-sns-data {𝓤} = ι , ρ , θ
 where
  ι : (F′ G′ : Frame (𝓤 ⁺) 𝓤 𝓤) → sip.⟨ F′ ⟩ ≃ sip.⟨ G′ ⟩ → 𝓤 ⁺ ̇
  ι F′ G′ e = is-homomorphic F′ G′ e holds

  ρ : (L : Frame (𝓤 ⁺) 𝓤 𝓤) → ι L L (≃-refl sip.⟨ L ⟩)
  ρ L = 𝔦𝔡-is-frame-homomorphism L , 𝔦𝔡-is-frame-homomorphism L

  θ : {X : 𝓤 ⁺ ̇ } (str₁ str₂ : frame-structure 𝓤 𝓤 X)
    → is-equiv (canonical-map ι ρ str₁ str₂)
  θ {X = X} str₁ str₂ = (homomorphic-equivalence-gives-structural-equality , †)
                      , (homomorphic-equivalence-gives-structural-equality , ‡)
   where
    open SIP-For-Frames str₁ str₂

    † : (h : is-homomorphic F G (≃-refl X) holds)
      → let
         p = homomorphic-equivalence-gives-structural-equality h
        in
        canonical-map ι ρ str₁ str₂ p ＝ h
    † h = holds-is-prop
           (is-homomorphic F G (≃-refl X))
           (canonical-map
             ι
             ρ
             str₁
             str₂
             (homomorphic-equivalence-gives-structural-equality h))
           h

    ‡ : (p : str₁ ＝ str₂)
      → homomorphic-equivalence-gives-structural-equality
         (canonical-map ι ρ str₁ str₂ p)
        ＝ p
    ‡ p = frame-structure-is-set
           X
           𝓤
           𝓤
           pe
           (homomorphic-equivalence-gives-structural-equality
             (canonical-map ι ρ str₁ str₂ p))
           p

\end{code}

Finally, we get that the identity type between frames `F` and `G` is equivalent
to the type of equivalences between them.

\begin{code}

characterization-of-frame-＝ : (F G : Frame (𝓤 ⁺) 𝓤 𝓤)
                             → (F ＝ G) ≃ (F ≃[ frame-sns-data ] G)
characterization-of-frame-＝ {𝓤} F G =
 characterization-of-＝ (ua (𝓤 ⁺)) frame-sns-data F G

\end{code}

The notion of equivalence induced by `frame-sns-data` is logically equivalent
to the notion of isomorphism of frames from module
`Locales.ContinuousMap.FrameIsomorphism-Definition`.

\begin{code}

sns-equivalence-to-frame-isomorphism : (F G : Frame (𝓤 ⁺) 𝓤 𝓤)
                                     → F ≃[ frame-sns-data ] G → F ≅f≅ G
sns-equivalence-to-frame-isomorphism F G (f , e , φ) =
 isomorphism₀-to-isomorphismᵣ F G ((f , e) , φ)

isomorphism-to-sns-equivalence : (F G : Frame (𝓤 ⁺) 𝓤 𝓤)
                               → F ≅f≅ G → F ≃[ frame-sns-data ] G
isomorphism-to-sns-equivalence F G iso = ⌜ e ⌝ , ⌜⌝-is-equiv e , †
 where
  iso₀ : Isomorphism₀ F G
  iso₀ = isomorphismᵣ-to-isomorphism₀ F G iso

  e : ⟨ F ⟩ ≃ ⟨ G ⟩
  e = pr₁ iso₀

  † : homomorphic frame-sns-data F G e
  † = pr₂ iso₀

\end{code}

Combining `isomorphism-to-sns-equivalence` with `characterization-of-frame-＝`,
we get that two isomorphic frames are equal.

\begin{code}

isomorphic-frames-are-equal : (F G : Frame (𝓤 ⁺) 𝓤 𝓤) → F ≅f≅ G → F ＝ G
isomorphic-frames-are-equal {𝓤} F G iso =
 h (isomorphism-to-sns-equivalence F G iso)
  where
   e : (F ＝ G) ≃ (F ≃[ frame-sns-data ] G)
   e = characterization-of-frame-＝ F G

   h : F ≃[ frame-sns-data ] G → F ＝ G
   h = inverse ⌜ e ⌝ (⌜⌝-is-equiv e)

\end{code}
