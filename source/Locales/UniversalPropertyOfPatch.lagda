Ayberk Tosun, started 7th December 2022

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size
open import UF.Equiv
open import UF.Retracts
open import UF.Embeddings
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.UniversalPropertyOfPatch
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import UF.Subsingletons-FunExt

open AllCombinators pt fe
open import UF.ImageAndSurjection
open ImageAndSurjection pt

open import Locales.Frame pt fe
open import Locales.CompactRegular pt fe
open import Locales.BooleanAlgebra pt fe
open import Locales.PatchLocale pt fe
open import Locales.PatchProperties pt fe

open PropositionalTruncation pt

\end{code}

\begin{code}

open Locale

module UniversalProperty (A : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral (𝒪 A) holds) where

 open PatchConstruction A σ renaming (Patch to Patch-A)
 open ClosedNucleus A σ

 ump-of-patch : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
              → is-stone (𝒪 X) holds
              → (𝒻 : X ─c→ A)
              → is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds
              → is-contr (Σ 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’))
 ump-of-patch X 𝕤 𝒻 μ = ∥∥-rec (being-singleton-is-prop fe) γ σ
  where
   γ : spectralᴰ (𝒪 A)
     → is-contr (Σ 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’))
   γ σᴰ = ∥∥-rec {!!} {!!} {!!}
    where
     open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)
     open BasisOfPatch A σᴰ


     clopens-are-basic : (𝒿 : ⟨ 𝒪 Patch-A ⟩)
                       → is-clopen (𝒪 Patch-A) 𝒿 holds
                       → ∃ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ]
     clopens-are-basic 𝒿 ϟ = {!∥∥-rec ? ? ? !}
      where
       ϡ : {!!}
       ϡ = compacts-are-basic-in-spectralᴰ-frames (𝒪 Patch-A) {!!} 𝒿 {!!}

     𝒞𝓁ℴ𝓅 : 𝓤 ⁺  ̇
     𝒞𝓁ℴ𝓅 = Σ 𝒿 ꞉ ⟨ 𝒪 Patchₛ-A ⟩ , is-clopen (𝒪 Patchₛ-A) 𝒿 holds

     _≼ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → Ω 𝓤
     (𝒿 , _) ≼ₓ (𝓀 , _) = 𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] 𝓀

     ℬ𝒶𝓈𝒾𝒸 : 𝓤 ⁺  ̇
     ℬ𝒶𝓈𝒾𝒸 = Σ 𝒿 ꞉ ⟨ 𝒪 Patchₛ-A ⟩ , ∃ i ꞉ index ℬ-patch-↑ , ℬ-patch-↑ [ i ] ＝ 𝒿

     B = index ℬ-patch-↑

     β : B → ⟨ 𝒪 Patchₛ-A ⟩
     β i = ℬ-patch-↑ [ i ]

     resize-basic : ℬ𝒶𝓈𝒾𝒸 is 𝓤 small
     resize-basic = sr β (B , ≃-refl B) † carrier-of-[ poset-of (𝒪 Patchₛ-A) ]-is-set
      where
       † : ⟨ 𝒪 Patchₛ-A ⟩ is-locally 𝓤 small
       † 𝒿 𝓀 = (𝒿 ＝ᵏ 𝓀) holds , logically-equivalent-props-are-equivalent ♥ ♠ to from
        where
         ♥ : is-prop ((𝒿 ＝ᵏ 𝓀) holds)
         ♥ = holds-is-prop (𝒿 ＝ᵏ 𝓀)

         ♠ : is-prop (𝒿 ＝ 𝓀)
         ♠ = carrier-of-[ poset-of (𝒪 Patchₛ-A) ]-is-set

         to : (𝒿 ＝ᵏ 𝓀) holds → 𝒿 ＝ 𝓀
         to (p , q) = ≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A)) p q

         from : 𝒿 ＝ 𝓀 → (𝒿 ＝ᵏ 𝓀) holds
         from p = γ₁ , γ₂
          where
           ζ : (i : index ℬ) → ((𝒿 $ (ℬ [ i ])) ≤[ poset-of (𝒪 A) ] (𝒿 $ (ℬ [ i ]))) holds
           ζ i = ≤-is-reflexive (poset-of (𝒪 A)) (𝒿 $ (ℬ [ i ]))

           γ₁ : (𝒿 ≼ᵏ 𝓀) holds
           γ₁ = transport (λ - → (𝒿 ≼ᵏ -) holds) p ζ

           γ₂ : (𝓀 ≼ᵏ 𝒿) holds
           γ₂ = transport (λ - → (- ≼ᵏ 𝒿) holds) p ζ

     open PatchStoneᴰ A σᴰ

     iso : ℬ𝒶𝓈𝒾𝒸 ≃ 𝒞𝓁ℴ𝓅
     iso = to , (section-retraction-equiv to (from , r) {!!})
      where
       to : ℬ𝒶𝓈𝒾𝒸 → 𝒞𝓁ℴ𝓅
       to (𝒿 , p) = 𝒿 , ∥∥-rec ((holds-is-prop (is-clopen (𝒪 Patchₛ-A) 𝒿))) † p
        where
         † : (Σ i ꞉ index ℬ-patch-↑ , ℬ-patch-↑ [ i ] ＝ 𝒿)
           → is-clopen (𝒪 Patchₛ-A) 𝒿 holds
         † (k , eq) = ∥∥-rec
                       (holds-is-prop (is-clopen (𝒪 Patchₛ-A) 𝒿))
                       ‡
                       patch-zero-dimensional
          where
           ‡ : _ → is-clopen (𝒪 Patchₛ-A) 𝒿 holds
           ‡ zᴰ = transport
                   (λ - → is-clopen (𝒪 Patchₛ-A) - holds)
                   eq (ℬ-patch-↑-consists-of-clopens k)

         -- † = ∥∥-rec
         --      (holds-is-prop (is-clopen (𝒪 Patchₛ-A) 𝒿))
         --      ‡
         --      patch-zero-dimensional

       from : 𝒞𝓁ℴ𝓅 → ℬ𝒶𝓈𝒾𝒸
       from (𝒿 , p) = {!clopens-are-basic!}

       r : (to ∘ from) ∼ id
       r = {!!}

     -- 𝒻⁻ : X ─c→ Patchₛ-A
     -- 𝒻⁻ = {!!}

     ℂ : BooleanAlgebra (𝓤 ⁺) 𝓤
     ℂ = 𝒞𝓁ℴ𝓅 , (_≼ₓ_ , 𝟏ₓ , _⋏ₓ_ , 𝟎ₓ , _⋎ₓ_ , ¡_) , {!!} , φ₁ , φ₂ , φ₃ , φ₄ , φ₅ , φ₆
      where
       𝟏ₓ : 𝒞𝓁ℴ𝓅
       𝟏ₓ = 𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A)

       _⋏ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
       (𝒿 , 𝒿′ , p) ⋏ₓ (𝓀 , 𝓀′ , q) =
        (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀) , (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′) , ※
         where
          ※ : is-boolean-complement-of (𝒪 Patchₛ-A) (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′) (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀) holds
          ※ = ∧-complement (𝒪 Patchₛ-A) † ‡
           where
            † : is-boolean-complement-of (𝒪 Patchₛ-A) 𝒿 𝒿′ holds
            † = (complementation-is-symmetric (𝒪 Patchₛ-A) 𝒿′ 𝒿 p)

            ‡ : is-boolean-complement-of (𝒪 Patchₛ-A) 𝓀 𝓀′ holds
            ‡ = complementation-is-symmetric (𝒪 Patchₛ-A) 𝓀′ 𝓀 q

       𝟎ₓ : 𝒞𝓁ℴ𝓅
       𝟎ₓ = 𝟎[ 𝒪 Patchₛ-A ] , 𝟎-is-clopen (𝒪 Patchₛ-A)

       _⋎ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
       (𝒿 , 𝒿′ , p) ⋎ₓ (𝓀 , 𝓀′ , q) =
        (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀) , (𝒿′ ∧[ 𝒪 Patchₛ-A ] 𝓀′) , ※
         where
          ※ : is-boolean-complement-of (𝒪 Patchₛ-A) (𝒿′ ∧[ 𝒪 Patchₛ-A ] 𝓀′) (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀) holds
          ※ = complementation-is-symmetric (𝒪 Patchₛ-A) (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀) (𝒿′ ∧[ 𝒪 Patchₛ-A ] 𝓀′) (∧-complement (𝒪 Patchₛ-A) p q)

       ¡_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
       ¡ (𝒿 , 𝒿′ , p) = 𝒿′ , 𝒿 , complementation-is-symmetric (𝒪 Patchₛ-A) 𝒿′ 𝒿 p

       open Meets (λ x y → x ≼ₓ y)

       φ₁ : (𝒿 𝓀 : 𝒞𝓁ℴ𝓅) → ((𝒿 ⋏ₓ 𝓀) is-glb-of (𝒿 , 𝓀)) holds
       φ₁ (𝒿 , _) (𝓀 , _) =
         (∧[ 𝒪 Patchₛ-A ]-lower₁ 𝒿 𝓀 , ∧[ 𝒪 Patchₛ-A ]-lower₂ 𝒿 𝓀)
        , λ { ((u , _) , p , q) → ∧[ 𝒪 Patchₛ-A ]-greatest 𝒿 𝓀 u p q }

       φ₂ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝒿 ≼ₓ 𝟏ₓ) holds
       φ₂ (𝒿 , _) = 𝟏-is-top (𝒪 Patchₛ-A) 𝒿

       open Joins (λ x y → x ≼ₓ y)

       φ₃ : (𝒿 𝓀 : 𝒞𝓁ℴ𝓅) → ((𝒿 ⋎ₓ 𝓀) is-lub-of₂ (𝒿 , 𝓀)) holds
       φ₃ (𝒿 , _) (𝓀 , _) = (∨[ 𝒪 Patchₛ-A ]-upper₁ 𝒿 𝓀 , ∨[ 𝒪 Patchₛ-A ]-upper₂ 𝒿 𝓀)
                          , λ { ((u , _) , p , q) → ∨[_]-least (𝒪 Patchₛ-A) {z = u}  p q }

       φ₄ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝟎ₓ ≼ₓ 𝒿) holds
       φ₄ (𝒿 , _) = 𝟎-is-bottom (𝒪 Patchₛ-A) 𝒿

       φ₅ : (𝒿 𝓀 : 𝒞𝓁ℴ𝓅) → {!!}
       φ₅ = {!!}

       φ₆ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝒿 ⋏ₓ (¡ 𝒿) ＝ 𝟎ₓ) × (𝒿 ⋎ₓ (¡ 𝒿) ＝ 𝟏ₓ)
       φ₆ (𝒿 , p) = {!!} , {!!}

       ext : {!!}
       ext = {!extension-lemma ℂ ?!}

\end{code}
