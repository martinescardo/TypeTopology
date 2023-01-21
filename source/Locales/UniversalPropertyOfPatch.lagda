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
open import UF.Logic
open import UF.Subsingletons-FunExt

open AllCombinators pt fe
open import UF.ImageAndSurjection
open UF.ImageAndSurjection pt

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
              → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
 ump-of-patch X 𝕤 𝒻 μ = ∥∥-rec (being-singleton-is-prop fe) γ σ
  where
   γ : spectralᴰ (𝒪 A)
     → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
   γ σᴰ = ∥∥-rec (∃!-is-prop fe) {!!} {!!}
    where
     open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)
     open BasisOfPatch A σᴰ

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
     open PatchStone  A ∣ σᴰ ∣

     þ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → is-prop (is-clopen (𝒪 Patchₛ-A) 𝒿 holds)
     þ = holds-is-prop ∘ is-clopen (𝒪 Patchₛ-A)

     iso : ℬ𝒶𝓈𝒾𝒸 ≃ 𝒞𝓁ℴ𝓅
     iso = to , (section-retraction-equiv to (from , r) s)
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

       from : 𝒞𝓁ℴ𝓅 → ℬ𝒶𝓈𝒾𝒸
       from (𝒿 , p) = 𝒿 , ∥∥-rec ∃-is-prop † υ
        where
         † : Σ i ꞉ index ℬ-patch-↑ , (𝒿 ＝ ℬ-patch-↑ [ i ])
           → ∃ i ꞉ index ℬ-patch-↑ , ℬ-patch-↑ [ i ] ＝ 𝒿
         † (i , p) = ∣ i , (p ⁻¹) ∣

         υ : ∥ Σ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ] ∥
         υ = clopens-are-basic-in-stone-locales
              (𝒪 Patchₛ-A)
              patchₛ-is-stone
              ℬ-patch-↑
              ℬ-patch-↑-is-directed-basisₛ 𝒿 p

       r : (to ∘ from) ∼ id
       r (𝒿 , p) = to-subtype-＝ þ refl

       ρ : (from ∘ to) ∼ id
       ρ (𝒿 , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

       s : is-section to
       s = from , ρ

     -- 𝒻⁻ : X ─c→ Patchₛ-A
     -- 𝒻⁻ = {!!}

     ψ : is-partial-order 𝒞𝓁ℴ𝓅 _≼ₓ_
     ψ = (ψ₁ , ψ₂) , ψ₃
      where
       ψ₁ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝒿 ≼ₓ 𝒿) holds
       ψ₁ (𝒿 , p) = ≤-is-reflexive (poset-of (𝒪 Patchₛ-A)) 𝒿

       ψ₂ : is-transitive _≼ₓ_ holds
       ψ₂ (𝒿 , _) (𝓀 , _) (𝓁 , _)= ≤-is-transitive (poset-of (𝒪 Patchₛ-A)) 𝒿 𝓀 𝓁

       ψ₃ : is-antisymmetric _≼ₓ_
       ψ₃ {(𝒿 , _)} {(𝓀 , _)} p q =
        to-subtype-＝ þ ψ₄
         where
          ψ₄ : 𝒿 ＝ 𝓀
          ψ₄ = ≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A)) p q

     B₀ : Set 𝓤
     B₀ = pr₁ resize-basic

     iso₂ : B₀ ≃ ℬ𝒶𝓈𝒾𝒸
     iso₂ = pr₂ resize-basic

     iso₃ : B₀ ≃ 𝒞𝓁ℴ𝓅
     iso₃ = B₀ ≃⟨ iso₂ ⟩ ℬ𝒶𝓈𝒾𝒸 ≃⟨ iso ⟩ 𝒞𝓁ℴ𝓅 ■

     to-clop : B₀ → 𝒞𝓁ℴ𝓅
     to-clop = pr₁ iso₃

     to-clop-is-injective : (x y : B₀) → to-clop x ＝ to-clop y → x ＝ y
     to-clop-is-injective x y = equivs-are-lc to-clop (pr₂ iso₃)

     from-clop : 𝒞𝓁ℴ𝓅 → B₀
     from-clop = Eqtofun 𝒞𝓁ℴ𝓅 B₀ (≃-sym iso₃)

     ♣ : to-clop ∘ from-clop ∼ id
     ♣ = pr₂ (equivs-have-sections to-clop (pr₂ iso₃))

     ♥ : from-clop ∘ to-clop ∼ id
     ♥ 𝓍 = {!!}

     ℂ : BooleanAlgebra (𝓤 ⁺) 𝓤
     ℂ = 𝒞𝓁ℴ𝓅 , (_≼ₓ_ , 𝟏ₓ , _⋏ₓ_ , 𝟎ₓ , _⋎ₓ_ , ¡_) , ψ , φ₁ , φ₂ , φ₃ , φ₄ , φ₅ , φ₆
      where
       𝟏ₓ : 𝒞𝓁ℴ𝓅
       𝟏ₓ = 𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A)

       _⋏ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
       (𝒿 , 𝒿′ , p) ⋏ₓ (𝓀 , 𝓀′ , q) =
        (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀) , (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′) , ※
         where
          ※ : is-boolean-complement-of
               (𝒪 Patchₛ-A)
               (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′)
               (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)
              holds
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
          ※ = complementation-is-symmetric
               (𝒪 Patchₛ-A)
               (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀)
               (𝒿′ ∧[ 𝒪 Patchₛ-A ] 𝓀′)
               (∧-complement (𝒪 Patchₛ-A) p q)

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

       φ₅ : (𝒿 𝓀 𝓁 : 𝒞𝓁ℴ𝓅) → 𝒿 ⋏ₓ (𝓀 ⋎ₓ 𝓁) ＝ (𝒿 ⋏ₓ 𝓀) ⋎ₓ (𝒿 ⋏ₓ 𝓁)
       φ₅ (𝒿 , _) (𝓀 , _) (𝓁 , _) =
        to-subtype-＝ þ (binary-distributivity (𝒪 Patchₛ-A) 𝒿 𝓀 𝓁)

       φ₆ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝒿 ⋏ₓ (¡ 𝒿) ＝ 𝟎ₓ) × (𝒿 ⋎ₓ (¡ 𝒿) ＝ 𝟏ₓ)
       φ₆ (𝒿 , 𝒿′ , p , q) = to-subtype-＝ þ p , to-subtype-＝ þ q

       ℂ₀ : BooleanAlgebra 𝓤 𝓤
       ℂ₀ = B₀ , d , †
        where
         _≼ᵢ_ : B₀ → B₀ → Ω 𝓤
         x ≼ᵢ y = to-clop x ≼ₓ to-clop y


         to-clop-reflects-order : (x y : B₀)
                                → (to-clop x ≼ₓ to-clop y ⇒ x ≼ᵢ y) holds
         to-clop-reflects-order x y p = p

         𝟏ᵢ : B₀
         𝟏ᵢ = from-clop 𝟏ₓ

         𝟎ᵢ : B₀
         𝟎ᵢ = from-clop 𝟎ₓ

         _⋏ᵢ_ : B₀ → B₀ → B₀
         x ⋏ᵢ y = from-clop (to-clop x ⋏ₓ to-clop y)

         _⋎ᵢ_ : B₀ → B₀ → B₀
         x ⋎ᵢ y = from-clop (to-clop x ⋎ₓ to-clop y)

         ¬ᵢ_ : B₀ → B₀
         ¬ᵢ_ = from-clop ∘ ¡_ ∘ to-clop

         d : ba-data 𝓤 B₀
         d = _≼ᵢ_ , 𝟏ᵢ , _⋏ᵢ_ , 𝟎ᵢ , _⋎ᵢ_ , ¬ᵢ_

         ρ : is-partial-order B₀ _≼ᵢ_
         ρ = (ρ₁ , ρ₂) , ρ₃
          where
           ρ₁ : (x : B₀) → (x ≼ᵢ x) holds
           ρ₁ x = ≤-is-reflexive (poset-of (𝒪 Patchₛ-A)) (pr₁ (to-clop x))

           ρ₂ : is-transitive _≼ᵢ_ holds
           ρ₂ x y z p q = ≤-is-transitive
                           (poset-of (𝒪 Patchₛ-A))
                           (pr₁ (to-clop x))
                           (pr₁ (to-clop y))
                           (pr₁ (to-clop z))
                           p
                           q

           ρ₃ : is-antisymmetric _≼ᵢ_
           ρ₃ {x} {y} p q =
            to-clop-is-injective x y
             (to-subtype-＝ þ (≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A)) p q))

         ξ₁ : (x y : B₀) → Meets._is-glb-of_ _≼ᵢ_ (x ⋏ᵢ y) (x , y) holds
         ξ₁ x y = {!!}

         † : satisfies-ba-laws d
         † = ρ , ξ₁ , {!!}

       η : ⟪ ℂ₀ ⟫ → ⟨ 𝒪 Patchₛ-A ⟩
       η = pr₁ ∘ to-clop

       ϟ : contains-compact-opens (𝒪 Patchₛ-A) ℂ₀ η holds
       ϟ 𝒿 κ = ∥∥-rec
                ∃-is-prop
                ※
                (compact-opens-are-basic-in-compact-frames
                  (𝒪 Patchₛ-A)
                  ℬ-patch-↑
                  ℬ-patch-↑-is-directed-basisₛ
                  patchₛ-is-compact 𝒿 κ )
        where
         ※ : Σ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ]
           → ∃ b ꞉ ⟪ ℂ₀ ⟫ , η b ＝ 𝒿
         ※ (i , p) = ∣ from-clop (ℬ-patch-↑ [ i ] , foo) , ♠ ∣
          where
           abstract
            foo : is-clopen (𝒪 Patchₛ-A) (ℬ-patch-↑ [ i ]) holds
            foo = directification-preserves-clopenness (𝒪 Patchₛ-A) ℬ-patch ℬ-patchₛ-consists-of-clopens i

           𝓍 : 𝒞𝓁ℴ𝓅
           𝓍 = ℬ-patch-↑ [ i ] , foo

           ♠ : η (from-clop 𝓍) ＝ 𝒿
           ♠ = η (from-clop 𝓍)               ＝⟨ refl         ⟩
               pr₁ (to-clop (from-clop 𝓍))   ＝⟨ ap pr₁ (♣ 𝓍) ⟩
               pr₁ 𝓍                         ＝⟨ p ⁻¹         ⟩
               𝒿                             ∎

       h : ⟪ ℂ₀ ⟫ → ⟨ 𝒪 X ⟩
       h = {!!}

       h-is-a-lattice-homomorphism : is-lattice-homomorphism ℂ₀ (𝒪 X) h holds
       h-is-a-lattice-homomorphism = {!!}

       ext : ∃! 𝒻⁻⋆ ꞉ (⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩)
           , ((is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻⋆ holds) × (h ＝ 𝒻⁻⋆ ∘ η))
       ext = extension-lemma ℂ₀ (𝒪 Patchₛ-A) (𝒪 X) η {!!} patchₛ-is-spectral {!!} {!!} {!!} ϟ h h-is-a-lattice-homomorphism

\end{code}
