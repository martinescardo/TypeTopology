Ayberk Tosun, started 7th December 2022

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size
open import UF.Equiv renaming (_■ to _𝔔𝔈𝔇)
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
-- open UF.ImageAndSurjection pt

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

\end{code}

\begin{code}

 module AlgebraOfClopensOfPatch (σᴰ : spectralᴰ (𝒪 A)) where

  open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)
  open BasisOfPatch A σᴰ
  open PatchStoneᴰ A σᴰ
  open PatchStone  A ∣ σᴰ ∣

\end{code}

Throughout this module, we will have to keep referring to the fact that being
clopen is a proposition so we introduce the shorthand `þ` (Old Norse letter
Thorn) for this.

\begin{code}

  þ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → is-prop (is-clopen (𝒪 Patchₛ-A) 𝒿 holds)
  þ = holds-is-prop ∘ is-clopen (𝒪 Patchₛ-A)

\end{code}

We also add a shorthand for the fact that the basis of Patch(A) consists of
clopens. Using this proof results in the typechecking taking an unreasonably
long time so we mark it as `abstract` to avoid this.

\begin{code}

  abstract
   𝕫 : (i : index ℬ-patch-↑) → is-clopen (𝒪 Patchₛ-A) (ℬ-patch-↑ [ i ]) holds
   𝕫 = directification-preserves-clopenness
        (𝒪 Patchₛ-A)
        ℬ-patch
        ℬ-patchₛ-consists-of-clopens

\end{code}

We denote by `𝒞𝓁ℴ𝓅` the type of clopens of Patch(A) and define the order `_≼ₓ_`
on this type.

\begin{code}

  𝒞𝓁ℴ𝓅 : 𝓤 ⁺  ̇
  𝒞𝓁ℴ𝓅 = Σ 𝒿 ꞉ ⟨ 𝒪 Patch-A ⟩ , is-clopen (𝒪 Patchₛ-A) 𝒿 holds

  _≼ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → Ω 𝓤
  (𝒿 , _) ≼ₓ (𝓀 , _) = 𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] 𝓀

\end{code}

Note that this type lives in 𝓤⁺ and not 𝓤 which is to say that is not a priori
small. Before we proceed to prove the universal property of patch, we will first
show that this type can be resized.

We now define `ℬ𝒶𝓈𝒾𝒸`, the type of _basic opens_ of Patch(A), that is equivalent
to `𝒞𝓁ℴ𝓅` in the case of a Stone locale.

\begin{code}

  ℬ𝒶𝓈𝒾𝒸 : 𝓤 ⁺  ̇
  ℬ𝒶𝓈𝒾𝒸 = image pt (λ - → ℬ-patch-↑ [ - ])

\end{code}

To show that `ℬ𝒶𝓈𝒾𝒸` and `𝒞𝓁ℴ𝓅` are equivalent, we define the following pair of
maps forming a section-retraction pair:

\begin{code}

  𝔰₁ : ℬ𝒶𝓈𝒾𝒸 → 𝒞𝓁ℴ𝓅
  𝔰₁ (𝒿 , p) = 𝒿 , ∥∥-rec (þ 𝒿) † p
   where
    † : Σ i ꞉ index ℬ-patch-↑ , ℬ-patch-↑ [ i ] ＝ 𝒿
      → is-clopen (𝒪 Patchₛ-A) 𝒿 holds
    † (i , q) = transport (λ - → is-clopen (𝒪 Patchₛ-A) - holds) q (𝕫 i)

  𝔯₁ : 𝒞𝓁ℴ𝓅 → ℬ𝒶𝓈𝒾𝒸
  𝔯₁ (𝒿 , p) = 𝒿 , ∥∥-rec ∃-is-prop † γ
   where
    γ : ∃ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ]
    γ = clopens-are-basic-in-stone-locales
         (𝒪 Patchₛ-A)
         patchₛ-is-stone
         ℬ-patch-↑
         ℬ-patch-↑-is-directed-basisₛ
         𝒿
         p

    † : Σ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ]
      → ∃ i ꞉ index ℬ-patch-↑ , ℬ-patch-↑ [ i ] ＝ 𝒿
    † (i , p) = ∣ i , (p ⁻¹) ∣

  𝔰₁-has-section : has-section 𝔰₁
  𝔰₁-has-section = 𝔯₁ , †
   where
    † : 𝔰₁ ∘ 𝔯₁ ∼ id
    † (𝒿 , _) = to-subtype-＝ þ (refl {x = 𝒿})

  𝔰₁-is-section : is-section 𝔰₁
  𝔰₁-is-section = 𝔯₁ , †
   where
    † : 𝔯₁ ∘ 𝔰₁ ∼ id
    † (𝒿 , _) = to-subtype-＝ (λ _ → ∃-is-prop) (refl {x = 𝒿})

  basic-is-equivalent-to-clop : ℬ𝒶𝓈𝒾𝒸 ≃ 𝒞𝓁ℴ𝓅
  basic-is-equivalent-to-clop =
   𝔰₁ , section-retraction-equiv 𝔰₁ 𝔰₁-has-section 𝔰₁-is-section

\end{code}

We now proceed to show that the type `ℬ𝒶𝓈𝒾𝒸` is small. Let `B` and `β` denote
the index and the enumeration function of the family of basic opens of Patch(A)
respectively.

\begin{code}

  B : 𝓤  ̇
  B = index ℬ-patch-↑

  γγ : index ℬ-patch-↑ → ⟨ 𝒪 Patchₛ-A ⟩
  γγ = λ - → ℬ-patch-↑ [ - ]

\end{code}

We can show patch Patch(A) is locally small by using the logical equivalence
between the pointwise nuclei ordering and the basic one.

\begin{code}

  patch-is-locally-small : ⟨ 𝒪 Patchₛ-A ⟩ is-locally 𝓤 small
  patch-is-locally-small 𝒿 𝓀 = (𝒿 ＝ᵏ 𝓀) holds , †
   where
    r = ≤-is-reflexive (poset-of (𝒪 Patchₛ-A)) 𝒿

    †₁ : (𝒿 ＝ᵏ 𝓀) holds → 𝒿 ＝ 𝓀
    †₁ = uncurry ≼ᵏ-is-antisymmetric

    †₂ : 𝒿 ＝ 𝓀 → (𝒿 ＝ᵏ 𝓀) holds
    †₂ p = transport (λ - → (𝒿 ＝ᵏ -) holds) p (r , r)

    † : (𝒿 ＝ᵏ 𝓀) holds ≃ (𝒿 ＝ 𝓀)
    † = logically-equivalent-props-are-equivalent
         (holds-is-prop (𝒿 ＝ᵏ 𝓀))
         carrier-of-[ poset-of (𝒪 Patchₛ-A) ]-is-set
         †₁
         †₂

\end{code}

Using the assumption of the set replacement axiom and the fact that the carrier
set of Patch(A) is locally small, we prove that the type of basic opens is
small.

\begin{code}

  basic-is-small : ℬ𝒶𝓈𝒾𝒸 is 𝓤 small
  basic-is-small =
   sr γγ (B , ≃-refl B) † carrier-of-[ poset-of (𝒪 Patchₛ-A) ]-is-set
    where
     † : ⟨ 𝒪 Patchₛ-A ⟩ is-locally 𝓤 small
     † = patch-is-locally-small

\end{code}

We denote by `ℬ𝒶𝓈𝒾𝒸₀` the small copy of `ℬ𝒶𝓈𝒾𝒸` given by `basic-is-small`.

\begin{code}

  ℬ𝒶𝓈𝒾𝒸₀ : 𝓤  ̇
  ℬ𝒶𝓈𝒾𝒸₀ = pr₁ basic-is-small

  𝔰₂ : ℬ𝒶𝓈𝒾𝒸₀ → ℬ𝒶𝓈𝒾𝒸
  𝔰₂ = pr₁ (pr₂ basic-is-small)

  𝔯₂ : ℬ𝒶𝓈𝒾𝒸 → ℬ𝒶𝓈𝒾𝒸₀
  𝔯₂ = inverse 𝔰₂ (pr₂ (pr₂ basic-is-small))

  𝔰₂-is-section-of-𝔯₂ : 𝔯₂ ∘ 𝔰₂ ∼ id
  𝔰₂-is-section-of-𝔯₂ =
   inverses-are-sections 𝔯₂ (pr₂ (≃-sym (pr₂ basic-is-small)))

  𝔯₂-is-section-of-𝔰₂ : 𝔰₂ ∘ 𝔯₂ ∼ id
  𝔯₂-is-section-of-𝔰₂ = inverses-are-sections 𝔰₂ (pr₂ (pr₂ basic-is-small))

\end{code}

Since `ℬ𝒶𝓈𝒾𝒸₀` is equivalent to `ℬ𝒶𝓈𝒾𝒸` which is in turn equivalent to `𝒞𝓁ℴ𝓅`,
we have that `ℬ𝒶𝓈𝒾𝒸₀` is equivalent to `𝒞𝓁ℴ𝓅`.

\begin{code}

  basic₀-is-equivalent-to-clop : ℬ𝒶𝓈𝒾𝒸₀ ≃ 𝒞𝓁ℴ𝓅
  basic₀-is-equivalent-to-clop = ℬ𝒶𝓈𝒾𝒸₀ ≃⟨ † ⟩ ℬ𝒶𝓈𝒾𝒸 ≃⟨ ‡ ⟩ 𝒞𝓁ℴ𝓅 𝔔𝔈𝔇
    where
     † = pr₂ basic-is-small
     ‡ = basic-is-equivalent-to-clop

\end{code}

In the next section we show that the set of clopens forms a Boolean algebra. We
then transport this Boolean algebra structure on `𝒞𝓁ℴ𝓅` along the equivalence
`ℬ𝒶𝓈𝒾𝒸₀ ≃ 𝒞𝓁ℴ𝓅` to obtain a small version of this Boolean algebra.

\section{The Algebra of Clopens of Patch}

We now show that the type of clopens of Patch forms a Boolean algebra. We denote
this by `ℂ`.

\begin{code}

  ο : is-partial-order 𝒞𝓁ℴ𝓅 _≼ₓ_
  ο = (ο₁ , ο₂) , ο₃
   where
    ο₁ : (𝒿 : 𝒞𝓁ℴ𝓅) → (𝒿 ≼ₓ 𝒿) holds
    ο₁ (𝒿 , p) = ≤-is-reflexive (poset-of (𝒪 Patchₛ-A)) 𝒿

    ο₂ : is-transitive _≼ₓ_ holds
    ο₂ (𝒿 , _) (𝓀 , _) (𝓁 , _)= ≤-is-transitive (poset-of (𝒪 Patchₛ-A)) 𝒿 𝓀 𝓁

    ο₃ : is-antisymmetric _≼ₓ_
    ο₃ {(𝒿 , _)} {(𝓀 , _)} =
     curry
      (to-subtype-＝ þ ∘ uncurry (≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A))))

\end{code}

The top and bottom elements of `ℂ`.

\begin{code}

  𝟏ₓ : 𝒞𝓁ℴ𝓅
  𝟏ₓ = 𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A)

  𝟎ₓ : 𝒞𝓁ℴ𝓅
  𝟎ₓ = 𝟎[ 𝒪 Patchₛ-A ] , 𝟎-is-clopen (𝒪 Patchₛ-A)

\end{code}

The meet and the join of `ℂ`.

\begin{code}

  _⋏ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
  (𝒿 , 𝒿′ , p) ⋏ₓ (𝓀 , 𝓀′ , q) =
   (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀) , (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′) , ※
    where
     † : is-boolean-complement-of (𝒪 Patchₛ-A) 𝒿 𝒿′ holds
     † = (complementation-is-symmetric (𝒪 Patchₛ-A) 𝒿′ 𝒿 p)

     ‡ : is-boolean-complement-of (𝒪 Patchₛ-A) 𝓀 𝓀′ holds
     ‡ = complementation-is-symmetric (𝒪 Patchₛ-A) 𝓀′ 𝓀 q

     ※ : is-boolean-complement-of
          (𝒪 Patchₛ-A)
          (𝒿′ ∨[ 𝒪 Patchₛ-A ] 𝓀′)
          (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)
         holds
     ※ = ∧-complement (𝒪 Patchₛ-A) † ‡

  _⋎ₓ_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
  (𝒿 , 𝒿′ , p) ⋎ₓ (𝓀 , 𝓀′ , q) = (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀) , (𝒿′ ⋏ 𝓀′) , ※
   where
    ※ : is-boolean-complement-of (𝒪 Patchₛ-A) (𝒿′ ⋏ 𝓀′) (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀) holds
    ※ = complementation-is-symmetric
         (𝒪 Patchₛ-A)
         (𝒿 ∨[ 𝒪 Patchₛ-A ] 𝓀)
         (𝒿′ ∧[ 𝒪 Patchₛ-A ] 𝓀′)
         (∧-complement (𝒪 Patchₛ-A) p q)

\end{code}

The negation operation of `ℂ`.

\begin{code}

  ¡_ : 𝒞𝓁ℴ𝓅 → 𝒞𝓁ℴ𝓅
  ¡ (𝒿 , 𝒿′ , p) = 𝒿′ , 𝒿 , complementation-is-symmetric (𝒪 Patchₛ-A) 𝒿′ 𝒿 p

\end{code}

Finally, the complete definition of the algebra of clopens `ℂ`.

\begin{code}

  ℂ : BooleanAlgebra (𝓤 ⁺) 𝓤
  ℂ = 𝒞𝓁ℴ𝓅 , (_≼ₓ_ , 𝟏ₓ , _⋏ₓ_ , 𝟎ₓ , _⋎ₓ_ , ¡_) , ο , φ₁ , φ₂ , φ₃ , φ₄ , φ₅ , φ₆
   where
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

\end{code}

\section{Small version of `ℂ`}

\begin{code}

  to-clop : ℬ𝒶𝓈𝒾𝒸₀ → 𝒞𝓁ℴ𝓅
  to-clop = 𝔰₁ ∘ 𝔰₂

  to-basic₀ : 𝒞𝓁ℴ𝓅 → ℬ𝒶𝓈𝒾𝒸₀
  to-basic₀ = inverse to-clop (pr₂ basic₀-is-equivalent-to-clop)

  to-basic₀-is-equiv : is-equiv to-basic₀
  to-basic₀-is-equiv = pr₂ (≃-sym basic₀-is-equivalent-to-clop)

  to-basic₀-is-section-of-to-clop : to-clop ∘ to-basic₀ ∼ id
  to-basic₀-is-section-of-to-clop =
   pr₂ (equivs-have-sections to-clop (pr₂ basic₀-is-equivalent-to-clop))

  to-clop-is-section-of-to-basic₀ : to-basic₀ ∘ to-clop ∼ id
  to-clop-is-section-of-to-basic₀ =
   pr₂ (equivs-have-sections to-basic₀ (pr₂ (≃-sym basic₀-is-equivalent-to-clop)))

  ℂ₀ : BooleanAlgebra 𝓤 𝓤
  ℂ₀ = ℬ𝒶𝓈𝒾𝒸₀ , b′
   where
    ξ : Σ b′ ꞉ ba-structure 𝓤 ℬ𝒶𝓈𝒾𝒸₀ ,
         is-ba-homomorphism ℂ (ℬ𝒶𝓈𝒾𝒸₀ , b′) to-basic₀ holds
    ξ = transport-ba-structure 𝒞𝓁ℴ𝓅 ℬ𝒶𝓈𝒾𝒸₀ to-basic₀ to-basic₀-is-equiv (pr₂ ℂ)

    b′ : ba-structure 𝓤 ℬ𝒶𝓈𝒾𝒸₀
    b′ = pr₁ ξ

  ℂb : BooleanAlgebra (𝓤 ⁺) 𝓤
  ℂb = ℬ𝒶𝓈𝒾𝒸 , b′
   where
    ξ : Σ b′ ꞉ ba-structure 𝓤 ℬ𝒶𝓈𝒾𝒸 , is-ba-homomorphism ℂ (ℬ𝒶𝓈𝒾𝒸 , b′) 𝔯₁ holds
    ξ = transport-ba-structure 𝒞𝓁ℴ𝓅 ℬ𝒶𝓈𝒾𝒸 𝔯₁ (pr₂ (≃-sym basic-is-equivalent-to-clop)) (pr₂ ℂ)

    b′ : ba-structure 𝓤 ℬ𝒶𝓈𝒾𝒸
    b′ = pr₁ ξ

  𝔯₁-is-ba-homomorphism : is-ba-homomorphism ℂ ℂb 𝔯₁ holds
  𝔯₁-is-ba-homomorphism =
   pr₂ (transport-ba-structure 𝒞𝓁ℴ𝓅 ℬ𝒶𝓈𝒾𝒸 𝔯₁ (pr₂ (≃-sym basic-is-equivalent-to-clop)) (pr₂ ℂ))

\end{code}

\section{Proof of the Universal Property}

\begin{code}

 ump-of-patch : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
              → is-stone (𝒪 X) holds
              → (𝒻 : X ─c→ A)
              → is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds
              → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
 ump-of-patch X 𝕤 𝒻 μ = ∥∥-rec₂ (being-singleton-is-prop fe) γ σ (pr₂ 𝕤)
  where
   γ : spectralᴰ (𝒪 A)
     → zero-dimensionalᴰ (𝒪 X)
     → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
   γ σᴰ 𝕫ᴰ = {!!}
    where
     open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)
     open BasisOfPatch A σᴰ
     open AlgebraOfClopensOfPatch σᴰ
     open PatchStoneᴰ A σᴰ
     open OpenNucleus A ∣ σᴰ ∣
     open ContinuousMapNotation X A
     open BasicComplements (𝒪 X) (pr₁ 𝕤) 𝕫ᴰ

     X-is-set : is-set ⟨ 𝒪 X ⟩
     X-is-set = carrier-of-[ poset-of (𝒪 X) ]-is-set

     ℬ-X : Fam 𝓤 ⟨ 𝒪 X ⟩
     ℬ-X = pr₁ 𝕫ᴰ

     ¬𝒻_ : index ℬ → ⟨ 𝒪 X ⟩
     ¬𝒻 i = ¬ₓ (𝒻 ⋆∙ (ℬ [ i ]) , μ (ℬ [ i ]) (pr₁ (pr₂ (pr₂ σᴰ)) i))

     ¬𝒻-lemma : (i : index ℬ) (ℬᵢ′ : ⟨ 𝒪 A ⟩)
              → is-complement-of (𝒪 A) ℬᵢ′ (ℬ [ i ])
              → ¬𝒻 i ＝ 𝒻 ⋆∙ ℬᵢ′
     ¬𝒻-lemma i ℬᵢ′ (p , q) =
      complements-are-unique (𝒪 X) (𝒻 ⋆∙ (ℬ [ i ])) (¬𝒻 i) (𝒻 ⋆∙ ℬᵢ′) † ‡
       where
        † : is-complement-of (𝒪 X) (¬𝒻 i) (𝒻 ⋆∙ (ℬ [ i ]))
        † = ¬ₓ-gives-complement (𝒻 ⋆∙ (ℬ [ i ])) (μ (ℬ [ i ]) (pr₁ (pr₂ (pr₂ σᴰ)) i))

        ‡₁ : ℬᵢ′ ∧[ 𝒪 A ] (ℬ [ i ]) ＝ 𝟎[ 𝒪 A ]
        ‡₁ = ℬᵢ′     ∧[ 𝒪 A ] (ℬ [ i ]) ＝⟨ ∧[ 𝒪 A ]-is-commutative ℬᵢ′ (ℬ [ i ]) ⟩
             ℬ [ i ] ∧[ 𝒪 A ] ℬᵢ′       ＝⟨ p                                     ⟩
             𝟎[ 𝒪 A ]                   ∎

        ‡₂ : ℬᵢ′ ∨[ 𝒪 A ] (ℬ [ i ]) ＝ 𝟏[ 𝒪 A ]
        ‡₂ = ℬᵢ′ ∨[ 𝒪 A ] (ℬ [ i ])     ＝⟨ ∨[ 𝒪 A ]-is-commutative ℬᵢ′ (ℬ [ i ]) ⟩
             (ℬ [ i ]) ∨[ 𝒪 A ] ℬᵢ′     ＝⟨ q ⟩
             𝟏[ 𝒪 A ]                   ∎

        ‡ : is-complement-of (𝒪 X) (𝒻 ⋆∙ ℬᵢ′) (𝒻 ⋆∙ (ℬ [ i ]))
        ‡ = frame-homomorphisms-preserve-complements (𝒪 A) (𝒪 X) 𝒻 (‡₁ , ‡₂)

     g : index ℬ-patch-↑ → ⟨ 𝒪 X ⟩
     g []             = 𝟎[ 𝒪 X ]
     g ((i , j) ∷ ks) = (𝒻 ⋆∙ (ℬ [ i ]) ∧[ 𝒪 X ] ¬𝒻 j) ∨[ 𝒪 X ] g ks

     congruence-wrt-β : (i j : index ℬ-patch-↑) → γγ i ＝ γγ j → g i ＝ g j
     congruence-wrt-β []       []               p = refl
     congruence-wrt-β []       ((j₁ , j₂) ∷ js) p = †
      where
       foo : g js ＝ 𝟎[ 𝒪 X ]
       foo = congruence-wrt-β js [] (join-𝟎-lemma₂ (𝒪 Patchₛ-A) (p ⁻¹))

       open OpenMeetClosedLemmata A σᴰ

       crux : ((ℬ [ j₁ ]) ≤[ poset-of (𝒪 A) ] (ℬ [ j₂ ])) holds
       crux = closed-meet-open-𝟎-lemma
               (ℬ [ j₁ ])
               (ℬ [ j₂ ])
               (pr₁ (pr₂ (pr₂ σᴰ)) j₂)
               (join-𝟎-lemma₁ (𝒪 Patchₛ-A) (p ⁻¹))

       bar : 𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂ ＝ 𝟎[ 𝒪 X ]
       bar = only-𝟎-is-below-𝟎 (𝒪 X) (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂) ※
        where
         open PosetReasoning (poset-of (𝒪 X))

         ※ : (((𝒻 ⋆∙ (ℬ [ j₁ ])) ∧[ 𝒪 X ] (¬𝒻 j₂)) ≤[ poset-of (𝒪 X) ] 𝟎[ 𝒪 X ]) holds
         ※ = (𝒻 ⋆∙ (ℬ [ j₁ ])) ∧[ 𝒪 X ] ¬𝒻 j₂    ≤⟨ I  ⟩
             (𝒻 ⋆∙ (ℬ [ j₂ ])) ∧[ 𝒪 X ] ¬𝒻 j₂    ＝⟨ II ⟩ₚ
             𝟎[ 𝒪 X ]                            ■
              where
               I  = ∧[ 𝒪 X ]-left-monotone
                     (frame-morphisms-are-monotonic
                       (𝒪 A)
                       (𝒪 X)
                       (𝒻 .pr₁)
                       (pr₂ 𝒻)
                       (ℬ [ j₁ ] , ℬ [ j₂ ])
                       crux)
               II = pr₁ (¬ₓ-gives-complement (𝒻 ⋆∙ (ℬ [ j₂ ])) (μ (ℬ [ j₂ ]) (κ j₂)))

       † : 𝟎[ 𝒪 X ] ＝ g (j₁ , j₂ ∷ js)
       † = 𝟎[ 𝒪 X ]                                           ＝⟨ bar ⁻¹ ⟩
           (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂)                   ＝⟨ I    ⟩
           (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂) ∨[ 𝒪 X ] 𝟎[ 𝒪 X ] ＝⟨ II   ⟩
           (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂) ∨[ 𝒪 X ] g js     ＝⟨ refl ⟩
           g (j₁ , j₂ ∷ js)                                   ∎
            where
             I  = 𝟎-left-unit-of-∨ (𝒪 X) (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂) ⁻¹
             II = ap (λ - → (𝒻 ⋆∙ (ℬ [ j₁ ]) ∧[ 𝒪 X ] ¬𝒻 j₂) ∨[ 𝒪 X ] -) (foo ⁻¹)
     congruence-wrt-β (i ∷ is) []               p = {!!}
     congruence-wrt-β ((i₁ , i₂) ∷ is) ((j₁ , j₂) ∷ js) p = †
      where
       † : g ((i₁ , i₂) ∷ is) ＝ g ((j₁ , j₂) ∷ js)
       † = {!!}

     h₀ : ℬ𝒶𝓈𝒾𝒸 → ⟨ 𝒪 X ⟩
     h₀ = pr₁ (pr₁ (factor-through-image pt fe γγ X-is-set g congruence-wrt-β))

     -- h₁(j) ≔ ⋁ ⁅ f*(Bₘ) ∧ ¬f*(Bₙ) ∣ Bₘ ≤ j(Bₙ) ⁆

     h₁ : ℬ𝒶𝓈𝒾𝒸 → ⟨ 𝒪 X ⟩
     h₁ (j , p) =
      ⋁[ 𝒪 X ] (I , (λ { ((m , n) , _) → (𝒻 ⋆∙ (ℬ [ m ])) ∧[ 𝒪 X ] ¬𝒻 n }))
       where
        I = Σ (m , n) ꞉ index ℬ × index ℬ , (((ℬ [ m ]) ≤[ poset-of (𝒪 A) ] j .pr₁ (ℬ [ n ]) ) holds)

     υ : h₀ ∘ corestriction pt γγ ∼ g
     υ = pr₂ (pr₁ (factor-through-image pt fe γγ X-is-set g congruence-wrt-β))

     h : ℬ𝒶𝓈𝒾𝒸₀ → ⟨ 𝒪 X ⟩
     h = h₀ ∘ 𝔰₂

     𝕚 : ⟪ ℂ₀ ⟫ → ⟨ 𝒪 Patchₛ-A ⟩
     𝕚 = pr₁ ∘ to-clop

     † : contains-compact-opens (𝒪 Patchₛ-A) ℂ₀ 𝕚 holds
     † 𝒿 φ = ∥∥-rec ∃-is-prop ‡ ※
      where
       ‡ : Σ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ]
         → ∃ b ꞉ ⟪ ℂ₀ ⟫ , 𝕚 b ＝ 𝒿
       ‡ (i , p) = ∣ to-basic₀ ℬᵢ , q ∣
        where
         ζ : is-clopen (𝒪 Patchₛ-A) (ℬ-patch-↑ [ i ]) holds
         ζ = directification-preserves-clopenness
              (𝒪 Patchₛ-A)
              ℬ-patch
              ℬ-patchₛ-consists-of-clopens
              i

         ℬᵢ : 𝒞𝓁ℴ𝓅
         ℬᵢ = ℬ-patch-↑ [ i ] , ζ

         q : 𝕚 (to-basic₀ ℬᵢ) ＝ 𝒿
         q = 𝕚 (to-basic₀ ℬᵢ)              ＝⟨ refl        ⟩
             pr₁ (to-clop (to-basic₀ ℬᵢ))  ＝⟨ ♣           ⟩
             pr₁ ℬᵢ                        ＝⟨ refl        ⟩
             ℬ-patch-↑ [ i ]               ＝⟨ p ⁻¹        ⟩
             𝒿                             ∎
              where
               ♣ = ap pr₁ (to-basic₀-is-section-of-to-clop ℬᵢ)

       ※ : ∥ Σ i ꞉ index ℬ-patch-↑ , 𝒿 ＝ ℬ-patch-↑ [ i ] ∥
       ※ = compact-opens-are-basic-in-compact-frames
            (𝒪 Patchₛ-A)
            ℬ-patch-↑
            ℬ-patch-↑-is-directed-basisₛ
            patchₛ-is-compact
            𝒿
            φ

     𝕚-is-embedding : is-ba-embedding ℂ₀ (𝒪 Patchₛ-A) 𝕚 holds
     𝕚-is-embedding = ι
                    , 𝕚-preserves-⊤
                    , 𝕚-preserves-∧
                    , 𝕚-preserves-⊥
                    , 𝕚-preserves-∨
      where
       ι : (x y : ⟪ ℂ₀ ⟫) → 𝕚 x ＝ 𝕚 y → x ＝ y
       ι x y p = x                       ＝⟨ Ⅰ ⟩
                 to-basic₀ (to-clop x)   ＝⟨ Ⅱ ⟩
                 to-basic₀ (to-clop y)   ＝⟨ Ⅲ ⟩
                 y                       ∎
                  where
                   Ⅰ = to-clop-is-section-of-to-basic₀ x ⁻¹
                   Ⅱ = ap
                        to-basic₀
                        (to-subtype-＝ (is-clopen₀-is-prop (𝒪 Patchₛ-A)) p)
                   Ⅲ = to-clop-is-section-of-to-basic₀ y

       𝕚-preserves-⊤ : 𝕚 ⊤[ ℂ₀ ] ＝ 𝟏[ 𝒪 Patchₛ-A ]
       𝕚-preserves-⊤ = ap pr₁ (to-basic₀-is-section-of-to-clop ⊤[ ℂ ])

       𝕚-preserves-∧ : (x y : ⟪ ℂ₀ ⟫)
                     → 𝕚 (x ⋏[ ℂ₀ ] y) ＝ 𝕚 x ∧[ 𝒪 Patchₛ-A ] 𝕚 y
       𝕚-preserves-∧ x y =
        ap pr₁ (to-basic₀-is-section-of-to-clop (to-clop x ⋏[ ℂ ] to-clop y))

       𝕚-preserves-⊥ : 𝕚 ⊥[ ℂ₀ ] ＝ 𝟎[ 𝒪 Patchₛ-A ]
       𝕚-preserves-⊥ = ap pr₁ (to-basic₀-is-section-of-to-clop ⊥[ ℂ ])

       𝕚-preserves-∨ : (x y : ⟪ ℂ₀ ⟫) → 𝕚 (x ⋎[ ℂ₀ ] y) ＝ 𝕚 x ∨[ 𝒪 Patchₛ-A ] 𝕚 y
       𝕚-preserves-∨ x y =
        ap pr₁ (to-basic₀-is-section-of-to-clop (to-clop x ⋎[ ℂ ] to-clop y))

     𝕚-is-spectral : is-spectral′ ℂ₀ (𝒪 Patchₛ-A) 𝕚 holds
     𝕚-is-spectral b =
      pr₁ (clopen-iff-compact-in-stone-frame (𝒪 Patchₛ-A) ♠ (𝕚 b)) ♣
       where
        ♠ : is-stone (𝒪 Patchₛ-A) holds
        ♠ = patchₛ-is-stone

        ♣ : is-clopen (𝒪 Patchₛ-A) (𝕚 b) holds
        ♣ = pr₂ (to-clop b)

     open Epsilon A σᴰ

     h-is-homomorphism : is-lattice-homomorphism ℂ₀ (𝒪 X) h holds
     h-is-homomorphism = ∥∥-rec₂
                          (holds-is-prop (is-lattice-homomorphism ℂ₀ (𝒪 X) h)) ϟ 𝟎-is-basic 𝟏-is-basic
      where
       𝟎-is-basic : ∃ ib ꞉ index ℬ , 𝟎[ 𝒪 A ] ＝ ℬ [ ib ]
       𝟎-is-basic =
        compact-opens-are-basic-in-compact-frames
         (𝒪 A)
         ℬ
         {!!}
         (spectral-implies-compact (𝒪 A) σ)
         𝟎[ 𝒪 A ]
         (𝟎-is-compact (𝒪 A))

       𝟏-is-basic : ∃ iu ꞉ index ℬ , 𝟏[ 𝒪 A ] ＝ ℬ [ iu ]
       𝟏-is-basic = {!!}

       ϟ : Σ ib ꞉ index ℬ , 𝟎[ 𝒪 A ] ＝ ℬ [ ib ]
         → Σ iu ꞉ index ℬ , 𝟏[ 𝒪 A ] ＝ ℬ [ iu ]
         → is-lattice-homomorphism ℂ₀ (𝒪 X) h holds
       ϟ (ib , q₁) (iu , q₂) = α₁ , {!α₂!} , α₃ , α₄
        where
         k = (iu , ib) ∷ []

         ♣ : ℬ-patch-↑ [ k ] ＝ 𝟏[ 𝒪 Patchₛ-A ]
         ♣ = ℬ-patch-↑ [ k ]                                                                ＝⟨ refl ⟩
             (‘ ℬ [ iu ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ ℬₖ [ ib ] ’) ∨[ 𝒪 Patchₛ-A ] 𝟎[ 𝒪 Patchₛ-A ]  ＝⟨ Ⅰ    ⟩
             ‘ ℬ [ iu ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ ℬₖ [ ib ] ’                                    ＝⟨ Ⅱ    ⟩
             ‘ 𝟏[ 𝒪 A ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ ℬₖ [ ib ] ’                                    ＝⟨ Ⅲ    ⟩
             ‘ 𝟏[ 𝒪 A ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ 𝟎ₖ  ’                                          ＝⟨ Ⅳ    ⟩
             ‘ 𝟏[ 𝒪 A ] ’ ∧[ 𝒪 Patchₛ-A ] 𝟏[ 𝒪 Patchₛ-A ]                                   ＝⟨ Ⅴ    ⟩
             𝟏[ 𝒪 Patchₛ-A ] ∧[ 𝒪 Patchₛ-A ] 𝟏[ 𝒪 Patchₛ-A ]                                ＝⟨ Ⅵ    ⟩
             𝟏[ 𝒪 Patchₛ-A ]                                                                ∎
              where
               Ⅰ =  𝟎-left-unit-of-∨ (𝒪 Patchₛ-A) (‘ ℬ [ iu ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ ℬₖ [ ib ] ’)
               Ⅱ = ap (λ - → ‘ - ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ ℬₖ [ ib ] ’) (q₂ ⁻¹)
               Ⅲ = ap
                    (λ - → ‘ 𝟏[ 𝒪 A ] ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ - ’)
                    (to-subtype-＝ (λ x → holds-is-prop (is-compact-open (𝒪 A) x)) (q₁ ⁻¹))
               Ⅳ = ap (λ - → ‘ 𝟏[ 𝒪 A ] ’ ∧[ 𝒪 Patchₛ-A ] -) ¬‘’-reflects-𝟎
               Ⅴ = ap (λ - →  - ∧[ 𝒪 Patchₛ-A ] 𝟏[ 𝒪 Patchₛ-A ]) ϵ-preserves-𝟏
               Ⅵ = ∧[ 𝒪 Patchₛ-A ]-is-idempotent 𝟏[ 𝒪 Patchₛ-A ] ⁻¹

         α₁ : h ⊤[ ℂ₀ ] ＝ 𝟏[ 𝒪 X ]
         α₁ = h ⊤[ ℂ₀ ]                                                       ＝⟨ refl  ⟩
              h₀ (𝔰₂ ⊤[ ℂ₀ ])                                                 ＝⟨ refl  ⟩
              h₀ (𝔰₂ (to-basic₀ ⊤[ ℂ ]))                                      ＝⟨ refl  ⟩
              h₀ (𝔰₂ (𝔯₂ (𝔯₁ (𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A)))))  ＝⟨ Ⅱ     ⟩
              h₀ (𝔯₁ (𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A)))            ＝⟨ Ⅰ     ⟩
              h₀ (𝟏[ 𝒪 Patchₛ-A ] , ∣ k , ♣ ∣)                                ＝⟨ Ⅲ     ⟩
              h₀ (ℬ-patch-↑ [ k ] , ∣ k , refl ∣)                             ＝⟨ refl  ⟩
              h₀ (corestriction pt γγ k)                                      ＝⟨ υ k   ⟩
              g (iu , ib ∷ [])                                                ＝⟨ refl  ⟩
              (𝒻 ⋆∙ (ℬ [ iu ]) ∧[ 𝒪 X ] ¬𝒻 ib) ∨[ 𝒪 X ] 𝟎[ 𝒪 X ]              ＝⟨ Ⅳ     ⟩
              (𝒻 ⋆∙ (ℬ [ iu ]) ∧[ 𝒪 X ] ¬𝒻 ib)                                ＝⟨ Ⅴ     ⟩
              (𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻 ib)                                  ＝⟨ Ⅵ     ⟩
              (𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] 𝒻 ⋆∙ 𝟏[ 𝒪 A ])                          ＝⟨ Ⅶ     ⟩
              𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                      ＝⟨ Ⅷ     ⟩
              𝟏[ 𝒪 X ]                                                        ∎
               where
                Ⅰ = ap h₀ (to-subtype-＝ (λ _ → ∃-is-prop) refl)
                Ⅱ = ap h₀ (𝔯₂-is-section-of-𝔰₂ (𝔯₁ (𝟏[ 𝒪 Patchₛ-A ] , 𝟏-is-clopen (𝒪 Patchₛ-A))))
                Ⅲ = ap h₀ (to-subtype-＝ (λ _ → ∃-is-prop) (♣ ⁻¹))
                Ⅳ = 𝟎-left-unit-of-∨ (𝒪 X) (𝒻 ⋆∙ (ℬ [ iu ]) ∧[ 𝒪 X ] ¬𝒻 ib)
                Ⅴ = ap (λ - → (𝒻 ⋆∙ -) ∧[ 𝒪 X ] (¬𝒻 ib)) (q₂ ⁻¹)
                Ⅵ = ap (λ - → (𝒻 ⋆∙ 𝟏[ 𝒪 A ]) ∧[ 𝒪 X ] -) (¬𝒻-lemma ib 𝟏[ 𝒪 A ] ※)
                     where
                      ※ = transport
                           (is-complement-of (𝒪 A) 𝟏[ 𝒪 A ])
                           q₁
                           (pr₂ (𝟎-is-clopen (𝒪 A)))
                Ⅶ = ap₂ (λ x y → x ∧[ 𝒪 X ] y) ※ ※
                     where
                      ※ = (frame-homomorphisms-preserve-top (𝒪 A) (𝒪 X) 𝒻)
                Ⅷ = ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ] ⁻¹

         α₃ : h ⊥[ ℂ₀ ] ＝ 𝟎[ 𝒪 X ]
         α₃ = {!!}

         α₄ : (x y : ⟪ ℂ₀ ⟫) → h (x ⋎[ ℂ₀ ] y) ＝ h x ∨[ 𝒪 X ] h y
         α₄ x y = h (x ⋎[ ℂ₀ ] y)                      ＝⟨ refl ⟩
                  h₀ (𝔰₂ (x ⋎[ ℂ₀ ] y))                ＝⟨  {!!}   ⟩
                  h₀ (𝔰₂ x ⋎[ ℂb ] 𝔰₂ y)               ＝⟨  {!!}   ⟩
                  h₀ (𝔰₂ x ⋎[ ℂb ] 𝔰₂ y)               ＝⟨  {!!}   ⟩
                  h₀ (𝔰₂ x) ∨[ 𝒪 X ] h₀ (𝔰₂ y)         ＝⟨ refl    ⟩
                  h x ∨[ 𝒪 X ] h y                     ∎
                   where
                    κp : is-clopen (𝒪 Patchₛ-A) (pr₁ (to-clop x) ∨[ 𝒪 Patchₛ-A ] pr₁ (to-clop y)) holds
                    κp = clopens-are-closed-under-∨ (𝒪 Patchₛ-A) _ _ (pr₂ (to-clop x)) (pr₂ (to-clop y))

     ξ : ∃! 𝒻⁻⋆ ꞉ (⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩) ,
            (is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻⋆ holds)
          × (h ＝ 𝒻⁻⋆ ∘ 𝕚)
     ξ = extension-lemma
          ℂ₀
          (𝒪 Patchₛ-A)
          (𝒪 X)
          𝕚
          𝕚-is-embedding
          patchₛ-is-spectral
          𝕚-is-spectral
          {!!}
          †
          h
          h-is-homomorphism

\end{code}
