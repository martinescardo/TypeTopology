\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.TarskiLFPfromPropResizing
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pr : Propositional-resizing)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import UF.ImageAndSurjection pt
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe
open import OrderedTypes.InfLattice fe pt hiding
 (⟨_⟩ ; order-of ; is-monotone-endomap)

open AllCombinators pt fe
open PropositionalTruncation pt

open import OrderedTypes.PredicativeLFP pt fe pe
    
module _ {L : Sup-Lattice 𝓤 𝓦 𝓥} {B : 𝓥 ̇}
         (β : B → ⟨ L ⟩) (h : is-basis L β)
         (f : ⟨ L ⟩ → ⟨ L ⟩)
         (f-mono : is-monotone-endomap L f)
       where

 open local-inductive-definitions L β h
 open correspondance-from-locally-small-ϕ L β h
       (ind-def-from-monotone-map f f-mono) (local-from-monotone-map f f-mono)

\end{code}

TODO. Can we show that certain QITs including the one assumed in the anonomous
module below follow from propositional resizing?

\begin{code}

 module _ (ind-e : inductively-generated-subset-exists L β h
                     (ind-def-from-monotone-map f f-mono))
        where

  open small-𝓘nd-from-exists ind-e
  open trunc-ind-def L β h (ind-def-from-monotone-map f f-mono) ind-e
  open smallness-assumption (λ - → pr (- ∈ 𝓘nd) (holds-is-prop (- ∈ₚ 𝓘nd)))

  TarskiLFP-from-predicative : has-least-fixed-point L f
  TarskiLFP-from-predicative
   = transport (has-least-fixed-point L)
      (dfunext fe (local-ind-def-is-section-of-Γ f f-mono))
       Γ-has-least-fixed-point

\end{code}

TODO: Show TarskiLFP follows directly from propositional resizing.

This code is currently commented out. In the classic argument one would
take the infimum of pre-fixed points, then one shows that this infimum is
iteslf a fixed-point and by construction the least such. In the process of
it is fixed we need to use the set of pre-fixed points is closed under the
monotone map, etc.

Unfortunately, the type of pre-fixed is not "small", so one if forced tp
consider the pre-fixed points from the basis. Unfortunately, this type is
not closed under the monotone map, as the monotone map is not closed under
the basis. So we must proceed in another direction.

Main Idea: Use properties of the basis for infimum analgous to those for
supremum

 1) if A ⊆ B the ⋀ B ≤ ⋀ A↑ 
 2) (⋀ A) = A and ⋀ ( ↑ a) = a

these properties aren't currently formalized and there is no guarentee that
they are sufficient to complete the proof.

begin{code}

module _ {L : Sup-Lattice 𝓤 𝓦 𝓥} {B : 𝓥 ̇}
         (β : B → ⟨ L ⟩) (h : is-basis L β)
         (f : ⟨ L ⟩ → ⟨ L ⟩)
         (f-mono : is-monotone-endomap L f)
       where

 _≤⟨small⟩_ : ⟨ L ⟩ → ⟨ L ⟩ → 𝓥 ̇
 x ≤⟨small⟩ y = resize pr ((x ≤⟨ L ⟩ y) holds) (holds-is-prop (x ≤⟨ L ⟩ y))

 TarskiLFP : (f : ⟨ L ⟩ → ⟨ L ⟩)
           → is-monotone-endomap L f
           → has-least-fixed-point L f
 TarskiLFP f f-mono = (fix-f , {!!} , {!!})
  where
   L-inf-lat : Inf-Lattice 𝓤 𝓦 𝓥 
   L-inf-lat = inf-lattice-from-sup-lattice L β h
   fix-f : ⟨ L ⟩
   fix-f = ⋀⟨ L-inf-lat ⟩ ((Σ b ꞉ B , (f (β b) ≤⟨small⟩ β b)) , β ∘ pr₁) 
