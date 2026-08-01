Ian Ray. July 25 2026.

In this file we will prove a version of Tarski's least fixed point theorem
which relies on propositional resizing (as well as a seemingly innocuous QIT)
and is valid for any large sup-lattice with a small basis.

In the traditional proof of Tarski's least fixed point theorem one would take
the infimum of pre-fixed points, then one shows that this infimum is itself a
fixed-point and by construction the least such. One crucial fact used in the
traditional argument is that the set of pre-fixed points is closed under the
monotone endomap.

Unfortunately, the type of pre-fixed points is not small, so one is forced to
consider the pre-fixed points taken from the basis:

                    Σ b ꞉ B , (f (β b) ≤ β b)

This type is not closed under the monotone endomap, because the monotone
endomap does not necessarily restrict to basis elements. So we must proceed in
another direction.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module OrderedTypes.TarskiLFP-SmallBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pr : Propositional-resizing)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe
open import OrderedTypes.InfLattice fe pt
 hiding (⟨_⟩ ; order-of ; is-monotone-endomap)

open AllCombinators pt fe
open PropositionalTruncation pt

open import OrderedTypes.PredicativeLFP pt fe pe

\end{code}

Here we are importing a file that explores a predicative version of the least
fixed point theorem which only applies for sup-lattices that are "presentable"
and monotone maps that are "inductively generated" (see the file for more
details but we attempt to recount the development here).

In PredicativeLFP we show that any monotone endomap produces a moderately
well-behaved inductive definition. We observe that (small) subsets which are
"closed" under the inductive definition correspond to pre-fixed points of the
monotone endomap. Assuming the existence of a seemingly innocuous QIT we can
then inductively generate a subset 𝓘nd of the basis closed under the inductive
definition. Now, by construction 𝓘nd is not necessarily small, but if it is, it
corresponds to the least fixed point. The remainder of PredicativeLFP explores
conditions on the sup-lattice and monotone endomap that guarantee this
smallness assumption. But with propositional resizing available we are able to
immediately satisfy this condition and as a result we get a version of Tarski's
least fixed point theorem for a large sup-lattice with small basis.

\begin{code}
    
module _ {L : Sup-Lattice 𝓤 𝓦 𝓥} {B : 𝓥 ̇}
         (β : B → ⟨ L ⟩) (h : is-basis L β)
         (f : ⟨ L ⟩ → ⟨ L ⟩)
         (f-mono : is-monotone-endomap L f)
       where

 open local-inductive-definitions L β h
 open correspondence-from-locally-small-ϕ L β h
       (ind-def-from-monotone-map f f-mono) (local-from-monotone-map f f-mono)

\end{code}

TODO. Certain QITs can be encoded using impredicativity. Is this the case for
the one assumed in the anonymous module below?

\begin{code}

 module _ (ind-e : inductively-generated-subset-exists L β h
                    (ind-def-from-monotone-map f f-mono))
        where

  open small-𝓘nd-from-exists ind-e
  open trunc-ind-def L β h (ind-def-from-monotone-map f f-mono) ind-e
  open smallness-assumption (λ - → pr (- ∈ 𝓘nd) (holds-is-prop (- ∈ₚ 𝓘nd)))

  impredicative-Tarski-LFP : has-least-fixed-point L f
  impredicative-Tarski-LFP
   = transport (has-least-fixed-point L)
      (dfunext fe (local-ind-def-is-section-of-Γ f f-mono))
       Γ-has-least-fixed-point

\end{code}

TODO: Determine whether TarskiLFP follows directly from propositional resizing.
One approach would be to construct the aforementioned QIT from propositional
resizing. 
