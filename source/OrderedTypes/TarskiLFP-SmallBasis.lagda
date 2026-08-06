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
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import OrderedTypes.InfLattice fe pt
 hiding (⟨_⟩ ; is-monotone-endomap ; order-of ; antisymmetry-of ;
         transitivity-of)
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)

open import Slice.Family
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

  impredicative-Tarski-LFP : Propositional-resizing
                           → has-least-fixed-point L f
  impredicative-Tarski-LFP pr
   = transport (has-least-fixed-point L)
      (dfunext fe (local-ind-def-is-section-of-Γ f f-mono))
       Γ-has-least-fixed-point
   where
    open smallness-assumption (λ - → pr (- ∈ 𝓘nd) (holds-is-prop (- ∈ₚ 𝓘nd)))

\end{code}

Following a discussion with the author on the issues associated with a direct
proof of the least fixed point theorem Carlo Angiuli suggested that we consider
closing the basis under the monotone map. Unfortunately, this approach still
doesn't work because such a modified basis would not necessarily be closed
under infima; another critical fact used in the traditional proof. But, this
suggested an alternative approach to Carlo which was subsequently sketched and
explained to the author. We will formaliz the proof here.

We first consider the following subset S : B → Ω

                  S(b) ≔ (x : L) → (f x ≤ x) → (b ≤ᴮ x).

Using propositional resizing we can resize each S(b) to a proposition in 𝓥 thus
allowing us to take the supremum of its total space. We claim that

                     p ≔ ⋁ (𝕋(resized(S)) , β ∘ pr₁)
                            
is the least fixed point of f. Although the type of pre-fixed points is large
and its infimum does not necessarily exist we can show that p is the greatest
lower bound of all pre-fixed points. With this fact in hand the least fixed
point theorem follows immediately.

We start by defining the type of pre-fixed points (and observing that it is
large).

\begin{code}

 Pre-Fixed-Points : 𝓤 ⊔ 𝓦 ̇
 Pre-Fixed-Points = Σ x ꞉ ⟨ L ⟩ , ((f x ≤⟨ L ⟩ x) holds)

\end{code}

Now we define a subset of the basis that is below all pre-fixed points.

\begin{code}

 module _ (pr : Propositional-resizing) where

  open is-basis h

  S : B → 𝓤 ⊔ 𝓦 ̇
  S b = (x : ⟨ L ⟩) → (f x ≤⟨ L ⟩ x) holds → (β b ≤⟨ L ⟩ x) holds

  S-is-prop : (b : B) → is-prop (S b)
  S-is-prop b
   = Π-is-prop fe (λ x → Π-is-prop fe (λ o → holds-is-prop (β b ≤⟨ L ⟩ x)))

  S-subset : 𝓟 {𝓤 ⊔ 𝓦} B
  S-subset b = (S b , S-is-prop b)

\end{code}

This subset is also large but with propositional resizing we can resize it.

\begin{code}

  S-is-small : (b : B) → S b is 𝓥 small
  S-is-small b = pr (S b) (S-is-prop b)

  resized-S : B → 𝓥 ̇
  resized-S b = resized (S b) (S-is-small b)

  resized-S≃S : (b : B) → resized-S b ≃ S b
  resized-S≃S b = resizing-condition (S-is-small b)

  S-to-resized-S : (b : B) → S b → resized-S b
  S-to-resized-S b = ⌜ (resized-S≃S b) ⌝⁻¹

  resized-S-is-prop : (b : B) → is-prop (resized-S b)
  resized-S-is-prop b = equiv-to-prop (resized-S≃S b) (S-is-prop b)

  resized-S-subset : 𝓟 {𝓥} B
  resized-S-subset b = (resized-S b , resized-S-is-prop b)

\end{code}

The join of the resized subset, which we call p, is the least fixed point.

\begin{code}

  p : ⟨ L ⟩
  p = ⋁⟨ L ⟩ 【 β , resized-S-subset 】

  open Joins (order-of L)

  p-lub-S : (p is-lub-of 【 β , S-subset 】) holds
  p-lub-S = sup-of-small-fam-is-lub L (β ∘ pr₁)
             (𝕋 resized-S-subset , Σ-cong resized-S≃S)

  p-upper-bound-S : (p is-an-upper-bound-of 【 β , S-subset 】) holds
  p-upper-bound-S = pr₁ p-lub-S

  p-least-upperbound-S : ((u , _) : upper-bound (【 β , S-subset 】))
                       → (p ≤⟨ L ⟩ u) holds
  p-least-upperbound-S = pr₂ p-lub-S

\end{code}

To see that p is the least fixed point we need to observe that p is the greatest
lower bound of the type of pre-fixed points.

\begin{code}

  open Infs (order-of L)

  p-is-a-lower-bound : (p is-a-lower-bound-of (Pre-Fixed-Points , pr₁)) holds
  p-is-a-lower-bound (x , fx≤x)
   = p-least-upperbound-S (x , λ (b , S-holds) → S-holds x fx≤x)

  p-is-greatest-lower-bound : ((l , _) : lower-bound (Pre-Fixed-Points , pr₁))
                            → (l ≤⟨ L ⟩ p) holds
  p-is-greatest-lower-bound (l , lb)
   = transitivity-of L l (⋁⟨ L ⟩ (small-↓ᴮ l , small-↓ᴮ-inclusion l)) p
      (＝-to-≤ L (is-supᴮ' l))
       (joins-preserve-containment L β
        {λ - → (- ≤ᴮ l , ≤ᴮ-is-prop-valued)} {resized-S-subset}
         (λ b o → S-to-resized-S b (λ x fx≤x
           → transitivity-of L (β b) l x (≤ᴮ-to-≤ o) (lb (x , fx≤x)))))

  p-glb-pre-fixed-points : (p is-glb-of (Pre-Fixed-Points , pr₁)) holds
  p-glb-pre-fixed-points = (p-is-a-lower-bound , p-is-greatest-lower-bound)

\end{code}

Now it follows rather directly that p is the least fixed point.

\begin{code}

 impredicative-Tarski-LFP-update : Propositional-resizing
                                 → has-least-fixed-point L f
 impredicative-Tarski-LFP-update pr
  = (p pr , antisymmetry-of L I II , III)
  where
   I : (f (p pr) ≤⟨ L ⟩ p pr) holds
   I = p-is-greatest-lower-bound pr (f (p pr) , λ (x , fx≤x)
         → transitivity-of L (f (p pr)) (f x) x
            (f-mono (p pr) x (p-is-a-lower-bound pr (x , fx≤x))) fx≤x)
   II : (p pr ≤⟨ L ⟩ f (p pr)) holds
   II = p-is-a-lower-bound pr (f (p pr) , f-mono (f (p pr)) (p pr) I)
   III : (a : ⟨ L ⟩) → f a ＝ a → order-of L (p pr) a holds
   III a fa＝a = p-is-a-lower-bound pr (a , ＝-to-≤ L fa＝a)

