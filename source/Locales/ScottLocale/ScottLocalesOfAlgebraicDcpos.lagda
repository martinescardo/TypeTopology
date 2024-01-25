Ayberk Tosun.

Started  on: 29 September 2023.
Finished on: 2 October 2023.

This module contains the definition of the Scott locale of a large and locally
small dcpo with a specified small compact basis, a notion defined in Tom de
Jong's domain theory development.

If one starts with a dcpo with a specified small compact basis, one can ensure
that the resulting Scott locale is locally small by quantifying over only the
basic/compact opens. This is the difference between the construction in this
module and the one in `ScottLocale.Definition`

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse

\end{code}

We assume the existence of propositional truncations as well as function
extensionality, and we assume a universe `𝓤` over which we consider large and
locally small dcpos.

\begin{code}

module Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤  : Universe)
        where

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open import Locales.Frame pt fe

open import DomainTheory.Basics.Dcpo                   pt fe 𝓤 renaming
                                                                (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology        pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases      pt fe 𝓤

open import Locales.ScottLocale.Definition pt fe 𝓤

open Locale

open PropositionalTruncation pt

\end{code}

The construction is carried out over a large and locally small dcpo `𝓓` equipped
with a small compact basis. Because the type of small compact bases for large
and locally small dcpos has _split support_, the construction can also be
carried out without assuming a specified small compact basis.

TODO: use the following module to do the same construction with only the
truncation of the basis in consideration.

\begin{code}

module ScottLocaleConstruction (𝓓    : DCPO {𝓤 ⁺} {𝓤})
                               (hscb : has-specified-small-compact-basis 𝓓)
                               (pe   : propext 𝓤)                          where

 open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
 open DefnOfScottTopology 𝓓 𝓤
 open DefnOfScottLocale 𝓓 𝓤 pe using (𝒪ₛ-equality; _⊆ₛ_; ⊆ₛ-is-reflexive;
                                      ⊆ₛ-is-transitive; ⊆ₛ-is-antisymmetric;
                                      ⊤ₛ; ⊤ₛ-is-top; _∧ₛ_; ∧ₛ-is-meet;
                                      distributivityₛ; ⋁ₛ_; ⋁ₛ-is-join)
                               renaming (ScottLocale to ScottLocale′)

\end{code}

We denote by `𝕒` the fact that the dcpo `𝓓` in consideration is _structurally
algebraic_.

\begin{code}

 𝕒 : structurally-algebraic 𝓓
 𝕒 = structurally-algebraic-if-specified-small-compact-basis 𝓓 hscb

\end{code}

We denote by `I` the index type of the basis and by `β` its enumeration
function.

\begin{code}

 I = index-of-compact-basis 𝓓 hscb
 β = family-of-basic-opens  𝓓 hscb

\end{code}

\begin{code}

 ℬ : Fam 𝓤 ⟨ 𝓓 ⟩∙
 ℬ = I , β

\end{code}

The order `_⊆ₖ_` is the small version of the relation that quantifies only over
the basic opens. The order `_⊆ₛ_` is the large version.

\begin{code}

 open structurally-algebraic

 _⊆ₖ_ : 𝒪ₛ → 𝒪ₛ → Ω 𝓤
 (U , _) ⊆ₖ (V , _) = Ɐ i ꞉ I , U (ℬ [ i ]) ⇒ V (ℬ [ i ])

 ⊆ₖ-implies-⊆ₛ : (𝔘 𝔙 : 𝒪ₛ) → (𝔘 ⊆ₖ 𝔙 ⇒ 𝔘 ⊆ₛ 𝔙) holds
 ⊆ₖ-implies-⊆ₛ 𝔘@(U , ι₁ , υ₁) 𝔙@(V , ι₂ , υ₂) φ x p =
  transport (λ - → (- ∈ₛ 𝔙) holds) (eq ⁻¹) †
   where
    S : Fam 𝓤 ⟨ 𝓓 ⟩∙
    S = index-of-compact-family 𝕒 x , compact-family 𝕒 x

    S↑ : Fam↑
    S↑ = S , compact-family-is-directed 𝕒 x

    eq : x ＝ ⋁ S↑
    eq = compact-family-∐-＝ 𝕒 x ⁻¹

    p′ : ((⋁ S↑) ∈ₛ 𝔘) holds
    p′ = transport (λ - → (- ∈ₛ 𝔘) holds) eq p

    † : ((⋁ S↑) ∈ₛ 𝔙) holds
    † = ∥∥-rec (holds-is-prop ((⋁ S↑) ∈ₛ 𝔙)) ‡ (υ₁ S↑ p′)
     where
      ‡ : Σ i ꞉ index S , ((S [ i ]) ∈ₛ 𝔘) holds → ((⋁ S↑) ∈ₛ 𝔙) holds
      ‡ (i , q) = ι₂ (S [ i ]) (⋁ S↑) r (⋁-is-upperbound S↑ i)
       where
        r : ((S [ i ]) ∈ₛ 𝔙) holds
        r = φ (pr₁ i) q

 ⊆ₛ-implies-⊆ₖ : (𝔘 𝔙 : 𝒪ₛ) → (𝔘 ⊆ₛ 𝔙 ⇒ 𝔘 ⊆ₖ 𝔙) holds
 ⊆ₛ-implies-⊆ₖ 𝔘 𝔙 p = p ∘ (ℬ [_])

 ⊆ₛ-iff-⊆ₖ : (𝔘 𝔙 : 𝒪ₛ) → (𝔘 ⊆ₛ 𝔙 ⇔ 𝔘 ⊆ₖ 𝔙) holds
 ⊆ₛ-iff-⊆ₖ 𝔘 𝔙 = ⊆ₛ-implies-⊆ₖ 𝔘 𝔙 , ⊆ₖ-implies-⊆ₛ 𝔘 𝔙

 ⊆ₖ-is-reflexive : is-reflexive _⊆ₖ_ holds
 ⊆ₖ-is-reflexive 𝔘@(U , δ) = ⊆ₛ-implies-⊆ₖ 𝔘 𝔘 (⊆ₛ-is-reflexive 𝔘)

 ⊆ₖ-is-transitive : is-transitive _⊆ₖ_ holds
 ⊆ₖ-is-transitive 𝔘@(U , δ) 𝔙@(V , ϵ) 𝔚@(W , ζ) p q = ⊆ₛ-implies-⊆ₖ 𝔘 𝔚 †
  where
   † : (𝔘 ⊆ₛ 𝔚) holds
   † = ⊆ₛ-is-transitive 𝔘 𝔙 𝔚 (⊆ₖ-implies-⊆ₛ 𝔘 𝔙 p) (⊆ₖ-implies-⊆ₛ 𝔙 𝔚 q)

 ⊆ₖ-is-antisymmetric : is-antisymmetric _⊆ₖ_
 ⊆ₖ-is-antisymmetric {𝔘} {𝔙} p q = ⊆ₛ-is-antisymmetric † ‡
  where
   † : (𝔘 ⊆ₛ 𝔙) holds
   † = ⊆ₖ-implies-⊆ₛ 𝔘 𝔙 p

   ‡ : (𝔙 ⊆ₛ 𝔘) holds
   ‡ = ⊆ₖ-implies-⊆ₛ 𝔙 𝔘 q

 ⊆ₖ-is-partial-order : is-partial-order 𝒪ₛ _⊆ₖ_
 ⊆ₖ-is-partial-order = (⊆ₖ-is-reflexive , ⊆ₖ-is-transitive) , ⊆ₖ-is-antisymmetric

\end{code}

The top open.

\begin{code}

 ⊤ₛ-is-top-wrt-⊆ₖ : (𝔘 : 𝒪ₛ) → (𝔘 ⊆ₖ ⊤ₛ) holds
 ⊤ₛ-is-top-wrt-⊆ₖ 𝔘 = ⊆ₛ-implies-⊆ₖ 𝔘 ⊤ₛ (⊤ₛ-is-top 𝔘)

\end{code}

The meet of two opens.

\begin{code}

 open Meets _⊆ₖ_

 ∧ₛ-is-meet-wrt-⊆ₖ : (𝔘 𝔙 : 𝒪ₛ) → ((𝔘 ∧ₛ 𝔙) is-glb-of (𝔘 , 𝔙)) holds
 ∧ₛ-is-meet-wrt-⊆ₖ 𝔘 𝔙 = † , ‡
  where
   † : ((𝔘 ∧ₛ 𝔙) is-a-lower-bound-of (𝔘 , 𝔙)) holds
   † = ⊆ₛ-implies-⊆ₖ (𝔘 ∧ₛ 𝔙) 𝔘 (∧[ 𝒪 ScottLocale′ ]-lower₁ 𝔘 𝔙)
     , ⊆ₛ-implies-⊆ₖ (𝔘 ∧ₛ 𝔙) 𝔙 (∧[ 𝒪 ScottLocale′ ]-lower₂ 𝔘 𝔙)

   ‡ : ((W , _) : lower-bound (𝔘 , 𝔙)) → (W ⊆ₖ (𝔘 ∧ₛ 𝔙)) holds
   ‡ (𝔚 , p , q) =
    ⊆ₛ-implies-⊆ₖ 𝔚 (𝔘 ∧ₛ 𝔙) (∧[ 𝒪 ScottLocale′ ]-greatest 𝔘 𝔙 𝔚 ♣ ♠)
     where
      ♣ : (𝔚 ⊆ₛ 𝔘) holds
      ♣ = ⊆ₖ-implies-⊆ₛ 𝔚 𝔘 p

      ♠ : (𝔚 ⊆ₛ 𝔙) holds
      ♠ = ⊆ₖ-implies-⊆ₛ 𝔚 𝔙 q

\end{code}

The 𝓤-join of opens.

\begin{code}

 open Joins _⊆ₖ_

 ⋁ₛ-is-join-wrt-⊆ₖ : (S : Fam 𝓤 𝒪ₛ) → ((⋁ₛ S) is-lub-of S) holds
 ⋁ₛ-is-join-wrt-⊆ₖ S = † , ‡
  where
   † : ((⋁ₛ S) is-an-upper-bound-of S) holds
   † i = ⊆ₛ-implies-⊆ₖ (S [ i ]) (⋁ₛ S) (⋁[ 𝒪 ScottLocale′ ]-upper S i)

   ‡ : ((U , _) : upper-bound S) → ((⋁ₛ S) ⊆ₖ U) holds
   ‡ (𝔘 , p) = ⊆ₛ-implies-⊆ₖ (⋁ₛ S) 𝔘 ((⋁[ 𝒪 ScottLocale′ ]-least S (𝔘 , ※)))
    where
     ※ : (i : index S) → ((S [ i ]) ⊆ₛ 𝔘) holds
     ※ i = ⊆ₖ-implies-⊆ₛ (S [ i ]) 𝔘 (p i)

\end{code}

\begin{code}

 𝒪ₛ-frame-structure : frame-structure 𝓤 𝓤 𝒪ₛ
 𝒪ₛ-frame-structure = (_⊆ₖ_ , ⊤ₛ , _∧ₛ_ , ⋁ₛ_)
                    , ⊆ₖ-is-partial-order
                    , ⊤ₛ-is-top-wrt-⊆ₖ
                    , (λ (U , V) → ∧ₛ-is-meet-wrt-⊆ₖ U V)
                    , ⋁ₛ-is-join-wrt-⊆ₖ
                    , λ (U , S) → distributivityₛ U S

\end{code}

We finally define the locally small Scott locale of algebraic dcpo `𝓓`:

\begin{code}

 ScottLocale : Locale (𝓤 ⁺) 𝓤 𝓤
 ScottLocale = record { ⟨_⟩ₗ = 𝒪ₛ ; frame-str-of = 𝒪ₛ-frame-structure }

\end{code}
