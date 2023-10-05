Ayberk Tosun.

Started on 29 September 2023
Finished on 2 October 2023.

This module contains the definition of the Scott locale of a large and locally
small _algebraic_ dcpo, using the definition of algebraic dcpo from the
`DomainTheory` development due to Tom de Jong.

If one starts with an algebraic dcpo, one can ensure that the resulting Scott
locale is locally small by quantifying over only the basic/compact opens. This
is the difference between the construction in this module and the one in
`ScottLocale.Definition`

TODO: In the future, it would be good to call the other module something else
other than `Definition`, because it's not a very useful construction. It should
have a name conveying the fact that it's an overly general construction that is
not useful in most cases.

TODO: The construction in the module that is currently called
`ScottLocale.Definition` is almost the same things as the one here. In the
future, it might be good to refactor the common structure that they share into a
separate module, and make both of them instances of this --- or something along
these lines.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import Slice.Family
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse hiding (_⊆_)

\end{code}

We assume the existence of propositional truncations as well as function
extensionality, and we assume a universe 𝓤 over which we consider large and
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
 open DefnOfScottLocale 𝓓 𝓤 pe using (𝒪ₛ-equality; _⊆ₛ_)

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

 I = pr₁ hscb
 β = pr₁ (pr₂ hscb)

\end{code}

\begin{code}

 ℬ : Fam 𝓤 ⟨ 𝓓 ⟩∙
 ℬ = I , β

\end{code}

The order `_⊆ₖ_` is the small version of the relation that quantifies only
over the basic opens. The order `_⊆_` is the large version.

\begin{code}

 open structurally-algebraic

 _⊆ₖ_ : 𝒪ₛ → 𝒪ₛ → Ω 𝓤
 (U , _) ⊆ₖ (V , _) = Ɐ i ꞉ I , U (ℬ [ i ]) ⇒ V (ℬ [ i ])

 _⊆_ : 𝒪ₛ → 𝒪ₛ → Ω (𝓤 ⁺)
 (U , _) ⊆ (V , _) = Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , U x ⇒ V x

 ⊆ₖ-is-reflexive : is-reflexive _⊆ₖ_ holds
 ⊆ₖ-is-reflexive (U , δ) _ = id

 ⊆ₖ-is-transitive : is-transitive _⊆ₖ_ holds
 ⊆ₖ-is-transitive (U , δ) (V , ϵ) (W , ζ) p q x = q x ∘ p x

 ⊆ₖ-implies-⊆ : (𝔘 𝔙 : 𝒪ₛ) → (𝔘 ⊆ₖ 𝔙 ⇒ 𝔘 ⊆ 𝔙) holds
 ⊆ₖ-implies-⊆ 𝔘@(U , ι₁ , υ₁) 𝔙@(V , ι₂ , υ₂) φ x p =
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

 𝒪ₛ-equalityₛ : (U V : 𝒪ₛ)
              → ((i : I) → (ℬ [ i ]) ∈ₛ U  ＝ (ℬ [ i ]) ∈ₛ V)
              → U ＝ V
 𝒪ₛ-equalityₛ 𝔘@(U , (υ , ι)) 𝔙 φ =
  to-subtype-＝ (holds-is-prop ∘ is-scott-open) (dfunext fe †)
   where
    † : (x : ⟨ 𝓓 ⟩∙) → x ∈ₛ 𝔘 ＝ x ∈ₛ 𝔙
    † x = to-subtype-＝ (λ _ → being-prop-is-prop fe) ‡
     where
      foo : (𝔘 ⊆ₖ 𝔙) holds
      foo i p = transport (λ - → - holds) (φ i) p

      bar : (𝔙 ⊆ₖ 𝔘) holds
      bar i p = transport _holds (φ i ⁻¹) p

      ♣ : (x ∈ₛ 𝔘 ⇒ x ∈ₛ 𝔙) holds
      ♣ = ⊆ₖ-implies-⊆ 𝔘 𝔙 foo x

      ♠ : (x ∈ₛ 𝔙 ⇒ x ∈ₛ 𝔘) holds
      ♠ = ⊆ₖ-implies-⊆ 𝔙 𝔘 bar x

      ‡ : (x ∈ₛ 𝔘) holds ＝ (x ∈ₛ 𝔙) holds
      ‡ = pe (holds-is-prop (x ∈ₛ 𝔘)) (holds-is-prop (x ∈ₛ 𝔙)) ♣ ♠

 ⊆-is-antisymmetric : is-antisymmetric _⊆_
 ⊆-is-antisymmetric {𝔘} {𝔙} p q =
  𝒪ₛ-equality 𝔘 𝔙
   (dfunext fe λ x →
     to-subtype-＝
      (λ _ → being-prop-is-prop fe)
      (pe (holds-is-prop (x ∈ₛ 𝔘)) (holds-is-prop (x ∈ₛ 𝔙)) (p x) (q x)))

 ⊆ₖ-is-antisymmetric : is-antisymmetric _⊆ₖ_
 ⊆ₖ-is-antisymmetric {𝔘} {𝔙} p q = ⊆-is-antisymmetric † ‡
  where
   † : (𝔘 ⊆ 𝔙) holds
   † = ⊆ₖ-implies-⊆ 𝔘 𝔙 p

   ‡ : (𝔙 ⊆ 𝔘) holds
   ‡ = ⊆ₖ-implies-⊆ 𝔙 𝔘 q

 ⊆ₖ-is-partial-order : is-partial-order 𝒪ₛ _⊆ₖ_
 ⊆ₖ-is-partial-order = (⊆ₖ-is-reflexive , ⊆ₖ-is-transitive) , ⊆ₖ-is-antisymmetric

\end{code}

The top open.

\begin{code}

 ⊤ₛ : 𝒪ₛ
 ⊤ₛ = (λ _ → ⊤ {𝓤}) , υ , ι
  where
   υ : is-upwards-closed (λ _ → ⊤) holds
   υ _ _ _ _ = ⋆

   ι : is-inaccessible-by-directed-joins (λ _ → ⊤) holds
   ι (S , (∣i∣ , γ)) ⋆ = ∥∥-rec ∃-is-prop † ∣i∣
    where
     † : index S → ∃ _ ꞉ index S , ⊤ holds
     † i = ∣ i , ⋆ ∣

 ⊤ₛ-is-top : (U : 𝒪ₛ) → (U ⊆ₖ ⊤ₛ) holds
 ⊤ₛ-is-top U = λ _ _ → ⋆

\end{code}

The meet of two opens.

\begin{code}

 _∧ₛ_ : 𝒪ₛ → 𝒪ₛ → 𝒪ₛ
 (U , (υ₁ , ι₁)) ∧ₛ (V , (υ₂ , ι₂)) = (λ x → U x ∧ V x) , υ , ι
  where
   υ : is-upwards-closed (λ x → U x ∧ V x) holds
   υ x y (p₁ , p₂) q = υ₁ x y p₁ q , υ₂ x y p₂ q

   ι : is-inaccessible-by-directed-joins (λ x → U x ∧ V x) holds
   ι (S , δ) (p , q) = ∥∥-rec₂ ∃-is-prop γ (ι₁ (S , δ) p) (ι₂ (S , δ) q)
    where
     γ : Σ i ꞉ index S , U (S [ i ]) holds
       → Σ j ꞉ index S , V (S [ j ]) holds
       → ∃ k ꞉ index S , (U (S [ k ]) ∧ V (S [ k ])) holds
     γ (i , r₁) (j , r₂) = ∥∥-rec ∃-is-prop † (pr₂ δ i j)
      where
       † : Σ k₀ ꞉ index S ,
            ((S [ i ]) ⊑⟨ 𝓓 ⟩ₚ (S [ k₀ ]) ∧ (S [ j ]) ⊑⟨ 𝓓 ⟩ₚ (S [ k₀ ])) holds
         → ∃ k ꞉ index S , (U (S [ k ]) ∧ V (S [ k ])) holds
       † (k₀ , φ , ψ) =
        ∣ k₀ , υ₁ (S [ i ]) (S [ k₀ ]) r₁ φ , υ₂ (S [ j ]) (S [ k₀ ]) r₂ ψ ∣

 open Meets _⊆ₖ_

 ∧ₛ-is-meet : (U V : 𝒪ₛ) → ((U ∧ₛ V) is-glb-of ((U , V))) holds
 ∧ₛ-is-meet U V = † , ‡
  where
   † : ((U ∧ₛ V) is-a-lower-bound-of (U , V)) holds
   † = (λ _ (p , _) → p) , (λ _ (_ , q) → q)

   ‡ : ((W , _) : lower-bound (U , V)) → (W ⊆ₖ (U ∧ₛ V)) holds
   ‡ (W , p) x q = pr₁ p x q , pr₂ p x q

\end{code}

The 𝓤-join of opens.

\begin{code}

 ⋁ₛ_ : Fam 𝓤 𝒪ₛ → 𝒪ₛ
 ⋁ₛ_ S@(_ , up) = from-𝒪ₛᴿ 𝔘
  where
   open 𝒪ₛᴿ

   ⋃S : 𝓟 {𝓤} ⟨ 𝓓 ⟩∙
   ⋃S x = Ǝ i ꞉ index S , (x ∈ₛ (S [ i ])) holds

   υ : is-upwards-closed ⋃S holds
   υ x y p q = ∥∥-rec (holds-is-prop (⋃S y)) † p
    where
     † : Σ i ꞉ index S , (x ∈ₛ (S [ i ])) holds → ⋃S y holds
     † (i , r) = ∣ i , ♣ ∣
      where
       Sᵢᴿ : 𝒪ₛᴿ
       Sᵢᴿ = to-𝒪ₛᴿ (S [ i ])

       ♣ : (y ∈ₛ (S [ i ])) holds
       ♣ = pred-is-upwards-closed Sᵢᴿ x y r q

   ι : is-inaccessible-by-directed-joins ⋃S holds
   ι (T , δ) p = ∥∥-rec ∃-is-prop † p
    where
     † : Σ i ꞉ index S , ((⋁ (T , δ)) ∈ₛ (S [ i ])) holds
       → ∃ i ꞉ index T , ⋃S (T [ i ]) holds
     † (i , r) = ∥∥-rec ∃-is-prop ‡ ♠
      where

       Sᵢᴿ : 𝒪ₛᴿ
       Sᵢᴿ = to-𝒪ₛᴿ (S [ i ])

       ♠ : ∃ k ꞉ index T , pred Sᵢᴿ (T [ k ]) holds
       ♠ = pred-is-inaccessible-by-dir-joins Sᵢᴿ (T , δ) r

       ‡ : (Σ k ꞉ index T , pred Sᵢᴿ (T [ k ]) holds)
         → ∃ i ꞉ index T , ⋃S (T [ i ]) holds
       ‡ (k , q) = ∣ k , ∣ i , q ∣ ∣

   𝔘 : 𝒪ₛᴿ
   𝔘 = record
        { pred                              = ⋃S
        ; pred-is-upwards-closed            = υ
        ; pred-is-inaccessible-by-dir-joins = ι
        }

 open Joins _⊆ₖ_

 ⋁ₛ-is-join : (S : Fam 𝓤 𝒪ₛ) → ((⋁ₛ S) is-lub-of S) holds
 ⋁ₛ-is-join S = † , ‡
  where
   † : ((⋁ₛ S) is-an-upper-bound-of S) holds
   † i y p = ∣ i , p ∣

   ‡ : ((U , _) : upper-bound S) → ((⋁ₛ S) ⊆ₖ U) holds
   ‡ ((U , δ) , p) i = ∥∥-rec (holds-is-prop (U (ℬ [ i ]))) ※
    where
     ※ : Σ j ꞉ index S , ((ℬ [ i ]) ∈ₛ (S [ j ])) holds → U (ℬ [ i ]) holds
     ※ (j , q) = p j i q

\end{code}

\begin{code}

 distributivityₛ : (U : 𝒪ₛ) (S : Fam 𝓤 𝒪ₛ) → U ∧ₛ (⋁ₛ S) ＝ ⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆
 distributivityₛ U S = ⊆ₖ-is-antisymmetric † ‡
  where
   † : ((U ∧ₛ (⋁ₛ S)) ⊆ₖ (⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆)) holds
   † i (p , q) =
    ∥∥-rec (holds-is-prop ((ℬ [ i ]) ∈ₛ (⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆))) †₀ q
     where
      †₀ : Σ k ꞉ index S , ((S [ k ]) .pr₁ (ℬ [ i ])) holds
         → (⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆) .pr₁ (ℬ [ i ]) holds
      †₀ (i , r) = ∣ i , (p , r) ∣

   ‡ : ((⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆) ⊆ₖ (U ∧ₛ (⋁ₛ S))) holds
   ‡ i p = ∥∥-rec (holds-is-prop ((U ∧ₛ (⋁ₛ S)) .pr₁ (ℬ [ i ]))) ‡₀ p
    where
     ‡₀ : (Σ k ꞉ index S , ((U ∧ₛ (S [ k ])) .pr₁ (ℬ [ i ]) holds))
        → (U ∧ₛ (⋁ₛ S)) .pr₁ (ℬ [ i ]) holds
     ‡₀ (i , (q , r)) = q , ∣ i , r ∣

\end{code}

\begin{code}

 𝒪ₛ-frame-structure : frame-structure 𝓤 𝓤 𝒪ₛ
 𝒪ₛ-frame-structure = (_⊆ₖ_ , ⊤ₛ , _∧ₛ_ , ⋁ₛ_)
                    , ⊆ₖ-is-partial-order
                    , ⊤ₛ-is-top
                    , (λ (U , V) → ∧ₛ-is-meet U V)
                    , ⋁ₛ-is-join
                    , λ (U , S) → distributivityₛ U S

\end{code}

We finally define the locally small Scott locale of algebraic dcpo `𝓓`:

\begin{code}

 ScottLocale : Locale (𝓤 ⁺) 𝓤 𝓤
 ScottLocale = record { ⟨_⟩ₗ = 𝒪ₛ ; frame-str-of = 𝒪ₛ-frame-structure }

\end{code}
