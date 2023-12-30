Ayberk Tosun, 30 June 2023

This module contains a definition of the Scott locale of a dcpo, using the
definition of dcpo from the `DomainTheory` development due to Tom de Jong.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We assume the existence of propositional truncations as well as function
extensionality.

\begin{code}

module Locales.ScottLocale.Definition (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext)
                                      (𝓥  : Universe)                      where

open Universal fe
open Implication fe
open Existential pt
open Conjunction
open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓥 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓥

open PropositionalTruncation pt

\end{code}

We carry out the construction in the following submodule which is parametrised
by

  1. a dcpo `𝓓` whose (a) carrier set lives in universe `𝓤`, (b) whose relation
     lives in universe `𝓣`, and (c) whose directed joins are over families with
     index types living in universe `𝓥`.
  2. a universe `𝓦` where the Scott-open subsets are to live,
  3. an assumption that `𝓦` satisfies propositional extensionality.

\begin{code}

module DefnOfScottLocale (𝓓 : DCPO {𝓤} {𝓣}) (𝓦 : Universe) (pe : propext 𝓦) where

 open import DomainTheory.Lifting.LiftingSet pt fe 𝓦 pe
 open DefnOfScottTopology 𝓓 𝓦

\end{code}

`𝒪ₛ` is the type of 𝓦-Scott-opens over dcpo `𝓓`.

\begin{code}

 𝒪ₛ-equality : (𝔘 𝔙 : 𝒪ₛ) → _∈ₛ 𝔘 ＝ _∈ₛ 𝔙 → 𝔘 ＝ 𝔙
 𝒪ₛ-equality U V = to-subtype-＝ (holds-is-prop ∘ is-scott-open)

\end{code}

These are ordered by inclusion. The subscript `ₛ` in the symbol `⊆ₛ` is intended
be mnemonic for "Scott open".

\begin{code}

 _⊆ₛ_ : 𝒪ₛ → 𝒪ₛ → Ω (𝓤 ⊔ 𝓦)
 (U , _) ⊆ₛ (V , _) = Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , U x ⇒ V x

 ⊆ₛ-is-reflexive : is-reflexive _⊆ₛ_ holds
 ⊆ₛ-is-reflexive (U , δ) _ = id

 ⊆ₛ-is-transitive : is-transitive _⊆ₛ_ holds
 ⊆ₛ-is-transitive (U , δ) (V , ϵ) (W , ζ) p q x = q x ∘ p x

 ⊆ₛ-is-antisymmetric : is-antisymmetric _⊆ₛ_
 ⊆ₛ-is-antisymmetric {U} {V} p q =
  𝒪ₛ-equality
   U
   V
   (dfunext fe λ x → to-subtype-＝
     (λ _ → being-prop-is-prop fe)
     (pe (holds-is-prop (x ∈ₛ U)) (holds-is-prop (x ∈ₛ V)) (p x) (q x)))

 ⊆ₛ-is-partial-order : is-partial-order 𝒪ₛ _⊆ₛ_
 ⊆ₛ-is-partial-order = (⊆ₛ-is-reflexive , ⊆ₛ-is-transitive) , ⊆ₛ-is-antisymmetric

\end{code}

The top Scott open.

\begin{code}

 ⊤ₛ : 𝒪ₛ
 ⊤ₛ = (λ _ → ⊤ {𝓦}) , υ , ι
  where
   υ : is-upwards-closed (λ _ → ⊤) holds
   υ _ _ _ _ = ⋆

   ι : is-inaccessible-by-directed-joins (λ _ → ⊤) holds
   ι (S , (∣i∣ , γ)) ⋆ = ∥∥-rec ∃-is-prop † ∣i∣
    where
     † : index S → ∃ _ ꞉ index S , ⊤ holds
     † i = ∣ i , ⋆ ∣

 ⊤ₛ-is-top : (U : 𝒪ₛ) → (U ⊆ₛ ⊤ₛ) holds
 ⊤ₛ-is-top U = λ _ _ → ⋆

\end{code}

The meet of two Scott opens.

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

 open Meets _⊆ₛ_

 ∧ₛ-is-meet : (U V : 𝒪ₛ) → ((U ∧ₛ V) is-glb-of ((U , V))) holds
 ∧ₛ-is-meet U V = † , ‡
  where
   † : ((U ∧ₛ V) is-a-lower-bound-of (U , V)) holds
   † = (λ _ (p , _) → p) , (λ _ (_ , q) → q)

   ‡ : ((W , _) : lower-bound (U , V)) → (W ⊆ₛ (U ∧ₛ V)) holds
   ‡ (W , p) x q = pr₁ p x q , pr₂ p x q

\end{code}

The union of a 𝓦-family of Scott opens.

\begin{code}

 ⋁ₛ_ : Fam 𝓦 𝒪ₛ → 𝒪ₛ
 ⋁ₛ_ S = ⋃S , υ , ι
  where
   ⋃S : ⟨ 𝓓 ⟩∙ → Ω 𝓦
   ⋃S = λ x → Ǝ i ꞉ index S , pr₁ (S [ i ]) x holds

   υ : is-upwards-closed ⋃S holds
   υ x y p q = ∥∥-rec (holds-is-prop (⋃S y)) † p
    where
     † : Σ i ꞉ index S , (S [ i ]) .pr₁ x holds → ⋃S y holds
     † (i , r) = ∣ i , pr₁ (pr₂ (S [ i ])) x y r q ∣

   ι : is-inaccessible-by-directed-joins ⋃S holds
   ι (T , δ) p = ∥∥-rec ∃-is-prop † p
    where
     † : Σ i ꞉ index S , (S [ i ]) .pr₁ (⋁ (T , δ)) holds
       → ∃ k ꞉ index T , ⋃S (T [ k ]) holds
     † (i , q) = ∥∥-rec ∃-is-prop ‡ (pr₂ (pr₂ (S [ i ])) (T , δ) q)
      where
       ‡ : (Σ k ꞉ index T , (S [ i ]) .pr₁ (T [ k ]) holds)
         → ∃ k ꞉ index T , ⋃S (T [ k ]) holds
       ‡ (k , r) = ∣ k , ∣ i , r ∣ ∣

 open Joins _⊆ₛ_

 ⋁ₛ-is-join : (S : Fam 𝓦 𝒪ₛ) → ((⋁ₛ S) is-lub-of S) holds
 ⋁ₛ-is-join S = † , ‡
  where
   † : ((⋁ₛ S) is-an-upper-bound-of S) holds
   † i y p = ∣ i , p ∣

   ‡ : ((U , _) : upper-bound S) → ((⋁ₛ S) ⊆ₛ U) holds
   ‡ ((U , δ) , p) x q = ∥∥-rec (holds-is-prop (U x) ) γ q
    where
     γ : Σ i ꞉ index S , (S [ i ]) .pr₁ x holds
       → U x holds
     γ (i , r) = p i x r

\end{code}

Distributivity is trivial as this is a lattice of subsets.

\begin{code}

 distributivityₛ : (U : 𝒪ₛ) (S : Fam 𝓦 𝒪ₛ) → U ∧ₛ (⋁ₛ S) ＝ ⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆
 distributivityₛ U S = ⊆ₛ-is-antisymmetric † ‡
  where
   † : ((U ∧ₛ (⋁ₛ S)) ⊆ₛ (⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆)) holds
   † x (p , q) = ∥∥-rec (holds-is-prop ((⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆) .pr₁ x)) †₀ q
    where
     †₀ : Σ i ꞉ index S , ((S [ i ]) .pr₁ x) holds
        → (⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆) .pr₁ x holds
     †₀ (i , r) = ∣ i , (p , r) ∣

   ‡ : ((⋁ₛ ⁅ U ∧ₛ V ∣ V ε S ⁆) ⊆ₛ (U ∧ₛ (⋁ₛ S))) holds
   ‡ x p = ∥∥-rec (holds-is-prop ((U ∧ₛ (⋁ₛ S)) .pr₁ x)) ‡₀ p
    where
     ‡₀ : (Σ i ꞉ index S , ((U ∧ₛ (S [ i ])) .pr₁ x holds))
        → (U ∧ₛ (⋁ₛ S)) .pr₁ x holds
     ‡₀ (i , (q , r)) = q , ∣ i , r ∣

\end{code}

We now have everything we need to write down the Scott locale of `𝓓`.

\begin{code}

 𝒪ₛ-frame-structure : frame-structure (𝓤 ⊔ 𝓦) 𝓦 𝒪ₛ
 𝒪ₛ-frame-structure = (_⊆ₛ_ , ⊤ₛ , _∧ₛ_ , ⋁ₛ_) , ⊆ₛ-is-partial-order
                    , ⊤ₛ-is-top
                    , (λ (U , V) → ∧ₛ-is-meet U V)
                    , ⋁ₛ-is-join
                    , λ (U , S) → distributivityₛ U S

 ScottLocale : Locale (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓦) 𝓦
 ScottLocale = record { ⟨_⟩ₗ = 𝒪ₛ ; frame-str-of = 𝒪ₛ-frame-structure }

\end{code}

For clarity, we define the special case of `ScottLocale` for the large and
locally small case.

\begin{code}

module DefnOfScottLocaleLocallySmallCase (𝓓  : DCPO {𝓥 ⁺} {𝓥})
                                         (pe : propext 𝓥)        where


 open DefnOfScottLocale 𝓓 𝓥 pe

 ScottLocale' : Locale (𝓥 ⁺) (𝓥 ⁺) 𝓥
 ScottLocale' = ScottLocale

\end{code}
