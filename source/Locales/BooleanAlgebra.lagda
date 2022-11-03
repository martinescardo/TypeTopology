Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.
 * Frame bases.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.BooleanAlgebra
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import UF.Subsingletons-FunExt

open AllCombinators pt fe

open import Locales.Frame pt fe

\end{code}

\section{Definition of a Boolean algebra}

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ 𝓤′′ 𝓥′′ : Universe

ba-data : {𝓤 : Universe} → (𝓥 : Universe) → 𝓤  ̇ → 𝓤 ⊔ 𝓥 ⁺  ̇
ba-data 𝓥 A = (A → A → Ω 𝓥 )  -- order
            × A               -- top element
            × (A → A → A)     -- binary meets
            × A               -- bottom element
            × (A → A → A)     -- binary joins
            × (A → A)         -- negation

\end{code}

\begin{code}

module Complementation {A : 𝓤  ̇} (iss : is-set A) (𝟎 𝟏 : A) (_⋏_ _⋎_ : A → A → A) where

 _complements_ : A → A → Ω 𝓤
 x′ complements x = (x ⋏ x′ ＝[ iss ]＝ 𝟎) ∧ (x ⋎ x′ ＝[ iss ]＝ 𝟏)

\end{code}

\begin{code}

satisfies-ba-laws : {A : 𝓤  ̇} → ba-data 𝓥 A → 𝓤 ⊔ 𝓥  ̇
satisfies-ba-laws {𝓤 = 𝓤} {𝓥 = 𝓥} {A = A} (_≤_ , 𝟏 , _⊓_ , 𝟎 , _⋎_ , ¬_) =
 Σ p ꞉ is-partial-order A _≤_ , rest p holds
  where
   open Meets (λ x y → x ≤ y)
   open Joins (λ x y → x ≤ y)

   rest : is-partial-order A _≤_ → Ω (𝓤 ⊔ 𝓥)
   rest p = β ∧ γ ∧ δ ∧ ϵ ∧ ζ
    where
     P : Poset 𝓤 𝓥
     P = A , _≤_ , p

     iss : is-set A
     iss = carrier-of-[ P ]-is-set

     open Complementation iss 𝟎 𝟏 _⊓_ _⋎_

     β : Ω (𝓤 ⊔ 𝓥)
     β = Ɐ x ∶ A , Ɐ y ∶ A , (x ⊓ y) is-glb-of (x , y)

     γ : Ω (𝓤 ⊔ 𝓥)
     γ = Ɐ x ∶ A , x ≤ 𝟏

     δ : Ω (𝓤 ⊔ 𝓥)
     δ = Ɐ x ∶ A , Ɐ y ∶ A , _is-lub-of₂_ (x ⋎ y) (x , y)

     ϵ : Ω (𝓤 ⊔ 𝓥)
     ϵ = Ɐ x ∶ A , 𝟎 ≤ x

     ζ : Ω (𝓤 ⊔ 𝓤)
     ζ = Ɐ x ∶ A , Ɐ y ∶ A , Ɐ z ∶ A , x ⊓ (y ⋎ z) ＝[ iss ]＝ (x ⊓ y) ⋎ (x ⊓ z)

     η : Ω (𝓤 ⊔ 𝓤)
     η = Ɐ x ∶ A , (¬ x) complements x

\end{code}
