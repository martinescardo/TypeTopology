---
title:         Isomorphisms of distributive lattices
author:        Ayberk Tosun
date-started:  2024-04-24
dates-updated: [2024-06-17, 2024-05-30, 2024-06-01]
---

This module contains the definition of the notion of distributive lattice
isomorphism.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.DistributiveLattice.Isomorphism
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Adjunctions.Properties pt fe
open import Locales.Adjunctions.Properties-DistributiveLattice pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import Locales.PosetalAdjunction pt fe
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_)

\end{code}

We work in a module parameterized by a 𝓤-distributive-lattice `L₁` and a
𝓥-distributive-lattice `L₂`.

\begin{code}

module DistributiveLatticeIsomorphisms (L₁ : DistributiveLattice 𝓤)
                                       (L₂ : DistributiveLattice 𝓥) where

\end{code}

The type `Isomorphismᵈᵣ L₁ L₂`, defined below, is the type of isomorphisms
between distributive lattices `L₁` and `L₂`.

\begin{code}

 record Isomorphismᵈᵣ : (𝓤 ⊔ 𝓥) ⁺ ̇ where
  field
   𝓈 : L₁ ─d→ L₂
   𝓇 : L₂ ─d→ L₁

  s : ∣ L₁ ∣ᵈ → ∣ L₂ ∣ᵈ
  s = Homomorphismᵈᵣ.h 𝓈

  r : ∣ L₂ ∣ᵈ → ∣ L₁ ∣ᵈ
  r = Homomorphismᵈᵣ.h 𝓇

  s-is-homomorphism : is-homomorphismᵈ L₁ L₂ s holds
  s-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓈

  r-is-homomorphism : is-homomorphismᵈ L₂ L₁ r holds
  r-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism 𝓇

  field
   r-cancels-s : r ∘ s ∼ id
   s-cancels-r : s ∘ r ∼ id

\end{code}

Added on 2024-05-30.

Lemma for showing the equality two distributive lattice isomorphisms.

\begin{code}

 open Isomorphismᵈᵣ

 to-isomorphismᵈᵣ-＝ : (𝒾 𝒿 : Isomorphismᵈᵣ) → s 𝒾 ∼ s 𝒿 → r 𝒾 ∼ r 𝒿 → 𝒾 ＝ 𝒿
 to-isomorphismᵈᵣ-＝ 𝒾 𝒿 φ ψ = † p q
  where
   open DistributiveLattice

   p : 𝓈 𝒾 ＝ 𝓈 𝒿
   p = to-homomorphismᵈ-＝ L₁ L₂ (𝓈 𝒾) (𝓈 𝒿) φ

   q : 𝓇 𝒾 ＝ 𝓇 𝒿
   q = to-homomorphismᵈ-＝ L₂ L₁ (𝓇 𝒾) (𝓇 𝒿) ψ

   g : (r 𝒾 ∘ s 𝒾) ∼ id → (s 𝒾 ∘ r 𝒾) ∼ id → Isomorphismᵈᵣ
   g e₁ e₂ = record { 𝓈 = 𝓈 𝒾 ; 𝓇 = 𝓇 𝒾 ; r-cancels-s = e₁ ; s-cancels-r = e₂}

   f : 𝓈 𝒾 ＝ 𝓈 𝒿 → 𝓇 𝒾 ＝ 𝓇 𝒿 → Isomorphismᵈᵣ
   f refl refl =
    record
     { 𝓈           = 𝓈 𝒾
     ; 𝓇           = 𝓇 𝒾
     ; r-cancels-s = r-cancels-s 𝒾
     ; s-cancels-r = s-cancels-r 𝒾
    }

   † : 𝓈 𝒾 ＝ 𝓈 𝒿 → 𝓇 𝒾 ＝ 𝓇 𝒿 → 𝒾 ＝ 𝒿
   † refl refl = ap₂ g β γ
    where
     β : r-cancels-s 𝒾 ＝ r-cancels-s 𝒿
     β = Π-is-prop fe (λ _ → X-is-set L₁) (r-cancels-s 𝒾) (r-cancels-s 𝒿)

     γ : s-cancels-r 𝒾 ＝ s-cancels-r 𝒿
     γ = Π-is-prop fe (λ _ → X-is-set L₂) (s-cancels-r 𝒾) (s-cancels-r 𝒿)

\end{code}

End of addition.

Pretty syntax for `Isomorphismᵈᵣ`.

\begin{code}

Isomorphismᵈᵣ-Syntax : DistributiveLattice 𝓤
                     → DistributiveLattice 𝓥
                     → (𝓤 ⊔ 𝓥) ⁺ ̇
Isomorphismᵈᵣ-Syntax K L = DistributiveLatticeIsomorphisms.Isomorphismᵈᵣ K L

infix 0 Isomorphismᵈᵣ-Syntax
syntax Isomorphismᵈᵣ-Syntax K L = K ≅d≅ L

\end{code}

Added on 2024-05-17.

We now give an alternative definition of the notion of distributive lattice
homomorphism: an equivalence whose both sides are monotone.

\begin{code}

module HomomorphicEquivalences (K : DistributiveLattice 𝓤)
                               (L : DistributiveLattice 𝓤) where

 is-homomorphic : (∣ K ∣ᵈ ≃ ∣ L ∣ᵈ) → Ω 𝓤
 is-homomorphic e =  is-monotonic (poset-ofᵈ K) (poset-ofᵈ L) ⌜ e   ⌝
                  ∧ₚ is-monotonic (poset-ofᵈ L) (poset-ofᵈ K) ⌜ e⁻¹ ⌝
  where
   e⁻¹ : ∣ L ∣ᵈ ≃ ∣ K ∣ᵈ
   e⁻¹ = ≃-sym e

\end{code}

We denote by `Isomorphism₀` the type of isomorphisms given via this alternative
definition.

\begin{code}

 Isomorphism₀ : 𝓤 ̇
 Isomorphism₀ = Σ e ꞉ ∣ K ∣ᵈ ≃ ∣ L ∣ᵈ , is-homomorphic e holds

\end{code}

We now prove that this is equivalent to the categorical definition.

The part of the equivalence going from `Isomorphismᵈᵣ K L` to
`Isomorphism₀` is easy.

\begin{code}

 open DistributiveLatticeIsomorphisms
 open Some-Properties-Of-Posetal-Adjunctions

 open Properties-Of-Posetal-Adjunctions-on-Distributive-Lattices

 to-isomorphism₀ : Isomorphismᵈᵣ K L → Isomorphism₀
 to-isomorphism₀ 𝒾 = e , 𝒽
  where
   open Isomorphismᵈᵣ 𝒾
    using (s; 𝓈; 𝓇; r; s-cancels-r; r-cancels-s; s-is-homomorphism)
   open Homomorphismᵈᵣ 𝓈
    using ()
    renaming (h-preserves-∧ to 𝓈-preserves-∧; h-is-monotone to 𝓈-is-monotone)
   open Homomorphismᵈᵣ 𝓇
    using ()
    renaming (h-is-monotone to 𝓇-is-monotone)
   open DistributiveLattice K
    using ()
    renaming (_∧_ to _∧₁_)
   open DistributiveLattice L
    using ()
    renaming (_∧_ to _∧₂_)

   e : ∣ K ∣ᵈ ≃ ∣ L ∣ᵈ
   e = s , qinvs-are-equivs s (r , r-cancels-s , s-cancels-r)

   𝒽 : is-homomorphic e holds
   𝒽 = 𝓈-is-monotone , 𝓇-is-monotone

\end{code}

We now address the other direction.

Both parts of an equivalence are both a left adjoint and a right adjoint.
Therefore, they preserve finite meets and finite joins.

\begin{code}

 open AdjointFunctorTheorem
 open PosetalAdjunctionBetween (poset-ofᵈ L) (poset-ofᵈ K) renaming (_⊣_ to _⊣₁_)
 open PosetalAdjunctionBetween (poset-ofᵈ K) (poset-ofᵈ L) renaming (_⊣_ to _⊣₂_)

 to-isomorphismᵈᵣ : Isomorphism₀ → Isomorphismᵈᵣ K L
 to-isomorphismᵈᵣ (e , (μ₁ , μ₂)) =
  record
   { 𝓈           = 𝓈
   ; 𝓇           = 𝓇
   ; r-cancels-s = inverses-are-retractions' e
   ; s-cancels-r = inverses-are-sections' e
  }
    where
     open DistributiveLattice L using () renaming (𝟏 to 𝟏L; 𝟎 to 𝟎L)
     open DistributiveLattice K using () renaming (𝟏 to 𝟏K; 𝟎 to 𝟎K)

\end{code}

We have the monotone equivalence `e`, the forward and backward components of
which we denote by `s` and `r`:

\begin{code}

     s = ⌜ e ⌝
     r = ⌜ ≃-sym e ⌝

\end{code}

We denote by `sₘ` and `rₘ`, the versions of these packaged up with the proofs
that they are monotone.

\begin{code}

     sₘ : poset-ofᵈ K ─m→ poset-ofᵈ L
     sₘ = s , μ₁

     rₘ : poset-ofᵈ L ─m→ poset-ofᵈ K
     rₘ = r , μ₂

\end{code}

The map `s` is the left adjoint of `r` and vice versa.

\begin{code}

     𝒶𝒹𝒿 : (rₘ ⊣₁ sₘ) holds
     𝒶𝒹𝒿 = monotone-equivalences-are-adjoint
            (poset-ofᵈ L)
            (poset-ofᵈ K)
            rₘ
            sₘ
            (inverses-are-retractions' e)
            (inverses-are-sections' e)


     𝒶𝒹𝒿' : (sₘ ⊣₂ rₘ) holds
     𝒶𝒹𝒿' = monotone-equivalences-are-adjoint
             (poset-ofᵈ K)
             (poset-ofᵈ L)
             sₘ
             rₘ
             (inverses-are-sections' e)
             (inverses-are-retractions' e)

\end{code}

Because `r` is a right adjoint, it preserves `𝟏`.

\begin{code}

     α₁ : preserves-𝟏 K L s holds
     α₁ = right-adjoint-preserves-𝟏 L K rₘ sₘ 𝒶𝒹𝒿

\end{code}

Because `s` is a right adjoint, it preserves binary meets.

\begin{code}

     β₁ : preserves-∧ K L s holds
     β₁ = right-adjoint-preserves-∧ L K rₘ sₘ 𝒶𝒹𝒿

\end{code}

Because `s` is a left adjoint, it preserves the bottom element `𝟎`.

\begin{code}

     γ₁ : preserves-𝟎 K L s holds
     γ₁ = left-adjoint-preserves-𝟎 K L sₘ rₘ 𝒶𝒹𝒿'

\end{code}

Because `s` is a left adjoint, it preserves binary joins.

\begin{code}

     δ₁ : preserves-∨ K L s holds
     δ₁ = left-adjoint-preserves-∨ K L sₘ rₘ 𝒶𝒹𝒿'

\end{code}

Because `r` is a right adjoint, it preserves the top element `𝟏`.

\begin{code}

     α₂ : preserves-𝟏 L K r holds
     α₂ = right-adjoint-preserves-𝟏 K L sₘ rₘ 𝒶𝒹𝒿'

\end{code}

Because `r` is a right adjoint, it preserves binary meets.

\begin{code}

     β₂ : preserves-∧ L K r holds
     β₂ = right-adjoint-preserves-∧ K L sₘ rₘ 𝒶𝒹𝒿'

\end{code}

Because `r` is a left adjoint, it preserves the bottom element `𝟎`.

\begin{code}

     γ₂ : preserves-𝟎 L K r holds
     γ₂ = left-adjoint-preserves-𝟎 L K rₘ sₘ 𝒶𝒹𝒿

\end{code}

Because `r` is a left adjoint, it preserves binary joins.

\begin{code}

     δ₂ : preserves-∨ L K r holds
     δ₂ = left-adjoint-preserves-∨ L K rₘ sₘ 𝒶𝒹𝒿

\end{code}

Finally, we package everything up into the distributive lattice homomorphism
type.

\begin{code}

     𝓈 : Homomorphismᵈᵣ K L
     𝓈 = record
          { h                 = s
          ; h-is-homomorphism = α₁ , β₁ , γ₁ , δ₁}

     𝓇 : Homomorphismᵈᵣ L K
     𝓇 = record
          { h                 = r
          ; h-is-homomorphism = α₂ , β₂ , γ₂ , δ₂
         }

\end{code}

The actual proof that these form an equivalence is trivial.

\begin{code}

 isomorphismᵈᵣ-is-equivalent-to-isomorphism₀ : Isomorphism₀ ≃ Isomorphismᵈᵣ K L
 isomorphismᵈᵣ-is-equivalent-to-isomorphism₀ =
  to-isomorphismᵈᵣ , qinvs-are-equivs to-isomorphismᵈᵣ (to-isomorphism₀ , † , ‡)
  where
   † : to-isomorphism₀ ∘ to-isomorphismᵈᵣ ∼ id
   † 𝒾@(e , μ₁ , μ₂) =
    to-subtype-＝
     (holds-is-prop ∘ is-homomorphic)
     (to-subtype-＝ (being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥})) refl)

   ‡ : to-isomorphismᵈᵣ ∘ to-isomorphism₀ ∼ id
   ‡ 𝒾 = to-isomorphismᵈᵣ-＝
          K
          L
          (to-isomorphismᵈᵣ (to-isomorphism₀ 𝒾))
          𝒾
          (λ _ → refl)
          (λ _ → refl)

\end{code}

Added on 2024-06-01.

We define the identity homomorphism on a distributive lattice.

The identity function preserves the bottom element.

\begin{code}

id-preserves-bottom : (L : DistributiveLattice 𝓤) → preserves-𝟎 L L id holds
id-preserves-bottom _ = refl

\end{code}

The identity function preserves the top element definitionally.

\begin{code}

id-preserves-top : (L : DistributiveLattice 𝓤) → preserves-𝟏 L L id holds
id-preserves-top _ = refl

\end{code}

The identity function preserves the meets definitionally.

\begin{code}

id-preserves-meets : (L : DistributiveLattice 𝓤) → preserves-∧ L L id holds
id-preserves-meets _ _ _ = refl

\end{code}

The identity function preserves the joins definitionally.

\begin{code}

id-preserves-joins : (L : DistributiveLattice 𝓤) → preserves-∨ L L id holds
id-preserves-joins _ _ _ = refl

\end{code}

We package up these into the proof that `id` is a homomorphism.

\begin{code}

id-is-homomorphism : (L : DistributiveLattice 𝓤) → is-homomorphismᵈ L L id holds
id-is-homomorphism L = id-preserves-top L
                     , id-preserves-meets L
                     , id-preserves-bottom L
                     , id-preserves-joins L

\end{code}

We package up the identity function together with the proof that it is a
homomorphism and denote it `𝔦𝔡`.

\begin{code}

𝔦𝔡 : (L : DistributiveLattice 𝓤) → L ─d→ L
𝔦𝔡 L = record { h = id ; h-is-homomorphism = id-is-homomorphism L}

\end{code}
