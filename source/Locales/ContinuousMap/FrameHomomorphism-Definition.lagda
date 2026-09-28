--------------------------------------------------------------------------------
title:          Frame homomorphisms
author:         Ayberk Tosun
date-started:   2024-04-10
--------------------------------------------------------------------------------

Originally written as part of Ayberk Tosun's MSc thesis on 2020-02-23.

Ported to TypeTopology as part of the `Locales.Frame` module on 2021-03-09.

Factored out from the `Locales.Frame` module into this module on 2024-04-10.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.FrameHomomorphism-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import Slice.Family
open import UF.Equiv
open import UF.Logic
open import UF.Sets
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We work in a module parameterized by two frames.

\begin{code}

module FrameHomomorphisms (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤' 𝓥' 𝓦) where

\end{code}

We denote by `σ` the proof that the carrier of frame `G` is a set.

\begin{code}

 private
  σ : is-set ⟨ G ⟩
  σ = carrier-of-[ poset-of G ]-is-set

\end{code}

The following predicate expresses what it means for a function between frames to
preserve the top element.

\begin{code}

 preserves-top : (⟨ F ⟩ → ⟨ G ⟩) → Ω 𝓤'
 preserves-top h = h 𝟏[ F ] ＝[ σ ]＝ 𝟏[ G ]

\end{code}

The following predicate expresses what it means for a function between frames
to preserve binary meets.

\begin{code}

 preserves-binary-meets : (⟨ F ⟩ → ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓤')
 preserves-binary-meets h =
  Ɐ x ꞉ ⟨ F ⟩ , Ɐ y ꞉ ⟨ F ⟩ , h (x ∧[ F ] y) ＝[ σ ]＝ h x ∧[ G ] h y

\end{code}

The following predicate expresses what it means for a function between frames
to preserve the small joins.

\begin{code}

 open Joins (λ x y → x ≤[ poset-of G ] y)

 preserves-joins : (⟨ F ⟩ → ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥' ⊔ 𝓦 ⁺)
 preserves-joins h = Ɐ S ꞉ Fam 𝓦 ⟨ F ⟩ , h (⋁[ F ] S) is-lub-of ⁅ h x ∣ x ε S ⁆

\end{code}

We package these up into a predicate that express the notion of frame
homomorphism: a function that preserves finite meets, and the small joins.

\begin{code}

 is-a-frame-homomorphism : (⟨ F ⟩ → ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤' ⊔ 𝓥')
 is-a-frame-homomorphism h = α ∧ β ∧ γ
  where
   α = preserves-top h
   β = preserves-binary-meets h
   γ = preserves-joins h

\end{code}

Using this, we write down the type of frame homomorphisms between two frames.

\begin{code}

 _─f→_ : 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤' ⊔ 𝓥' ̇
 _─f→_ = Σ f ꞉ (⟨ F ⟩ → ⟨ G ⟩) , is-a-frame-homomorphism f holds

\end{code}

We denote by `fun 𝒽` the underlying function of a frame homomorphism `𝒽`.

\begin{code}

 fun : _─f→_ → ⟨ F ⟩ → ⟨ G ⟩
 fun (h , _) = h

 infixr 3 fun

 syntax fun f x = f $ x

 fun-is-a-frame-homomorphism : (h : _─f→_)
                             → is-a-frame-homomorphism (fun h) holds
 fun-is-a-frame-homomorphism (_ , φ) = φ

\end{code}

We also write down a record-based version of the same type and prove their
equivalence.

\begin{code}

 record _─f·→_ : 𝓤 ⊔ 𝓤' ⊔ 𝓥' ⊔ 𝓦 ⁺ ̇ where
  field
   h : ⟨ F ⟩ → ⟨ G ⟩

   h-preserves-top   : preserves-top h holds
   h-preserves-meets : preserves-binary-meets h holds
   h-preserves-joins : preserves-joins h holds

 frame-homomorphism-to-frame-homomorphismᵣ : _─f→_ → _─f·→_
 frame-homomorphism-to-frame-homomorphismᵣ (h , α , β , γ) =
  record
   { h                 = h
   ; h-preserves-top   = α
   ; h-preserves-meets = β
   ; h-preserves-joins = γ
  }

 frame-homomorphismᵣ-to-frame-homomorphism : _─f·→_ → _─f→_
 frame-homomorphismᵣ-to-frame-homomorphism 𝒽 =
  let
   open _─f·→_ 𝒽
  in
   h , h-preserves-top , h-preserves-meets , h-preserves-joins

 frame-homomorphism-equiv-to-frame-homomorphismᵣ : _─f→_ ≃ _─f·→_
 frame-homomorphism-equiv-to-frame-homomorphismᵣ =
  s , (r , †) , r , ‡
   where
    s : _─f→_ → _─f·→_
    s = frame-homomorphism-to-frame-homomorphismᵣ

    r : _─f·→_ → _─f→_
    r = frame-homomorphismᵣ-to-frame-homomorphism

    † : (s ∘ r) ∼ id
    † _ = refl

    ‡ : (r ∘ s) ∼ id
    ‡ _ = refl

\end{code}

For convenience, we also define some direct projections on the Σ-based type.

\begin{code}

 frame-homomorphisms-preserve-top : (h : _─f→_)
                                  → preserves-top (fun h) holds
 frame-homomorphisms-preserve-top 𝒽 =
  let
   open _─f·→_ (frame-homomorphism-to-frame-homomorphismᵣ 𝒽)
  in
   h-preserves-top

 frame-homomorphisms-preserve-meets : (h : _─f→_)
                                    → preserves-binary-meets (fun h) holds
 frame-homomorphisms-preserve-meets 𝒽 =
  let
   open _─f·→_ (frame-homomorphism-to-frame-homomorphismᵣ 𝒽)
  in
   h-preserves-meets

 frame-homomorphisms-preserve-all-joins : (h : _─f→_)
                                        → preserves-joins (fun h) holds
 frame-homomorphisms-preserve-all-joins 𝒽 =
  let
   open _─f·→_ (frame-homomorphism-to-frame-homomorphismᵣ 𝒽)
  in
   h-preserves-joins

 frame-homomorphisms-preserve-all-joins′
  : (h : _─f→_)
  → (S : Fam 𝓦 ⟨ F ⟩)
  → h $ (⋁[ F ] S) ＝ ⋁[ G ] ⁅ h $ x ∣ x ε S ⁆
 frame-homomorphisms-preserve-all-joins′ h S =
  ⋁[ G ]-unique
   ⁅ h $ x ∣ x ε S ⁆
   (h $ (⋁[ F ] S))
   (frame-homomorphisms-preserve-all-joins h S)

\end{code}
