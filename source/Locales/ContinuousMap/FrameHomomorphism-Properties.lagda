--------------------------------------------------------------------------------
title:          Properties of frame homomorphisms
author:         Ayberk Tosun
date-started:   2024-04-10
dates-updated:  [2024-05-06]
--------------------------------------------------------------------------------

Originally written as part of the `Locales.Frame` module on 2021-03-09.

Factored out from the `Locales.Frame` module on 2024-04-10.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.FrameHomomorphism-Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Hedberg
open import UF.Logic
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

We work in a module parameterized by two frames.

\begin{code}

module FrameHomomorphismProperties (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤' 𝓥' 𝓦) where

 open FrameHomomorphisms using (_─f→_)
 open FrameHomomorphisms F G hiding (_─f→_)

\end{code}

The following lemma says that if the underlying functions of two frame
homomorphisms are extensionally equal, then the frame homomorphisms are equal.

\begin{code}

 to-frame-homomorphism-＝ : (h₁ h₂  : F ─f→ G)
                         → ((x : ⟨ F ⟩) → h₁ .pr₁ x ＝ h₂ .pr₁ x)
                         → h₁ ＝ h₂
 to-frame-homomorphism-＝ h₁ h₂ ψ = to-subtype-＝ † (dfunext fe ψ)
  where
   † : (f : ⟨ F ⟩ → ⟨ G ⟩) → is-prop (is-a-frame-homomorphism f holds)
   † f = holds-is-prop (is-a-frame-homomorphism f)

\end{code}

\begin{code}

 frame-morphisms-are-monotonic : (h : ⟨ F ⟩ → ⟨ G ⟩)
                               → is-a-frame-homomorphism h holds
                               → is-monotonic (poset-of F) (poset-of G) h holds
 frame-morphisms-are-monotonic f (_ , ψ , _) (x , y) p =
  f x              ≤⟨ Ⅰ ⟩
  f (x ∧[ F ] y)   ≤⟨ Ⅱ ⟩
  f x ∧[ G ] f y   ≤⟨ Ⅲ ⟩
  f y              ■
   where
    open PosetReasoning (poset-of G)

    Ⅰ = reflexivity+ (poset-of G) (ap f (connecting-lemma₁ F p))
    Ⅱ = reflexivity+ (poset-of G) (ψ x y)
    Ⅲ = ∧[ G ]-lower₂ (f x) (f y)

\end{code}

\begin{code}

 monotone-map-of : (F ─f→ G) → poset-of F ─m→ poset-of G
 monotone-map-of h = fun h , †
  where
   † : is-monotonic (poset-of F) (poset-of G) (pr₁ h) holds
   † = frame-morphisms-are-monotonic (pr₁ h) (pr₂ h)

\end{code}

\begin{code}

 meet-preserving-implies-monotone : (h : ⟨ F ⟩ → ⟨ G ⟩)
                                  → preserves-binary-meets h holds
                                  → is-monotonic (poset-of F) (poset-of G) h holds
 meet-preserving-implies-monotone h μ (x , y) p =
  h x              ＝⟨ i   ⟩ₚ
  h (x ∧[ F ] y)   ＝⟨ ii  ⟩ₚ
  h x ∧[ G ] h y   ≤⟨ iii ⟩
  h y              ■
   where
    open PosetReasoning (poset-of G)

    i   = ap h (connecting-lemma₁ F p)
    ii  = μ x y
    iii = ∧[ G ]-lower₂ (h x) (h y)

\end{code}

\begin{code}

 frame-homomorphisms-preserve-bottom : (h : F ─f→ G)
                                     → h .pr₁ 𝟎[ F ] ＝ 𝟎[ G ]
 frame-homomorphisms-preserve-bottom 𝒽@(h , _ , _ , γ) =
  only-𝟎-is-below-𝟎 G (𝒽 .pr₁ 𝟎[ F ]) †
   where
    † : (h 𝟎[ F ] ≤[ poset-of G ] 𝟎[ G ]) holds
    † = pr₂ (γ (∅ _)) ((⋁[ G ] ∅ 𝓦) , λ ())

\end{code}

\begin{code}

 frame-homomorphisms-preserve-binary-joins : (h : F ─f→ G)
                                           → (x y : ⟨ F ⟩)
                                           → h .pr₁ (x ∨[ F ] y)
                                           ＝ (h .pr₁ x) ∨[ G ] (h .pr₁ y)
 frame-homomorphisms-preserve-binary-joins 𝒽@(h , _ , _ , γ) x y =
  ⋁[ G ]-unique ⁅ h x , h y ⁆ (h (x ∨[ F ] y)) († , ‡)
   where
    open Joins (λ x y → x ≤[ poset-of G ] y)

    † : (h (x ∨[ F ] y) is-an-upper-bound-of ⁅ h x , h y ⁆) holds
    † (inl ⋆) = pr₁ (γ ⁅ x , y ⁆) (inl ⋆)
    † (inr ⋆) = pr₁ (γ ⁅ x , y ⁆) (inr ⋆)

    ‡ : ((u , _) : upper-bound ⁅ h x , h y ⁆)
      → (h (x ∨[ F ] y) ≤[ poset-of G ] u) holds
    ‡ (u , p) = pr₂ (γ ⁅ x , y ⁆) (u , q)
     where
      q : (u is-an-upper-bound-of ⁅ h z ∣ z ε ⁅ x , y ⁆ ⁆) holds
      q (inl ⋆) = p (inl ⋆)
      q (inr ⋆) = p (inr ⋆)

\end{code}

Added on 2024-05-06.

\begin{code}

sections-are-order-embeddings : (P : Poset 𝓤 𝓥) (Q : Poset 𝓤' 𝓥')
                              → (s : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                              → (r : ∣ Q ∣ₚ → ∣ P ∣ₚ )
                              → is-monotonic Q P r holds
                              → r ∘ s ∼ id
                              → {x y : ∣ P ∣ₚ}
                              → (s x ≤[ Q ] s y ⇒ x ≤[ P ] y) holds
sections-are-order-embeddings P Q s r 𝓂 φ {x} {y} p =
 transport₂ (λ x y → (x ≤[ P ] y) holds) (φ x) (φ y) †
  where
   † : (r (s x) ≤[ P ] r (s y)) holds
   † = 𝓂 (s x , s y) p

\end{code}
