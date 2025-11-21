---
title:          Construction of a basis for the discrete locale
author:         Ayberk Tosun
date-started:   2024-09-13
date-completed: 2024-09-17
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.DiscreteLocale.Basis
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import Locales.DiscreteLocale.Definition fe pe pt
open import Locales.Frame pt fe hiding (∅)
open import Locales.SmallBasis pt fe sr
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Powerset
open import UF.Sets
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work in a module parameterized by a set `X`.

\begin{code}

module basis-for-the-discrete-locale (X : 𝓤 ̇ ) (σ : is-set X) where

 open binary-unions-of-subsets pt
 open singleton-subsets σ
 open DefnOfDiscreteLocale X σ

 𝓟-Frm : Frame (𝓤 ⁺) 𝓤 𝓤
 𝓟-Frm = frame-of-subsets

\end{code}

We define the function `finite-union` that gives the subset corresponding to
membership in a list.

\begin{code}

 finite-join : List X → 𝓟 X
 finite-join []       = ∅
 finite-join (x ∷ xs) = ❴ x ❵ ∪ finite-join xs

\end{code}

This maps the concatenation operator `_++_` to binary union `_∪_`.

\begin{code}

 finite-join-is-homomorphic
  : (xs ys : List X) → finite-join (xs ++ ys) ＝ finite-join xs ∪ finite-join ys
 finite-join-is-homomorphic []       ys = finite-join ys      ＝⟨ † ⟩
                                          ∅ ∪ finite-join ys  ∎
  where
   † = ∅-left-neutral-for-∪ pe fe (finite-join ys) ⁻¹
 finite-join-is-homomorphic (x ∷ xs) ys =
  finite-join ((x ∷ xs) ++ ys)               ＝⟨refl⟩
  finite-join (x ∷ xs ++ ys)                 ＝⟨refl⟩
  ❴ x ❵ ∪ finite-join (xs ++ ys)             ＝⟨ Ⅰ    ⟩
  ❴ x ❵ ∪ (finite-join xs ∪ finite-join ys)  ＝⟨ Ⅱ    ⟩
  (❴ x ❵ ∪ finite-join xs) ∪ finite-join ys  ＝⟨refl⟩
  finite-join (x ∷ xs) ∪ finite-join ys      ∎
   where
    IH = finite-join-is-homomorphic xs ys

    Ⅰ = ap (λ - → ❴ x ❵ ∪ -) IH
    Ⅱ = ∪-assoc pe fe ❴ x ❵ (finite-join xs) (finite-join ys) ⁻¹

\end{code}

Given a subset `S ⊆ 𝓟 X`, the index of the basic covering family for it
is the type of lists whose finite join is included in `S`:

\begin{code}

 Basic-Cover-Index : 𝓟 X → 𝓤 ̇
 Basic-Cover-Index S = Σ xs ꞉ List X , finite-join xs ⊆ S

\end{code}

Using this, we define the covering families:

\begin{code}

 lists-within : 𝓟 X → Fam 𝓤 (List X)
 lists-within S = Basic-Cover-Index S , pr₁

\end{code}

It is easy to see that these covering families are directed:

\begin{code}

 lists-within-is-directed : (S : 𝓟 X)
                          → is-directed
                             𝓟-Frm
                             ⁅ finite-join xs ∣ xs ε lists-within S ⁆
                              holds
 lists-within-is-directed S = ι , υ
  where
   open PosetReasoning (poset-of 𝓟-Frm)

   ι : ∥ Basic-Cover-Index S ∥
   ι = ∣ [] , ∅-is-least S ∣

   υ : ((xs , _) (ys , _) : Basic-Cover-Index S)
     → ∃ (zs , _) ꞉ Basic-Cover-Index S ,
        finite-join xs ⊆ finite-join zs × finite-join ys ⊆ finite-join zs
   υ (xs , p) (ys , q) = ∣ ((xs ++ ys) , †) , φ , ψ ∣
    where
     ‡ = ∪-is-lowerbound-of-upperbounds (finite-join xs) (finite-join ys) S p q

     † : finite-join (xs ++ ys) ⊆ S
     † = transport (λ - → - ⊆ S) (finite-join-is-homomorphic xs ys ⁻¹) ‡

     φ : finite-join xs ⊆ finite-join (xs ++ ys)
     φ = transport
          (λ - → finite-join xs ⊆ -)
          (finite-join-is-homomorphic xs ys ⁻¹)
          (∪-is-upperbound₁ (finite-join xs) (finite-join ys))

     ψ : finite-join ys ⊆ finite-join (xs ++ ys)
     ψ = transport
          (λ - → finite-join ys ⊆ -)
          (finite-join-is-homomorphic xs ys ⁻¹)
          (∪-is-upperbound₂ (finite-join xs) (finite-join ys))

\end{code}

We conclude that the family `finite-join : List X → 𝓟(X)` forms a directed
basis.

\begin{code}

 list-forms-directed-basis : directed-basis-forᴰ 𝓟-Frm (List X , finite-join)
 list-forms-directed-basis S = lists-within S , γ , lists-within-is-directed S
  where
   open Joins (λ S T → S ≤[ poset-of 𝓟-Frm ] T)

   †₁ : S ⊆ (⋁[ 𝓟-Frm ] ⁅ finite-join xs ∣ xs ε lists-within S ⁆)
   †₁ x μ =
    ⋁[ 𝓟-Frm ]-upper ⁅ finite-join xs ∣ xs ε lists-within S ⁆ ((x ∷ []) , φ) x ∣ inl refl ∣
     where
      φ : finite-join (x ∷ []) ⊆ S
      φ y p = transport (λ - → - ∈ S) q μ
       where
        q : y ∈ ❴ x ❵
        q = transport (λ - → y ∈ -) (∅-right-neutral-for-∪ pe fe ❴ x ❵ ⁻¹) p


   †₂ : (⋁[ 𝓟-Frm ] ⁅ finite-join xs ∣ xs ε lists-within S ⁆) ⊆ S
   †₂ = ⋁[ 𝓟-Frm ]-least ⁅ finite-join xs ∣ xs ε lists-within S ⁆ (S , γ)
    where

     γ : (S is-an-upper-bound-of ⁅ finite-join xs ∣ xs ε lists-within S ⁆) holds
     γ (xs , p) = p

   † : S ＝ ⋁[ 𝓟-Frm ] ⁅ finite-join xs ∣ xs ε lists-within S ⁆
   † = ≤-is-antisymmetric (poset-of 𝓟-Frm) †₁ †₂

   γ : (S is-lub-of ⁅ finite-join xs ∣ xs ε lists-within S ⁆) holds
   γ = transport
        (λ - → (- is-lub-of ⁅ finite-join xs ∣ xs ε lists-within S ⁆) holds)
        († ⁻¹)
        (⋁[ 𝓟-Frm ]-upper ⁅ finite-join xs ∣ xs ε lists-within S ⁆
        , ⋁[ 𝓟-Frm ]-least ⁅ finite-join xs ∣ xs ε lists-within S ⁆)

\end{code}
