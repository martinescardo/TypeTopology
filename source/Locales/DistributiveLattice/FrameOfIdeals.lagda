---
title:       Ideals of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-21
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.FrameOfIdeals
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.Frame pt fe
open import UF.Powerset-MultiUniverse
open import MLTT.Spartan
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic
open import Slice.Family

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)

open PropositionalSubsetInclusionNotation fe

open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

module DefnOfFrameOfIdeal (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L renaming (X-is-set to σ)

 _⊆ᵢ_ : Ideal L → Ideal L → Ω (𝓤)
 ℐ₁ ⊆ᵢ ℐ₂ = Ɐ x ꞉ ∣ L ∣ᵈ , x ∈ₚ I₁ ⇒ x ∈ₚ I₂
  where
   open Ideal ℐ₁ renaming (I to I₁)
   open Ideal ℐ₂ renaming (I to I₂)

 ⊆ᵢ-is-reflexive : (I : Ideal L) → (I ⊆ᵢ I) holds
 ⊆ᵢ-is-reflexive _ _ = id

 ⊆ᵢ-is-transitive : (I₁ I₂ I₃ : Ideal L) → (I₁ ⊆ᵢ I₂ ⇒ I₂ ⊆ᵢ I₃ ⇒ I₁ ⊆ᵢ I₃) holds
 ⊆ᵢ-is-transitive I₁ I₂ I₃ p q x r = q x (p x r)

 ⊆ᵢ-is-antisymmetric : (I₁ I₂ : Ideal L) → (I₁ ⊆ᵢ I₂) holds → (I₂ ⊆ᵢ I₁) holds → I₁ ＝ I₂
 ⊆ᵢ-is-antisymmetric = ideal-extensionality L

 poset-of-ideals : Poset (𝓤 ⁺) 𝓤
 poset-of-ideals = (Ideal L)
                 , _⊆ᵢ_
                 , (⊆ᵢ-is-reflexive  , ⊆ᵢ-is-transitive)
                 , ⊆ᵢ-is-antisymmetric _ _

\end{code}

The top ideal.

\begin{code}

 open PrincipalIdeals L

 𝟏ᵢ : Ideal L
 𝟏ᵢ = principal-ideal 𝟏

 𝟏ᵢ-is-top : (I : Ideal L) → (I ⊆ᵢ 𝟏ᵢ) holds
 𝟏ᵢ-is-top I x _ = 𝟏ᵈ-is-top L x

\end{code}

The binary meets of two ideals `I₁` and `I₂` is just the set intersection
`I₁ ∩ I₂`.

\begin{code}

 _∧ᵢ_ : Ideal L → Ideal L → Ideal L
 ℐ₁ ∧ᵢ ℐ₂ =
  record
   { I                    = I₁ ∩ I₂
   ; I-is-downward-closed = †
   ; I-is-closed-under-∨  = ‡
   }
  where
   open Ideal ℐ₁ renaming (I to I₁)
   open Ideal ℐ₂ renaming (I to I₂)

   † : is-downward-closed L (I₁ ∩ I₂) holds
   † x y p (q₁ , q₂) = Ideal.I-is-downward-closed ℐ₁ x y p q₁
                     , Ideal.I-is-downward-closed ℐ₂ x y p q₂

   ‡ : is-closed-under-binary-joins L (I₁ ∩ I₂) holds
   ‡ x y (p₁ , p₂) (q₁ , q₂) = Ideal.I-is-closed-under-∨ ℐ₁ x y p₁ q₁
                             , Ideal.I-is-closed-under-∨ ℐ₂ x y p₂ q₂

 open Meets _⊆ᵢ_

 ∧ᵢ-is-lower : (I₁ I₂ : Ideal L)
             → ((I₁ ∧ᵢ I₂) is-a-lower-bound-of (I₁ , I₂)) holds
 ∧ᵢ-is-lower I₁ I₂ = (λ _ → pr₁) , (λ _ → pr₂)

 ∧ᵢ-is-greatest : (I₁ I₂ I₃ : Ideal L)
                → (I₃ is-a-lower-bound-of (I₁ , I₂) ⇒ I₃ ⊆ᵢ (I₁ ∧ᵢ I₂)) holds
 ∧ᵢ-is-greatest I₁ I₂ I₃ (φ , ψ) x p = φ x p , ψ x p

 ∧ᵢ-is-glb : (I₁ I₂ : Ideal L) → ((I₁ ∧ᵢ I₂) is-glb-of (I₁ , I₂)) holds
 ∧ᵢ-is-glb I₁ I₂ = ∧ᵢ-is-lower I₁ I₂ , λ { (I₃ , p) → ∧ᵢ-is-greatest I₁ I₂ I₃ p }

\end{code}

We now define the covering relation.

\begin{code}

 open IdealNotation L

 open binary-unions-of-subsets pt

 infix 30 covering-syntax

 covering-syntax : (S : Fam 𝓤 (Ideal L)) → List ∣ L ∣ᵈ → 𝓤  ̇
 covering-syntax S []       = 𝟙
 covering-syntax S (x ∷ xs) =
  (Σ i ꞉ index S , (x ∈ᵢ (S [ i ])) holds) × covering-syntax S xs

 syntax covering-syntax S xs = xs ◁ S

\end{code}

\begin{code}

 ⋃ᵢ_ : Fam 𝓤 (Ideal L) → 𝓟 {𝓤} ∣ L ∣ᵈ
 ⋃ᵢ_ S = λ z → Ǝ xs ꞉ List ∣ L ∣ᵈ , (xs ◁ S) × (z ＝ join-listᵈ L xs)

 infix 41 ⋃ᵢ_

 join-list-maps-∨-to-++ : (xs ys : List ∣ L ∣ᵈ)
                        → join-listᵈ L xs ∨ join-listᵈ L ys ＝ join-listᵈ L (xs ++ ys)
 join-list-maps-∨-to-++ []        ys = ∨-unit₁ (join-listᵈ L ys)
 join-list-maps-∨-to-++ (x₀ ∷ xs) ys =
  join-listᵈ L (x₀ ∷ xs) ∨ join-listᵈ L ys     ＝⟨ refl ⟩
  (x₀ ∨ join-listᵈ L xs) ∨ join-listᵈ L ys     ＝⟨ Ⅰ    ⟩
  x₀ ∨ (join-listᵈ L xs ∨ join-listᵈ L ys)     ＝⟨ Ⅱ    ⟩
  x₀ ∨ (join-listᵈ L (xs ++ ys))               ＝⟨ refl ⟩
  join-listᵈ L (x₀ ∷ xs ++ ys)                 ∎
   where
    Ⅰ = ∨-associative x₀ (join-listᵈ L xs) (join-listᵈ L ys) ⁻¹
    Ⅱ = ap (x₀ ∨_) (join-list-maps-∨-to-++ xs ys)

 covering-++ : (S : Fam 𝓤 (Ideal L)) (xs ys : List ∣ L ∣ᵈ)
             → covering-syntax S xs → ys ◁ S → (xs ++ ys) ◁ S
 covering-++ S [] [] p q                           = ⋆
 covering-++ S [] (x ∷ ys) p q                     = q
 covering-++ S xs@(_ ∷ _)       []  p q            = transport
                                                      (λ - → - ◁ S)
                                                      ([]-right-neutral xs)
                                                      p
 covering-++ S (x ∷ xs) (y ∷ ys)  ((i , r) , p₂) q =
  (i , r) , (covering-++ S xs (y ∷ ys) p₂ q)

 ideal-join-is-closed-under-∨ : (I : Fam 𝓤 (Ideal L))
                              → is-closed-under-binary-joins L (⋃ᵢ I) holds
 ideal-join-is-closed-under-∨ S x y μ₁ μ₂ =
  ∥∥-rec₂ (holds-is-prop ((x ∨ y) ∈ₚ ⋃ᵢ S)) † μ₁ μ₂
   where
    † : Σ xs ꞉ List X , xs ◁ S × (x ＝ join-listᵈ L xs)
      → Σ ys ꞉ List X , ys ◁ S × (y ＝ join-listᵈ L ys)
      → (x ∨ y) ∈ (⋃ᵢ S)
    † (xs , c₁ , p₁) (ys , c₂ , p₂) = ∣ (xs ++ ys) , c , p ∣
     where
      c : (xs ++ ys) ◁ S
      c = covering-++ S xs ys c₁ c₂

      p : (x ∨ y) ＝ join-listᵈ L (xs ++ ys)
      p = x ∨ y                             ＝⟨ Ⅰ ⟩
          join-listᵈ L xs ∨ y               ＝⟨ Ⅱ ⟩
          join-listᵈ L xs ∨ join-listᵈ L ys ＝⟨ Ⅲ ⟩
          join-listᵈ L (xs ++ ys)           ∎
           where
            Ⅰ = ap (_∨ y) p₁
            Ⅱ = ap (join-listᵈ L xs ∨_) p₂
            Ⅲ = join-list-maps-∨-to-++ xs ys

 covering-∧ : (S : Fam 𝓤 (Ideal L)) (x : ∣ L ∣ᵈ) (xs : List ∣ L ∣ᵈ)
            → xs ◁ S
            → map (x ∧_) xs ◁ S
 covering-∧ S x [] ⋆ = ⋆
 covering-∧ S y (x ∷ xs) ((i , r) , c) = (i , †) , covering-∧ S y xs c
  where
   open Ideal (S [ i ]) renaming (I to I₁; I-is-downward-closed to Sᵢ-is-downward-closed)

   † : ((y ∧ x) ∈ᵢ (S [ i ])) holds
   † = Sᵢ-is-downward-closed (y ∧ x) x (∧-is-a-lower-bound₂ L y x) r


 ideal-join-is-downward-closed : (S : Fam 𝓤 (Ideal L))
                               → is-downward-closed L (⋃ᵢ S) holds
 ideal-join-is-downward-closed S x y q = ∥∥-rec (holds-is-prop (x ∈ₚ ⋃ᵢ S)) †
  where
   open PosetReasoning (poset-ofᵈ L)

   † : Σ ys ꞉ List X , ys ◁ S × (y ＝ join-listᵈ L ys) → x ∈ (⋃ᵢ S)
   † (ys , c , p) = ∣ map (x ∧_) ys , c′ , r ∣
    where
     c′ : map (x ∧_) ys ◁ S
     c′ = covering-∧ S x ys c

     Ⅰ : (x ≤ᵈ[ L ] join-listᵈ L ys) holds
     Ⅰ = x ≤⟨ q ⟩ y ＝⟨ p ⟩ₚ join-listᵈ L ys ■

     Ⅱ = finite-distributivity L ys x

     r : x ＝ join-listᵈ L (map (x ∧_) ys)
     r = x                            ＝⟨ Ⅰ ⁻¹ ⟩
         x ∧ join-listᵈ L ys          ＝⟨ Ⅱ    ⟩
         join-listᵈ L (map (x ∧_) ys) ∎

 ⋁ᵢ_ : Fam 𝓤 (Ideal L) → Ideal L
 ⋁ᵢ S = record
         { I                    = ⋃ᵢ S
         ; I-is-downward-closed = ideal-join-is-downward-closed S
         ; I-is-closed-under-∨  = ideal-join-is-closed-under-∨ S
         }

\end{code}
