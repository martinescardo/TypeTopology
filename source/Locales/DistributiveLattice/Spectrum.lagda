--------------------------------------------------------------------------------
title:          The spectrum of a distributive lattice
author:         Ayberk Tosun
date-started:   2024-02-21
date-completed: 2024-03-01
--------------------------------------------------------------------------------

We define the spectrum locale over a distributive lattice `L`, the defining
frame of which is the frame of ideals over `L`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.Spectrum
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work with a fixed distributive lattice `L` in this module.

\begin{code}

module DefnOfFrameOfIdeal (L : DistributiveLattice 𝓤) where

 open DistributiveLattice L renaming (X-is-set to σ)

\end{code}

We denote by `_⊆ᵢ_` the inclusion ordering between two ideals.

\begin{code}

 _⊆ᵢ_ : Ideal L → Ideal L → Ω (𝓤)
 ℐ₁ ⊆ᵢ ℐ₂ = Ɐ x ꞉ ∣ L ∣ᵈ , x ∈ₚ I₁ ⇒ x ∈ₚ I₂
  where
   open Ideal ℐ₁ renaming (I to I₁)
   open Ideal ℐ₂ renaming (I to I₂)

 infix 30 _⊆ᵢ_

 ⊆ᵢ-is-reflexive : (I : Ideal L) → I ⊆ᵢ I holds
 ⊆ᵢ-is-reflexive _ _ = id

 ⊆ᵢ-is-transitive : (I₁ I₂ I₃ : Ideal L) → (I₁ ⊆ᵢ I₂ ⇒ I₂ ⊆ᵢ I₃ ⇒ I₁ ⊆ᵢ I₃) holds
 ⊆ᵢ-is-transitive I₁ I₂ I₃ p q x r = q x (p x r)

 ⊆ᵢ-is-antisymmetric : {I₁ I₂ : Ideal L}
                     → I₁ ⊆ᵢ I₂ holds → I₂ ⊆ᵢ I₁ holds → I₁ ＝ I₂
 ⊆ᵢ-is-antisymmetric {I₁} {I₂} = ideal-extensionality L I₁ I₂

 ⊆ᵢ-is-partial-order : is-partial-order (Ideal L) _⊆ᵢ_
 ⊆ᵢ-is-partial-order = (⊆ᵢ-is-reflexive , ⊆ᵢ-is-transitive) , ⊆ᵢ-is-antisymmetric

 poset-of-ideals : Poset (𝓤 ⁺) 𝓤
 poset-of-ideals = Ideal L
                 , _⊆ᵢ_
                 , (⊆ᵢ-is-reflexive  , ⊆ᵢ-is-transitive)
                 , ⊆ᵢ-is-antisymmetric

\end{code}

We denote by `𝟏ᵢ` the top ideal, which is the principal ideal on the top element
of the lattice `L`.

\begin{code}

 open PrincipalIdeals L

 𝟏ᵢ : Ideal L
 𝟏ᵢ = principal-ideal 𝟏

 𝟏ᵢ-is-top : (I : Ideal L) → (I ⊆ᵢ 𝟏ᵢ) holds
 𝟏ᵢ-is-top I x _ = 𝟏ᵈ-is-top L x

\end{code}

The binary meets of two ideals `I₁` and `I₂` is just the set intersection
`I₁ ∩ I₂`. We denote this by `I₁ ∧ᵢ I₂`.

\begin{code}

 _∧ᵢ_ : Ideal L → Ideal L → Ideal L
 ℐ₁ ∧ᵢ ℐ₂ =
  record
   { I                    = I₁ ∩ I₂
   ; I-is-inhabited       = ∣ 𝟎 , I₁-contains-𝟎 , I₂-contains-𝟎 ∣
   ; I-is-downward-closed = †
   ; I-is-closed-under-∨  = ‡
  }
   where
    open Ideal ℐ₁ renaming (I to I₁; I-contains-𝟎 to I₁-contains-𝟎)
    open Ideal ℐ₂ renaming (I to I₂; I-contains-𝟎 to I₂-contains-𝟎)

    † : is-downward-closed L (I₁ ∩ I₂) holds
    † x y p (q₁ , q₂) = Ideal.I-is-downward-closed ℐ₁ x y p q₁
                      , Ideal.I-is-downward-closed ℐ₂ x y p q₂

    ‡ : is-closed-under-binary-joins L (I₁ ∩ I₂) holds
    ‡ x y (p₁ , p₂) (q₁ , q₂) = Ideal.I-is-closed-under-∨ ℐ₁ x y p₁ q₁
                              , Ideal.I-is-closed-under-∨ ℐ₂ x y p₂ q₂

 infix 32 _∧ᵢ_

 open Meets _⊆ᵢ_

 ∧ᵢ-is-lower : (I₁ I₂ : Ideal L)
             → ((I₁ ∧ᵢ I₂) is-a-lower-bound-of (I₁ , I₂)) holds
 ∧ᵢ-is-lower I₁ I₂ = (λ _ → pr₁) , (λ _ → pr₂)

 ∧ᵢ-is-greatest : (I₁ I₂ I₃ : Ideal L)
                → (I₃ is-a-lower-bound-of (I₁ , I₂) ⇒ I₃ ⊆ᵢ (I₁ ∧ᵢ I₂)) holds
 ∧ᵢ-is-greatest I₁ I₂ I₃ (φ , ψ) x p = φ x p , ψ x p

 ∧ᵢ-is-glb : (I₁ I₂ : Ideal L) → ((I₁ ∧ᵢ I₂) is-glb-of (I₁ , I₂)) holds
 ∧ᵢ-is-glb I₁ I₂ = ∧ᵢ-is-lower I₁ I₂ , λ { (I₃ , p) → ∧ᵢ-is-greatest I₁ I₂ I₃ p}

\end{code}

We now begin to do some preparation for the construction of small joins of
ideals. We first define the covering relation `xs ◁ ( Iⱼ )_{j : J}` which
expresses that a list `xs` of elements of the lattice `L` is contained in the
union of ideals `⋃_{j : J} I_j`. Intuitively, this just says: for every `x` in
`xs`, there is an ideal `Iⱼ` with `x ∈ Iⱼ`.

\begin{code}

 open IdealNotation L

 open binary-unions-of-subsets pt

 infix 30 covering-syntax

 covering-syntax : (S : Fam 𝓤 (Ideal L)) → List ∣ L ∣ᵈ → 𝓤 ̇
 covering-syntax S []       = 𝟙
 covering-syntax S (x ∷ xs) =
  (Σ i ꞉ index S , x ∈ᵢ (S [ i ]) holds) × covering-syntax S xs

 syntax covering-syntax S xs = xs ◁ S

\end{code}

Below are some simple lemmas about the covering relation.

\begin{code}

 covering-cons : (S : Fam 𝓤 (Ideal L)) {x : ∣ L ∣ᵈ} {xs : List ∣ L ∣ᵈ}
               → (x ∷ xs) ◁ S → xs ◁ S
 covering-cons S (_ , c) = c

 covering-lemma : (S : Fam 𝓤 (Ideal L)) (xs : List ∣ L ∣ᵈ)
                → xs ◁ S
                → (x : ∣ L ∣ᵈ) → member x xs → Σ i ꞉ index S , x ∈ⁱ (S [ i ])
 covering-lemma S []       p             x  m =
  𝟘-elim (lists-with-members-are-non-empty m)
 covering-lemma S (x ∷ xs) ((i , r) , q) x  in-head     = i , r
 covering-lemma S (x ∷ xs) p             x′ (in-tail r) = IH
  where
   IH : Σ i ꞉ index S , x′ ∈ᵢ (S [ i ]) holds
   IH = covering-lemma S xs (covering-cons S p) x′ r

 covering-++ : (S : Fam 𝓤 (Ideal L)) (xs ys : List ∣ L ∣ᵈ)
             → xs ◁ S → ys ◁ S → (xs ++ ys) ◁ S
 covering-++ S    []       []         _ q             = q
 covering-++ S    []       ys@(_ ∷ _) _ q             = q
 covering-++ S xs@(_ ∷ _)  []         p q             = transport
                                                         (λ - → - ◁ S)
                                                         ([]-right-neutral xs)
                                                         p
 covering-++ S    (x ∷ xs) (y ∷ ys)  ((i , r) , p₂) q =
  (i , r) , covering-++ S xs (y ∷ ys) p₂ q

 covering-intersection : (S : Fam 𝓤 (Ideal L)) (I : Ideal L) (xs : List ∣ L ∣ᵈ)
                       → join-listᵈ L xs ∈ⁱ I
                       → xs ◁ S
                       → xs ◁ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆
 covering-intersection S I []       _ _             = ⋆
 covering-intersection S I (x ∷ xs) p ((i , r) , c) =
  (i , q , r) , covering-intersection S I xs p′ c
   where
    open Ideal I using (I-is-downward-closed)

    † : (join-listᵈ L xs ≤ᵈ[ L ] join-listᵈ L (x ∷ xs)) holds
    † = ∨-is-an-upper-bound₂ L x (join-listᵈ L xs)

    q : x ∈ⁱ I
    q = I-is-downward-closed
         x
         (join-listᵈ L (x ∷ xs))
         (∨-is-an-upper-bound₁ L x (join-listᵈ L xs)) p

    p′ : join-listᵈ L xs ∈ⁱ I
    p′ = I-is-downward-closed (join-listᵈ L xs) (join-listᵈ L (x ∷ xs)) † p

 covering-∧ : (S : Fam 𝓤 (Ideal L)) (x : ∣ L ∣ᵈ) (xs : List ∣ L ∣ᵈ)
            → xs ◁ S → map (x ∧_) xs ◁ S
 covering-∧ S x []       q             = q
 covering-∧ S y (x ∷ xs) ((i , r) , c) = (i , †) , covering-∧ S y xs c
  where
   open Ideal (S [ i ]) renaming (I to I₁;
                                  I-is-downward-closed to Sᵢ-is-downward-closed)

   † : (y ∧ x) ∈ᵢ (S [ i ]) holds
   † = Sᵢ-is-downward-closed (y ∧ x) x (∧-is-a-lower-bound₂ L y x) r

\end{code}

The lemma below captures the fact that covers of lists always have a finite
subcover.

\begin{code}

 open Locale
 open import Locales.DirectedFamily pt fe _⊆ᵢ_


 finite-subcover : (S : Fam 𝓤 (Ideal L)) (xs : List ∣ L ∣ᵈ)
                 → is-directed S holds
                 → xs ◁ S
                 → ∃ i ꞉ index S , join-listᵈ L xs ∈ᵢ (S [ i ]) holds
 finite-subcover S [] δ c = ∥∥-rec ∃-is-prop γ (directed-implies-inhabited S δ)
  where
   γ : index S → ∃ i ꞉ index S , join-listᵈ L [] ∈ⁱ (S [ i ])
   γ i = ∣ i , Sᵢ-contains-𝟎 ∣
    where
     open Ideal (S [ i ]) renaming (I-contains-𝟎 to Sᵢ-contains-𝟎)
 finite-subcover S (x ∷ xs) δ ((i , μ) , c) = ∥∥-rec ∃-is-prop † IH
  where
   IH : ∃ i ꞉ index S , join-listᵈ L xs ∈ᵢ (S [ i ]) holds
   IH = finite-subcover S xs δ c

   † : Σ i ꞉ index S , join-listᵈ L xs ∈ⁱ (S [ i ])
     → ∃ k ꞉ index S , join-listᵈ L (x ∷ xs) ∈ⁱ (S [ k ])
   † (j , p) = ∥∥-rec ∃-is-prop ‡ (pr₂ δ i j)
    where
     ‡ : Σ k ꞉ index S , ((S [ i ]) ⊆ᵢ (S [ k ]) ∧ₚ (S [ j ]) ⊆ᵢ (S [ k ])) holds
       → ∃ k ꞉ index S , join-listᵈ L (x ∷ xs) ∈ⁱ (S [ k ])
     ‡ (k , μ₁ , μ₂) =
      ∣ k , Sᵢ-is-closed-under-∨ x (join-listᵈ L xs ) (μ₁ x μ) (μ₂ (join-listᵈ L xs) p) ∣
       where
        open Ideal (S [ k ]) renaming (I-is-closed-under-∨ to Sᵢ-is-closed-under-∨)

\end{code}

We are now ready to define the join. Given a family `( Iⱼ )_{j : J}` of ideals,
their union is given by the family:

    { (⋁ F) ∣ F ⊆ (⋃_{j : J} I_j), F finite}.

We capture finiteness using lists instead (which amounts to Kuratowski
finiteness).

We start by defining a preliminary version of the join operation that gives the
underlying subset of the ideal. We then proceed to prove that this forms an
ideal.

\begin{code}

 ⋁⁰ᵢ_ : Fam 𝓤 (Ideal L) → 𝓟 {𝓤} ∣ L ∣ᵈ
 ⋁⁰ᵢ_ S = λ y → Ǝ xs ꞉ List ∣ L ∣ᵈ , xs ◁ S × (y ＝ join-listᵈ L xs)

 infix 41 ⋁⁰ᵢ_

\end{code}

It is easy to see that this operation gives subsets that are closed under binary
joins.

\begin{code}

 ideal-join-is-closed-under-∨ : (I : Fam 𝓤 (Ideal L))
                              → is-closed-under-binary-joins L (⋁⁰ᵢ I) holds
 ideal-join-is-closed-under-∨ S x y μ₁ μ₂ =
  ∥∥-rec₂ (holds-is-prop ((x ∨ y) ∈ₚ ⋁⁰ᵢ S)) † μ₁ μ₂
   where
    † : Σ xs ꞉ List X , xs ◁ S × (x ＝ join-listᵈ L xs)
      → Σ ys ꞉ List X , ys ◁ S × (y ＝ join-listᵈ L ys)
      → (x ∨ y) ∈ (⋁⁰ᵢ S)
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
            Ⅲ = join-list-maps-∨-to-++ L xs ys

\end{code}

The operation `⋁⁰ᵢ_` gives subsets that are downward closed.

\begin{code}

 ideal-join-is-downward-closed : (S : Fam 𝓤 (Ideal L))
                               → is-downward-closed L (⋁⁰ᵢ S) holds
 ideal-join-is-downward-closed S x y q = ∥∥-rec (holds-is-prop (x ∈ₚ ⋁⁰ᵢ S)) †
  where
   open PosetReasoning (poset-ofᵈ L)

   † : Σ ys ꞉ List X , ys ◁ S × (y ＝ join-listᵈ L ys) → x ∈ (⋁⁰ᵢ S)
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

\end{code}

We package the proofs up into the following join operation `⋁ᵢ_`.

\begin{code}

 ⋁ᵢ_ : Fam 𝓤 (Ideal L) → Ideal L
 ⋁ᵢ S = record
         { I                    = ⋁⁰ᵢ S
         ; I-is-inhabited       = ∣ 𝟎 , ∣ [] , (⋆ , refl) ∣ ∣
         ; I-is-downward-closed = ideal-join-is-downward-closed S
         ; I-is-closed-under-∨  = ideal-join-is-closed-under-∨ S
        }

\end{code}

It is obvious that this gives contains all the ideals in the family.

\begin{code}

 ⋁ᵢ-is-an-upper-bound : (S : Fam 𝓤 (Ideal L))
                      → (i : index S) → (S [ i ]) ⊆ᵢ (⋁ᵢ S) holds
 ⋁ᵢ-is-an-upper-bound S i x p = ∣ (x ∷ []) , † , (∨-unit x ⁻¹) ∣
  where
   open Ideal (S [ i ]) renaming (I-is-downward-closed
                                   to Sᵢ-is-downward-closed)

   † : (x ∷ []) ◁ S
   † = (i , p) , ⋆

\end{code}

The fact that it is a least upper bound is not as trivial and uses the
`covering-lemma` we gave above.

\begin{code}

 open Joins _⊆ᵢ_

 ⋁ᵢ-is-least : (S  : Fam 𝓤 (Ideal L))
             → (Iᵤ : Ideal L)
             → (Iᵤ is-an-upper-bound-of S ⇒ (⋁ᵢ S) ⊆ᵢ Iᵤ) holds
 ⋁ᵢ-is-least S Iᵤ υ x = ∥∥-rec (holds-is-prop (x ∈ᵢ Iᵤ)) †
  where
   † : Σ xs ꞉ List X , xs ◁ S × (x ＝ join-listᵈ L xs) → x ∈ᵢ Iᵤ holds
   † (xs , c , r) = transport
                     (λ - → - ∈ᵢ Iᵤ holds)
                     (r ⁻¹)
                     (ideals-are-closed-under-finite-joins L Iᵤ xs φ)
    where
     φ : ((x , _) : type-from-list xs) → x ∈ᵢ Iᵤ holds
     φ (x , μ) = υ iₓ x ν
      where
       θ : Σ i ꞉ index S , x ∈ᵢ (S [ i ]) holds
       θ = covering-lemma S xs c x μ

       iₓ = pr₁ θ

       ν : (x ∈ᵢ (S [ iₓ ])) holds
       ν = pr₂ θ

\end{code}

Finally, we prove the distributivity law.

\begin{code}

 distributivityᵢ : (I : Ideal L) (S : Fam 𝓤 (Ideal L))
                 → I ∧ᵢ (⋁ᵢ S) ＝ ⋁ᵢ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆
 distributivityᵢ I S = ⊆ᵢ-is-antisymmetric † ‡
  where
   † : I ∧ᵢ (⋁ᵢ S) ⊆ᵢ (⋁ᵢ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆) holds
   † x (μ₁ , μ₂) =
    ∥∥-rec (holds-is-prop (x ∈ᵢ (⋁ᵢ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆))) γ μ₂
     where
      γ : Σ xs ꞉ List X , xs ◁ S × (x ＝ join-listᵈ L xs)
       → x ∈ᵢ (⋁ᵢ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆) holds
      γ (xs , c , r) = ∣ xs , c′ , r ∣
       where
        μ : join-listᵈ L xs ∈ᵢ I holds
        μ = transport (λ - → - ∈ᵢ I holds) r μ₁

        c′ : xs ◁ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆
        c′ = covering-intersection S I xs μ c

   ‡ : (⋁ᵢ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆) ⊆ᵢ (I ∧ᵢ (⋁ᵢ S)) holds
   ‡ x p = ∥∥-rec (holds-is-prop (x ∈ᵢ (I ∧ᵢ (⋁ᵢ S)))) γ p
    where
     open PosetReasoning (poset-ofᵈ L)

     γ : Σ xs ꞉ List X ,
          xs ◁ ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆ × (x ＝ join-listᵈ L xs)
       → x ∈ᵢ I ∧ᵢ (⋁ᵢ S) holds
     γ (xs , c , r) = μ₁ , μ₂
      where
       ϟ : (x : ∣ L ∣ᵈ)
         → member x xs
         → Σ i ꞉ index S , x ∈ᵢ I ∧ᵢ (S [ i ]) holds
       ϟ x μ = covering-lemma ⁅ I ∧ᵢ (S [ i ]) ∣ i ∶ index S ⁆ xs c x μ

       ϵ : ((x , μ) : type-from-list xs) → x ∈ⁱ I
       ϵ (x , μ) = pr₁ (pr₂ (ϟ x μ))

       δ : join-listᵈ L xs ∈ⁱ I
       δ = ideals-are-closed-under-finite-joins L I xs ϵ

       μ₁ : x ∈ᵢ I holds
       μ₁ = transport (λ - → (- ∈ᵢ I) holds) (r ⁻¹) δ

       ι : ((x , μ) : type-from-list xs) → x ∈ᵢ (⋁ᵢ S) holds
       ι (x , μ) = ⋁ᵢ-is-an-upper-bound S iₓ x μ′
        where
         ν : Σ i ꞉ index S , x ∈ⁱ I ∧ᵢ (S [ i ])
         ν = ϟ x μ

         iₓ : index S
         iₓ = pr₁ ν

         μ′ : x ∈ⁱ (S [ iₓ ])
         μ′ = pr₂ (pr₂ ν)

       θ : join-listᵈ L xs ∈ⁱ (⋁ᵢ S)
       θ = ideals-are-closed-under-finite-joins L (⋁ᵢ S) xs ι

       μ₂ : x ∈ᵢ (⋁ᵢ S) holds
       μ₂ = transport (λ - → - ∈ᵢ (⋁ᵢ S) holds) (r ⁻¹) θ

\end{code}

We are now ready to package everything up as a frame.

\begin{code}

 frame-of-ideals : Frame (𝓤 ⁺) 𝓤 𝓤
 frame-of-ideals =
   Ideal L
  , (_⊆ᵢ_ , 𝟏ᵢ , _∧ᵢ_ , ⋁ᵢ_)
  , ⊆ᵢ-is-partial-order
  , 𝟏ᵢ-is-top
  , (λ (I₁ , I₂) → ∧ᵢ-is-lower I₁ I₂ , λ (I₃ , lb) → ∧ᵢ-is-greatest I₁ I₂ I₃ lb)
  , (λ S → ⋁ᵢ-is-an-upper-bound S , λ (I , ub) → ⋁ᵢ-is-least S I ub)
  , λ { (I , S) → distributivityᵢ I S}

\end{code}

This is the frame of opens of the “spectrum space” of the distributive lattice
`L`. Because we work with locales as our notion of space, we just take the
locale that this frame defines as the spectrum over the distributive lattice
`L`.

\begin{code}

 spectrum : Locale (𝓤 ⁺) 𝓤 𝓤
 spectrum = record
             { ⟨_⟩ₗ         = Ideal L
             ; frame-str-of = pr₂ frame-of-ideals}

\end{code}
