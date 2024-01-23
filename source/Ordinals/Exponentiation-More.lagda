Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

TEMPORARILY SPLIT UP TO SPEED UP TYPECHECKING

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence

module Ordinals.Exponentiation-More
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Sigma
-- open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

-- our imports
open import MLTT.List
open import Ordinals.Exponentiation ua

{-

(1 + α)^(⋁ᵢ βᵢ)

= Σ l : List (α × ⋁ᵢ βᵢ) , decreasing-pr2 l
= Σ l : List (⋁ᵢ (α × βᵢ)) , ...
?= ⋁ᵢ (Σ l : List (α × βᵢ) , decreasing-pr2 l)
= ⋁ᵢ (1 + α)^β


(1) Try for general families
(1.5) Try for monotone families
(2) Try for (x ↦ α ↓ x) for α an ordinal

-}

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open PropositionalTruncation pt

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr

 module _ {I : 𝓤 ̇  }
          (i₀ : I)
          (β : I → Ordinal 𝓤)
          (α : Ordinal 𝓤)
  where

  {-
  f : ⟨ [𝟙+ α ]^ (sup β) ⟩ → ⟨ sup (λ i → [𝟙+ α ]^ (β i)) ⟩
  f ([] , δ) = sum-to-sup (λ i → [𝟙+ α ]^ β i) (i₀ , ([] , []-decr))
  f ((a , x ∷ l) , δ) = {!!}
  -}

  private
   γ : I → Ordinal 𝓤
   γ i = [𝟙+ α ]^ (β i)

   ι : (ζ : I → Ordinal 𝓤) → {i : I} → ⟨ ζ i ⟩ → ⟨ sup ζ ⟩
   ι ζ {i} = pr₁ (sup-is-upper-bound ζ i)

   ι-is-surjective : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩)
                   → ∃ i ꞉ I , Σ x ꞉ ⟨ ζ i ⟩ , ι ζ {i} x ＝ s
   ι-is-surjective = {!!}

   ι-is-surjective⁺ : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩) (i : I) (x : ⟨ ζ i ⟩)
                    → s ≺⟨ sup ζ ⟩ ι ζ x
                    → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
   ι-is-surjective⁺ = {!!}

   module _ (i : I) where
    f₁ : List (⟨ α ×ₒ β i ⟩) → List (⟨ α ×ₒ sup β ⟩)
    f₁ [] = []
    f₁ (a , b ∷ l) = a , ι β b ∷ f₁ l
    f₂ : (l : List (⟨ α ×ₒ β i ⟩))
       → is-decreasing-pr₂ α (β i) l
       → is-decreasing-pr₂ α (sup β) (f₁ l)
    f₂ [] δ = []-decr
    f₂ (a , b ∷ []) δ = sing-decr
    f₂ (a , b ∷ a' , b' ∷ l) (many-decr p δ) =
      many-decr (simulations-are-order-preserving (β i) (sup β)
                  (ι β)
                  (pr₂ (sup-is-upper-bound β i)) b' b p)
                (f₂ (a' , b' ∷ l) δ)
    f : ⟨ γ i ⟩ → ⟨ [𝟙+ α ]^ (sup β) ⟩
    f (l , δ) = f₁ l , f₂ l δ

   f₁-surj-lemma : (a : ⟨ α ⟩) (i : I) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
                 → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
                 → Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a , ι β b ∷ l) ＝ f₁ i l'
   f₁-surj-lemma a i b [] δ = (a , b ∷ []) , refl
   f₁-surj-lemma a i b ((a' , s) ∷ l) δ = (a , b ∷ l') , ap (a , ι β b ∷_) (ap (λ - → a' , - ∷ l) ((pr₂ lem) ⁻¹) ∙ pr₂ IH)
    where
     lem : Σ b' ꞉ ⟨ β i ⟩ , ι β b' ＝ s
     lem = ι-is-surjective⁺ β s i b (is-decreasing-heads (underlying-order (sup β)) δ)
     b' : ⟨ β i ⟩
     b' = pr₁ lem
     IH : Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a' , ι β b' ∷ l) ＝ f₁ i l'
     IH = f₁-surj-lemma a' i b' l (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) (a' , - ∷ l)) (pr₂ lem) (is-decreasing-tail (underlying-order (sup β)) δ))
     l' = pr₁ IH

   f₁-surj : (l : List (⟨ α ×ₒ sup β ⟩))
           → is-decreasing-pr₂ α (sup β) l
           → ∃ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , l ＝ f₁ i l'
   f₁-surj [] δ = ∣ i₀ , [] , refl ∣
   f₁-surj (a , s ∷ l) δ = ∥∥-functor h (ι-is-surjective β s)
    where
     h : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , ι β b ＝ s)
       → Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , (a , s ∷ l) ＝ f₁ i l'
     h (i , b , refl) = i , (f₁-surj-lemma a i b l δ)


--  exp-sup-is-upper-bound : (i : I) → γ i ⊴ ([𝟙+ α ]^ (sup β))
--  exp-sup-is-upper-bound i = f i , {!!} , {!!}

  -- Possible strategy
  -- for every i : I, x : [𝟙+ α]^ (β i),
  -- [𝟙+ α]^ (sup β) ↓ (f x) =ₒ [𝟙+ α ]^ (β i) ↓ x
  -- ??


{-
  exp-sup-lemma : (i : I) (a : ⟨ α ⟩) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
                → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
                → ⟨ sup γ ⟩
  exp-sup-lemma i a b [] δ = ι γ {i} ([] , []-decr)
  exp-sup-lemma i a b (a' , s ∷ l) (many-decr p δ) = {!!}

-}

\end{code}
