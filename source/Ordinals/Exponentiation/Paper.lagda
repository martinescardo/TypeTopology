Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
January 2025

This file follows the definitions, equations, lemmas, propositions, theorems and
remarks of the paper "Ordinal Exponentiation in Homotopy Type Theory".

See also Ordinals.Exponentiation.index.lagda for an overview of the relevant
files.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

\end{code}

Our global assumptions are univalence, the existence of propositional
truncations and set replacement (equivalently, small set quotients).

Function extensionality can be derived from univalence.

\begin{code}

module Ordinals.Exponentiation.Paper
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import Notation.General

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import UF.ClassicalLogic
open import UF.ImageAndSurjection pt
open PropositionalTruncation pt

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open suprema pt sr
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua
open import Ordinals.Exponentiation.DecreasingListProperties-Concrete ua pt sr
open import Ordinals.Exponentiation.PropertiesViaTransport ua pt sr
open import Ordinals.Exponentiation.RelatingConstructions ua pt sr
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.Taboos ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

\end{code}

Section III. Ordinals in Homotopy Type Theory

\begin{code}

Lemma-1 : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
        → (is-simulation α β f → (a : ⟨ α ⟩) → α ↓ a ＝ β ↓ f a)
        × (is-simulation α β f → left-cancellable f × is-order-reflecting α β f)
        × (is-simulation α β f × is-surjection f ↔ is-order-equiv α β f)
Lemma-1 α β f = [1] , [2] , [3]
 where
  [1] : is-simulation α β f → (a : ⟨ α ⟩) → α ↓ a ＝ β ↓ f a
  [1] f-sim a = simulations-preserve-↓ α β (f , f-sim) a

  [2] : is-simulation α β f → left-cancellable f × is-order-reflecting α β f
  [2] f-sim =   simulations-are-lc α β f f-sim
              , simulations-are-order-reflecting α β f f-sim

  [3] : is-simulation α β f × is-surjection f ↔ is-order-equiv α β f
  [3] =   (λ (f-sim , f-surj) →
            order-preserving-reflecting-equivs-are-order-equivs α β f
             (surjective-embeddings-are-equivs f
               (simulations-are-embeddings fe α β f f-sim) f-surj)
             (simulations-are-order-preserving α β f f-sim)
             (simulations-are-order-reflecting α β f f-sim))
        , (λ f-equiv →   order-equivs-are-simulations α β f f-equiv
                       , equivs-are-surjections
                          (order-equivs-are-equivs α β f-equiv))

Eq-1 : (α β : Ordinal 𝓤)
     → ((a : ⟨ α ⟩) → (α +ₒ β) ↓ inl a ＝ α ↓ a)
     × ((b : ⟨ β ⟩) → (α +ₒ β) ↓ inr b ＝ α +ₒ (β ↓ b))
Eq-1 α β = (λ a → (+ₒ-↓-left a) ⁻¹) , (λ b → (+ₒ-↓-right b) ⁻¹)

Eq-2 : (α β : Ordinal 𝓤) (a : ⟨ α ⟩) (b : ⟨ β ⟩)
     → (α ×ₒ β) ↓ (a , b) ＝ α ×ₒ (β ↓ b) +ₒ (α ↓ a)
Eq-2 α β a b = ×ₒ-↓ α β

Eq-3 : (I : 𝓤 ̇  ) (F : I → Ordinal 𝓤) (y : ⟨ sup F ⟩)
     → ∃ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ ,
          (y ＝ [ F i , sup F ]⟨ sup-is-upper-bound F i ⟩ x)
        × (sup F ↓ y ＝ F i ↓ x)
Eq-3 I F y = ∥∥-functor h
              (initial-segment-of-sup-is-initial-segment-of-some-component F y)
 where
  h : (Σ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ , sup F ↓ y ＝ F i ↓ x)
    → Σ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ ,
         (y ＝ [ F i , sup F ]⟨ sup-is-upper-bound F i ⟩ x)
       × (sup F ↓ y ＝ F i ↓ x)
  h (i , x , p) = i , x , q , p
   where
    [i,x] = [ F i , sup F ]⟨ sup-is-upper-bound F i ⟩ x
    q : y ＝ [i,x]
    q = ↓-lc (sup F) y [i,x] (p ∙ (initial-segment-of-sup-at-component F i x) ⁻¹)

Lemma-2 : (α : Ordinal 𝓤)
        → ((β γ : Ordinal 𝓥) → β ⊴ γ → α ×ₒ β ⊴ α ×ₒ γ)
        × ({I : 𝓤 ̇  } (F : I → Ordinal 𝓤) → α ×ₒ sup F ＝ sup (λ i → α ×ₒ F i))
Lemma-2 α = ×ₒ-right-monotone-⊴ α , ×ₒ-preserves-suprema pt sr α

Eq-4 : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
Eq-4 = exp-full-specification

Lemma-3 : (α : Ordinal 𝓤) (exp-α : Ordinal 𝓤 → Ordinal 𝓤)
        → exp-specification-zero α exp-α
        → exp-specification-succ α exp-α
        → exp-specification-sup  α exp-α
        → (exp-α 𝟙ₒ ＝ α)
        × (exp-α 𝟚ₒ ＝ α ×ₒ α)
        × ((α ≠ 𝟘ₒ) → is-monotone (OO 𝓤) (OO 𝓤) exp-α)
Lemma-3 α exp-α exp-spec-zero exp-spec-succ exp-spec-sup =
   𝟙ₒ-neutral-exp α exp-α exp-spec-zero exp-spec-succ
 , exp-𝟚ₒ-is-×ₒ α exp-α exp-spec-zero exp-spec-succ
 , (λ α-nonzero → is-monotone-if-continuous exp-α (exp-spec-sup α-nonzero))

Proposition-4
 : (Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exp-full-specification exp)
 ↔ EM 𝓤
Proposition-4 =
   (λ (exp , (exp-zero , exp-succ , exp-sup)) →
    exponentiation-defined-everywhere-implies-EM
     exp
     exp-zero
     exp-succ
     (λ α → pr₁ (exp-sup α)))
 , EM-gives-full-exponentiation

\end{code}

Section IV. Abstract Algebraic Exponentiation

\begin{code}

Lemma-5 : (β : Ordinal 𝓤) → β ＝ sup (λ b → (β ↓ b) +ₒ 𝟙ₒ)
Lemma-5 = supremum-of-successors-of-initial-segments pt sr

Definition-6 : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
Definition-6 α β = α ^ₒ β

Proposition-7 : (α β : Ordinal 𝓤)
                (a : ⟨ α ⟩) (b : ⟨ β ⟩) (e : ⟨ α ^ₒ (β ↓ b) ⟩)
              → α ^ₒ β ↓ ×ₒ-to-^ₒ α β {b} (e , a)
                ＝ α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e)
Proposition-7 α β a b e = ^ₒ-↓-×ₒ-to-^ₒ α β

Proposition-8 : (α β γ : Ordinal 𝓤)
              → (β ⊴ γ → α ^ₒ β ⊴ α ^ₒ γ)
              × (𝟙ₒ ⊲ α → β ⊲ γ → α ^ₒ β ⊲ α ^ₒ γ)
Proposition-8 α β γ =   ^ₒ-monotone-in-exponent α β γ
                      , ^ₒ-order-preserving-in-exponent α β γ

Theorem-9 : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α
          → exp-specification-zero α (α ^ₒ_)
          × exp-specification-succ α (α ^ₒ_)
          × exp-specification-sup α (α ^ₒ_)
Theorem-9 {𝓤} α α-pos =   ^ₒ-satisfies-zero-specification {𝓤} {𝓤} α
                        , ^ₒ-satisfies-succ-specification {𝓤} {𝓤} α α-pos
                        , ^ₒ-satisfies-sup-specification α

Proposition-10 : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
               → α ^ₒ (β +ₒ γ) ＝ (α ^ₒ β) ×ₒ (α ^ₒ γ)
Proposition-10 = ^ₒ-by-+ₒ

Proposition-11 : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
               → α ^ₒ (β ×ₒ γ) ＝ (α ^ₒ β) ^ₒ γ
Proposition-11 = ^ₒ-by-×ₒ

\end{code}

Section V. Decreasing Lists: A Constructive Formulation
           of Sierpiński's Definition

\begin{code}

Definition-12 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝓤 ⊔ 𝓥 ̇
Definition-12 α β = DecrList₂ α β

Remark-13 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
            ((l , p) (l' , q) : DecrList₂ α β)
          → l ＝ l'
          → (l , p) ＝ (l' , q)
Remark-13 α β _ _ = to-DecrList₂-＝ α β

Proposition-14₁
 : EM 𝓤
 → ((α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
Proposition-14₁ = EM-implies-subtype-of-positive-elements-an-ordinal

Proposition-14₂
 : ((α : Ordinal (𝓤 ⁺⁺)) (x : ⟨ α ⟩) → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
 → EM 𝓤
Proposition-14₂ = subtype-of-positive-elements-an-ordinal-implies-EM

Lemma-15 : (α : Ordinal 𝓤)
         → (has-trichotomous-least-element α ↔ is-decomposable-into-one-plus α)
         × (((a₀ , a₀-tri) : has-trichotomous-least-element α)
            → (α ＝ 𝟙ₒ +ₒ α ⁺[ a₀ , a₀-tri ])
            × (⟨ α ⁺[ a₀ , a₀-tri ] ⟩ ＝ (Σ a ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ a)))
Lemma-15 α =   ( trichotomous-least-to-decomposable α
               , decomposable-to-trichotomous-least α)
             , (λ h →   α ⁺[ h ]-part-of-decomposition
                      , ⁺-is-subtype-of-positive-elements α h)

Definition-16 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
              → has-trichotomous-least-element α
              → Ordinal (𝓤 ⊔ 𝓥)
Definition-16 α β h = exponentiationᴸ α h β

Proposition-17 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                 (h : has-trichotomous-least-element α)
               → has-trichotomous-least-element (exponentiationᴸ α h β)
Proposition-17 α β h = exponentiationᴸ-has-trichotomous-least-element α h β



\end{code}