Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
September 2025
Updated October 2026

This file follows the definitions, equations, lemmas, propositions, theorems and
remarks of our paper

   Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu
   Constructive Ordinal Exponentiation
   Accepted for publication in the Journal of the ACM
   https://arxiv.org/abs/2501.14542v6

This paper is a journal version of the paper "Ordinal Exponentiation in Homotopy
Type Theory", whose definitions etc are listed in Ordinals.Exponentiation.Paper.

See also Ordinals.Exponentiation.index for an overview of the relevant files.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

\end{code}

Our global assumptions are univalence, the existence of propositional
truncations and set replacement (equivalently, small set quotients).

Function extensionality can be derived from univalence.

\begin{code}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.PaperJournal
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.List
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.ImageAndSurjection pt
open import UF.Subsingletons
open PropositionalTruncation pt

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticReflection ua pt sr
open import Ordinals.BoundedOperations ua pt sr
open import Ordinals.Equivalence
open import Ordinals.Fin
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Notions
open import Ordinals.OperationsByCases ua pt sr
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.SupremaPreservation ua pt sr
open import Ordinals.Type
open import Ordinals.Underlying
open suprema pt sr

open import Ordinals.Exponentiation.DecreasingList ua pt
open import Ordinals.Exponentiation.DecreasingListProperties-Concrete ua pt sr
open import Ordinals.Exponentiation.Grayson ua pt
open import Ordinals.Exponentiation.Miscellaneous ua pt sr
open import Ordinals.Exponentiation.PropertiesViaTransport ua pt sr
open import Ordinals.Exponentiation.RelatingConstructions ua pt sr
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.Taboos ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

\end{code}

To match the terminology of the paper, we put

\begin{code}

has-decidable-equality = is-discrete
is-ordinal-equiv       = is-order-equiv

\end{code}

Section 2. Ordinals in a Constructive Setting

\begin{code}

Definition-1 : 𝓤 ⁺ ̇
Definition-1 = Ordinal _

Lemma-2 : (α : Ordinal 𝓤) (P : ⟨ α ⟩ → 𝓥 ̇ )
        → is-transitive (subtype-order α P)
        × is-well-founded (subtype-order α P)
Lemma-2 α P =
 (subtype-order-is-transitive α P , subtype-order-is-well-founded α P)

Lemma-3 : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
        → (is-simulation α β f → (a : ⟨ α ⟩) → α ↓ a ＝ β ↓ f a)
        × (is-simulation α β f → left-cancellable f × is-order-reflecting α β f)
        × (is-simulation α β f × is-surjection f ↔ is-ordinal-equiv α β f)
Lemma-3 α β f = [1] , [2] , [3]
 where
  [1] : is-simulation α β f → (a : ⟨ α ⟩) → α ↓ a ＝ β ↓ f a
  [1] f-sim a = simulations-preserve-↓ α β (f , f-sim) a

  [2] : is-simulation α β f → left-cancellable f × is-order-reflecting α β f
  [2] f-sim =   simulations-are-lc α β f f-sim
              , simulations-are-order-reflecting α β f f-sim

  [3] : is-simulation α β f × is-surjection f ↔ is-ordinal-equiv α β f
  [3] =   (λ (f-sim , f-surj) → surjective-simulations-are-order-equivs
                                 pt fe α β f f-sim f-surj)
        , (λ f-equiv →   order-equivs-are-simulations α β f f-equiv
                       , equivs-are-surjections
                          (order-equivs-are-equivs α β f-equiv))

Eq-1 : (I : 𝓤 ̇  ) (F : I → Ordinal 𝓤) (y : ⟨ sup F ⟩)
     → ∃ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ ,
          (y ＝ [ F i , sup F ]⟨ sup-is-upper-bound F i ⟩ x)
        × (sup F ↓ y ＝ F i ↓ x)
Eq-1 I F y = ∥∥-functor h
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

Eq-2 : (α β : Ordinal 𝓤)
     → ((a : ⟨ α ⟩) → (α +ₒ β) ↓ inl a ＝ α ↓ a)
     × ((b : ⟨ β ⟩) → (α +ₒ β) ↓ inr b ＝ α +ₒ (β ↓ b))
Eq-2 α β = (λ a → (+ₒ-↓-left a) ⁻¹) , (λ b → (+ₒ-↓-right b) ⁻¹)

Eq-3 : (α β : Ordinal 𝓤) (a : ⟨ α ⟩) (b : ⟨ β ⟩)
     → (α ×ₒ β) ↓ (a , b) ＝ α ×ₒ (β ↓ b) +ₒ (α ↓ a)
Eq-3 α β a b = ×ₒ-↓ α β

Remark-4 : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤) → sup (fattened-family F) ＝ sup F
Remark-4 = sup-of-fattened-family-agrees

Lemma-5 : (α β γ : Ordinal 𝓤)
        → β ⊴ γ
        → α +ₒ β ⊴ α +ₒ γ
        × α ×ₒ β ⊴ α ×ₒ γ
Lemma-5 α β γ l = +ₒ-right-monotone-⊴ α β γ l , ×ₒ-right-monotone-⊴ α β γ l

Lemma-6 : (α : Ordinal 𝓤)
        → ({I : 𝓤 ̇ } (F : I → Ordinal 𝓤) → α ×ₒ sup F ＝ sup (λ i → α ×ₒ F i))
Lemma-6 α = ×ₒ-is-continuous pt sr α

Lemma-7 : (β : Ordinal 𝓤) → β ＝ sup (λ b → (β ↓ b) +ₒ 𝟙ₒ)
Lemma-7 = supremum-of-successors-of-initial-segments pt sr

Proposition-8 : (α : Ordinal 𝓤)
              → (α ×ₒ 𝟘ₒ {𝓥} ＝ 𝟘ₒ)
              × ((β : Ordinal 𝓤) → α ×ₒ (β +ₒ 𝟙ₒ) ＝ α ×ₒ β +ₒ α)
              × ({I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                    → α ×ₒ sup β ＝ sup (λ i → α ×ₒ β i))
              × ((α β : Ordinal 𝓤) → α ×ₒ β ＝ sup (λ b → (α ×ₒ (β ↓ b)) +ₒ α))
              × (∃! _⊗_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
                     ((α β : Ordinal 𝓤) → α ⊗ (β +ₒ 𝟙ₒ) ＝ (α ⊗ β) +ₒ α)
                   × ((α : Ordinal 𝓤) {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                         → α ⊗ (sup β) ＝ sup (λ i → α ⊗ β i)))
Proposition-8 α =
   ×ₒ-𝟘ₒ-right α
 , ×ₒ-successor α
 , ×ₒ-is-continuous pt sr α
 , ×ₒ-recursive-equation
 , ×ₒ-is-uniquely-specified
  where
   open multiplication

Lemma-9 : (α : Ordinal 𝓤) {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
        → α +ₒ sup β ＝ extended-sup (λ i → α +ₒ β i) α
Lemma-9 = +ₒ-preserves-suprema-up-to-join
 where
  open addition-by-fixed-ordinal

Proposition-10 : (α : Ordinal 𝓤)
               → (α +ₒ 𝟘ₒ ＝ α)
               × ((β : Ordinal 𝓤) → α +ₒ (β +ₒ 𝟙ₒ) ＝ (α +ₒ β) +ₒ 𝟙ₒ)
               × ({I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                     → α +ₒ sup β ＝ extended-sup (λ i → α +ₒ β i) α)
               × ((α β : Ordinal 𝓤)
                    → α +ₒ β ＝ extended-sup (λ b → α +ₒ (β ↓ b) +ₒ 𝟙ₒ) α)
               × (∃! _⊕_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
                      ((α β : Ordinal 𝓤) → α ⊕ (β +ₒ 𝟙ₒ) ＝ (α ⊕ β) +ₒ 𝟙ₒ)
                    × ((α : Ordinal 𝓤) {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                          → α ⊕ (sup β) ＝ extended-sup (λ i → α ⊕ β i) α))
Proposition-10 α =
   𝟘ₒ-right-neutral α
 , +ₒ-commutes-with-successor α
 , +ₒ-preserves-suprema-up-to-join α
 , +ₒ-recursive-equation
 , +ₒ-is-uniquely-specified
  where
   open addition
   open addition-by-fixed-ordinal

Eq-double-dagger : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
Eq-double-dagger = exp-full-specification

Lemma-11 : (α : Ordinal 𝓤) (exp-α : Ordinal 𝓤 → Ordinal 𝓤)
         → exp-specification-zero α exp-α
         → exp-specification-succ α exp-α
         → exp-specification-sup  α exp-α
         → (exp-α 𝟙ₒ ＝ α)
         × (exp-α 𝟚ₒ ＝ α ×ₒ α)
         × ((α ≠ 𝟘ₒ) → is-monotone-⊴ exp-α)
Lemma-11 α exp-α exp-spec-zero exp-spec-succ exp-spec-sup =
   𝟙ₒ-neutral-exp α exp-α exp-spec-zero exp-spec-succ
 , exp-𝟚ₒ-is-×ₒ α exp-α exp-spec-zero exp-spec-succ
 , (λ α-nonzero → is-monotone-if-preserves-inhabited-suprema
                   exp-α (exp-spec-sup α-nonzero))

Proposition-12
 : (Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exp-full-specification exp)
 ↔ EM 𝓤
Proposition-12 =
   (λ (exp , (exp-zero , exp-succ , exp-sup)) →
    exponentiation-defined-everywhere-implies-EM
     exp
     exp-zero
     exp-succ
     (λ α → pr₁ (exp-sup α)))
 , EM-gives-full-exponentiation

Eq-double-dagger' : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
Eq-double-dagger' {𝓤} exp =
   ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-succ α (exp α))
 × ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-zero-sup-combined α (exp α))

\end{code}

Section 3. Abstract Algebraic Exponentiation

\begin{code}

Definition-13 : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
Definition-13 α β = α ^ₒ β

Proposition-14 : (α β : Ordinal 𝓤)
                 (a : ⟨ α ⟩) (b : ⟨ β ⟩) (e : ⟨ α ^ₒ (β ↓ b) ⟩)
               → α ^ₒ β ↓ ×ₒ-to-^ₒ α β {b} (e , a)
                 ＝ α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e)
Proposition-14 α β a b e = ^ₒ-↓-×ₒ-to-^ₒ α β

Proposition-15 : (α β γ : Ordinal 𝓤)
               → (β ⊴ γ → α ^ₒ β ⊴ α ^ₒ γ)
               × (𝟙ₒ ⊲ α → β ⊲ γ → α ^ₒ β ⊲ α ^ₒ γ)
Proposition-15 α β γ =   ^ₒ-monotone-in-exponent α β γ
                       , ^ₒ-order-preserving-in-exponent α β γ

Theorem-16 : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α
           → exp-specification-zero α (α ^ₒ_)
           × exp-specification-succ α (α ^ₒ_)
           × exp-specification-zero-sup-combined α (α ^ₒ_)
           × exp-specification-sup α (α ^ₒ_)
Theorem-16 {𝓤} α α-pos =   ^ₒ-satisfies-zero-specification {𝓤} {𝓤} α
                         , ^ₒ-satisfies-succ-specification {𝓤} {𝓤} α α-pos
                         , ^ₒ-satisfies-zero-sup-combined-specification α
                         , ^ₒ-satisfies-sup-specification α

Proposition-17 : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
               → α ^ₒ (β +ₒ γ) ＝ (α ^ₒ β) ×ₒ (α ^ₒ γ)
Proposition-17 = ^ₒ-by-+ₒ

Proposition-18 : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
               → (α ^ₒ β) ^ₒ γ ＝ α ^ₒ (β ×ₒ γ)
Proposition-18 α β γ = (^ₒ-by-×ₒ α β γ) ⁻¹

\end{code}

Section 4. Decreasing Lists: A Constructive Formulation
           of Sierpiński's Definition

\begin{code}

Definition-19 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝓤 ⊔ 𝓥 ̇
Definition-19 α β = DecrList₂ α β

Remark-20 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
            ((l , p) (l' , q) : DecrList₂ α β)
          → l ＝ l'
          → (l , p) ＝ (l' , q)
Remark-20 α β _ _ = to-DecrList₂-＝ α β

Proposition-21-i
 : EM 𝓤
 → ((α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
Proposition-21-i = EM-implies-subtype-of-positive-elements-an-ordinal

Proposition-21-ii
 : ((α : Ordinal (𝓤 ⁺⁺)) (x : ⟨ α ⟩) → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
 → EM 𝓤
Proposition-21-ii = subtype-of-positive-elements-an-ordinal-implies-EM

Lemma-22-i : (α : Ordinal 𝓤)
           → has-trichotomous-least-element α ↔ is-decomposable-into-one-plus α
Lemma-22-i α =   trichotomous-least-to-decomposable α
               , decomposable-to-trichotomous-least α

Lemma-22-ii : (α : Ordinal 𝓤)
              ((a₀ , a₀-tri) : has-trichotomous-least-element α)
              (β : Ordinal 𝓤)
            → α ＝ 𝟙ₒ +ₒ β
            → (β ＝ α ⁺[ a₀ , a₀-tri ])
            × (⟨ α ⁺[ a₀ , a₀-tri ] ⟩ ＝ (Σ a ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ a))
Lemma-22-ii α (a₀ , a₀-tri) β p =
   +ₒ-left-cancellable 𝟙ₒ β (α ⁺[ a₀ , a₀-tri ]) (p ⁻¹ ∙ q)
 , ⁺-is-subtype-of-positive-elements α (a₀ , a₀-tri)
  where
   q : α ＝ 𝟙ₒ +ₒ α ⁺[ a₀ , a₀-tri ]
   q = α ⁺[ a₀ , a₀-tri ]-part-of-decomposition

Definition-23 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
              → has-trichotomous-least-element α
              → Ordinal (𝓤 ⊔ 𝓥)
Definition-23 α β h = exponentiationᴸ α h β

module fixed-assumptions-1
        (α : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
       where

 α⁺ = α ⁺[ h ]

 NB[α⁺-eq] : α ＝ 𝟙ₒ +ₒ α⁺
 NB[α⁺-eq] = α ⁺[ h ]-part-of-decomposition

 exp[α,_] : Ordinal 𝓦 → Ordinal (𝓤 ⊔ 𝓦)
 exp[α, γ ] = exponentiationᴸ α h γ

 Proposition-24 : (β : Ordinal 𝓥) → has-trichotomous-least-element exp[α, β ]
 Proposition-24 β = exponentiationᴸ-has-trichotomous-least-element α h β

 Lemma-25-i : (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
              (f : ⟨ β ⟩ → ⟨ γ ⟩)
            → is-order-preserving β γ f
            → Σ f̅ ꞉ (⟨ exp[α, β ] ⟩ → ⟨ exp[α, γ ] ⟩)
                  , is-order-preserving exp[α, β ] exp[α, γ ] f̅
 Lemma-25-i β γ f f-order-pres =
    expᴸ-map α⁺ β γ f f-order-pres
  , expᴸ-map-is-order-preserving α⁺ β γ f f-order-pres

 Lemma-25-ii : (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
             → β ⊴ γ → exp[α, β ] ⊴ exp[α, γ ]
 Lemma-25-ii β γ (f , (f-init-seg , f-order-pres)) =
    expᴸ-map α⁺ β γ f f-order-pres
  , expᴸ-map-is-simulation α⁺ β γ f f-order-pres f-init-seg

module fixed-assumptions-2
        (α : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
        (β : Ordinal 𝓥)
       where

 open fixed-assumptions-1 α h

 Eq-4 : (b : ⟨ β ⟩) → exp[α, β ↓ b ] ⊴ exp[α, β ]
 Eq-4 = expᴸ-segment-inclusion-⊴ α⁺ β

 ι = expᴸ-segment-inclusion α⁺ β
 ι-list = expᴸ-segment-inclusion-list α⁺ β

 Eq-5 : (a : ⟨ α ⁺[ h ] ⟩) (b : ⟨ β ⟩)
      → (l : ⟨ exp[α, β ] ⟩)
      → is-decreasing-pr₂ α⁺ β ((a , b) ∷ pr₁ l)
      → ⟨ exponentiationᴸ α h (β ↓ b) ⟩
 Eq-5 a b l δ = expᴸ-tail α⁺ β a b (pr₁ l) δ

 τ = expᴸ-tail α⁺ β

 Eq-5-addendum-i
  : (a : ⟨ α⁺ ⟩) (b : ⟨ β ⟩)
    (l₁ l₂ : List ⟨ α⁺ ×ₒ β ⟩)
    (δ₁ : is-decreasing-pr₂ α⁺ β ((a , b) ∷ l₁))
    (δ₂ : is-decreasing-pr₂ α⁺ β ((a , b) ∷ l₂))
  → l₁ ≺⟨List (α⁺ ×ₒ β) ⟩ l₂
  → τ a b l₁ δ₁ ≺⟨ exp[α, β ↓ b ] ⟩ τ a b l₂ δ₂
 Eq-5-addendum-i a b l₁ l₂ δ₁ δ₂ = expᴸ-tail-is-order-preserving α⁺ β a b δ₁ δ₂

 Eq-5-addendum-ii : (a : ⟨ α⁺ ⟩) (b : ⟨ β ⟩)
                    (l : List ⟨ α⁺ ×ₒ β ⟩)
                    {δ : is-decreasing-pr₂ α⁺ β ((a , b) ∷ l)}
                    {ε : is-decreasing-pr₂ α⁺ β l}
                  → ι b (τ a b l δ) ＝ (l , ε)
 Eq-5-addendum-ii a b = expᴸ-tail-section-of-expᴸ-segment-inclusion α⁺ β a b

 Eq-5-addendum-iii : (a : ⟨ α⁺ ⟩) (b : ⟨ β ⟩)
                     (l : List ⟨ α⁺ ×ₒ (β ↓ b) ⟩)
                     {δ : is-decreasing-pr₂ α⁺ (β ↓ b) l}
                     {ε : is-decreasing-pr₂ α⁺ β ((a , b) ∷ ι-list b l)}
                   → τ a b (ι-list b l) ε ＝ (l , δ)
 Eq-5-addendum-iii a b l {δ} =
  expᴸ-segment-inclusion-section-of-expᴸ-tail α⁺ β a b l δ

 Proposition-26-i
  : (a : ⟨ α⁺ ⟩) (b : ⟨ β ⟩) (l : List ⟨ α⁺ ×ₒ β ⟩)
    (δ : is-decreasing-pr₂ α⁺ β ((a , b) ∷ l))
  → exp[α, β ] ↓ ((a , b ∷ l) , δ)
    ＝ exp[α, β ↓ b ] ×ₒ (𝟙ₒ +ₒ (α⁺ ↓ a)) +ₒ (exp[α, β ↓ b ] ↓ τ a b l δ)
 Proposition-26-i = expᴸ-↓-cons α⁺ β

 Proposition-26-ii
  : (a : ⟨ α⁺ ⟩) (b : ⟨ β ⟩) (l : ⟨ exp[α, β ↓ b ] ⟩)
  → exp[α, β ] ↓ extended-expᴸ-segment-inclusion α⁺ β b l a
    ＝ exp[α, β ↓ b ] ×ₒ (𝟙ₒ +ₒ (α⁺ ↓ a)) +ₒ (exp[α, β ↓ b ] ↓ l)
 Proposition-26-ii = expᴸ-↓-cons' α⁺ β

module fixed-assumptions-3
        (α : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
        (β : Ordinal 𝓥)
       where

 open fixed-assumptions-1 α h

 Theorem-27 : exp-specification-zero α (λ - → exp[α, - ])
            × exp-specification-succ α (λ - → exp[α, - ])
            × exp-specification-zero-sup-combined α (λ - → exp[α, - ])
            × exp-specification-sup α (λ - → exp[α, - ])
 Theorem-27 =   expᴸ-satisfies-zero-specification {𝓤} {𝓤} α⁺
              , transport⁻¹
                 (λ - → exp-specification-succ - (λ - → exp[α, - ]))
                 NB[α⁺-eq]
                 (expᴸ-satisfies-succ-specification {𝓤} α⁺)
              , transport⁻¹
                 (λ - → exp-specification-zero-sup-combined - (λ - → exp[α, - ]))
                 NB[α⁺-eq]
                 (expᴸ-satisfies-zero-sup-combined-specification {𝓤} α⁺)
              , transport⁻¹
                 (λ - → exp-specification-sup - (λ - → exp[α, - ]))
                 NB[α⁺-eq]
                 (expᴸ-satisfies-sup-specification {𝓤} α⁺)


 Proposition-28 : (β γ : Ordinal 𝓥)
                → exp[α, β +ₒ γ ] ＝ exp[α, β ] ×ₒ exp[α, γ ]
 Proposition-28 = expᴸ-by-+ₒ α⁺

 Proposition-29 : (β : Ordinal 𝓥)
                → has-decidable-equality ⟨ α ⟩
                → has-decidable-equality ⟨ β ⟩
                → has-decidable-equality ⟨ exp[α, β ] ⟩
 Proposition-29 β = exponentiationᴸ-preserves-discreteness α β h

private
 tri-least : (α : Ordinal 𝓤)
           → has-least α
           → is-trichotomous α
           → has-trichotomous-least-element α
 tri-least α (⊥ , ⊥-is-least) t =
  ⊥ ,
  is-trichotomous-and-least-implies-is-trichotomous-least α ⊥ (t ⊥) ⊥-is-least

Proposition-30
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (h : has-least α)
 → (t : is-trichotomous α)
 → is-trichotomous β
 → is-trichotomous (exponentiationᴸ α (tri-least α h t) β)
Proposition-30 = exponentiationᴸ-preserves-trichotomy

\end{code}

Section 5. Abstract and Concrete Exponentiation

\begin{code}

Theorem-31 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
           → α ^ₒ β ＝ exponentiationᴸ α h β
Theorem-31 α β h = (exponentiation-constructions-agree α β h) ⁻¹

Corollary-32-i : (α β : Ordinal 𝓤)
               → has-trichotomous-least-element α
               → has-decidable-equality ⟨ α ⟩
               → has-decidable-equality ⟨ β ⟩
               → has-decidable-equality ⟨ α ^ₒ β ⟩
Corollary-32-i =
 ^ₒ-preserves-discreteness-for-base-with-trichotomous-least-element

Corollary-32-ii : (α β : Ordinal 𝓤)
                → has-least α
                → is-trichotomous α
                → is-trichotomous β
                → is-trichotomous (α ^ₒ β)
Corollary-32-ii = ^ₒ-preserves-trichotomy

module fixed-assumptions-4
        (α β γ : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
       where

 private
  h' : has-trichotomous-least-element (exponentiationᴸ α h β)
  h' = exponentiationᴸ-has-trichotomous-least-element α h β

 Corollary-33
  : exponentiationᴸ α h (β ×ₒ γ) ＝ exponentiationᴸ (exponentiationᴸ α h β) h' γ
 Corollary-33 = exponentiationᴸ-by-×ₒ α h β γ

module fixed-assumptions-5
        (α : Ordinal 𝓤)
       where

 open denotations α

 Definition-34 : (β : Ordinal 𝓥) → DecrList₂ α β → ⟨ α ^ₒ β ⟩
 Definition-34 β l = ⟦ l ⟧⟨ β ⟩

 -- Remark-35: By inspection of the definition of denotation.

 Proposition-36 : (β : Ordinal 𝓥) → is-surjection (λ l → ⟦ l ⟧⟨ β ⟩)
 Proposition-36 = ⟦⟧-is-surjection

module fixed-assumptions-6
        (α : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
        (β : Ordinal 𝓤)
       where

 open denotations

 private
  α⁺ = α ⁺[ h ]

  NB : α ＝ 𝟙ₒ +ₒ α⁺
  NB = α ⁺[ h ]-part-of-decomposition

 con-to-abs : ⟨ expᴸ[𝟙+ α⁺ ] β ⟩ → ⟨ (𝟙ₒ +ₒ α⁺) ^ₒ β ⟩
 con-to-abs = induced-map α⁺ β

 Lemma-38 : con-to-abs ∼ denotation' α⁺ β

 Lemma-39 : denotation (𝟙ₒ +ₒ α⁺) β ∼ denotation' α⁺ β ∘ normalize α⁺ β

 Theorem-37 : denotation (𝟙ₒ +ₒ α⁺) β ∼ con-to-abs ∘ (normalize α⁺ β)
 Theorem-37 l = (Lemma-39 l) ∙ (Lemma-38 (normalize α⁺ β l) ⁻¹)

 Lemma-38 = induced-map-is-denotation' α⁺ β

 Lemma-39 = denotations-are-related-via-normalization α⁺ β

 -- Remark-40: No formalizable content

Definition-41 : (α β : Ordinal 𝓤) → 𝓤 ̇
Definition-41 α β = GraysonList (underlying-order α) (underlying-order β)

Proposition-42-i
 : EM 𝓤
 → (α β : Ordinal 𝓤)
 → is-well-order (Grayson-order (underlying-order α) (underlying-order β))
Proposition-42-i = EM-implies-GraysonList-is-ordinal

Proposition-42-ii
 : ((α β : Ordinal (𝓤 ⁺⁺))
   → has-least α
   → is-well-order (Grayson-order (underlying-order α) (underlying-order β)))
 → EM 𝓤
Proposition-42-ii = GraysonList-always-ordinal-implies-EM

\end{code}

Section 6. Abstract Cancellation Arithmetic

\begin{code}

Eq-6 : (𝟘ₒ +ₒ ω ＝ ω)  ×  (𝟙ₒ ×ₒ ω ＝ ω)  ×  (𝟚ₒ ^ₒ ω ＝ ω)
     × (𝟙ₒ +ₒ ω ＝ ω)  ×  (𝟚ₒ ×ₒ ω ＝ ω)  ×  (𝟛ₒ ^ₒ ω ＝ ω)
Eq-6 = 𝟘ₒ+ₒω-is-ω , 𝟙ₒ×ₒω-is-ω , [1]
     , 𝟙ₒ+ₒω-is-ω , 𝟚ₒ×ₒω-is-ω , [2]
 where
  [1] = (ap (_^ₒ ω) (Fin-ordinal-two ua ⁻¹) ∙ (Fin-ordinal- 2 ^ₒω-is-ω ⋆))
  [2] = (ap (_^ₒ ω) (Fin-ordinal-three ua ⁻¹) ∙ (Fin-ordinal- 3 ^ₒω-is-ω ⋆))

Eq-6-addendum-i : ¬ ((α β γ : Ordinal 𝓤₀) → α +ₒ γ ＝ β +ₒ γ → α ＝ β)
Eq-6-addendum-i = no-right-cancellation-+ₒ

Eq-6-addendum-ii : ¬ ((α β γ : Ordinal 𝓤₀) → α ×ₒ γ ＝ β ×ₒ γ → α ＝ β)
Eq-6-addendum-ii = no-right-cancellation-×ₒ

Eq-6-addendum-iii : ¬ ((α β γ : Ordinal 𝓤₀) → α ^ₒ γ ＝ β ^ₒ γ → α ＝ β)
Eq-6-addendum-iii = no-right-cancellation-^ₒ

Lemma-43 : (α β : Ordinal 𝓤)
         → β ⊲ α → ¬ (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f)
Lemma-43 α β l 𝕗 = order-preserving-gives-not-⊲ α β 𝕗 l

Lemma-44 : (α β γ : Ordinal 𝓤)
         → (α ⊴ β → α ≤ᶜˡ β)
         × (α ⊲ β → α <ᶜˡ β)
         × (α <ᶜˡ β → α ≤ᶜˡ β)
         × (α <ᶜˡ β → β ≤ᶜˡ γ → α <ᶜˡ γ)
         × (α ≤ᶜˡ β → β <ᶜˡ γ → α <ᶜˡ γ)
         × ¬ (α <ᶜˡ α)
Lemma-44 α β γ =
   ⊴-gives-≤ᶜˡ α β
 , ⊲-gives-<ᶜˡ α β
 , <ᶜˡ-gives-≤ᶜˡ α β
 , <ᶜˡ-≤ᶜˡ-to-<ᶜˡ α β γ
 , ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ α β γ
 , <ᶜˡ-irrefl α

Definition-45 : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
Definition-45 {𝓤} F = Σ S ꞉ (Ordinal 𝓤 → Ordinal 𝓤) ,
                      Σ Z ꞉ Ordinal 𝓤 ,
                         ((β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
                       × ({I : 𝓤 ̇ } (L : I → Ordinal 𝓤)
                            → F (sup L) ＝ extended-sup (F ∘ L) Z)

Remark-46 : (F : Ordinal 𝓤 → Ordinal 𝓤)
          → ((S , Z , _) : Definition-45 F)
          → F ＝ canonical-spec-by-cases S Z
Remark-46 F (S , Z , F-succ , F-sup) =
 dfunext fe' presentation-by-transfinite-recursion
  where
   open operation-by-cases-framework F S Z F-succ F-sup

module fixed-assumptions-7
        (F : Ordinal 𝓤 → Ordinal 𝓤)
        (S : Ordinal 𝓤 → Ordinal 𝓤)
        (Z : Ordinal 𝓤)
        (F-succ : (β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
        (F-sup : {I : 𝓤 ̇ } (L : I → Ordinal 𝓤)
               → F (sup L) ＝ extended-sup (F ∘ L) Z)
       where

 Assumption-1 : 𝓤 ⁺ ̇
 Assumption-1 = framework.Assumption-1 F S Z F-succ F-sup

 Assumption-2 : 𝓤 ⁺ ̇
 Assumption-2 = framework.Assumption-2 F S Z F-succ F-sup

 Assumption-3 : 𝓤 ⁺ ̇
 Assumption-3 = framework.Assumption-3 F S Z F-succ F-sup

 open framework F S Z F-succ F-sup
  hiding (Assumption-1; Assumption-2; Assumption-3)

 Lemma-47 : (β γ : Ordinal 𝓤) → β ⊴ γ → F β ⊴ F γ
 Lemma-47 = is-monotone-if-preserves-suprema-up-to-join F Z F-sup

 Lemma-48 : Assumption-2 → (β γ : Ordinal 𝓤) → β ⊲ γ → F β ⊲ F γ
 Lemma-48 = F-preserves-⊲

 Lemma-49 : (β γ : Ordinal 𝓤)
          → F 𝟘ₒ ⊴ β
          → β ⊲ F γ
          → Assumption-1
          → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
 Lemma-49 β γ l₀ l₁ asm-1 = F-tightening-bounds asm-1 β l₀ γ l₁

 open uo-order

 Lemma-50 : (A : 𝓤 ̇ )(_≺_ : A → A → 𝓥 ̇ )
          → is-well-founded _≺_
          → is-well-founded (_≺ᵤₒ_ A _≺_)
 Lemma-50 = ≺ᵤₒ-is-well-founded

 Lemma-51 : Assumption-1
          → Assumption-2
          → Assumption-3
          → (β γ δ : Ordinal 𝓤)
          → F β ⊴ F γ +ₒ δ
          → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ)
          → β ⊴ γ
 Lemma-51 _ = F-reflects-⊴'

 Corollary-52 : Assumption-1
              → Assumption-2
              → Assumption-3
              → (β γ : Ordinal 𝓤)
              → (F β ⊴ F γ → β ⊴ γ)
              × (F β ＝ F γ → β ＝ γ)
 Corollary-52 asm-1 asm-2 asm-3 β γ =
    framework-with-assumptions.F-reflects-⊴ asm-2 asm-3 β γ
  , framework-with-assumptions.F-left-cancellable asm-2 asm-3

Theorem-53 : (α : Ordinal 𝓤)
           → is-⊴-reflecting (α +ₒ_) × left-cancellable (α +ₒ_)
           × (𝟙ₒ ⊴ α → is-⊴-reflecting (α ×ₒ_) × left-cancellable (α ×ₒ_))
           × (𝟚ₒ ⊴ α → has-trichotomous-least-element α
               → is-⊴-reflecting (α ^ₒ_) × left-cancellable (α ^ₒ_))
Theorem-53 α =
   +ₒ-reflects-⊴ α , +ₒ-left-cancellable' α
 , (λ l → let l' = lr-implication (at-least-𝟙₀-iff-greater-than-𝟘ₒ α) l
          in ×ₒ-reflects-⊴ α l' , ×ₒ-left-cancellable' α l')
 , (λ l t → ^ₒ-reflects-⊴ α l t , ^ₒ-left-cancellable α l t)

Proposition-54-i : (α β γ : Ordinal 𝓤)
                 → ((f , _) : α +ₒ β ⊴ α +ₒ γ)
                 → Σ (h , _) ꞉ β ⊴ γ , ((a : ⟨ α ⟩) → f (inl a) ＝ inl a)
                       × ((b : ⟨ β ⟩) → f (inr b) ＝ inr (h b))
Proposition-54-i = +ₒ-simulation-behaviour

Proposition-54-ii
 : (α β γ : Ordinal 𝓤)
 → 𝟘ₒ ⊲ α
 → ((f , _) : α ×ₒ β ⊴ α ×ₒ γ)
 → Σ (h , _) ꞉ β ⊴ γ , ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → f (a , b) ＝ (a , h b))
Proposition-54-ii = ×ₒ-simulation-behaviour

Proposition-54-iii
 : (α β γ : Ordinal 𝓤)
 → (t : has-trichotomous-least-element α)
 → 𝟚ₒ ⊴ α
 → ((f , _) : exponentiationᴸ α t β ⊴ exponentiationᴸ α t γ)
 → Σ (h , _) ꞉ β ⊴ γ ,
     ((ℓ : ⟨ exponentiationᴸ α t β ⟩)
               → DecrList₂-list _ _ (f ℓ)
                 ＝ map (λ (a , b) → (a , h b)) (DecrList₂-list _ _ ℓ))
Proposition-54-iii = exponentiationᴸ-simulation-behaviour

\end{code}

Section 7. Constructive Taboos

\begin{code}

Proposition-55
 : (((α β γ : Ordinal 𝓤) → has-trichotomous-least-element α
                         → has-trichotomous-least-element β
                         → α ⊴ β → α ^ₒ γ ⊴ β ^ₒ γ)
   ↔ EM 𝓤)
 × (((α β γ : Ordinal 𝓤) → has-trichotomous-least-element α
                         → has-trichotomous-least-element β
                         → α ⊲ β → α ^ₒ γ ⊴ β ^ₒ γ)
   → EM 𝓤)
 × (((α β : Ordinal 𝓤) → has-trichotomous-least-element α
                       → has-trichotomous-least-element β
                       → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β)
   → EM 𝓤)
Proposition-55 =   (  ^ₒ-monotone-in-base-implies-EM
                   , (λ em α β γ _ _ → EM-implies-exp-monotone-in-base em α β γ))
                 , ^ₒ-weakly-monotone-in-base-implies-EM
                 , ×ₒ-weakly-monotone-in-both-arguments-implies-EM

Lemma-56 : (P : 𝓤 ̇  ) (i : is-prop P)
         → let Pₒ = prop-ordinal P i in
           𝟚ₒ {𝓤} ^ₒ Pₒ ＝ 𝟙ₒ +ₒ Pₒ
Lemma-56 = ^ₒ-𝟚ₒ-by-prop

Lemma-57
 : ((α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩) → is-order-preserving α β f → α ⊴ β)
 ↔ EM 𝓤
Lemma-57 =   order-preserving-gives-≼-implies-EM ∘ H₁
           , H₂ ∘ EM-implies-order-preserving-gives-≼
 where
  H₁ = λ h α β (f , f-order-pres) → ⊴-gives-≼ α β (h α β  f   f-order-pres)
  H₂ = λ h α β  f   f-order-pres  → ≼-gives-⊴ α β (h α β (f , f-order-pres))

Proposition-58-i : ((α β : Ordinal 𝓤) → β ⊴ α +ₒ β) ↔ EM 𝓤
Proposition-58-i =   +ₒ-as-large-as-right-summand-implies-EM
                   , EM-implies-+ₒ-as-large-as-right-summand

Proposition-58-i' : ((α β : Ordinal 𝓤) → has-trichotomous-least-element α
                                       → has-trichotomous-least-element β
                                       → β ⊴ α +ₒ β)
                  → EM 𝓤
Proposition-58-i' hyp P P-is-prop =
 decidability
  (hyp α β (decomposable-to-trichotomous-least α (Pₒ , refl))
           (decomposable-to-trichotomous-least β (𝟙ₒ , refl)))
  where
   open +ₒ-inflationary-counterexample P P-is-prop

Proposition-58-ii : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β) ↔ EM 𝓤
Proposition-58-ii =  ×ₒ-as-large-as-right-factor-implies-EM
                   , EM-implies-×ₒ-as-large-as-right-factor

Proposition-58-ii' : ((α β : Ordinal 𝓤) → has-trichotomous-least-element α
                                        → has-trichotomous-least-element β
                                        → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β)
                   → EM 𝓤
Proposition-58-ii' = ×ₒ-as-large-as-right-factor-implies-EM'

Proposition-58-iii : ((β : Ordinal 𝓤) → β ⊴ 𝟚ₒ ^ₒ β) ↔ EM 𝓤
Proposition-58-iii = 𝟚ₒ^ₒ-as-large-as-exponent-implies-EM
                     , (λ em β → EM-implies-^ₒ-as-large-as-exponent
                                  em 𝟚ₒ β (successor-increasing 𝟙ₒ))

Proposition-58-iii'
 : ((β : Ordinal 𝓤) → has-trichotomous-least-element β → β ⊴ 𝟚ₒ ^ₒ β) → EM 𝓤
Proposition-58-iii' = 𝟚ₒ^ₒ-as-large-as-exponent-implies-EM'

Proposition-58-iv
 : ((α β : Ordinal 𝓤) → 𝟙ₒ ⊲ α → β ⊴ α ^ₒ β) ↔ EM 𝓤
Proposition-58-iv =   ^ₒ-as-large-as-exponent-implies-EM
                    , EM-implies-^ₒ-as-large-as-exponent

Proposition-58-iv'
 : ((α β : Ordinal 𝓤) → 𝟙ₒ ⊲ α
                      → has-trichotomous-least-element α
                      → has-trichotomous-least-element β → β ⊴ α ^ₒ β)
 → EM 𝓤
Proposition-58-iv' =   ^ₒ-as-large-as-exponent-implies-EM'

\end{code}

Section 8. Approximating subtraction, division and logarithm operations

\begin{code}

Definition-59 : (P : Ordinal 𝓤 → 𝓥 ̇ ) → (𝓤 ⁺ ⊔ 𝓥 ̇) × (𝓤 ⁺ ⊔ 𝓥 ̇) × (𝓤 ⁺ ⊔ 𝓥 ̇)
Definition-59 P = bounded P , antitone P , closed-under-suprema P

Proposition-60 : (P : Ordinal 𝓤 → 𝓤 ̇ )
               → antitone P
               → bounded P
               → is-prop-valued-family P
               → closed-under-suprema P
               → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying P
Proposition-60 P at b p = greatest-ordinal-satisfying-predicate P p b at

Theorem-61-i : (t : Ordinal 𝓤 → Ordinal 𝓤)
             → (δ₀ : Ordinal 𝓤)
             → ({I : 𝓤 ̇ } (F : I → Ordinal 𝓤) → t (sup F) ＝ extended-sup (t ∘ F) δ₀)
             → (δ : Ordinal 𝓤)
             → δ₀ ⊴ δ
             → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (t - ⊴ δ) × (- ⊴ δ))
Theorem-61-i t δ₀ t-sup δ l = Enderton-like.enderton-like t δ₀ δ l t-sup

Theorem-61-ii : (t : Ordinal 𝓤 → Ordinal 𝓤)
              → (δ₀ : Ordinal 𝓤)
              → ({I : 𝓤 ̇ } (F : I → Ordinal 𝓤) → t (sup F) ＝ extended-sup (t ∘ F) δ₀)
              → ((α : Ordinal 𝓤) → α ⊴ t α)
              → (δ : Ordinal 𝓤)
              → δ₀ ⊴ δ
              → Σ γ ꞉ Ordinal 𝓤 , γ ⊴ δ × γ greatest-satisfying (λ - → (t - ⊴ δ))
Theorem-61-ii t δ₀ t-sup t-infl δ l =
 Enderton-like-inflationary.enderton-like-inflationary t δ₀ δ l t-sup t-infl

Proposition-62
 : (α β : Ordinal 𝓤)
 → (α ⊴ β → Σ γˢ ꞉ Ordinal 𝓤 ,
              γˢ greatest-satisfying (λ - → (α +ₒ - ⊴ β) × (- ⊴ β)))
 × (Σ γᵈ ꞉ Ordinal 𝓤 ,
      γᵈ greatest-satisfying (λ - → (α ×ₒ - ⊴ β) × (- ⊴ β)))
 × (𝟙ₒ ⊴ β → Σ γˡ ꞉ Ordinal 𝓤 ,
               γˡ greatest-satisfying (λ - → (α ^ₒ - ⊴ β) × (- ⊴ β)))
Proposition-62 α β =
   approximate-subtraction α β
 , approximate-division α β
 , aproximate-logarithm α β

Proposition-63-i
 : ((α β : Ordinal 𝓤) → α ⊴ β
     → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β))))
 ↔ EM 𝓤
Proposition-63-i =
   approximate-subtraction-variation-implies-EM
 , EM-implies-approximate-subtraction-variation

Proposition-63-ii
 : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β))))
 ↔ EM 𝓤
Proposition-63-ii =
   approximate-division-variation-implies-EM
 , EM-implies-approximate-division-variation

Proposition-63-iii
 : ((α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → 𝟙ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β))))
 ↔ EM 𝓤
Proposition-63-iii =
   approximate-logarithm-variation-implies-EM
 , EM-implies-approximate-logarithm-variation

\end{code}
