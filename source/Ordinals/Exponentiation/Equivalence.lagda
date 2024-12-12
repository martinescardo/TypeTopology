Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 May 2023.

TODO: COMMENT

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Equivalence
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.List
open import MLTT.Spartan

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

open PropositionalTruncation pt
open suprema pt sr

equivalence-of-exponentiation-constructions' : (α β : Ordinal 𝓤)
                                             → (𝟙ₒ +ₒ α) ^ₒ β ＝ expᴸ α β
equivalence-of-exponentiation-constructions' {𝓤} α =
 transfinite-induction-on-OO (λ β → α⁺ ^ₒ β ＝ expᴸ α β) I
  where
   α⁺ = 𝟙ₒ +ₒ α

   I : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → α⁺ ^ₒ (β ↓ b) ＝ (expᴸ α (β ↓ b)))
     → α⁺ ^ₒ β ＝ (expᴸ α β)
   I β IH = ⊴-antisym (α⁺ ^ₒ β) (expᴸ α β)
             (to-⊴ (α⁺ ^ₒ β) (expᴸ α β) III)
             (to-⊴ (expᴸ α β) (α⁺ ^ₒ β) II)
    where
     II : (y : ⟨ expᴸ α β ⟩) → expᴸ α β ↓ y ⊲ α⁺ ^ₒ β
     II ([] , δ)            = ^ₒ-⊥ α⁺ β ,
      (expᴸ α β ↓ ([] , δ) ＝⟨ ([𝟙+α]^β-has-least' α β δ) ⁻¹ ⟩
       𝟘ₒ                    ＝⟨ (^ₒ-↓-⊥ α⁺ β) ⁻¹ ⟩
       α⁺ ^ₒ β ↓ ^ₒ-⊥ α⁺ β   ∎)
     II (((a , b) ∷ l) , δ) = e' ,
      (expᴸ α β ↓ ((a , b ∷ l) , δ)                                 ＝⟨ II₁ ⟩
       expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ((expᴸ α (β ↓ b)) ↓ l') ＝⟨ II₂ ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ ((expᴸ α (β ↓ b)) ↓ l')  ＝⟨ II₃ ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)      ＝⟨ II₄ ⟩
       α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ (inr a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)       ＝⟨ II₅ ⟩
       α⁺ ^ₒ β ↓ e'                                                 ∎)
        where
         l' = expᴸ-tail α β a b l δ
         e  = Idtofunₒ (IH b ⁻¹) l'
         e' = ×ₒ-to-^ₒ α⁺ β (e , inr a)

         II₁ = expᴸ-↓-cons α β a b l δ
         II₂ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l'))
                  ((IH b) ⁻¹)
         II₃ = ap (α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                  (Idtofunₒ-↓-lemma (IH b ⁻¹))
         II₄ = ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e))
                  (+ₒ-↓-right a)
         II₅ = (^ₒ-↓-×ₒ-to-^ₒ α⁺ β) ⁻¹

     III : (y : ⟨ α⁺ ^ₒ β ⟩) → α⁺ ^ₒ β ↓ y ⊲ expᴸ α β
     III y = ∥∥-rec
              (⊲-is-prop-valued (α⁺ ^ₒ β ↓ y) (expᴸ α β))
              IV
              (^ₒ-↓ α⁺ β)
      where
       IV : (α⁺ ^ₒ β ↓ y ＝ 𝟘ₒ)
           + (Σ b ꞉ ⟨ β ⟩ , Σ e ꞉ ⟨ α⁺ ^ₒ (β ↓ b) ⟩ , Σ x ꞉ ⟨ α⁺ ⟩ ,
               α⁺ ^ₒ β ↓ y ＝ α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ x) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e))
           → α⁺ ^ₒ β ↓ y ⊲ (expᴸ α β)
       IV (inl p) = expᴸ-⊥ α β ,
        (α⁺ ^ₒ β ↓ y           ＝⟨ p ⟩
         𝟘ₒ                    ＝⟨ (expᴸ-↓-⊥ α β) ⁻¹ ⟩
         expᴸ α β ↓ expᴸ-⊥ α β ∎)
       IV (inr (b , e , inl ⋆ , p)) = l₂ ,
        (α⁺ ^ₒ β ↓ y                                          ＝⟨ p   ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ inl ⋆) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e) ＝⟨ IV₁ ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ ↓ ⋆) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)     ＝⟨ IV₂ ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ 𝟘ₒ +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)           ＝⟨ IV₃ ⟩
         𝟘ₒ +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)                            ＝⟨ IV₄ ⟩
         α⁺ ^ₒ (β ↓ b) ↓ e                                    ＝⟨ IV₅ ⟩
         (expᴸ α (β ↓ b)) ↓ l₁                                ＝⟨ IV₆ ⟩
         expᴸ α β ↓ l₂                                        ∎)
        where
         σ : expᴸ α (β ↓ b) ⊴ expᴸ α β
         σ = expᴸ-segment-inclusion-⊴ α β b
         l₁ = Idtofunₒ (IH b) e
         l₂ = [ expᴸ α (β ↓ b) , expᴸ α β ]⟨ σ ⟩ l₁

         IV₁ = ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e))
                  ((+ₒ-↓-left ⋆) ⁻¹)
         IV₂ = ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) 𝟙ₒ-↓
         IV₃ = ap (_+ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)) (×ₒ-𝟘ₒ-right (α⁺ ^ₒ (β ↓ b)))
         IV₄ = 𝟘ₒ-left-neutral (α⁺ ^ₒ (β ↓ b) ↓ e)
         IV₅ = Idtofunₒ-↓-lemma (IH b)
         IV₆ = simulations-preserve-↓ (expᴸ α (β ↓ b)) (expᴸ α β) σ l₁
       IV (inr (b , e , inr a , p)) = l₂ ,
        (α⁺ ^ₒ β ↓ y                                                ＝⟨ p   ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (α⁺ ↓ inr a) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)       ＝⟨ IV₁ ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e)    ＝⟨ IV₂ ⟩
         α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l₁)  ＝⟨ IV₃ ⟩
         expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l₁) ＝⟨ IV₄ ⟩
         expᴸ α β ↓ l₂                                              ∎)
        where
         l₁ = Idtofunₒ (IH b) e
         l₂ = extended-expᴸ-segment-inclusion α β b l₁ a

         IV₁ = ap (λ - → α⁺ ^ₒ (β ↓ b) ×ₒ - +ₒ (α⁺ ^ₒ (β ↓ b) ↓ e))
                  ((+ₒ-↓-right a) ⁻¹)
         IV₂ = ap (α⁺ ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                  (Idtofunₒ-↓-lemma (IH b))
         IV₃ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l₁)) (IH b)
         IV₄ = expᴸ-↓-cons' α β a b l₁ ⁻¹

equivalence-of-exponentiation-constructions
 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
 → exponentiationᴸ α h β ＝ α ^ₒ β
equivalence-of-exponentiation-constructions α β h =
 exponentiationᴸ α h β ＝⟨ refl ⟩
 expᴸ α⁺ β             ＝⟨ I ⟩
 (𝟙ₒ +ₒ α⁺) ^ₒ β       ＝⟨ II ⟩
 α ^ₒ β                ∎
  where
   α⁺ = α ⁺[ h ]
   I = (equivalence-of-exponentiation-constructions' α⁺ β) ⁻¹
   II = ap (_^ₒ β) ((α ⁺[ h ]-part-of-decomposition) ⁻¹)

\end{code}