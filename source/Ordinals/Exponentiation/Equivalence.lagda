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

exponentiation-constructions-agree' : (α β : Ordinal 𝓤)
                                    → expᴸ[𝟙+ α ] β ＝ (𝟙ₒ +ₒ α) ^ₒ β
exponentiation-constructions-agree' {𝓤} α =
 transfinite-induction-on-OO (λ β → expᴸ[𝟙+ α ] β ＝ α' ^ₒ β) I
  where
   α' = 𝟙ₒ +ₒ α

   I : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → expᴸ[𝟙+ α ] (β ↓ b) ＝ α' ^ₒ (β ↓ b))
     → expᴸ[𝟙+ α ] β ＝ α' ^ₒ β
   I β IH = ⊴-antisym (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
             (to-⊴ (expᴸ[𝟙+ α ] β) (α' ^ₒ β) II)
             (to-⊴ (α' ^ₒ β) (expᴸ[𝟙+ α ] β) III)
    where
     II : (y : ⟨ expᴸ[𝟙+ α ] β ⟩) → expᴸ[𝟙+ α ] β ↓ y ⊲ α' ^ₒ β
     II ([] , δ) = ^ₒ-⊥ α' β ,
      (expᴸ[𝟙+ α ] β ↓ ([] , δ) ＝⟨ expᴸ-↓-⊥' α β ⟩
       𝟘ₒ                       ＝⟨ (^ₒ-↓-⊥ α' β) ⁻¹ ⟩
       α' ^ₒ β ↓ ^ₒ-⊥ α' β      ∎)
     II (((a , b) ∷ l) , δ) = e' ,
      (expᴸ[𝟙+ α ] β ↓ ((a , b ∷ l) , δ)                                    ＝⟨ II₁ ⟩
       expᴸ[𝟙+ α ] (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l') ＝⟨ II₂ ⟩
       α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l')       ＝⟨ II₃ ⟩
       α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α' ^ₒ (β ↓ b) ↓ e)              ＝⟨ II₄ ⟩
       α' ^ₒ (β ↓ b) ×ₒ (α' ↓ (inr a)) +ₒ (α' ^ₒ (β ↓ b) ↓ e)               ＝⟨ II₅ ⟩
       α' ^ₒ β ↓ e'                                                         ∎)
        where
         l' = expᴸ-tail α β a b l δ
         e  = Idtofunₒ (IH b) l'
         e' = ×ₒ-to-^ₒ α' β (e , inr a)

         II₁ = expᴸ-↓-cons α β a b l δ
         II₂ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l'))
                  (IH b)
         II₃ = ap (α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                  (Idtofunₒ-↓-lemma (IH b))
         II₄ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e))
                  (+ₒ-↓-right a)
         II₅ = (^ₒ-↓-×ₒ-to-^ₒ α' β) ⁻¹

     III : (y : ⟨ α' ^ₒ β ⟩) → α' ^ₒ β ↓ y ⊲ expᴸ[𝟙+ α ] β
     III y = ∥∥-rec
              (⊲-is-prop-valued (α' ^ₒ β ↓ y) (expᴸ[𝟙+ α ] β))
              IV
              (^ₒ-↓ α' β)
      where
       IV : (α' ^ₒ β ↓ y ＝ 𝟘ₒ)
           + (Σ b ꞉ ⟨ β ⟩ , Σ e ꞉ ⟨ α' ^ₒ (β ↓ b) ⟩ , Σ x ꞉ ⟨ α' ⟩ ,
               α' ^ₒ β ↓ y ＝ α' ^ₒ (β ↓ b) ×ₒ (α' ↓ x) +ₒ (α' ^ₒ (β ↓ b) ↓ e))
           → α' ^ₒ β ↓ y ⊲ (expᴸ[𝟙+ α ] β)
       IV (inl p) = expᴸ-⊥ α β ,
        (α' ^ₒ β ↓ y           ＝⟨ p ⟩
         𝟘ₒ                    ＝⟨ (expᴸ-↓-⊥ α β) ⁻¹ ⟩
         expᴸ[𝟙+ α ] β ↓ expᴸ-⊥ α β ∎)
       IV (inr (b , e , inl ⋆ , p)) = l₂ ,
        (α' ^ₒ β ↓ y                                          ＝⟨ p   ⟩
         α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inl ⋆) +ₒ (α' ^ₒ (β ↓ b) ↓ e) ＝⟨ IV₁ ⟩
         α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ ↓ ⋆) +ₒ (α' ^ₒ (β ↓ b) ↓ e)     ＝⟨ IV₂ ⟩
         α' ^ₒ (β ↓ b) ×ₒ 𝟘ₒ +ₒ (α' ^ₒ (β ↓ b) ↓ e)           ＝⟨ IV₃ ⟩
         𝟘ₒ +ₒ (α' ^ₒ (β ↓ b) ↓ e)                            ＝⟨ IV₄ ⟩
         α' ^ₒ (β ↓ b) ↓ e                                    ＝⟨ IV₅ ⟩
         (expᴸ[𝟙+ α ] (β ↓ b)) ↓ l₁                           ＝⟨ IV₆ ⟩
         expᴸ[𝟙+ α ] β ↓ l₂                                   ∎)
        where
         σ : expᴸ[𝟙+ α ] (β ↓ b) ⊴ expᴸ[𝟙+ α ] β
         σ = expᴸ-segment-inclusion-⊴ α β b
         l₁ = Idtofunₒ (IH b ⁻¹) e
         l₂ = [ expᴸ[𝟙+ α ] (β ↓ b) , expᴸ[𝟙+ α ] β ]⟨ σ ⟩ l₁

         IV₁ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e))
                  ((+ₒ-↓-left ⋆) ⁻¹)
         IV₂ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e)) 𝟙ₒ-↓
         IV₃ = ap (_+ₒ (α' ^ₒ (β ↓ b) ↓ e)) (×ₒ-𝟘ₒ-right (α' ^ₒ (β ↓ b)))
         IV₄ = 𝟘ₒ-left-neutral (α' ^ₒ (β ↓ b) ↓ e)
         IV₅ = Idtofunₒ-↓-lemma (IH b ⁻¹)
         IV₆ = simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (expᴸ[𝟙+ α ] β) σ l₁
       IV (inr (b , e , inr a , p)) = l₂ ,
        (α' ^ₒ β ↓ y                                                          ＝⟨ p   ⟩
         α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inr a) +ₒ (α' ^ₒ (β ↓ b) ↓ e)                 ＝⟨ IV₁ ⟩
         α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α' ^ₒ (β ↓ b) ↓ e)              ＝⟨ IV₂ ⟩
         α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁)       ＝⟨ IV₃ ⟩
         expᴸ[𝟙+ α ] (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁) ＝⟨ IV₄ ⟩
         expᴸ[𝟙+ α ] β ↓ l₂                                                   ∎)
        where
         l₁ = Idtofunₒ (IH b ⁻¹) e
         l₂ = extended-expᴸ-segment-inclusion α β b l₁ a

         IV₁ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e))
                  ((+ₒ-↓-right a) ⁻¹)
         IV₂ = ap (α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                  (Idtofunₒ-↓-lemma (IH b ⁻¹))
         IV₃ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁)) (IH b ⁻¹)
         IV₄ = expᴸ-↓-cons' α β a b l₁ ⁻¹

exponentiation-constructions-agree
 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
 → exponentiationᴸ α h β ＝ α ^ₒ β
exponentiation-constructions-agree α β h =
 exponentiationᴸ α h β ＝⟨ refl ⟩
 expᴸ[𝟙+ α⁺ ] β        ＝⟨ I ⟩
 (𝟙ₒ +ₒ α⁺) ^ₒ β       ＝⟨ II ⟩
 α ^ₒ β                ∎
  where
   α⁺ = α ⁺[ h ]
   I = exponentiation-constructions-agree' α⁺ β
   II = ap (_^ₒ β) ((α ⁺[ h ]-part-of-decomposition) ⁻¹)

\end{code}

TODO: Clean up and rename
TODO: 80 char limit

TODO: Implement commented code below

\begin{code}

{-
-- Define alias DL for expᴸ

 f : (α β : Ordinal 𝓤)
   → ((b : ⟨ β ⟩) → ⟨ DL α (β ↓ b) ⟩ → ⟨ α ^ₒ (β ↓ b) ⟩)
   → ⟨ DL α β ⟩ → ⟨ α ^ₒ β ⟩
 f α β r ([] , δ) = ^ₒ-⊥ α β
 f α β r (((a , b) ∷ l) , δ) = ×ₒ-to-^ₒ α β (r b (expᴸ-tail α β a b l δ) , a)

 F : (α β : Ordinal 𝓤) → ⟨ DL α β ⟩ → ⟨ α ^ₒ β ⟩
 F {𝓤} α = transfinite-induction-on-OO (λ β → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ α ^ₒ β ⟩) (f α)

 F-is-surjective?

 (f (ℓ : (𝟙 + α) ^ₒ (β ↓ b)) , inl ⋆) ＝ f ℓ
-}

abstract
 f : (α β : Ordinal 𝓤)
   → ((b : ⟨ β ⟩) → ⟨ expᴸ[𝟙+ α ] (β ↓ b) ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ (β ↓ b) ⟩)
   → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ β ⟩
 f α β r ([] , δ) = ^ₒ-⊥ (𝟙ₒ +ₒ α) β
 f α β r (((a , b) ∷ l) , δ) = ×ₒ-to-^ₒ (𝟙ₒ +ₒ α) β (r b (expᴸ-tail α β a b l δ) , inr a)

 F : (α β : Ordinal 𝓤) → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ β ⟩
 F {𝓤} α = transfinite-induction-on-OO (λ β → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ β ⟩) (f α)

 open import UF.Base
 open import Ordinals.Maps

 F-behaviour : (α β : Ordinal 𝓤) → F α β ＝ f α β (λ b → F α (β ↓ b))
 F-behaviour α β =
  transfinite-induction-on-OO-behaviour (λ β → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ β ⟩) (f α) β

 F-behaviour-cons : (α β : Ordinal 𝓤)
                    (a : ⟨ α ⟩) (b : ⟨ β ⟩)
                    (l : List ⟨ α ×ₒ β ⟩) (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
                  → F α β (((a , b) ∷ l) , δ)
                    ＝ ×ₒ-to-^ₒ (𝟙ₒ +ₒ α) β (F α (β ↓ b) (expᴸ-tail α β a b l δ) , inr a)
 F-behaviour-cons α β a b l δ = happly (F-behaviour α β) (((a , b) ∷ l) , δ)

 F-behaviour-[] : (α β : Ordinal 𝓤) → F α β ([] , []-decr) ＝ ^ₒ-⊥ (𝟙ₒ +ₒ α) β
 F-behaviour-[] α β = happly (F-behaviour α β) ([] , []-decr)

 G-⊴ : (α β : Ordinal 𝓤) → expᴸ[𝟙+ α ] β ⊴ (𝟙ₒ +ₒ α) ^ₒ β
 G-⊴ α β = ＝-to-⊴ (expᴸ[𝟙+ α ] β) ((𝟙ₒ +ₒ α) ^ₒ β) (exponentiation-constructions-agree' α β)

G : (α β : Ordinal 𝓤) → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ (𝟙ₒ +ₒ α) ^ₒ β ⟩
G α β = [ expᴸ[𝟙+ α ] β , (𝟙ₒ +ₒ α) ^ₒ β ]⟨ G-⊴ α β ⟩

G-sim : (α β : Ordinal 𝓤) → is-simulation (expᴸ[𝟙+ α ] β) ((𝟙ₒ +ₒ α) ^ₒ β) (G α β)
G-sim α β = [ expᴸ[𝟙+ α ] β , (𝟙ₒ +ₒ α) ^ₒ β ]⟨ G-⊴ α β ⟩-is-simulation

fact : (α β : Ordinal 𝓤) → G α β ∼ F α β
fact {𝓤} α = transfinite-induction-on-OO (λ β → G α β ∼ F α β) I
 where
  α' = 𝟙ₒ +ₒ α
  I : (β : Ordinal 𝓤)
    → ((b : ⟨ β ⟩) → G α (β ↓ b) ∼ F α (β ↓ b))
    → G α β ∼ F α β
  I β IH ([] , []-decr) =
   ↓-lc (α' ^ₒ β) (G α β ([] , []-decr)) (F α β ([] , []-decr)) II
    where
     II = α' ^ₒ β ↓ G α β ([] , []-decr) ＝⟨ e₁ ⟩
          expᴸ[𝟙+ α ] β ↓ ([] , []-decr) ＝⟨ expᴸ-↓-⊥ α β ⟩
          𝟘ₒ                             ＝⟨ (^ₒ-↓-⊥ α' β) ⁻¹ ⟩
          α' ^ₒ β ↓ ^ₒ-⊥ α' β            ＝⟨ e₂ ⟩
          α' ^ₒ β ↓ F α β ([] , []-decr) ∎
      where
       e₁ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
              (G-⊴ α β)
              ([] , []-decr)) ⁻¹
       e₂ = ap (α' ^ₒ β ↓_) ((F-behaviour-[] α β) ⁻¹)
  I β IH (((a , b) ∷ l) , δ) =
   ↓-lc (α' ^ₒ β) (G α β ((a , b ∷ l) , δ)) (F α β ((a , b ∷ l) , δ)) II
    where
     II =
      α' ^ₒ β ↓ G α β (((a , b) ∷ l) , δ)                                 ＝⟨ e₁ ⟩
      expᴸ[𝟙+ α ] β ↓ (((a , b) ∷ l) , δ)                                 ＝⟨ e₂ ⟩
      expᴸ[𝟙+ α ] (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ) ＝⟨ e₃ ⟩
      α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ)       ＝⟨ e₄ ⟩
      α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α' ^ₒ (β ↓ b) ↓ G α (β ↓ b) ℓ) ＝⟨ e₅ ⟩
      α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inr a) +ₒ (α' ^ₒ (β ↓ b) ↓ G α (β ↓ b) ℓ)    ＝⟨ e₆ ⟩
      α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (G α (β ↓ b) ℓ , inr a)                     ＝⟨ e₇ ⟩
      α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (F α (β ↓ b) ℓ , inr a)                     ＝⟨ e₈ ⟩
      α' ^ₒ β ↓ F α β (((a , b) ∷ l) , δ)                                 ∎
       where
        ℓ = expᴸ-tail α β a b l δ
        e₁ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
               (G-⊴ α β)
               (((a , b) ∷ l) , δ)) ⁻¹
        e₂ = expᴸ-↓-cons α β a b l δ
        e₃ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ))
                (exponentiation-constructions-agree' α (β ↓ b))
        e₄ = ap (α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                (simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (α' ^ₒ (β ↓ b))
                  (G-⊴ α (β ↓ b))
                  ℓ)
        e₅ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ G α (β ↓ b) ℓ))
                (+ₒ-↓-right a)
        e₆ = (^ₒ-↓-×ₒ-to-^ₒ α' β) ⁻¹
        e₇ = ap (λ - → α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (- , inr a)) (IH b ℓ)
        e₈ = ap (α' ^ₒ β ↓_) ((F-behaviour-cons α β a b l δ) ⁻¹)

\end{code}