Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 May 2024 with additions and refactorings in December 2024.

TODO: COMMENT

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

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
open import UF.Base
open import UF.ImageAndSurjection pt

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
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

There is a canonical function f_β : DecrList₂ α β → α ^ₒ β defined by
transfinite induction on β as

  f_β []            := ⊥
  f_β ((a , b) ∷ l) := [inr b , f_{β ↓ b} l' , a]

where
  l' : DecrList₂ α (β ↓ b)
is obtained from l and the fact that the list (a , b) ∷ l is decreasing in the
second component.

We show that this map is a surjection, which motivates and allows us to think of
lists in DecrList₂ α β as concrete representations of (abstract) elements of
α ^ₒ β. Put differently, such a list denotes the abstract element.

\begin{code}

module _
        (α : Ordinal 𝓤)
       where

 abstract
  private
   denotation-body : (β : Ordinal 𝓥)
                   → ((b : ⟨ β ⟩) → DecrList₂ α (β ↓ b) → ⟨ α ^ₒ (β ↓ b) ⟩)
                   → DecrList₂ α β → ⟨ α ^ₒ β ⟩
   denotation-body β r ([] , δ) = ^ₒ-⊥ α β
   denotation-body β r (((a , b) ∷ l) , δ) = ×ₒ-to-^ₒ α β
                                              (r b (expᴸ-tail α β a b l δ) , a)

  denotation : (β : Ordinal 𝓥) → DecrList₂ α β → ⟨ α ^ₒ β ⟩
  denotation =
   transfinite-induction-on-OO (λ β → DecrList₂ α β → ⟨ α ^ₒ β ⟩) denotation-body

  syntax denotation β l = ⟦ l ⟧⟨ β ⟩

  denotation-behaviour
   : (β : Ordinal 𝓥)
   → denotation β ＝ denotation-body β (λ b → denotation (β ↓ b))
  denotation-behaviour =
   transfinite-induction-on-OO-behaviour
    (λ β → DecrList₂ α β → ⟨ α ^ₒ β ⟩)
    denotation-body

  ⟦⟧-behaviour-cons : (β : Ordinal 𝓥)
                      (a : ⟨ α ⟩) (b : ⟨ β ⟩)
                      (l : List ⟨ α ×ₒ β ⟩)
                      (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
                    → ⟦ ((a , b) ∷ l) , δ ⟧⟨ β ⟩
                      ＝ ×ₒ-to-^ₒ α β (⟦ expᴸ-tail α β a b l δ ⟧⟨ β ↓ b ⟩ , a)
  ⟦⟧-behaviour-cons β a b l δ =
   happly (denotation-behaviour β) (((a , b) ∷ l) , δ)

  ⟦⟧-behaviour-[] : (β : Ordinal 𝓥) → ⟦ [] , []-decr ⟧⟨ β ⟩ ＝ ^ₒ-⊥ α β
  ⟦⟧-behaviour-[] β = happly (denotation-behaviour β) ([] , []-decr)

 ⟦⟧-is-surjection : (β : Ordinal 𝓥) → is-surjection (denotation β)
 ⟦⟧-is-surjection =
  transfinite-induction-on-OO (λ β → is-surjection (denotation β)) I
  where
   I : (β : Ordinal 𝓥)
     → ((b : ⟨ β ⟩) → is-surjection (denotation (β ↓ b)))
     → is-surjection (denotation β)
   I β IH =
    ^ₒ-induction α β
     (λ (e : ⟨ α ^ₒ β ⟩) → ∃ l ꞉ DecrList₂ α β , ⟦ l ⟧⟨ β ⟩ ＝ e)
     (λ e → ∃-is-prop)
     ∣ ([] , []-decr) , ⟦⟧-behaviour-[] β ∣
     II
      where
       II : (b : ⟨ β ⟩) (y : ⟨ α ^ₒ (β ↓ b) ×ₒ α ⟩)
         → ×ₒ-to-^ₒ α β y ∈image (denotation β)
       II b (e , a) = ∥∥-functor III (IH b e)
        where
         III : (Σ ℓ ꞉ DecrList₂ α (β ↓ b) , ⟦ ℓ ⟧⟨ β ↓ b ⟩ ＝ e)
             → Σ l ꞉ DecrList₂ α β , ⟦ l ⟧⟨ β ⟩ ＝ ×ₒ-to-^ₒ α β (e , a)
         III ((ℓ , δ) , refl) = (((a , b) ∷ ℓ') , ε) , IV
          where
           ℓ' : List ⟨ α ×ₒ β ⟩
           ℓ' = expᴸ-segment-inclusion-list α β b ℓ
           ε : is-decreasing-pr₂ α β ((a , b) ∷ ℓ')
           ε = extended-expᴸ-segment-inclusion-is-decreasing-pr₂ α β b ℓ a δ
           IV = ⟦ ((a , b) ∷ ℓ') , ε ⟧⟨ β ⟩                            ＝⟨ IV₁ ⟩
                ×ₒ-to-^ₒ α β (⟦ expᴸ-tail α β a b ℓ' ε ⟧⟨ β ↓ b ⟩ , a) ＝⟨ IV₂ ⟩
                ×ₒ-to-^ₒ α β (⟦ ℓ , δ ⟧⟨ β ↓ b ⟩ , a)                  ∎
            where
             IV₁ = ⟦⟧-behaviour-cons β a b ℓ' ε
             IV₂ = ap (λ - → ×ₒ-to-^ₒ α β (denotation (β ↓ b) - , a))
                      (expᴸ-segment-inclusion-section-of-expᴸ-tail α β a b ℓ δ)

\end{code}

The equality exponentiationᴸ α β ＝ α ^ₒ β, for α decomposable as α = 𝟙ₒ +ₒ α⁺,
induces a simulation, and in particular a map

  g_β : DecrList α⁺ β → α ^ₒ β.

Equivalently, writing α' = 𝟙ₒ +ₒ α, we obtain a map

  g_β : DecrList α β → α' ^ₒ β

We now show that this function is closely related to the above denotation
function, although this requires a new denotation function which has codomain
α' ^ₒ β.

\begin{code}

module _
        (α : Ordinal 𝓤)
       where

 private
  α' : Ordinal 𝓤
  α' = 𝟙ₒ +ₒ α

 abstract
  private
   denotation-body' : (β : Ordinal 𝓥)
                    → ((b : ⟨ β ⟩) → DecrList₂ α (β ↓ b) → ⟨ α' ^ₒ (β ↓ b) ⟩)
                    → DecrList₂ α β → ⟨ α' ^ₒ β ⟩
   denotation-body' β r ([] , δ) = ^ₒ-⊥ α' β
   denotation-body' β r (((a , b) ∷ l) , δ) = ×ₒ-to-^ₒ α' β
                                               (r b (expᴸ-tail α β a b l δ) , inr a)

  denotation' : (β : Ordinal 𝓥) → DecrList₂ α β → ⟨ α' ^ₒ β ⟩
  denotation' =
   transfinite-induction-on-OO (λ β → DecrList₂ α β → ⟨ α' ^ₒ β ⟩) denotation-body'

  syntax denotation' β l = ⟦ l ⟧'⟨ β ⟩

  denotation'-behaviour
   : (β : Ordinal 𝓥)
   → denotation' β ＝ denotation-body' β (λ b → denotation' (β ↓ b))
  denotation'-behaviour =
   transfinite-induction-on-OO-behaviour
    (λ β → DecrList₂ α β → ⟨ α' ^ₒ β ⟩)
    denotation-body'

  ⟦⟧'-behaviour-cons
   : (β : Ordinal 𝓥)
     (a : ⟨ α ⟩) (b : ⟨ β ⟩)
     (l : List ⟨ α ×ₒ β ⟩)
     (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
   → ⟦ ((a , b) ∷ l) , δ ⟧'⟨ β ⟩
     ＝ ×ₒ-to-^ₒ α' β (⟦ expᴸ-tail α β a b l δ ⟧'⟨ β ↓ b ⟩ , inr a)
  ⟦⟧'-behaviour-cons β a b l δ =
   happly (denotation'-behaviour β) (((a , b) ∷ l) , δ)

  ⟦⟧'-behaviour-[] : (β : Ordinal 𝓥) → ⟦ [] , []-decr ⟧'⟨ β ⟩ ＝ ^ₒ-⊥ α' β
  ⟦⟧'-behaviour-[] β = happly (denotation'-behaviour β) ([] , []-decr)

\end{code}

Looking at ⟦⟧'-behaviour-cons, one may wonder about the case where we don't have
(inr a) in the right component, but rather (inl ⋆). This is handled via the
following observation, which corresponds to the fact that if an ordinal γ has a
trichotomous (in particular, detachable) least element then elements of
DecrList₂ γ β can be "normalized" by removing entries which list the least
element of α.

\begin{code}

 private
  NB : (β : Ordinal 𝓤) (b : ⟨ β ⟩) (e : ⟨ α' ^ₒ (β ↓ b ) ⟩)
     → α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (e , inl ⋆) ＝ α' ^ₒ (β ↓ b) ↓ e
  NB β b e =
   α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (e , inl ⋆)                       ＝⟨ I   ⟩
   α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ α ↓ inl ⋆) +ₒ (α' ^ₒ (β ↓ b) ↓ e) ＝⟨ II  ⟩
   α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ ↓ ⋆) +ₒ (α' ^ₒ (β ↓ b) ↓ e)          ＝⟨ III ⟩
   α' ^ₒ (β ↓ b) ×ₒ 𝟘ₒ +ₒ (α' ^ₒ (β ↓ b) ↓ e)                ＝⟨ IV  ⟩
   𝟘ₒ +ₒ (α' ^ₒ (β ↓ b) ↓ e)                                 ＝⟨ V   ⟩
   α' ^ₒ (β ↓ b) ↓ e                                         ∎
    where
     I   = ^ₒ-↓-×ₒ-to-^ₒ α' β
     II  = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e))
              ((+ₒ-↓-left ⋆) ⁻¹)
     III = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e)) 𝟙ₒ-↓
     IV  = ap (_+ₒ (α' ^ₒ (β ↓ b) ↓ e)) (×ₒ-𝟘ₒ-right (α' ^ₒ (β ↓ b)))
     V   = 𝟘ₒ-left-neutral (α' ^ₒ (β ↓ b) ↓ e)

\end{code}

\begin{code}

 induced-simulation : (β : Ordinal 𝓤) → expᴸ[𝟙+ α ] β ⊴ α' ^ₒ β
 induced-simulation β =
  ＝-to-⊴ (expᴸ[𝟙+ α ] β) (α' ^ₒ β) (exponentiation-constructions-agree' α β)

 induced-map : (β : Ordinal 𝓤) → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ α' ^ₒ β ⟩
 induced-map β = [ expᴸ[𝟙+ α ] β , α' ^ₒ β ]⟨ induced-simulation β ⟩

 private
  NB' : (β : Ordinal 𝓥) → ⟨ expᴸ[𝟙+ α ] β ⟩ ＝ DecrList₂ α β
  NB' β = refl

 induced-map-is-denotation' : (β : Ordinal 𝓤) → induced-map β ∼ denotation' β
 induced-map-is-denotation' =
  transfinite-induction-on-OO (λ β → f β ∼ denotation' β) I
   where
    f = induced-map

    I : (β : Ordinal 𝓤)
      → ((b : ⟨ β ⟩) → f (β ↓ b) ∼ denotation' (β ↓ b))
      → f β ∼ denotation' β
    I β IH ([] , []-decr) =
     ↓-lc (α' ^ₒ β) (f β ([] , []-decr)) (⟦ [] , []-decr ⟧'⟨ β ⟩) II
      where
       II = α' ^ₒ β ↓ f β ([] , []-decr)     ＝⟨ e₁ ⟩
            expᴸ[𝟙+ α ] β ↓ ([] , []-decr)   ＝⟨ expᴸ-↓-⊥ α β ⟩
            𝟘ₒ                               ＝⟨ (^ₒ-↓-⊥ α' β) ⁻¹ ⟩
            α' ^ₒ β ↓ ^ₒ-⊥ α' β              ＝⟨ e₂ ⟩
            α' ^ₒ β ↓ ⟦ [] , []-decr ⟧'⟨ β ⟩ ∎
        where
         e₁ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
                (induced-simulation β)
                ([] , []-decr)) ⁻¹
         e₂ = ap (α' ^ₒ β ↓_) ((⟦⟧'-behaviour-[] β) ⁻¹)
    I β IH (((a , b) ∷ l) , δ) =
     ↓-lc (α' ^ₒ β) (f β ((a , b ∷ l) , δ)) (⟦ (a , b ∷ l) , δ ⟧'⟨ β ⟩) II
      where
       II =
        α' ^ₒ β ↓ f β (((a , b) ∷ l) , δ)                                   ＝⟨ e₁ ⟩
        expᴸ[𝟙+ α ] β ↓ (((a , b) ∷ l) , δ)                                 ＝⟨ e₂ ⟩
        expᴸ[𝟙+ α ] (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ) ＝⟨ e₃ ⟩
        α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ)       ＝⟨ e₄ ⟩
        α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ)   ＝⟨ e₅ ⟩
        α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inr a) +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ)      ＝⟨ e₆ ⟩
        α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (f (β ↓ b) ℓ , inr a)                       ＝⟨ e₇ ⟩
        α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (⟦ ℓ ⟧'⟨ β ↓ b ⟩ , inr a)                   ＝⟨ e₈ ⟩
        α' ^ₒ β ↓ ⟦ ((a , b) ∷ l) , δ ⟧'⟨ β ⟩                               ∎
         where
          ℓ = expᴸ-tail α β a b l δ
          e₁ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
                 (induced-simulation β)
                 (((a , b) ∷ l) , δ)) ⁻¹
          e₂ = expᴸ-↓-cons α β a b l δ
          e₃ = ap (λ - → - ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ))
                  (exponentiation-constructions-agree' α (β ↓ b))
          e₄ = ap (α' ^ₒ (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ_)
                  (simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (α' ^ₒ (β ↓ b))
                    (induced-simulation (β ↓ b))
                    ℓ)
          e₅ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ))
                  (+ₒ-↓-right a)
          e₆ = (^ₒ-↓-×ₒ-to-^ₒ α' β) ⁻¹
          e₇ = ap (λ - → α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (- , inr a)) (IH b ℓ)
          e₈ = ap (α' ^ₒ β ↓_) ((⟦⟧'-behaviour-cons β a b l δ) ⁻¹)

\end{code}