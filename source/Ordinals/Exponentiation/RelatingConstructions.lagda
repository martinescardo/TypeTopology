Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 May 2024 with additions and refactorings in December 2024.

We relate the abstract and concrete constructions of ordinal exponentiation.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.RelatingConstructions
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
open import Ordinals.OperationsByCases ua pt sr
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua pt
open import Ordinals.Exponentiation.DecreasingListProperties-Concrete ua pt sr
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

open PropositionalTruncation pt
open suprema pt sr

\end{code}

Our first main result is that the abstract and concrete constructions coincide
for base ordinals with a trichotomous least element.

\begin{code}

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
      (expᴸ[𝟙+ α ] β ↓ ((a , b ∷ l) , δ)                       ＝⟨ II₁ ⟩
       expᴸ[𝟙+ α ] (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l') ＝⟨ II₂ ⟩
       α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l')       ＝⟨ II₃ ⟩
       α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (α' ^ₒ (β ↓ b) ↓ e)              ＝⟨ II₄ ⟩
       α' ^ₒ (β ↓ b) ×ₒ (α' ↓ (inr a)) +ₒ (α' ^ₒ (β ↓ b) ↓ e)  ＝⟨ II₅ ⟩
       α' ^ₒ β ↓ e'                                            ∎)
        where
         αₐ = 𝟙ₒ +ₒ (α ↓ a)
         l' = expᴸ-tail α β a b l δ
         e  = Idtofunₒ (IH b) l'
         e' = ×ₒ-to-^ₒ α' β (e , inr a)

         II₁ = expᴸ-↓-cons α β a b l δ
         II₂ = ap (λ - → - ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l'))
                  (IH b)
         II₃ = ap (α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ_)
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
        (α' ^ₒ β ↓ y                                             ＝⟨ p   ⟩
         α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inr a) +ₒ (α' ^ₒ (β ↓ b) ↓ e)    ＝⟨ IV₁ ⟩
         α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (α' ^ₒ (β ↓ b) ↓ e)              ＝⟨ IV₂ ⟩
         α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁)       ＝⟨ IV₃ ⟩
         expᴸ[𝟙+ α ] (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁) ＝⟨ IV₄ ⟩
         expᴸ[𝟙+ α ] β ↓ l₂                                      ∎)
        where
         αₐ = 𝟙ₒ +ₒ (α ↓ a)
         l₁ = Idtofunₒ (IH b ⁻¹) e
         l₂ = extended-expᴸ-segment-inclusion α β b l₁ a

         IV₁ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ e))
                  ((+ₒ-↓-right a) ⁻¹)
         IV₂ = ap (α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ_)
                  (Idtofunₒ-↓-lemma (IH b ⁻¹))
         IV₃ = ap (λ - → - ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ l₁)) (IH b ⁻¹)
         IV₄ = expᴸ-↓-cons' α β a b l₁ ⁻¹

exponentiation-constructions-agree
 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
 → exponentiationᴸ α h β ＝ α ^ₒ β
exponentiation-constructions-agree α β h =
 exponentiationᴸ α h β ＝⟨refl⟩
 expᴸ[𝟙+ α⁺ ] β        ＝⟨ I ⟩
 (𝟙ₒ +ₒ α⁺) ^ₒ β       ＝⟨ II ⟩
 α ^ₒ β                ∎
  where
   α⁺ = α ⁺[ h ]
   I = exponentiation-constructions-agree' α⁺ β
   II = ap (_^ₒ β) ((α ⁺[ h ]-part-of-decomposition) ⁻¹)

\end{code}

An alternative proof added on 29 January 2025 by Tom de Jong.

\begin{code}

exponentiation-constructions-agree'-bis
 : (α β : Ordinal 𝓤) → expᴸ[𝟙+ α ] β ＝ (𝟙ₒ +ₒ α) ^ₒ β
exponentiation-constructions-agree'-bis α =
 happly (ap pr₁ (exponentiation-is-uniquely-specified (𝟙ₒ +ₒ α) I II))
  where
   I = expᴸ[𝟙+ α ] ,
       expᴸ-satisfies-succ-specification α ,
       (λ {I} → expᴸ-satisfies-zero-sup-combined-specification α)
   II = (𝟙ₒ +ₒ α) ^ₒ_ ,
        (^ₒ-satisfies-succ-specification (𝟙ₒ +ₒ α) (+ₒ-left-⊴ 𝟙ₒ α)) ,
        (λ {I} → ^ₒ-satisfies-zero-sup-combined-specification (𝟙ₒ +ₒ α))

exponentiation-constructions-agree-bis
 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
 → exponentiationᴸ α h β ＝ α ^ₒ β
exponentiation-constructions-agree-bis α β h =
 exponentiationᴸ α h β ＝⟨refl⟩
 expᴸ[𝟙+ α⁺ ] β        ＝⟨ I ⟩
 (𝟙ₒ +ₒ α⁺) ^ₒ β       ＝⟨ II ⟩
 α ^ₒ β                ∎
  where
   α⁺ = α ⁺[ h ]
   I = exponentiation-constructions-agree'-bis α⁺ β
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

We furthermore state and prove precisely how this canonical function f_β relates
to the simulation induced by the identification
  exponentiationᴸ α h β ＝ α ^ₒ β
obtained above.

\begin{code}

module denotations
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

Put differently, for an arbitrary ordinal α, and writing α' = 𝟙ₒ +ₒ α, we obtain
a map

  g_β : DecrList α β → α' ^ₒ β

We now show that this function is closely related to the above denotation
function, although this requires a new denotation function which has codomain
α' ^ₒ β.

\begin{code}

 private
  α' : Ordinal 𝓤
  α' = 𝟙ₒ +ₒ α

 abstract
  private
   denotation-body' : (β : Ordinal 𝓥)
                    → ((b : ⟨ β ⟩) → DecrList₂ α (β ↓ b) → ⟨ α' ^ₒ (β ↓ b) ⟩)
                    → DecrList₂ α β → ⟨ α' ^ₒ β ⟩
   denotation-body' β r ([] , δ) = ^ₒ-⊥ α' β
   denotation-body' β r (((a , b) ∷ l) , δ) =
    ×ₒ-to-^ₒ α' β (r b (expᴸ-tail α β a b l δ) , inr a)

  denotation' : (β : Ordinal 𝓥) → DecrList₂ α β → ⟨ α' ^ₒ β ⟩
  denotation' =
   transfinite-induction-on-OO
    (λ β → DecrList₂ α β → ⟨ α' ^ₒ β ⟩)
    denotation-body'

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
element of α (see the end of this file).

\begin{code}

 ^ₒ-skip-least : (β : Ordinal 𝓤) (b : ⟨ β ⟩) (e : ⟨ α' ^ₒ (β ↓ b ) ⟩)
               → α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (e , inl ⋆) ＝ α' ^ₒ (β ↓ b) ↓ e
 ^ₒ-skip-least β b e =
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

 induced-simulation : (β : Ordinal 𝓤) → expᴸ[𝟙+ α ] β ⊴ α' ^ₒ β
 induced-simulation β =
  ＝-to-⊴ (expᴸ[𝟙+ α ] β) (α' ^ₒ β) (exponentiation-constructions-agree' α β)

 induced-map : (β : Ordinal 𝓤) → ⟨ expᴸ[𝟙+ α ] β ⟩ → ⟨ α' ^ₒ β ⟩
 induced-map β = [ expᴸ[𝟙+ α ] β , α' ^ₒ β ]⟨ induced-simulation β ⟩

 private
  NB : (β : Ordinal 𝓥) → ⟨ expᴸ[𝟙+ α ] β ⟩ ＝ DecrList₂ α β
  NB β = refl

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
        α' ^ₒ β ↓ f β (((a , b) ∷ l) , δ)                              ＝⟨ e₁ ⟩
        expᴸ[𝟙+ α ] β ↓ (((a , b) ∷ l) , δ)                            ＝⟨ e₂ ⟩
        expᴸ[𝟙+ α ] (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ)         ＝⟨ e₃ ⟩
        α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ)               ＝⟨ e₄ ⟩
        α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ)           ＝⟨ e₅ ⟩
        α' ^ₒ (β ↓ b) ×ₒ (α' ↓ inr a) +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ) ＝⟨ e₆ ⟩
        α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (f (β ↓ b) ℓ , inr a)                  ＝⟨ e₇ ⟩
        α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (⟦ ℓ ⟧'⟨ β ↓ b ⟩ , inr a)              ＝⟨ e₈ ⟩
        α' ^ₒ β ↓ ⟦ ((a , b) ∷ l) , δ ⟧'⟨ β ⟩                          ∎
         where
          αₐ = 𝟙ₒ +ₒ (α ↓ a)
          ℓ = expᴸ-tail α β a b l δ
          e₁ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
                 (induced-simulation β)
                 (((a , b) ∷ l) , δ)) ⁻¹
          e₂ = expᴸ-↓-cons α β a b l δ
          e₃ = ap (λ - → - ×ₒ αₐ +ₒ (expᴸ[𝟙+ α ] (β ↓ b) ↓ ℓ))
                  (exponentiation-constructions-agree' α (β ↓ b))
          e₄ = ap (α' ^ₒ (β ↓ b) ×ₒ αₐ +ₒ_)
                  (simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (α' ^ₒ (β ↓ b))
                    (induced-simulation (β ↓ b))
                    ℓ)
          e₅ = ap (λ - → α' ^ₒ (β ↓ b) ×ₒ - +ₒ (α' ^ₒ (β ↓ b) ↓ f (β ↓ b) ℓ))
                  (+ₒ-↓-right a)
          e₆ = (^ₒ-↓-×ₒ-to-^ₒ α' β) ⁻¹
          e₇ = ap (λ - → α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (- , inr a)) (IH b ℓ)
          e₈ = ap (α' ^ₒ β ↓_) ((⟦⟧'-behaviour-cons β a b l δ) ⁻¹)

 denotation'-is-simulation
  : (β : Ordinal 𝓤) → is-simulation (expᴸ[𝟙+ α ] β) (α' ^ₒ β) (denotation' β)
 denotation'-is-simulation β =
  transport (is-simulation (expᴸ[𝟙+ α ] β) (α' ^ₒ β))
            (dfunext fe' (induced-map-is-denotation' β))
            [ expᴸ[𝟙+ α ] β , α' ^ₒ β ]⟨ induced-simulation β ⟩-is-simulation

 denotation'-⊴ : (β : Ordinal 𝓤) → expᴸ[𝟙+ α ] β ⊴ α' ^ₒ β
 denotation'-⊴ β = denotation' β , denotation'-is-simulation β

\end{code}

Indeed, the denotation maps are related via a normalization function.

\begin{code}

module _
        (α : Ordinal 𝓤)
        (β : Ordinal 𝓥)
       where

 private
  α' = 𝟙ₒ +ₒ α

 normalize-list : List ⟨ α' ×ₒ β ⟩ → List ⟨ α ×ₒ β ⟩
 normalize-list []                = []
 normalize-list ((inl ⋆ , b) ∷ l) = normalize-list l
 normalize-list ((inr a , b) ∷ l) = (a , b) ∷ normalize-list l

 normalize-list-preserves-decreasing-pr₂
  : (l : List ⟨ α' ×ₒ β ⟩)
  → is-decreasing-pr₂ α' β l
  → is-decreasing-pr₂ α β (normalize-list l)
 normalize-list-preserves-decreasing-pr₂ =
  course-of-values-induction-on-length
   (λ l → is-decreasing-pr₂ α' β l → is-decreasing-pr₂ α β (normalize-list l))
   ind
    where
     open import Naturals.Order
     open import Notation.Order
     ind : (l : List ⟨ α' ×ₒ β ⟩)
       → ((l' : List ⟨ α' ×ₒ β ⟩)
             → length l' < length l
             → is-decreasing-pr₂ α' β l'
             → is-decreasing-pr₂ α β (normalize-list l'))
       → is-decreasing-pr₂ α' β l
       → is-decreasing-pr₂ α β (normalize-list l)
     ind [] IH δ = []-decr
     ind ((inl ⋆ , b) ∷ l) IH δ =
      IH l (<-succ (length l))
           (tail-is-decreasing-pr₂ α' β (inl ⋆ , b) δ)
     ind ((inr a , b) ∷ []) IH δ = sing-decr
     ind ((inr a , b) ∷ (inl ⋆  , b') ∷ l) IH δ =
      IH ((inr a , b) ∷ l)
         (<-succ (length l))
         (is-decreasing-pr₂-skip α' β (inr a , b) (inl ⋆ , b') δ)
     ind ((inr a , b) ∷ (inr a' , b') ∷ l) IH 𝕕@(many-decr u δ) =
      many-decr u
       (IH (inr a' , b' ∷ l)
           (<-succ (length l))
           (tail-is-decreasing-pr₂ α' β (inr a , b) 𝕕))


 normalize : DecrList₂ α' β → DecrList₂ α β
 normalize (l , δ) = normalize-list l ,
                     normalize-list-preserves-decreasing-pr₂ l δ

\end{code}

Below, we need the following technical lemmas which say that normalization
commutes with the expᴸ-tail and expᴸ-segment-inclusion functions.

For expᴸ-tail, this means that the normalization of the decreasing list
(inl ⋆ , b) ∷ l in DecrList₂ α β coincides with the normalization of l in
DecrList₂ α (β ↓ b) after embedding it back into DecrList₂ α β.

\begin{code}

normalize-expᴸ-tail
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   {a : ⟨ α ⟩} {b : ⟨ β ⟩} {l : List ⟨ (𝟙ₒ +ₒ α) ×ₒ β ⟩}
   {δ : is-decreasing-pr₂ (𝟙ₒ +ₒ α) β ((inr a , b) ∷ l)}
 → normalize α (β ↓ b) (expᴸ-tail (𝟙ₒ +ₒ α) β (inr a) b l δ)
   ＝ expᴸ-tail α β a b
       (normalize-list α β l)
       (normalize-list-preserves-decreasing-pr₂ α β (inr a , b ∷ l) δ)
normalize-expᴸ-tail α β {a} {b} {l} = to-DecrList₂-＝ α (β ↓ b) (lemma l)
  where
   α' = 𝟙ₒ +ₒ α

   lemma : (l : List ⟨ α' ×ₒ β ⟩)
           {δ : is-decreasing-pr₂ α' β (inr a , b ∷ l)}
           {ε : is-decreasing-pr₂ α β (a , b ∷ normalize-list α β l)}
         → normalize-list α (β ↓ b) (expᴸ-tail-list α' β (inr a) b l δ)
           ＝ expᴸ-tail-list α β a b (normalize-list α β l) ε
   lemma [] = refl
   lemma (inl ⋆  , b' ∷ l) = lemma l
   lemma (inr a' , b' ∷ l) = ap₂ _∷_
                                 (ap (a' ,_) (segment-inclusion-lc β refl))
                                 (lemma l)

normalize-expᴸ-segment-inclusion
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   {b : ⟨ β ⟩} {l : List ⟨ (𝟙ₒ +ₒ α) ×ₒ β ⟩}
   {δ : is-decreasing-pr₂ (𝟙ₒ +ₒ α) β ((inl ⋆) , b ∷ l)}
 → normalize α β (((inl ⋆ , b) ∷ l) , δ)
   ＝ expᴸ-segment-inclusion α β b
       (normalize α (β ↓ b)
       (expᴸ-tail (𝟙ₒ +ₒ α) β (inl ⋆) b l δ))
normalize-expᴸ-segment-inclusion α β {b} {l} = to-DecrList₂-＝ α β (lemma l)
 where
   α' = 𝟙ₒ +ₒ α

   lemma : (l : List ⟨ α' ×ₒ β ⟩) {δ : is-decreasing-pr₂ α' β ((inl ⋆) , b ∷ l)}
         →  normalize-list α β ((inl ⋆ , b) ∷ l) ＝
              expᴸ-segment-inclusion-list α β b
               (normalize-list α (β ↓ b)
                (expᴸ-tail-list α' β (inl ⋆) b l δ))
   lemma [] = refl
   lemma (inl ⋆ , b' ∷ l) = lemma l
   lemma (inr a , b' ∷ l) = ap ((a , b') ∷_) (lemma l)

\end{code}

We are now ready to prove that the denotation functions are related via
normalization.

\begin{code}

open denotations

denotations-are-related-via-normalization
 : (α β : Ordinal 𝓤)
 → denotation (𝟙ₒ +ₒ α) β ∼ denotation' α β ∘ normalize α β
denotations-are-related-via-normalization {𝓤} α =
 transfinite-induction-on-OO
  (λ β → denotation (𝟙ₒ +ₒ α) β ∼ denotation' α β ∘ normalize α β)
  (λ β IH (l , δ) → ind β IH l δ)
   where
    α' = 𝟙ₒ +ₒ α

    ind : (β : Ordinal 𝓤)
        → ((b : ⟨ β ⟩) → denotation α' (β ↓ b)
                         ∼ denotation' α (β ↓ b) ∘ normalize α (β ↓ b))
        → (l : List ⟨ α' ×ₒ β ⟩) (δ : is-decreasing-pr₂ α' β l)
        → denotation α' β (l , δ) ＝ denotation' α β (normalize α β (l , δ))
    ind β IH [] []-decr =
     denotation α' β ([] , []-decr)                 ＝⟨ I  ⟩
     ^ₒ-⊥ α' β                                      ＝⟨ II ⟩
     denotation' α β (normalize α β ([] , []-decr)) ∎
      where
       I  = ⟦⟧-behaviour-[] α' β
       II = (⟦⟧'-behaviour-[] α β) ⁻¹
    ind β IH ((inl ⋆ , b) ∷ l) δ =
     denotation α' β (((inl ⋆ , b) ∷ l) , δ)               ＝⟨ I   ⟩
     ×ₒ-to-^ₒ α' β (denotation α' (β ↓ b) ℓ , inl ⋆)       ＝⟨ II  ⟩
     denotation' α β (ι (normalize α (β ↓ b) ℓ))           ＝⟨ III ⟩
     denotation' α β (normalize α β ((inl ⋆ , b ∷ l) , δ)) ∎
      where
       ℓ = expᴸ-tail α' β (inl ⋆) b l δ
       ι = expᴸ-segment-inclusion α β b

       I   = ⟦⟧-behaviour-cons α' β  (inl ⋆) b l δ
       III = ap (denotation' α β) (normalize-expᴸ-segment-inclusion α β ⁻¹)
       II  = ↓-lc (α' ^ₒ β) _ _ II'
        where
         II' =
          α' ^ₒ β ↓ ×ₒ-to-^ₒ α' β (denotation α' (β ↓ b) ℓ , inl ⋆)     ＝⟨ II₁ ⟩
          α' ^ₒ (β ↓ b) ↓ denotation α' (β ↓ b) ℓ                       ＝⟨ II₂ ⟩
          α' ^ₒ (β ↓ b) ↓ denotation' α (β ↓ b) (normalize α (β ↓ b) ℓ) ＝⟨ II₃ ⟩
          expᴸ[𝟙+ α ] (β ↓ b) ↓ normalize α (β ↓ b) ℓ                   ＝⟨ II₄ ⟩
          α' ^ₒ β ↓ denotation' α β (ι (normalize α (β ↓ b) ℓ))         ∎
           where
            II₁ = ^ₒ-skip-least α β b (denotation α' (β ↓ b) ℓ)
            II₂ = ap (α' ^ₒ (β ↓ b) ↓_) (IH b ℓ)
            II₃ = (simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (α' ^ₒ (β ↓ b))
                    (denotation'-⊴  α (β ↓ b))
                    (normalize α (β ↓ b) ℓ)) ⁻¹
            II₄ = simulations-preserve-↓ (expᴸ[𝟙+ α ] (β ↓ b)) (α' ^ₒ β)
                   (⊴-trans (expᴸ[𝟙+ α ] (β ↓ b)) (expᴸ[𝟙+ α ] β) (α' ^ₒ β)
                     (expᴸ-segment-inclusion-⊴ α β b)
                     (denotation'-⊴ α β))
                   (normalize α (β ↓ b) ℓ)
    ind β IH ((inr a , b) ∷ l) δ =
     denotation α' β (((inr a , b) ∷ l) , δ)                        ＝⟨ I   ⟩
     ϕ α' β (denotation α' (β ↓ b) ℓ , inr a)                       ＝⟨ II  ⟩
     ϕ α' β (denotation' α (β ↓ b) (normalize α (β ↓ b) ℓ) , inr a) ＝⟨ III ⟩
     ϕ α' β (denotation' α (β ↓ b) ℓ' , inr a)                      ＝⟨ IV  ⟩
     denotation' α β (normalize α β ((inr a , b ∷ l) , δ))          ∎
      where
       ϕ = ×ₒ-to-^ₒ
       ε = normalize-list-preserves-decreasing-pr₂ α β (inr a , b ∷ l) δ
       ℓ  = expᴸ-tail α' β (inr a) b l δ
       ℓ' = expᴸ-tail α β a b (normalize-list α β l) ε

       I   = ⟦⟧-behaviour-cons α' β (inr a) b l δ
       II  = ap (λ - → ×ₒ-to-^ₒ α' β (- , inr a)) (IH b ℓ)
       III = ap (λ - → ×ₒ-to-^ₒ α' β (denotation' α (β ↓ b) - , inr a))
                (normalize-expᴸ-tail α β)
       IV  = (⟦⟧'-behaviour-cons α β a b (normalize-list α β l) ε) ⁻¹

\end{code}
