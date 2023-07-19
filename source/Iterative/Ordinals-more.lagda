Martin Escardo & Tom de Jong, June 2023.

This is to be added to the file Iterative.ordinals when it is complete.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals-more
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import MLTT.W
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import Ordinals.Underlying
open import Ordinals.WellOrderTransport
open import UF.Equiv-FunExt
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt


open import Iterative.Ordinals 𝓤 ua

\end{code}

TODO. The lemma below should have a more descriptive name.

We perform a double induction: first on 𝕆 and then on the ordinal (𝕆-to-Ord α).

\begin{code}

𝕆-to-Ord-lemma : (α : 𝕆) (x : 𝕆-root α)
               → (𝕆-to-Ord α) ↓ x ＝ 𝕆-to-Ord (𝕆-forest α x)
𝕆-to-Ord-lemma = 𝕆-induction' _ inductive-proof₁
 where
  inductive-proof₁ : (α : 𝕆)
                   → ((x : 𝕆-root α) (y : 𝕆-root (𝕆-forest α x))
                         →    𝕆-to-Ord (𝕆-forest α x) ↓ y
                           ＝ 𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y))
                   → (x : 𝕆-root α) → (𝕆-to-Ord α ↓ x) ＝ 𝕆-to-Ord (𝕆-forest α x)
  inductive-proof₁ α IH₁ = Transfinite-induction (𝕆-to-Ord α) _ inductive-proof₂
   where
    inductive-proof₂ : (x : 𝕆-root α)
                     → ((y : 𝕆-root α) → y ≺⟨ 𝕆-to-Ord α ⟩ x
                           → (𝕆-to-Ord α ↓ y) ＝ 𝕆-to-Ord (𝕆-forest α y))
                     → (𝕆-to-Ord α ↓ x) ＝ 𝕆-to-Ord (𝕆-forest α x)
    inductive-proof₂ x IH₂ = ⊲-is-extensional _ _ (to-≼ I) (to-≼ II)
     where
      I : (y : ⟨ 𝕆-to-Ord α ↓ x ⟩)
        → ((𝕆-to-Ord α ↓ x) ↓ y) ⊲ 𝕆-to-Ord (𝕆-forest α x)
      I 𝕪@(y , l) = (y' , eq)
       where
        iterated-𝕆-forest₁ : Σ y' ꞉ 𝕆-root (𝕆-forest α x) ,
                                 𝕆-forest (𝕆-forest α x) y' ＝ 𝕆-forest α y
        iterated-𝕆-forest₁ = ⌜ <-behaviour (𝕆-forest α y) (𝕆-forest α x) ⌝
                             (⌜ 𝕆-to-Ord-order α y x ⌝⁻¹ l)
        y'  = pr₁ iterated-𝕆-forest₁
        eq' = pr₂ iterated-𝕆-forest₁

        eq = (𝕆-to-Ord α ↓ x) ↓ 𝕪                  ＝⟨ ⦅1⦆ ⟩
             𝕆-to-Ord α ↓ y                        ＝⟨ ⦅2⦆ ⟩
             𝕆-to-Ord (𝕆-forest α y)               ＝⟨ ⦅3⦆ ⟩
             𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y') ＝⟨ ⦅4⦆ ⟩
             𝕆-to-Ord (𝕆-forest α x) ↓ y'          ∎
         where
          ⦅1⦆ = iterated-↓ (𝕆-to-Ord α) x y l
          ⦅2⦆ = IH₂ y l
          ⦅3⦆ = ap 𝕆-to-Ord (eq' ⁻¹)
          ⦅4⦆ = (IH₁ x y') ⁻¹
      II : (y : ⟨ 𝕆-to-Ord (𝕆-forest α x) ⟩)
         → (𝕆-to-Ord (𝕆-forest α x) ↓ y) ⊲ (𝕆-to-Ord α ↓ x)
      II y = (𝕪 , (eq ⁻¹))
       where
        note : 𝕆-root (𝕆-forest α x) ＝ ⟨ 𝕆-to-Ord (𝕆-forest α x) ⟩
        note = refl
        iterated-𝕆-forest₂ : Σ y' ꞉ 𝕆-root α ,
                             𝕆-forest α y' ＝ 𝕆-forest (𝕆-forest α x) y
        iterated-𝕆-forest₂ = 𝕆-forest-is-lower-closed
                              α x
                              (𝕆-forest (𝕆-forest α x) y)
                              (𝕆-forest-is-< (𝕆-forest α x) y)
        y'  = pr₁ iterated-𝕆-forest₂
        eq' = pr₂ iterated-𝕆-forest₂

        l : 𝕆-forest α y' < 𝕆-forest α x
        l = ⌜ <-behaviour (𝕆-forest α y') (𝕆-forest α x) ⌝⁻¹
             (y , (eq' ⁻¹))
        l' : y' ≺⟨ 𝕆-to-Ord α ⟩ x
        l' = ⌜ 𝕆-to-Ord-order α y' x ⌝ l
        𝕪 = (y' , l')

        eq = (𝕆-to-Ord α ↓ x) ↓ 𝕪                 ＝⟨ ⦅1⦆ ⟩
             𝕆-to-Ord α ↓ y'                      ＝⟨ ⦅2⦆ ⟩
             𝕆-to-Ord (𝕆-forest α y')             ＝⟨ ⦅3⦆ ⟩
             𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y) ＝⟨ ⦅4⦆ ⟩
             𝕆-to-Ord (𝕆-forest α x) ↓ y          ∎
         where
          ⦅1⦆ = iterated-↓ (𝕆-to-Ord α) x y' l'
          ⦅2⦆ = IH₂ y' l'
          ⦅3⦆ = ap 𝕆-to-Ord eq'
          ⦅4⦆ = (IH₁ x y) ⁻¹

𝕆-to-Ord-preserves-< : (α β : 𝕆) → α < β → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β
𝕆-to-Ord-preserves-< α β l = II I
 where
  I : Σ y ꞉ 𝕆-root β , 𝕆-forest β y ＝ α
  I = ⌜ <-behaviour α β ⌝ l

  II : type-of I → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β
  II (y , refl) = IV
   where
    III : 𝕆-to-Ord (𝕆-forest β y) ＝ (𝕆-to-Ord β ↓ y)
    III = (𝕆-to-Ord-lemma β y)⁻¹

    IV : 𝕆-to-Ord (𝕆-forest β y) ⊲ 𝕆-to-Ord β
    IV = y , III

Ord-to-𝕆-is-equiv : is-equiv Ord-to-𝕆
Ord-to-𝕆-is-equiv = embeddings-with-sections-are-equivs
                     Ord-to-𝕆
                     Ord-to-𝕆-is-embedding
                     (𝕆-to-Ord , η)
 where
  f : (α : 𝕆)
    → ((x : 𝕆-root α) → Ord-to-𝕆 (𝕆-to-Ord (𝕆-forest α x)) ＝ 𝕆-forest α x)
    → Ord-to-𝕆 (𝕆-to-Ord α) ＝ α
  f α g =
   Ord-to-𝕆 (𝕆-to-Ord α) ＝⟨ I ⟩
   𝕆-ssup (𝕆-root α) (λ x → Ord-to-𝕆 (𝕆-to-Ord α ↓ x)) a b ＝⟨ II ⟩
   𝕆-ssup (𝕆-root α) (λ x → Ord-to-𝕆 (𝕆-to-Ord (𝕆-forest α x))) {!!} {!!} ＝⟨ {!!} ⟩
   {!!} ＝⟨ III ⟩
   𝕆-ssup (𝕆-root α) (𝕆-forest α) {!!} {!!} ＝⟨ 𝕆-η α ⟩
   α ∎
    where
     a = Ord-to-𝕆↓-is-embedding (𝕆-to-Ord α)
     b = Ord-to-𝕆↓-is-lower-closed (𝕆-to-Ord α)
     I   = Ord-to-𝕆-behaviour (𝕆-to-Ord α)
     II  = ap (λ - → 𝕆-ssup (𝕆-root α) (Ord-to-𝕆 ∘ -) {!!} {!!}) (dfunext fe (𝕆-to-Ord-lemma α))
     III = ap (λ - → 𝕆-ssup (𝕆-root α) - {!!} {!!}) (dfunext fe g)

  η : Ord-to-𝕆 ∘ 𝕆-to-Ord ∼ id
  η = 𝕆-induction' _ f

Ordinals-≃ : Ord ≃ 𝕆
Ordinals-≃ = Ord-to-𝕆 , Ord-to-𝕆-is-equiv

𝕆-to-Ord-reflects-< : (α β : 𝕆) → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β → α < β
𝕆-to-Ord-reflects-< α β (y , p) = III
 where
  I = 𝕆-to-Ord (𝕆-forest β y) ＝⟨ (𝕆-to-Ord-lemma β y)⁻¹ ⟩
      (𝕆-to-Ord β ↓ y)        ＝⟨ p ⁻¹ ⟩
      𝕆-to-Ord α              ∎

  II : 𝕆-forest β y ＝ α
  II = equivs-are-lc ⌜ Ordinals-≃ ⌝⁻¹ ⌜ Ordinals-≃ ⌝⁻¹-is-equiv I

  III : α < β
  III = ⌜ <-behaviour α β ⌝⁻¹ (y , II)


Ordinals-agreementₒ : 𝓞 ≃ₒ OO 𝓤
Ordinals-agreementₒ = ⌜ Ordinals-≃ ⌝⁻¹ ,
                      order-preserving-reflecting-equivs-are-order-equivs
                       𝓞
                       (OO 𝓤)
                       ⌜ Ordinals-≃ ⌝⁻¹
                       ⌜ Ordinals-≃ ⌝⁻¹-is-equiv
                       𝕆-to-Ord-preserves-<
                       𝕆-to-Ord-reflects-<

Ordinals-agreement : 𝓞 ＝ OO 𝓤
Ordinals-agreement = eqtoidₒ (ua 𝓤⁺) fe 𝓞 (OO 𝓤) Ordinals-agreementₒ

\end{code}
