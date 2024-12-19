Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
Started November 2023. Refactored December 2024.

TODO: REFACTOR FURTHER
TODO: USE --exact-split

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.DecreasingListProperties-Concrete
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.List
open import MLTT.Plus-Properties
open import MLTT.Spartan

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open import Ordinals.Exponentiation.DecreasingList ua
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

open PropositionalTruncation pt

open suprema pt sr

\end{code}

\begin{code}

expᴸ-zero-specification-≃ₒ : (α : Ordinal 𝓤)
                           → expᴸ[𝟙+ α ] (𝟘ₒ {𝓥}) ≃ₒ 𝟙ₒ {𝓤 ⊔ 𝓥}
expᴸ-zero-specification-≃ₒ α = f , f-order-preserving ,
                               qinvs-are-equivs f f-qinv ,
                               g-order-preserving
 where
  f : ⟨ expᴸ[𝟙+ α ] 𝟘ₒ ⟩ → 𝟙
  f _ = ⋆
  f-order-preserving : is-order-preserving (expᴸ[𝟙+ α ] 𝟘ₒ) 𝟙ₒ f
  f-order-preserving ([] , δ) ([] , ε) u =
   𝟘-elim (Irreflexivity (expᴸ[𝟙+ α ] 𝟘ₒ) ([] , δ) u)

  g : 𝟙 → ⟨ expᴸ[𝟙+ α ] 𝟘ₒ ⟩
  g _ = [] , []-decr

  g-order-preserving : is-order-preserving 𝟙ₒ (expᴸ[𝟙+ α ] 𝟘ₒ) g
  g-order-preserving ⋆ ⋆ = 𝟘-elim

  f-qinv : qinv f
  f-qinv = g , p , q
   where
    p : g ∘ f ∼ id
    p ([] , []-decr) = refl
    q : f ∘ g ∼ id
    q ⋆ = refl

expᴸ-zero-specification : (α : Ordinal 𝓤)
                        → exp-specification-zero {𝓤} {𝓥} (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ])
expᴸ-zero-specification {𝓤} {𝓥} α =
 eqtoidₒ (ua (𝓤 ⊔ 𝓥)) fe' (expᴸ[𝟙+ α ] 𝟘ₒ) 𝟙ₒ (expᴸ-zero-specification-≃ₒ α)

𝟙ₒ-neutral-expᴸ-≃ₒ : (α : Ordinal 𝓤) → expᴸ[𝟙+ α ] (𝟙ₒ {𝓥}) ≃ₒ 𝟙ₒ +ₒ α
𝟙ₒ-neutral-expᴸ-≃ₒ α = f , f-order-preserving ,
                       qinvs-are-equivs f f-qinv ,
                       g-order-preserving
 where
  f : ⟨ expᴸ[𝟙+ α ] (𝟙ₒ {𝓤}) ⟩ → ⟨ 𝟙ₒ +ₒ α ⟩
  f ([] , δ) = inl ⋆
  f (((a , ⋆) ∷ []) , δ) = inr a
  f (((a , ⋆) ∷ (a' , ⋆) ∷ l) , many-decr p δ) = 𝟘-elim (irrefl 𝟙ₒ ⋆ p)

  f-order-preserving : is-order-preserving (expᴸ[𝟙+ α ] (𝟙ₒ {𝓤})) (𝟙ₒ +ₒ α) f
  f-order-preserving ([] , δ) ([] , ε) q =
   𝟘-elim (irrefl (expᴸ[𝟙+ α ] 𝟙ₒ) ([] , δ) q)
  f-order-preserving ([] , δ) ((y ∷ []) , ε) q = ⋆
  f-order-preserving ([] , δ) (((a , ⋆) ∷ (a' , ⋆) ∷ l) , many-decr p ε) q =
   𝟘-elim (irrefl 𝟙ₒ ⋆ p)
  f-order-preserving (((a , ⋆) ∷ []) , δ) (((a' , ⋆) ∷ []) , ε)
   (head-lex (inr (r , q))) = q
  f-order-preserving (((a , ⋆) ∷ []) , δ)
                     (((a' , ⋆) ∷ (a'' , ⋆) ∷ l) , many-decr p ε) q =
   𝟘-elim (irrefl 𝟙ₒ ⋆ p)
  f-order-preserving (((a , ⋆) ∷ (a' , ⋆) ∷ l) , many-decr p δ) (l' , ε) q =
   𝟘-elim (irrefl 𝟙ₒ ⋆ p)

  g : ⟨ 𝟙ₒ +ₒ α ⟩ → ⟨ expᴸ[𝟙+ α ] (𝟙ₒ {𝓤}) ⟩
  g (inl ⋆) = ([] , []-decr)
  g (inr a) = ([ a , ⋆ ] , sing-decr)

  g-order-preserving : is-order-preserving (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ] (𝟙ₒ {𝓤})) g
  g-order-preserving (inl ⋆) (inr a) ⋆ = []-lex
  g-order-preserving (inr a) (inr a') p = head-lex (inr (refl , p))
  f-qinv : qinv f
  f-qinv = g , p , q
   where
    p : g ∘ f ∼ id
    p ([] , []-decr) = refl
    p (((a , ⋆) ∷ []) , δ) = to-expᴸ-＝ α 𝟙ₒ refl
    p (((a , ⋆) ∷ (a' , ⋆) ∷ l) , many-decr p δ) = 𝟘-elim (irrefl 𝟙ₒ ⋆ p)
    q : f ∘ g ∼ id
    q (inl ⋆) = refl
    q (inr a) = refl

𝟙ₒ-neutral-expᴸ : (α : Ordinal 𝓤) → (expᴸ[𝟙+ α ] 𝟙ₒ) ＝ 𝟙ₒ +ₒ α
𝟙ₒ-neutral-expᴸ {𝓤} α =
 eqtoidₒ (ua 𝓤) fe' (expᴸ[𝟙+ α ] (𝟙ₒ {𝓤})) (𝟙ₒ +ₒ α) (𝟙ₒ-neutral-expᴸ-≃ₒ α)

\end{code}

We next prove the equivalence
  expᴸ[𝟙+ α ] (β +ₒ γ) ≃ₒ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)
in several steps.

\begin{code}

module _
        (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
       where

 private
  forward-left-on-lists : List ⟨ α ×ₒ (β +ₒ γ) ⟩ → List ⟨ α ×ₒ β ⟩
  forward-left-on-lists [] = []
  forward-left-on-lists ((a , inl b) ∷ l) = (a , b) ∷ forward-left-on-lists l
  forward-left-on-lists ((a , inr c) ∷ l) = forward-left-on-lists l

  forward-left-on-lists-preserves-decreasing-pr₂
   : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
   → is-decreasing-pr₂ α (β +ₒ γ) l
   → is-decreasing-pr₂ α β (forward-left-on-lists l)
  forward-left-on-lists-preserves-decreasing-pr₂ [] δ = []-decr
  forward-left-on-lists-preserves-decreasing-pr₂ ((a , inr c) ∷ l) δ =
   forward-left-on-lists-preserves-decreasing-pr₂ l
    (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ)
  forward-left-on-lists-preserves-decreasing-pr₂ ((a , inl b) ∷ []) δ = sing-decr
  forward-left-on-lists-preserves-decreasing-pr₂
   ((a , inl b) ∷ (a' , inl b') ∷ l) (many-decr p δ) =
    many-decr p
     (forward-left-on-lists-preserves-decreasing-pr₂ ((a' , inl b') ∷ l) δ)
  forward-left-on-lists-preserves-decreasing-pr₂
   ((a , inl b) ∷ (a' , inr c) ∷ l) (many-decr p δ) = 𝟘-elim p

  forward-left : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] β ⟩
  forward-left (l , δ) = forward-left-on-lists l ,
                         forward-left-on-lists-preserves-decreasing-pr₂ l δ

  forward-right-on-lists : List ⟨ α ×ₒ (β +ₒ γ) ⟩ → List ⟨ α ×ₒ γ ⟩
  forward-right-on-lists [] = []
  forward-right-on-lists ((a , inl b) ∷ l) = forward-right-on-lists l
  forward-right-on-lists ((a , inr c) ∷ l) = (a , c) ∷ forward-right-on-lists l

\end{code}

Proving that forward-right-lits preserves the decreasing-pr₂ property requires
the following lemma which says that a decreasing-pr₂ list with a "left-entry"
(a , inl b) continues to have only left-entries and can't be followed by an
element (a' , inr c) (because that would not be decreasing in the second
component).

\begin{code}

  stay-left-list : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
                   (a : ⟨ α ⟩) (b : ⟨ β ⟩)
                   (δ : is-decreasing-pr₂ α (β +ₒ γ) ((a , inl b) ∷ l))
                 → forward-right-on-lists ((a , inl b) ∷ l) ＝ []
  stay-left-list [] a b δ = refl
  stay-left-list ((a' , inl b') ∷ l) a b (many-decr p δ) = stay-left-list l a b' δ
  stay-left-list ((a' , inr c)  ∷ l) a b (many-decr p δ) = 𝟘-elim p

  forward-right-on-lists-preserves-decreasing-pr₂
   : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
   → is-decreasing-pr₂ α (β +ₒ γ) l
   → is-decreasing-pr₂ α γ (forward-right-on-lists l)
  forward-right-on-lists-preserves-decreasing-pr₂ [] δ = []-decr
  forward-right-on-lists-preserves-decreasing-pr₂ ((a , inl b) ∷ l) δ =
   forward-right-on-lists-preserves-decreasing-pr₂ l
    (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ)
  forward-right-on-lists-preserves-decreasing-pr₂ ((a , inr c) ∷ []) δ = sing-decr
  forward-right-on-lists-preserves-decreasing-pr₂
   ((a , inr c) ∷ (a' , inr c') ∷ l) (many-decr p δ) =
    many-decr p
     (forward-right-on-lists-preserves-decreasing-pr₂ ((a' , inr c') ∷ l) δ)
  forward-right-on-lists-preserves-decreasing-pr₂
   ((a , inr c) ∷ (a' , inl b) ∷ l) (many-decr p δ) =
    transport⁻¹
     (is-decreasing-pr₂ α γ)
     (ap ((a , c) ∷_) (stay-left-list l a' b δ))
     sing-decr

  forward-right : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] γ ⟩
  forward-right (l , δ) = forward-right-on-lists l ,
                          forward-right-on-lists-preserves-decreasing-pr₂ l δ

  stay-left : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩) (a : ⟨ α ⟩) (b : ⟨ β ⟩)
              (δ : is-decreasing-pr₂ α (β +ₒ γ) ((a , inl b) ∷ l))
            → forward-right (((a , inl b) ∷ l) , δ) ＝ [] , []-decr
  stay-left l a b δ = to-expᴸ-＝ α γ (stay-left-list l a b δ)

  forward-right-constant-on-inl
   : (l₁ l₂ : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
     (a₁ a₂ : ⟨ α ⟩) (b₁ b₂ : ⟨ β ⟩)
     (δ₁ : is-decreasing-pr₂ α (β +ₒ γ) ((a₁ , inl b₁) ∷ l₁))
     (δ₂ : is-decreasing-pr₂ α (β +ₒ γ) ((a₂ , inl b₂) ∷ l₂))
   → forward-right (((a₁ , inl b₁) ∷ l₁) , δ₁)
     ＝ forward-right (((a₂ , inl b₂) ∷ l₂) , δ₂)
  forward-right-constant-on-inl l₁ l₂ a₁ a₂ b₁ b₂ δ₁ δ₂ =
   stay-left l₁ a₁ b₁ δ₁ ∙ (stay-left l₂ a₂ b₂ δ₂) ⁻¹

\end{code}

\begin{code}

  forward : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ ⟩
  forward l = forward-left l , forward-right l

  forward-is-order-preserving : is-order-preserving
                                 (expᴸ[𝟙+ α ] (β +ₒ γ))
                                 (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ)
                                 forward
  forward-is-order-preserving ([] , δ₁) (((a , inl b) ∷ l₂) , δ₂) []-lex =
   inr ((stay-left l₂ a b δ₂ ⁻¹) , []-lex)
  forward-is-order-preserving ([] , δ₁) (((a , inr c) ∷ l₂) , δ₂) []-lex =
   inl []-lex
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁) (((a' , inl b') ∷ l₂) , δ₂)
   (head-lex (inr (refl , p))) =
    inr (forward-right-constant-on-inl l₁ l₂ a a' b b' δ₁ δ₂ ,
         head-lex (inr (refl , p)))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁) (((a' , inr c)  ∷ l₂) , δ₂)
   (head-lex (inr (e , p))) = 𝟘-elim (+disjoint e)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁) (((a' , inl b)  ∷ l₂) , δ₂)
   (head-lex (inr (e , p))) = 𝟘-elim (+disjoint' e)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁) (((a' , inr c') ∷ l₂) , δ₂)
   (head-lex (inr (refl , p))) = inl (head-lex (inr (refl , p)))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁) (((a' , inl b') ∷ l₂) , δ₂)
   (head-lex (inl p)) =
    inr (forward-right-constant-on-inl l₁ l₂ a a' b b' δ₁ δ₂ ,
         head-lex (inl p))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁) (((a' , inr c)  ∷ l₂) , δ₂)
   (head-lex (inl p)) =
    inl (transport⁻¹
          (λ - → - ≺⟨ expᴸ[𝟙+ α ] γ ⟩ forward-right (((a' , inr c) ∷ l₂) , δ₂))
          (stay-left l₁ a b δ₁)
          []-lex)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁) (((a' , inl b)  ∷ l₂) , δ₂)
   (head-lex (inl p)) = 𝟘-elim p
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁) (((a' , inr c') ∷ l₂) , δ₂)
   (head-lex (inl p)) = inl (head-lex (inl p))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁) (((a , inl b) ∷ l₂) , δ₂)
   (tail-lex refl p) = h (forward-is-order-preserving (l₁ , ε₁) (l₂ , ε₂) p)
    where
     ε₁ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ₁
     ε₂ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ₂
     h : forward (l₁ , ε₁) ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (l₂ , ε₂)
       → forward (((a , inl b) ∷ l₁) , δ₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (((a , inl b) ∷ l₂) , δ₂)
     h (inl q) = inl q
     h (inr (e , q)) = inr (forward-right-constant-on-inl l₁ l₂ a a b b δ₁ δ₂ ,
                            tail-lex refl q)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁) (((a , inr c) ∷ l₂) , δ₂)
   (tail-lex refl p) = h (forward-is-order-preserving (l₁ , ε₁) (l₂ , ε₂) p)
    where
     ε₁ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ₁
     ε₂ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ₂
     h : forward (l₁ , ε₁) ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (l₂ , ε₂)
       → forward (((a , inr c) ∷ l₁) , δ₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (((a , inr c) ∷ l₂) , δ₂)
     h (inl q) = inl (tail-lex refl q)
     h (inr (e , q)) = inr (to-expᴸ-＝ α γ (ap ((a , c) ∷_) (ap pr₁ e)) , q)

\end{code}

We now construct an order preserving map in the other direction.

\begin{code}

  backward-on-lists : List ⟨ α ×ₒ β ⟩ → List ⟨ α ×ₒ γ ⟩ → List ⟨ α ×ₒ (β +ₒ γ) ⟩
  backward-on-lists l ((a , c) ∷ l') = (a , inr c) ∷ backward-on-lists l l'
  backward-on-lists ((a , b) ∷ l) [] = (a , inl b) ∷ backward-on-lists l []
  backward-on-lists [] [] = []

  backward-on-lists-preserves-decreasing-pr₂
   : (l₁ : List ⟨ α ×ₒ β ⟩) (l₂ : List ⟨ α ×ₒ γ ⟩)
   → is-decreasing-pr₂ α β l₁
   → is-decreasing-pr₂ α γ l₂
   → is-decreasing-pr₂ α (β +ₒ γ) (backward-on-lists l₁ l₂)
  backward-on-lists-preserves-decreasing-pr₂ l₁ ((a , c) ∷ (a' , c') ∷ l₂) δ₁
   (many-decr p δ) =
    many-decr p
     (backward-on-lists-preserves-decreasing-pr₂ l₁ ((a' , c') ∷ l₂) δ₁ δ)
  backward-on-lists-preserves-decreasing-pr₂ [] ((a , c) ∷ []) δ₁ δ₂ = sing-decr
  backward-on-lists-preserves-decreasing-pr₂ ((a' , b') ∷ l₁) ((a , c) ∷ [])
   δ₁ δ₂ = many-decr ⋆
            (backward-on-lists-preserves-decreasing-pr₂
              ((a' , b') ∷ l₁) [] δ₁ []-decr)
  backward-on-lists-preserves-decreasing-pr₂ ((a , b) ∷ []) [] δ₁ δ₂ = sing-decr
  backward-on-lists-preserves-decreasing-pr₂ ((a , b) ∷ (a' , b') ∷ l₁) []
   (many-decr p δ) δ₂ =
    many-decr p
     (backward-on-lists-preserves-decreasing-pr₂ ((a' , b') ∷ l₁) [] δ []-decr)
  backward-on-lists-preserves-decreasing-pr₂ [] [] δ₁ δ₂ = []-decr

  backward : ⟨ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ) ⟩ → ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩
  backward ((l₁ , δ₁) , (l₂ , δ₂)) =
   backward-on-lists l₁ l₂ ,
   backward-on-lists-preserves-decreasing-pr₂ l₁ l₂ δ₁ δ₂

  backward-is-order-preserving'
   : (l₁ l₁' : List ⟨ α ×ₒ β ⟩) (l₂ l₂' : List ⟨ α ×ₒ γ ⟩)
     (δ₁ : is-decreasing-pr₂ α β l₁)
     (δ₁' : is-decreasing-pr₂ α β l₁')
     (δ₂ : is-decreasing-pr₂ α γ l₂)
     (δ₂' : is-decreasing-pr₂ α γ l₂')
   → ((l₁ , δ₁) , (l₂ , δ₂)) ≺⟨ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ) ⟩
     ((l₁' , δ₁') , (l₂' , δ₂'))
   → backward ((l₁ , δ₁) , (l₂ , δ₂)) ≺⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩
     backward ((l₁' , δ₁') , (l₂' , δ₂'))
  backward-is-order-preserving' [] [] [] [] δ₁ δ₁' δ₂ δ₂' (inl ())
  backward-is-order-preserving' [] [] [] [] δ₁ δ₁' δ₂ δ₂' (inr (refl , ()))
  backward-is-order-preserving' [] [] [] (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂' p = []-lex
  backward-is-order-preserving' [] [] (_ ∷ l₂) [] δ₁ δ₁' δ₂ δ₂' (inl ())
  backward-is-order-preserving' [] [] (_ ∷ l₂) [] δ₁ δ₁' δ₂ δ₂' (inr (e , p)) =
   𝟘-elim ([]-is-not-cons _ l₂ (ap pr₁ (e ⁻¹)))
  backward-is-order-preserving' [] [] (_ ∷ l₂) (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inl p))) = head-lex (inl p)
  backward-is-order-preserving' [] [] (_ ∷ l₂) (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
  backward-is-order-preserving' [] [] ((a , c) ∷ l₂) ((a , c) ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (tail-lex refl p)) =
    tail-lex refl
     (backward-is-order-preserving' [] [] l₂ l₂' []-decr []-decr
       (tail-is-decreasing-pr₂ α γ (a , c) δ₂)
       (tail-is-decreasing-pr₂ α γ (a , c) δ₂')
       (inl p))
  backward-is-order-preserving' [] (_ ∷ l₁') [] [] δ₁ δ₁' δ₂ δ₂' p = []-lex
  backward-is-order-preserving' [] (_ ∷ l₁') [] (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂' p =
   []-lex
  backward-is-order-preserving' [] (_ ∷ l₁') (_ ∷ l₂) [] δ₁ δ₁' δ₂ δ₂' (inl ())
  backward-is-order-preserving' [] (_ ∷ l₁') (_ ∷ l₂) [] δ₁ δ₁' δ₂ δ₂'
   (inr (e , p)) = 𝟘-elim ([]-is-not-cons _ l₂ (ap pr₁ (e ⁻¹)))
  backward-is-order-preserving' [] (_ ∷ l₁') (_ ∷ l₂) (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inl p))) = head-lex (inl p)
  backward-is-order-preserving' [] (_ ∷ l₁') (_ ∷ l₂) (_ ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
  backward-is-order-preserving' [] (x ∷ l₁') (y ∷ l₂) (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (tail-lex refl p)) =
    tail-lex refl
     (backward-is-order-preserving' [] (x ∷ l₁') l₂ l₂' []-decr δ₁'
       (tail-is-decreasing-pr₂ α γ y δ₂)
       (tail-is-decreasing-pr₂ α γ z δ₂')
       (inl p))
  backward-is-order-preserving' [] (x ∷ l₁') (y ∷ l₂) (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inr (refl , p)) =
    tail-lex refl
     (backward-is-order-preserving' [] (x ∷ l₁') l₂ l₂ []-decr δ₁'
       (tail-is-decreasing-pr₂ α γ y δ₂')
       (tail-is-decreasing-pr₂ α γ z δ₂)
       (inr (refl , []-lex)))
  backward-is-order-preserving' (x ∷ l₁) [] [] [] δ₁ δ₁' δ₂ δ₂' (inl ())
  backward-is-order-preserving' (x ∷ l₁) [] [] [] δ₁ δ₁' δ₂ δ₂' (inr (refl , ()))
  backward-is-order-preserving' (x ∷ l₁) [] [] (x₁ ∷ l₂') δ₁ δ₁' δ₂ δ₂' p =
   head-lex (inl ⋆)
  backward-is-order-preserving' (x ∷ l₁) [] (y ∷ l₂) [] δ₁ δ₁' δ₂ δ₂' (inl ())
  backward-is-order-preserving' (x ∷ l₁) [] (y ∷ l₂) [] δ₁ δ₁' δ₂ δ₂'
   (inr (e , p)) = 𝟘-elim ([]-is-not-cons y l₂ (ap pr₁ (e ⁻¹)))
  backward-is-order-preserving' (x ∷ l₁) [] (y ∷ l₂) (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inl p))) = head-lex (inl p)
  backward-is-order-preserving' (x ∷ l₁) [] (y ∷ l₂) (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
  backward-is-order-preserving' (x ∷ l₁) [] (y ∷ l₂) (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   (inl (tail-lex refl p)) =
    tail-lex refl
     (backward-is-order-preserving' (x ∷ l₁) [] l₂ l₂' δ₁ []-decr
       (tail-is-decreasing-pr₂ α γ y δ₂)
       (tail-is-decreasing-pr₂ α γ z δ₂')
       (inl p))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') [] [] δ₁ δ₁' δ₂ δ₂'
   (inr (refl , head-lex (inl p))) = head-lex (inl p)
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') [] [] δ₁ δ₁' δ₂ δ₂'
   (inr (refl , head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') [] [] δ₁ δ₁' δ₂ δ₂'
   (inr (refl , tail-lex refl p)) =
    tail-lex refl
     (backward-is-order-preserving' l₁ l₁' [] []
       (tail-is-decreasing-pr₂ α β y δ₁)
       (tail-is-decreasing-pr₂ α β x δ₁')
       []-decr
       []-decr
       (inr (refl , p)))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') [] (z ∷ l₂') δ₁ δ₁' δ₂ δ₂'
   p = head-lex (inl ⋆)
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) [] δ₁ δ₁' δ₂ δ₂'
   (inl ())
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) [] δ₁ δ₁' δ₂ δ₂'
   (inr (e , p)) = 𝟘-elim ([]-is-not-cons z l₂ (ap pr₁ (e ⁻¹)))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) (w ∷ l₂')
   δ₁ δ₁' δ₂ δ₂' (inl (head-lex (inl p))) = head-lex (inl p)
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) (w ∷ l₂')
   δ₁ δ₁' δ₂ δ₂' (inl (head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) (w ∷ l₂')
   δ₁ δ₁' δ₂ δ₂' (inl (tail-lex refl p)) =
    tail-lex refl
     (backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') l₂ l₂' δ₁ δ₁'
       (tail-is-decreasing-pr₂ α γ z δ₂)
       (tail-is-decreasing-pr₂ α γ z δ₂')
       (inl p))
  backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') (z ∷ l₂) (w ∷ l₂')
   δ₁ δ₁' δ₂ δ₂' (inr (refl , p)) =
   tail-lex refl
    (backward-is-order-preserving' (x ∷ l₁) (y ∷ l₁') l₂ l₂ δ₁ δ₁'
      (tail-is-decreasing-pr₂ α γ z δ₂')
      (tail-is-decreasing-pr₂ α γ z δ₂)
      (inr (refl , p)))

  backward-is-order-preserving : is-order-preserving
                                  ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ))
                                  (expᴸ[𝟙+ α ] (β +ₒ γ))
                                  backward
  backward-is-order-preserving ((l₁ , δ₁) , (l₂ , δ₂))
                               ((l₁' , δ₁') , (l₂' , δ₂')) =
   backward-is-order-preserving' l₁ l₁' l₂ l₂' δ₁ δ₁' δ₂ δ₂'

\end{code}

\begin{code}

  backward-forward-is-id : backward ∘ forward ∼ id
  backward-forward-is-id (l , δ) = to-expᴸ-＝ α (β +ₒ γ) (I l δ)
   where
    I : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
      → is-decreasing-pr₂ α (β +ₒ γ) l
      → backward-on-lists (forward-left-on-lists l) (forward-right-on-lists l)
        ＝ l
    I [] δ      = refl
    I ((a , inr c) ∷ l) δ =
     ap ((a , inr c) ∷_)
        (I l (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ))
    I ((a , inl b) ∷ l) δ =
     backward-on-lists (fₗ ((a , inl b) ∷ l)) (fᵣ ((a , inl b) ∷ l)) ＝⟨ II   ⟩
     backward-on-lists (fₗ (a , inl b ∷ l)) []                       ＝⟨ refl ⟩
     backward-on-lists ((a , b) ∷ fₗ l) []                           ＝⟨ refl ⟩
     (a , inl b) ∷ backward-on-lists (fₗ l) []                       ＝⟨ III  ⟩
     (a , inl b) ∷ backward-on-lists (fₗ l) (fᵣ l)                   ＝⟨ IV   ⟩
     ((a , inl b) ∷ l)                                               ∎
      where
       fₗ = forward-left-on-lists
       fᵣ = forward-right-on-lists

       II  = ap (backward-on-lists (fₗ ((a , inl b) ∷ l)))
                (stay-left-list l a b δ)
       III = ap (λ - → (a , inl b) ∷ backward-on-lists (fₗ l) -)
                ((stay-left-list l a b δ) ⁻¹)
       IV  = ap ((a , inl b) ∷_)
                (I l (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ))

  forward-backward-is-id : forward ∘ backward ∼ id
  forward-backward-is-id ((l₁ , δ₁) , (l₂ , δ₂)) = to-×-＝ I II
   where
    I : forward-left (backward ((l₁ , δ₁) , l₂ , δ₂)) ＝ l₁ , δ₁
    I = to-expᴸ-＝ α β (I' l₁ l₂ δ₁ δ₂)
     where
      I' : (l₁ : List ⟨ α ×ₒ β ⟩) (l₂ : List ⟨ α ×ₒ γ ⟩)
         → is-decreasing-pr₂ α β l₁
         → is-decreasing-pr₂ α γ l₂
         → forward-left-on-lists (backward-on-lists l₁ l₂) ＝ l₁
      I' l₁ (y ∷ l₂) δ₁ δ₂ = I' l₁ l₂ δ₁ (tail-is-decreasing-pr₂ α γ y δ₂)
      I' [] [] δ₁ δ₂ = refl
      I' (x ∷ l₁) [] δ₁ δ₂ =
       ap (x ∷_) (I' l₁ [] (tail-is-decreasing-pr₂ α β x δ₁) []-decr)

    II : forward-right (backward ((l₁ , δ₁) , l₂ , δ₂)) ＝ l₂ , δ₂
    II = to-expᴸ-＝ α γ (I' l₁ l₂ δ₁ δ₂)
     where
      I' : (l₁ : List ⟨ α ×ₒ β ⟩) (l₂ : List ⟨ α ×ₒ γ ⟩)
         → is-decreasing-pr₂ α β l₁
         → is-decreasing-pr₂ α γ l₂
         → forward-right-on-lists (backward-on-lists l₁ l₂) ＝ l₂
      I' l₁ (y ∷ l₂) δ₁ δ₂ =
       ap (y ∷_) (I' l₁ l₂ δ₁ (tail-is-decreasing-pr₂ α γ y δ₂))
      I' [] [] δ₁ δ₂ = refl
      I' (x ∷ l₁) [] δ₁ δ₂ = I' l₁ [] (tail-is-decreasing-pr₂ α β x δ₁) []-decr

\end{code}

Finally, we put the piece togethere to obtain the desired equivalence.

\begin{code}

 expᴸ-by-+ₒ-≃ₒ : expᴸ[𝟙+ α ] (β +ₒ γ) ≃ₒ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)
 expᴸ-by-+ₒ-≃ₒ = forward , forward-is-order-preserving ,
                 qinvs-are-equivs forward
                  (backward , backward-forward-is-id , forward-backward-is-id) ,
                 backward-is-order-preserving

 expᴸ-by-+ₒ : expᴸ[𝟙+ α ] (β +ₒ γ) ＝ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)
 expᴸ-by-+ₒ = eqtoidₒ (ua (𝓤 ⊔ 𝓥)) fe'
               (expᴸ[𝟙+ α ] (β +ₒ γ))
               ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ))
               expᴸ-by-+ₒ-≃ₒ

\end{code}

As a corollary, we can now derive that expᴸ satisfies the successor specification:

\begin{code}

expᴸ-satisfies-succ-specification :
 (α : Ordinal 𝓤) → exp-specification-succ (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ])
expᴸ-satisfies-succ-specification α β =
 expᴸ[𝟙+ α ] (β +ₒ 𝟙ₒ)               ＝⟨ expᴸ-by-+ₒ α β 𝟙ₒ ⟩
 (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] 𝟙ₒ) ＝⟨ I ⟩
 (expᴸ[𝟙+ α ] β) ×ₒ (𝟙ₒ +ₒ α)        ∎
  where
   I = ap ((expᴸ[𝟙+ α ] β) ×ₒ_) (𝟙ₒ-neutral-expᴸ α)

\end{code}

\begin{code}


-- module _ {I : 𝓤 ̇  }
--          (i₀ : I)
--          (β : I → Ordinal 𝓤)
--          (α : Ordinal 𝓤)
--  where

--   private
--    γ : I → Ordinal 𝓤
--    γ i = expᴸ[𝟙+ α ] (β i)

--    ι : (ζ : I → Ordinal 𝓤) → {i : I} → ⟨ ζ i ⟩ → ⟨ sup ζ ⟩
--    ι ζ {i} = pr₁ (sup-is-upper-bound ζ i)

--    ι-is-simulation : (ζ : I → Ordinal 𝓤) → {i : I}
--                    → is-simulation (ζ i) (sup ζ ) (ι ζ)
--    ι-is-simulation ζ {i} = pr₂ (sup-is-upper-bound ζ i)

--    ι-is-order-preserving : (ζ : I → Ordinal 𝓤) {i : I}
--                          → is-order-preserving (ζ i) (sup ζ) (ι ζ)
--    ι-is-order-preserving ζ {i} = simulations-are-order-preserving (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

--    ι-is-order-reflecting : (ζ : I → Ordinal 𝓤) {i : I}
--                          → is-order-reflecting (ζ i) (sup ζ) (ι ζ)
--    ι-is-order-reflecting ζ {i} = simulations-are-order-reflecting (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

--    ι-is-lc : (ζ : I → Ordinal 𝓤) {i : I}
--            → left-cancellable (ι ζ)
--    ι-is-lc ζ {i} = simulations-are-lc (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

--    ι-is-initial-segment : (ζ : I → Ordinal 𝓤) → {i : I}
--                         → is-initial-segment (ζ i) (sup ζ ) (ι ζ)
--    ι-is-initial-segment ζ {i} = simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

--    ι-is-surjective : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩)
--                    → ∃ i ꞉ I , Σ x ꞉ ⟨ ζ i ⟩ , ι ζ {i} x ＝ s
--    ι-is-surjective = sup-is-upper-bound-jointly-surjective

--    ι-is-surjective⁺ : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩) (i : I) (x : ⟨ ζ i ⟩)
--                     → s ≺⟨ sup ζ ⟩ ι ζ x
--                     → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
--    ι-is-surjective⁺ ζ s i x p =
--     h (simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ) x s p)
--     where
--      h : Σ y ꞉ ⟨ ζ i ⟩ , y ≺⟨ ζ i ⟩ x × (ι ζ y ＝ s)
--        → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
--      h (y , (_ , q)) = y , q

--    module _ (i : I) where
--     f₁ : List (⟨ α ×ₒ β i ⟩) → List (⟨ α ×ₒ sup β ⟩)
--     f₁ [] = []
--     f₁ (a , b ∷ l) = a , ι β b ∷ f₁ l
--     f₂ : (l : List (⟨ α ×ₒ β i ⟩))
--        → is-decreasing-pr₂ α (β i) l
--        → is-decreasing-pr₂ α (sup β) (f₁ l)
--     f₂ [] δ = []-decr
--     f₂ (a , b ∷ []) δ = sing-decr
--     f₂ (a , b ∷ a' , b' ∷ l) (many-decr p δ) =
--       many-decr (simulations-are-order-preserving (β i) (sup β)
--                   (ι β)
--                   (pr₂ (sup-is-upper-bound β i)) b' b p)
--                 (f₂ (a' , b' ∷ l) δ)
--     f : ⟨ γ i ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
--     f (l , δ) = f₁ l , f₂ l δ

--    f₁-surj-lemma : (a : ⟨ α ⟩) (i : I) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
--                  → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
--                  → Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) (a , b ∷ l')
--                                               × ((a , ι β b ∷ l) ＝ f₁ i (a , b ∷ l'))
--    f₁-surj-lemma a i b [] δ = [] , sing-decr , refl
--    f₁-surj-lemma a i b ((a' , s) ∷ l) δ =
--     (a' , b' ∷ l') ,
--     many-decr order-lem₃ δ' ,
--     ap (a , ι β b ∷_) (ap (λ - → a' , - ∷ l) ((pr₂ lem) ⁻¹) ∙ pr₂ (pr₂ IH))
--      where
--       lem : Σ b' ꞉ ⟨ β i ⟩ , ι β b' ＝ s
--       lem = ι-is-surjective⁺ β s i b (heads-are-decreasing (underlying-order (sup β)) δ)
--       b' : ⟨ β i ⟩
--       b' = pr₁ lem
--       order-lem₁ : s ≺⟨ sup β ⟩ ι β b
--       order-lem₁ = heads-are-decreasing (underlying-order (sup β)) δ
--       order-lem₂ : ι β b' ≺⟨ sup β ⟩ ι β b
--       order-lem₂ = transport⁻¹ (λ - → underlying-order (sup β) - (ι β b)) (pr₂ lem) order-lem₁
--       order-lem₃ : b' ≺⟨ β i ⟩ b
--       order-lem₃ = ι-is-order-reflecting β b' b order-lem₂
--       IH : Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) (a' , b' ∷ l')
--                                       × ((a' , ι β b' ∷ l) ＝ f₁ i (a' , b' ∷ l'))
--       IH = f₁-surj-lemma a' i b' l
--             (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) (a' , - ∷ l)) (pr₂ lem)
--               (tail-is-decreasing (underlying-order (sup β)) δ))
--       l' : List (⟨ α ×ₒ β i ⟩)
--       l' = pr₁ IH
--       δ' : is-decreasing-pr₂ α (β i) (a' , b' ∷ l')
--       δ' = pr₁ (pr₂ IH)

--    f₁-surj : (l : List (⟨ α ×ₒ sup β ⟩))
--            → is-decreasing-pr₂ α (sup β) l
--            → ∃ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
--                                                   × (l ＝ f₁ i l')
--    f₁-surj [] δ = ∣ i₀ , [] , []-decr , refl ∣
--    f₁-surj (a , s ∷ l) δ = ∥∥-functor h (ι-is-surjective β s)
--     where
--      h : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , ι β b ＝ s)
--        → Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
--                                               × ((a , s ∷ l) ＝ f₁ i l')
--      h (i , b , refl) = i , (a , b ∷ pr₁ lem) , (pr₁ (pr₂ lem) , pr₂ (pr₂ lem))
--       where
--        lem : Σ l' ꞉ List ⟨ α ×ₒ β i ⟩ , is-decreasing-pr₂ α (β i) (a , b ∷ l')
--                                       × (a , ι β b ∷ l ＝ f₁ i (a , b ∷ l'))
--        lem = f₁-surj-lemma a i b l δ

--    f-surj : (y : ⟨ expᴸ[𝟙+ α ] (sup β) ⟩) → ∃ i ꞉ I , Σ x ꞉ ⟨ γ i ⟩ , f i x ＝ y
--    f-surj (l , δ) = ∥∥-functor h (f₁-surj l δ)
--     where
--      h : (Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
--                                                × (l ＝ f₁ i l'))
--        → Σ i ꞉ I , Σ x ꞉ ⟨ γ i ⟩ , (f i x ＝ l , δ)
--      h (i , l' , δ , refl) = i , (l' , δ) , to-expᴸ-＝ α (sup β) refl

--    f-is-order-preserving : (i : I) → is-order-preserving (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
--    f-is-order-preserving i ([] , δ) (_ , ε) []-lex = []-lex
--    f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-preserving β b b' m))
--    f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (refl , m))) = head-lex (inr (refl , m))
--    f-is-order-preserving i ((_ ∷ l) , δ) ((_ ∷ l') , ε) (tail-lex refl m) =
--      tail-lex refl (f-is-order-preserving i (l , tail-is-decreasing (underlying-order (β i)) δ) (l' , tail-is-decreasing (underlying-order (β i)) ε) m)

--    f-is-order-reflecting : (i : I) → is-order-reflecting (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
--    f-is-order-reflecting i ([] , δ) ((a , b ∷ l) , ε) []-lex = []-lex
--    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-reflecting β b b' m))
--    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (e , m))) = head-lex (inr (ι-is-lc β e , m))
--    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (tail-lex e m) =
--     tail-lex (to-×-＝ (ap pr₁ e) (ι-is-lc β (ap pr₂ e)))
--     (f-is-order-reflecting i (l , tail-is-decreasing (underlying-order (β i)) δ) (l' , tail-is-decreasing (underlying-order (β i)) ε) m)

--    -- We factor out:
--    partial-invertibility-lemma : (i : I) -- (a : ⟨ α ⟩) (b : ⟨ β i ⟩)
--                                → (l : List (⟨ α ×ₒ β i ⟩))
--                                → is-decreasing-pr₂ α (sup β) (f₁ i l) -- (f₁ i (a , b ∷ l))
--                                → is-decreasing-pr₂ α (β i) l -- (a , b ∷ l)
--    partial-invertibility-lemma i [] ds = []-decr
--    partial-invertibility-lemma i ((a , b) ∷ []) ds = sing-decr
--    partial-invertibility-lemma i ((a , b) ∷ (a' , b') ∷ l) (many-decr m ds) =
--      many-decr (ι-is-order-reflecting β b' b m) (partial-invertibility-lemma i ((a' , b') ∷ l) ds)

--    f-is-partially-invertible : (i : I)
--                              → (xs : List ⟨ α ×ₒ β i ⟩) → (δ : is-decreasing-pr₂ α (β i) xs)
--                              → (ys : List ⟨ α ×ₒ sup β ⟩) → (ε : is-decreasing-pr₂ α (sup β) ys)
--                              → (ys , ε) ≺⟨ expᴸ[𝟙+ α ] (sup β) ⟩ f i (xs , δ)
--                              → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ (ys , ε)
--    f-is-partially-invertible i xs δ [] []-decr p = ([] , []-decr) , refl
--    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ []) ε (head-lex (inl m)) = ((a' , pr₁ ι-sim ∷ []) , sing-decr) , (to-expᴸ-＝ α (sup β) (ap (λ - → (a' , -) ∷ []) (pr₂ (pr₂ ι-sim))))
--      where
--        ι-sim = ι-is-initial-segment β b b' m
--    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inl m)) =
--      let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl (Transitivity (sup β) _ _ _ p m)))
--          xs' = pr₁ (pr₁ IH)
--          ι-sim = ι-is-initial-segment β b b' m
--          b₀ = pr₁ ι-sim
--          p₀ = transport⁻¹ (λ - → b₁ ≺⟨ sup β ⟩ -) (pr₂ (pr₂ ι-sim)) p
--      in ((a' , b₀ ∷ xs') , partial-invertibility-lemma i ((a' , b₀) ∷ xs') (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b₀) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p₀ ε)))
--        , (to-expᴸ-＝ α (sup β) (ap₂ (λ x y → (a' , x) ∷ y) (pr₂ (pr₂ ι-sim)) (ap pr₁ (pr₂ IH))))
--    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ []) ε (head-lex (inr (refl , m))) = ((a' , b ∷ []) , sing-decr) , (to-expᴸ-＝ α (sup β) refl)
--    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inr (refl , m))) =
--      let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl p))
--          xs' = pr₁ (pr₁ IH)
--      in (((a' , b) ∷ xs') , partial-invertibility-lemma i ((a' , b) ∷ xs')
--                                                           (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p ε)))
--         , to-expᴸ-＝ α (sup β) (ap ((a' , ι β b) ∷_) (ap pr₁ (pr₂ IH)))
--    f-is-partially-invertible i ((a , b) ∷ xs) δ (.(a , ι β b) ∷ ys) ε (tail-lex refl p) =
--      let IH = f-is-partially-invertible i xs (tail-is-decreasing (underlying-order (β i)) δ) ys (tail-is-decreasing (underlying-order (sup β)) ε) p
--      in (((a , b) ∷ pr₁ (pr₁ IH)) , partial-invertibility-lemma i ((a , b) ∷ pr₁ (pr₁ IH))
--                                                                   (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) ε))
--        , to-expᴸ-＝ α (sup β) (ap ((a , ι β b) ∷_) (ap pr₁ (pr₂ IH)))

--    f-is-initial-segment : (i : I) → is-initial-segment (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
--    f-is-initial-segment i = order-reflecting-partial-surjections-are-initial-segments (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i) (f-is-order-reflecting i) g
--      where
--        g : (xs : ⟨ γ i ⟩) → (ys : ⟨ expᴸ[𝟙+ α ] (sup β) ⟩) → ys ≺⟨ expᴸ[𝟙+ α ] (sup β) ⟩ f i xs → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ ys
--        g (xs , δ) (ys , ε) = f-is-partially-invertible i xs δ ys ε

--   exp-sup-is-upper-bound : (i : I) → γ i ⊴ (expᴸ[𝟙+ α ] (sup β))
--   exp-sup-is-upper-bound i = f i , f-is-initial-segment i , f-is-order-preserving i

--   exp-sup-simulation : sup (λ i → (expᴸ[𝟙+ α ] (β i))) ⊴ (expᴸ[𝟙+ α ] (sup β))
--   exp-sup-simulation = sup-is-lower-bound-of-upper-bounds (λ i → (expᴸ[𝟙+ α ] (β i))) (expᴸ[𝟙+ α ] (sup β)) exp-sup-is-upper-bound

--   exp-sup-simulation-surjective : is-surjection (pr₁ exp-sup-simulation)
--   exp-sup-simulation-surjective = surjectivity-lemma γ (expᴸ[𝟙+ α ] (sup β)) exp-sup-is-upper-bound f-surj

--   sup-spec : sup (λ i → (expᴸ[𝟙+ α ] (β i))) ＝ (expᴸ[𝟙+ α ] (sup β))
--   sup-spec = surjective-simulation-gives-＝ pt fe' (ua _)
--                (sup (λ i → (expᴸ[𝟙+ α ] (β i))))
--                (expᴸ[𝟙+ α ] (sup β))
--                (pr₁ exp-sup-simulation)
--                (pr₂ exp-sup-simulation)
--                exp-sup-simulation-surjective

-- exp-sup-spec : (α : Ordinal 𝓤) {I : 𝓤 ̇  } → ∥ I ∥ → (β : I → Ordinal 𝓤) → (expᴸ[𝟙+ α ] (sup β)) ＝ sup (λ i → (expᴸ[𝟙+ α ] (β i)))
-- exp-sup-spec α i β = ∥∥-rec (the-type-of-ordinals-is-a-set (ua _) fe') (λ i₀ → sup-spec i₀ β α ⁻¹) i

-- \end{code}

-- \begin{code}

-- monotone-in-exponent : ∀ {𝓤} (α : Ordinal 𝓤)
--                      → is-monotone (OO 𝓤) (OO 𝓤) (expᴸ[𝟙+ α ])
-- monotone-in-exponent α = is-monotone-if-continuous (expᴸ[𝟙+ α ]) (exp-sup-spec α)

-- \end{code}