Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
Started November 2023. Refactored December 2024.

In Ordinals.Exponentiation.PropertiesViaTransport we derive various properties
of our concrete ordinal exponentiation (using decreasing lists) via transport
and the equivalence with the abstract construction (using suprema) in
Ordinals.Exponentiation.RelatingConstructions.

For comparison, and with an eye on to their combinatorial meaning, we offer
direct proofs of some of these properties here.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

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
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua pt
open import Ordinals.Exponentiation.Specification ua pt sr

open PropositionalTruncation pt

open suprema pt sr

\end{code}

The fact that the concrete exponentiation satisfies the zero specification is
easily shown, as is the fact that exponentiating by 𝟙ₒ is the identity.

\begin{code}

expᴸ-satisfies-zero-specification-≃ₒ : (α : Ordinal 𝓤)
                                     → expᴸ[𝟙+ α ] (𝟘ₒ {𝓥}) ≃ₒ 𝟙ₒ {𝓤 ⊔ 𝓥}
expᴸ-satisfies-zero-specification-≃ₒ α = f , f-order-preserving ,
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

expᴸ-satisfies-zero-specification
 : (α : Ordinal 𝓤)
 → exp-specification-zero {𝓤} {𝓥} (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ])
expᴸ-satisfies-zero-specification {𝓤} {𝓥} α =
 eqtoidₒ (ua (𝓤 ⊔ 𝓥)) fe' (expᴸ[𝟙+ α ] 𝟘ₒ) 𝟙ₒ
         (expᴸ-satisfies-zero-specification-≃ₒ α)

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
    p (((a , ⋆) ∷ []) , δ) = to-DecrList₂-＝ α 𝟙ₒ refl
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

Proving that forward-right-on-lists preserves the decreasing-pr₂ property requires
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
  stay-left-list ((a' , inl b') ∷ l) a b (many-decr p δ) =
   stay-left-list l a b' δ
  stay-left-list ((a' , inr c)  ∷ l) a b (many-decr p δ) = 𝟘-elim p

  forward-right-on-lists-preserves-decreasing-pr₂
   : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
   → is-decreasing-pr₂ α (β +ₒ γ) l
   → is-decreasing-pr₂ α γ (forward-right-on-lists l)
  forward-right-on-lists-preserves-decreasing-pr₂ [] δ = []-decr
  forward-right-on-lists-preserves-decreasing-pr₂ ((a , inl b) ∷ l) δ =
   forward-right-on-lists-preserves-decreasing-pr₂ l
    (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ)
  forward-right-on-lists-preserves-decreasing-pr₂ ((a , inr c) ∷ []) δ =
   sing-decr
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
  stay-left l a b δ = to-DecrList₂-＝ α γ (stay-left-list l a b δ)

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

The maps forward-left and forward-right are now combined into a single order
preserving forward map.

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
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁)
                              (((a' , inl b') ∷ l₂) , δ₂)
                              (head-lex (inr (refl , p))) =
   inr (forward-right-constant-on-inl l₁ l₂ a a' b b' δ₁ δ₂ ,
        head-lex (inr (refl , p)))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁)
                              (((a' , inr c)  ∷ l₂) , δ₂)
                              (head-lex (inr (e , p))) = 𝟘-elim (+disjoint e)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁)
                              (((a' , inl b)  ∷ l₂) , δ₂)
                              (head-lex (inr (e , p))) = 𝟘-elim (+disjoint' e)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁)
                              (((a' , inr c') ∷ l₂) , δ₂)
                              (head-lex (inr (refl , p))) =
   inl (head-lex (inr (refl , p)))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁)
                              (((a' , inl b') ∷ l₂) , δ₂)
                              (head-lex (inl p)) =
   inr (forward-right-constant-on-inl l₁ l₂ a a' b b' δ₁ δ₂ ,
        head-lex (inl p))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁)
                              (((a' , inr c)  ∷ l₂) , δ₂)
                              (head-lex (inl p)) =
   inl (transport⁻¹
         (λ - → - ≺⟨ expᴸ[𝟙+ α ] γ ⟩ forward-right (((a' , inr c) ∷ l₂) , δ₂))
         (stay-left l₁ a b δ₁)
         []-lex)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁)
                              (((a' , inl b)  ∷ l₂) , δ₂)
                              (head-lex (inl p)) = 𝟘-elim p
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁)
                              (((a' , inr c') ∷ l₂) , δ₂)
                              (head-lex (inl p)) = inl (head-lex (inl p))
  forward-is-order-preserving (((a , inl b) ∷ l₁) , δ₁)
                              (((a , inl b) ∷ l₂) , δ₂)
                              (tail-lex refl p) =
   h (forward-is-order-preserving (l₁ , ε₁) (l₂ , ε₂) p)
    where
     ε₁ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ₁
     ε₂ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ₂
     h : forward (l₁ , ε₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (l₂ , ε₂)
       → forward (((a , inl b) ∷ l₁) , δ₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (((a , inl b) ∷ l₂) , δ₂)
     h (inl q) = inl q
     h (inr (e , q)) = inr (forward-right-constant-on-inl l₁ l₂ a a b b δ₁ δ₂ ,
                            tail-lex refl q)
  forward-is-order-preserving (((a , inr c) ∷ l₁) , δ₁)
                              (((a , inr c) ∷ l₂) , δ₂)
                              (tail-lex refl p) =
   h (forward-is-order-preserving (l₁ , ε₁) (l₂ , ε₂) p)
    where
     ε₁ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ₁
     ε₂ = tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ₂
     h : forward (l₁ , ε₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (l₂ , ε₂)
       → forward (((a , inr c) ∷ l₁) , δ₁)
         ≺⟨ (expᴸ[𝟙+ α ] β ×ₒ expᴸ[𝟙+ α ] γ) ⟩ forward (((a , inr c) ∷ l₂) , δ₂)
     h (inl q) = inl (tail-lex refl q)
     h (inr (e , q)) = inr (to-DecrList₂-＝ α γ (ap ((a , c) ∷_) (ap pr₁ e)) , q)

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

The two maps are inverse to each other.

\begin{code}

  backward-forward-is-id : backward ∘ forward ∼ id
  backward-forward-is-id (l , δ) = to-DecrList₂-＝ α (β +ₒ γ) (I l δ)
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
     backward-on-lists (fₗ (a , inl b ∷ l)) []                       ＝⟨refl⟩
     backward-on-lists ((a , b) ∷ fₗ l) []                           ＝⟨refl⟩
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
    I = to-DecrList₂-＝ α β (I' l₁ l₂ δ₁ δ₂)
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
    II = to-DecrList₂-＝ α γ (I' l₁ l₂ δ₁ δ₂)
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

As a corollary, we can now derive that expᴸ satisfies the successor specification.

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

Finally, we give a direct proof that expᴸ satisfies the supremum specification.
It will be convenient to introduce some abbreviations first.

\begin{code}

module _ {I : 𝓤 ̇  }
         (β : I → Ordinal 𝓤)
         (α : Ordinal 𝓤)
 where

  private
   ι : {i : I} → ⟨ β i ⟩ → ⟨ sup β ⟩
   ι {i} = [ β i , sup β ]⟨ sup-is-upper-bound β i ⟩

   ι-is-simulation : {i : I} → is-simulation (β i) (sup β ) ι
   ι-is-simulation {i} = [ β i , sup β ]⟨ sup-is-upper-bound β i ⟩-is-simulation

   ι-is-order-preserving : {i : I} → is-order-preserving (β i) (sup β) ι
   ι-is-order-preserving {i} =
    simulations-are-order-preserving (β i) (sup β) ι ι-is-simulation

   ι-is-order-reflecting : {i : I} → is-order-reflecting (β i) (sup β) ι
   ι-is-order-reflecting {i} =
    simulations-are-order-reflecting (β i) (sup β) ι ι-is-simulation

   ι-is-lc : {i : I} → left-cancellable ι
   ι-is-lc {i} = simulations-are-lc (β i) (sup β) ι ι-is-simulation

   ι-is-initial-segment : {i : I} → is-initial-segment (β i) (sup β ) ι
   ι-is-initial-segment {i} =
    simulations-are-initial-segments (β i) (sup β) ι ι-is-simulation

   ι-is-surjection : (s : ⟨ sup β ⟩) → ∃ i ꞉ I , Σ x ꞉ ⟨ β i ⟩ , ι x ＝ s
   ι-is-surjection = sup-is-upper-bound-jointly-surjective β

   ι-is-surjection' : (s : ⟨ sup β ⟩) {i : I} (x : ⟨ β i ⟩)
                    → s ≺⟨ sup β ⟩ ι x
                    → Σ y ꞉ ⟨ β i ⟩ , ι y ＝ s
   ι-is-surjection' s {i} x p =
    h (ι-is-initial-segment x s p)
    where
     h : Σ y ꞉ ⟨ β i ⟩ , y ≺⟨ β i ⟩ x × (ι y ＝ s)
       → Σ y ꞉ ⟨ β i ⟩ , ι y ＝ s
     h (y , (_ , q)) = y , q

\end{code}

For each i : I, we construct an order preserving and reflecting map
  to-expᴸ-sup : expᴸ[𝟙+ α ] (β i) → expᴸ[𝟙+ α ] (sup β)
that is surjective and hence we get an equality of ordinals.

\begin{code}

  to-expᴸ-sup : {i : I} → ⟨ expᴸ[𝟙+ α ] (β i) ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
  to-expᴸ-sup {i} = expᴸ-map α (β i) (sup β) ι ι-is-order-preserving

  to-expᴸ-sup-list : {i : I} → ⟨ expᴸ[𝟙+ α ] (β i) ⟩ → List ⟨ α ×ₒ (sup β) ⟩
  to-expᴸ-sup-list = DecrList₂-list α (sup β) ∘ to-expᴸ-sup

  to-expᴸ-sup-is-order-preserving
   : {i : I}
   → is-order-preserving (expᴸ[𝟙+ α ] (β i)) (expᴸ[𝟙+ α ] (sup β)) to-expᴸ-sup
  to-expᴸ-sup-is-order-preserving {i} =
   expᴸ-map-is-order-preserving α (β i) (sup β) ι ι-is-order-preserving

  to-expᴸ-sup-is-order-reflecting
   : {i : I}
   → is-order-reflecting (expᴸ[𝟙+ α ] (β i)) (expᴸ[𝟙+ α ] (sup β)) to-expᴸ-sup
  to-expᴸ-sup-is-order-reflecting {i} =
   expᴸ-map-is-order-reflecting α (β i) (sup β) ι
    ι-is-order-preserving
    ι-is-order-reflecting
    ι-is-lc

  to-expᴸ-sup-is-simulation
   : {i : I}
   → is-simulation (expᴸ[𝟙+ α ] (β i)) (expᴸ[𝟙+ α ] (sup β)) to-expᴸ-sup
  to-expᴸ-sup-is-simulation {i} =
   expᴸ-map-is-simulation α (β i) (sup β) ι
    ι-is-order-preserving ι-is-initial-segment

  expᴸ-sup-is-upper-bound : (i : I) → expᴸ[𝟙+ α ] (β i) ⊴ expᴸ[𝟙+ α ] (sup β)
  expᴸ-sup-is-upper-bound i =
   to-expᴸ-sup , to-expᴸ-sup-is-simulation

  expᴸ-sup-⊴ : sup (expᴸ[𝟙+ α ] ∘ β) ⊴ expᴸ[𝟙+ α ] (sup β)
  expᴸ-sup-⊴ =
   sup-is-lower-bound-of-upper-bounds
    (λ i → (expᴸ[𝟙+ α ] (β i)))
    (expᴸ[𝟙+ α ] (sup β))
    expᴸ-sup-is-upper-bound

  expᴸ-sup-map : ⟨ sup (expᴸ[𝟙+ α ] ∘ β) ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
  expᴸ-sup-map = [ sup (expᴸ[𝟙+ α ] ∘ β) , expᴸ[𝟙+ α ] (sup β) ]⟨ expᴸ-sup-⊴ ⟩

  expᴸ-sup-surjectivity-lemma
   : (a : ⟨ α ⟩) {i : I} (b : ⟨ β i ⟩)
     (l : List (⟨ α ×ₒ sup β ⟩))
   → is-decreasing-pr₂ α (sup β) ((a , ι b) ∷ l)
   → Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) ,
      Σ δ ꞉ is-decreasing-pr₂ α (β i) ((a , b) ∷ l') ,
       (a , ι b ∷ l) ＝ to-expᴸ-sup-list (((a , b) ∷ l') , δ)
  expᴸ-sup-surjectivity-lemma a b [] δ = [] , sing-decr , refl
  expᴸ-sup-surjectivity-lemma a {i} b ((a' , s) ∷ l) δ =
   ((a' , b') ∷ l') ,
   many-decr ⦅4⦆ δ' ,
   ap (a , ι b ∷_) (ap (λ - → a' , - ∷ l) (⦅2⦆ ⁻¹) ∙ ⦅5⦆)
    where
     ⦅1⦆ : s ≺⟨ sup β ⟩ ι b
     ⦅1⦆ = heads-are-decreasing (underlying-order (sup β)) δ

     b' : ⟨ β i ⟩
     b' = pr₁ (ι-is-surjection' s b ⦅1⦆)
     ⦅2⦆ : ι b' ＝ s
     ⦅2⦆ = pr₂ (ι-is-surjection' s b ⦅1⦆)

     ⦅3⦆ : ι b' ≺⟨ sup β ⟩ ι b
     ⦅3⦆ = transport⁻¹ (λ - → underlying-order (sup β) - (ι b)) ⦅2⦆ ⦅1⦆

     ⦅4⦆ : b' ≺⟨ β i ⟩ b
     ⦅4⦆ = ι-is-order-reflecting b' b ⦅3⦆

     IH : Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) ,
           Σ δ' ꞉ is-decreasing-pr₂ α (β i) ((a' , b') ∷ l') ,
            (a' , ι b' ∷ l) ＝ to-expᴸ-sup-list (((a' , b') ∷ l') , δ')
     IH = expᴸ-sup-surjectivity-lemma a' b' l
           (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) (a' , - ∷ l)) ⦅2⦆
             (tail-is-decreasing (underlying-order (sup β)) δ))
     l' : List (⟨ α ×ₒ β i ⟩)
     l' = pr₁ IH
     δ' : is-decreasing-pr₂ α (β i) (a' , b' ∷ l')
     δ' = pr₁ (pr₂ IH)

     ⦅5⦆ : (a' , ι b' ∷ l) ＝ to-expᴸ-sup-list (((a' , b') ∷ l') , δ')
     ⦅5⦆ = pr₂ (pr₂ IH)

  expᴸ-sup-map-is-surjection
   : ∥ I ∥ → is-surjection expᴸ-sup-map
  expᴸ-sup-map-is-surjection I-inh =
   induced-simulation-from-sup-is-surjection
    (expᴸ[𝟙+ α ] ∘ β)
    (expᴸ[𝟙+ α ] (sup β))
    expᴸ-sup-is-upper-bound
    σ
     where
      σ : (y : ⟨ expᴸ[𝟙+ α ] (sup β) ⟩)
        → ∃ i ꞉ I , Σ b ꞉ ⟨ expᴸ[𝟙+ α ] (β i) ⟩ , to-expᴸ-sup b ＝ y
      σ ([] , []-decr) = ∥∥-functor (λ i → i , ([] , []-decr) , refl) I-inh
      σ (((a , s) ∷ l) , δ) = ∥∥-rec ∃-is-prop h (ι-is-surjection s)
       where
        h : Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , ι b ＝ s
          → ∃ i ꞉ I , Σ b ꞉ ⟨ expᴸ[𝟙+ α ] (β i) ⟩ ,
             to-expᴸ-sup b ＝ (((a , s) ∷ l) , δ)
        h (i , b , refl) =
         ∣ i , (((a , b) ∷ l') , δ') , to-DecrList₂-＝ α (sup β) (e ⁻¹) ∣
         where
          lemma : Σ l' ꞉ List ⟨ α ×ₒ β i ⟩ ,
                   Σ δ' ꞉ is-decreasing-pr₂ α (β i) ((a , b) ∷ l') ,
                    ((a , ι b) ∷ l ＝ to-expᴸ-sup-list ((a , b ∷ l') , δ'))
          lemma = expᴸ-sup-surjectivity-lemma a b l δ
          l' = pr₁ lemma
          δ' = pr₁ (pr₂ lemma)
          e  = pr₂ (pr₂ lemma)

  expᴸ-sup-＝
   : ∥ I ∥ → sup (expᴸ[𝟙+ α ] ∘ β) ＝ expᴸ[𝟙+ α ] (sup β)
  expᴸ-sup-＝ I-inh =
   surjective-simulation-gives-＝ pt fe' (ua 𝓤)
    (sup (expᴸ[𝟙+ α ] ∘ β))
    (expᴸ[𝟙+ α ] (sup β))
    expᴸ-sup-map
    [ sup (expᴸ[𝟙+ α ] ∘ β) , expᴸ[𝟙+ α ] (sup β) ]⟨ expᴸ-sup-⊴ ⟩-is-simulation
    (expᴸ-sup-map-is-surjection I-inh)

\end{code}

Finally, we obtain the desired result.

\begin{code}

expᴸ-satisfies-sup-specification :
 (α : Ordinal 𝓤) → exp-specification-sup (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ])
expᴸ-satisfies-sup-specification α α-nonzero I-inh β = (expᴸ-sup-＝ β α I-inh) ⁻¹

\end{code}

Added 29 January 2025 by Tom de Jong.

We now show that expᴸ also satisfies the stronger sup specification, i.e. that
  expᴸ[𝟙+ α ] (sup β) ＝ 𝟙ₒ ∨ expᴸ[𝟙+ α ] (sup β)
for all families β : I → Ordinal 𝓤 (regardless of whether I is inhabited).

The proof strategy is captured by the following diagram where f, g and h are all
simulations so that the diagram necessarily commutes.
Moreover, h = expᴸ-sup-map α β which is a surjection as soon as I is inhabited.
To see that g is a surjection, we note that the empty list is taken care of by
the left component (𝟙ₒ) of γ and that for a nonempty list (a , y) ∷ l with
y : sup β there exists i : I and x : β i such that y ＝ [i , x], so that in
particular, I is inhabited. Hence, in this case h is surjective giving us an
element s in the domain f with g (f s) ＝ h s ＝ (a , y) ∷ l.

                                  f
  sup (λ i → expᴸ[𝟙+ α ] (β i)) ----> 𝟙ₒ ∨ sup (λ i → expᴸ[𝟙+ α ] (β i)) = sup γ
                        \                           |
                         \                          |
                       h  \                         | g
                           \                        |
                            \                       v
                             ------------> expᴸ[𝟙+ α ] (sup β)

\begin{code}

module _ {I : 𝓤 ̇  }
         (β : I → Ordinal 𝓤)
         (α : Ordinal 𝓤)
 where

  private
   γ : 𝟙{𝓤} + I → Ordinal 𝓤
   γ = cases (λ _ → 𝟙ₒ) (λ i → expᴸ[𝟙+ α ] (β i))

   γ-incl : (x : 𝟙 + I) → ⟨ γ x ⟩ → ⟨ sup γ ⟩
   γ-incl x = [ γ x , sup γ ]⟨ sup-is-upper-bound γ x ⟩

   β-incl : (i : I) → ⟨ β i ⟩ → ⟨ sup β ⟩
   β-incl i = [ β i , sup β ]⟨ sup-is-upper-bound β i ⟩

   g-⊴ : sup γ ⊴ expᴸ[𝟙+ α ] (sup β)
   g-⊴ = sup-is-lower-bound-of-upper-bounds γ (expᴸ[𝟙+ α ] (sup β)) ub
    where
     ub : (x : 𝟙 + I) → γ x ⊴ expᴸ[𝟙+ α ] (sup β)
     ub (inl ⋆) = expᴸ-has-least α (sup β)
     ub (inr i) = expᴸ-sup-is-upper-bound β α i

   g : ⟨ sup γ ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
   g = [ sup γ , expᴸ[𝟙+ α ] (sup β) ]⟨ g-⊴ ⟩

   f-⊴ : sup (expᴸ[𝟙+ α ] ∘ β) ⊴ sup γ
   f-⊴ = sup-is-lower-bound-of-upper-bounds (expᴸ[𝟙+ α ] ∘ β) (sup γ) ub
    where
     ub : (i : I) → expᴸ[𝟙+ α ] (β i) ⊴ sup γ
     ub i = sup-is-upper-bound γ (inr i)

   f : ⟨ sup (expᴸ[𝟙+ α ] ∘ β) ⟩ → ⟨ sup γ ⟩
   f = [ sup (expᴸ[𝟙+ α ] ∘ β) , sup γ ]⟨ f-⊴ ⟩

   h-⊴ : sup (expᴸ[𝟙+ α ] ∘ β) ⊴ expᴸ[𝟙+ α ] (sup β)
   h-⊴ = expᴸ-sup-⊴ β α

   h : ⟨ sup (expᴸ[𝟙+ α ] ∘ β) ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
   h = expᴸ-sup-map β α

   g-after-f-is-h : g ∘ f ∼ h
   g-after-f-is-h =
    at-most-one-simulation
     (sup (expᴸ[𝟙+ α ] ∘ β))
     (expᴸ[𝟙+ α ] (sup β))
     (g ∘ f)
     h
     [ sup (expᴸ[𝟙+ α ] ∘ β) , expᴸ[𝟙+ α ] (sup β) ]⟨ σ ⟩-is-simulation
     [ sup (expᴸ[𝟙+ α ] ∘ β) , expᴸ[𝟙+ α ] (sup β) ]⟨ h-⊴ ⟩-is-simulation
      where
       σ : sup (expᴸ[𝟙+ α ] ∘ β) ⊴ expᴸ[𝟙+ α ] (sup β)
       σ = ⊴-trans (sup (expᴸ[𝟙+ α ] ∘ β)) (sup γ) (expᴸ[𝟙+ α ] (sup β)) f-⊴ g-⊴

   g-is-surjection : is-surjection g
   g-is-surjection ([] , []-decr) = ∣ x , e₂ ∣
    where
     x : ⟨ sup γ ⟩
     x = γ-incl (inl ⋆) ⋆
     e₁ = expᴸ[𝟙+ α ] (sup β) ↓ ([] , []-decr) ＝⟨ expᴸ-↓-⊥ α (sup β) ⟩
          𝟘ₒ                                   ＝⟨ 𝟙ₒ-↓ ⁻¹ ⟩
          𝟙ₒ ↓ ⋆                               ＝⟨ eq₁ ⟩
          sup γ ↓ γ-incl (inl ⋆) ⋆             ＝⟨ eq₂ ⟩
          expᴸ[𝟙+ α ] (sup β) ↓ g x            ∎
      where
       eq₁ = (initial-segment-of-sup-at-component γ (inl ⋆) ⋆) ⁻¹
       eq₂ = simulations-preserve-↓ (sup γ) (expᴸ[𝟙+ α ] (sup β)) g-⊴ x
     e₂ : g x ＝ ([] , []-decr)
     e₂ = ↓-lc (expᴸ[𝟙+ α ] (sup β)) (g x) ([] , []-decr) (e₁ ⁻¹)
   g-is-surjection (((a , y) ∷ l) , δ) =
    ∥∥-rec
     (being-in-the-image-is-prop ((a , y ∷ l) , δ) g)
     σ
     (sup-is-upper-bound-jointly-surjective β y)
      where
       σ : (Σ i ꞉ I , Σ x ꞉ ⟨ β i ⟩ , β-incl i x ＝ y)
         → ((a , y ∷ l) , δ) ∈image g
       σ (i , x , refl) =
        ∥∥-functor τ
         (expᴸ-sup-map-is-surjection β α ∣ i ∣ (((a , β-incl i x) ∷ l) , δ))
        where
         τ : (Σ s ꞉ ⟨ sup (expᴸ[𝟙+ α ] ∘ β) ⟩ ,
               h s ＝ (((a , β-incl i x) ∷ l) , δ))
           → Σ t ꞉ ⟨ sup γ ⟩ , g t ＝ (((a , β-incl i x) ∷ l) , δ)
         τ (s , p) = f s , (g-after-f-is-h s ∙ p)

  expᴸ-sup⁺-＝
   : expᴸ[𝟙+ α ] (sup β)
     ＝ sup (cases (λ _ → 𝟙ₒ) (expᴸ[𝟙+ α ] ∘ β))
  expᴸ-sup⁺-＝ =
   (surjective-simulation-gives-＝ pt fe' (ua 𝓤)
     (sup γ)
     (expᴸ[𝟙+ α ] (sup β))
     g
     [ sup γ , expᴸ[𝟙+ α ] (sup β) ]⟨ g-⊴ ⟩-is-simulation
     g-is-surjection) ⁻¹

expᴸ-satisfies-strong-sup-specification :
 (α : Ordinal 𝓤) → exp-specification-sup-strong (𝟙ₒ +ₒ α) (expᴸ[𝟙+ α ])
expᴸ-satisfies-strong-sup-specification α I β = expᴸ-sup⁺-＝ β α

\end{code}
