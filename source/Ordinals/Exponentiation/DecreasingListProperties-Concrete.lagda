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
                        → exp-specification-zero {𝓤} {𝓥} α (expᴸ[𝟙+ α ])
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
  forward-left-list : List ⟨ α ×ₒ (β +ₒ γ) ⟩ → List ⟨ α ×ₒ β ⟩
  forward-left-list [] = []
  forward-left-list ((a , inl b) ∷ l) = (a , b) ∷ forward-left-list l
  forward-left-list ((a , inr c) ∷ l) = forward-left-list l

  forward-left-list-preserves-decreasing-pr₂
   : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
   → is-decreasing-pr₂ α (β +ₒ γ) l
   → is-decreasing-pr₂ α β (forward-left-list l)
  forward-left-list-preserves-decreasing-pr₂ [] δ = []-decr
  forward-left-list-preserves-decreasing-pr₂ ((a , inr c) ∷ l) δ =
   forward-left-list-preserves-decreasing-pr₂ l
    (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inr c) δ)
  forward-left-list-preserves-decreasing-pr₂ ((a , inl b) ∷ []) δ = sing-decr
  forward-left-list-preserves-decreasing-pr₂
   ((a , inl b) ∷ (a' , inl b') ∷ l) (many-decr p δ) =
    many-decr p
     (forward-left-list-preserves-decreasing-pr₂ ((a' , inl b') ∷ l) δ)
  forward-left-list-preserves-decreasing-pr₂
   ((a , inl b) ∷ (a' , inr c) ∷ l) (many-decr p δ) = 𝟘-elim p

  forward-left : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] β ⟩
  forward-left (l , δ) = forward-left-list l ,
                         forward-left-list-preserves-decreasing-pr₂ l δ

  forward-right-list : List ⟨ α ×ₒ (β +ₒ γ) ⟩ → List ⟨ α ×ₒ γ ⟩
  forward-right-list [] = []
  forward-right-list ((a , inl b) ∷ l) = forward-right-list l
  forward-right-list ((a , inr c) ∷ l) = (a , c) ∷ forward-right-list l

\end{code}

Proving that forward-right-lits preserves the decreasing-pr₂ property requires
the following lemma:

TODO: CONTINUE HERE

\begin{code}

--   no-swapping-lemma : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
--                       (a : ⟨ α ⟩) → (b : ⟨ β ⟩)
--                       (δ : is-decreasing-pr₂ α (β +ₒ γ) ((a , inl b) ∷ l))
--                     → forward-right-lits ((a , inl b) ∷ l) ＝ []
--   no-swapping-lemma [] a b δ = refl
--   no-swapping-lemma ((a' , inl b') ∷ xs) a b (many-decr p δ) = no-swapping-lemma xs a b' δ
--   no-swapping-lemma ((a' , inr c) ∷ xs) a b (many-decr p δ) = 𝟘-elim p


--   forward-right-list-preserves-decreasing-pr₂
--    : (l : List ⟨ α ×ₒ (β +ₒ γ) ⟩)
--    → is-decreasing-pr₂ α (β +ₒ γ) l
--    → is-decreasing-pr₂ α γ (forward-right-list l)
--   forward-right-list-preserves-decreasing-pr₂ [] δ = []-decr
--   forward-right-list-preserves-decreasing-pr₂ ((a , inl b) ∷ l) δ =
--    forward-right-list-preserves-decreasing-pr₂ l
--     (tail-is-decreasing-pr₂ α (β +ₒ γ) (a , inl b) δ)
--   forward-right-list-preserves-decreasing-pr₂ ((a , inr c) ∷ []) δ = sing-decr
--   forward-right-list-preserves-decreasing-pr₂
--    ((a , inr c) ∷ (a' , inr c') ∷ l) (many-decr p δ) =
--     many-decr p
--      (forward-right-list-preserves-decreasing-pr₂ ((a' , inr c') ∷ l) δ)
--   forward-right-list-preserves-decreasing-pr₂
--    ((a , inr c) ∷ (a' , inl b) ∷ l) (many-decr p δ) =
--     forward-right-list-preserves-decreasing-pr₂ {!!} {!δ!}

--   forward-right : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] γ ⟩
--   forward-right (l , δ) = forward-right-list l ,
--                           forward-right-list-preserves-decreasing-pr₂ l δ

-- -- exp-+-distributes' : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
-- --                    → (expᴸ[𝟙+ α ] (β +ₒ γ)) ≃ₒ ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ))
-- -- exp-+-distributes' α β γ = f , f-order-preserving , qinvs-are-equivs f f-qinv , g-order-preserving
-- --  where

-- --   f₀₀ : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → List ⟨ α ×ₒ β ⟩
-- --   f₀₀ [] = []
-- --   f₀₀ ((a , inl b) ∷ xs) = (a , b) ∷ f₀₀ xs
-- --   f₀₀ ((a , inr c) ∷ xs) = f₀₀ xs

-- --   f₁₀ : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → List ⟨ α ×ₒ γ ⟩
-- --   f₁₀ [] = []
-- --   f₁₀ ((a , inl b) ∷ xs) = f₁₀ xs
-- --   f₁₀ ((a , inr c) ∷ xs) = (a , c) ∷ f₁₀ xs

-- --   f₀₁ : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → (δ : is-decreasing-pr₂ α (β +ₒ γ) xs) → is-decreasing-pr₂ α β (f₀₀ xs)
-- --   f₀₁ [] δ = []-decr
-- --   f₀₁ ((a , inl b) ∷ []) δ = sing-decr
-- --   f₀₁ ((a , inl b) ∷ (a' , inl b') ∷ xs) (many-decr p δ) = many-decr p (f₀₁ ((a' , inl b') ∷ xs) δ)
-- --   f₀₁ ((a , inl b) ∷ (a' , inr c) ∷ xs) (many-decr p δ) = 𝟘-elim p
-- --   f₀₁ ((a , inr c) ∷ []) δ = []-decr
-- --   f₀₁ ((a , inr c) ∷ (a' , inl b') ∷ xs) (many-decr ⋆ δ) = f₀₁ ((a' , inl b') ∷ xs) δ
-- --   f₀₁ ((a , inr c) ∷ (a' , inr c') ∷ xs) (many-decr p δ) = f₀₁ xs (tail-is-decreasing (underlying-order (β +ₒ γ)) δ)

-- --   no-swapping-lemma : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → (a : ⟨ α ⟩) → (b : ⟨ β ⟩)
-- --                     → (δ : is-decreasing-pr₂ α (β +ₒ γ) ((a , inl b) ∷ xs))
-- --                     → f₁₀ ((a , inl b) ∷ xs) ＝ []
-- --   no-swapping-lemma [] a b δ = refl
-- --   no-swapping-lemma ((a' , inl b') ∷ xs) a b (many-decr p δ) = no-swapping-lemma xs a b' δ
-- --   no-swapping-lemma ((a' , inr c) ∷ xs) a b (many-decr p δ) = 𝟘-elim p

-- --   f₁₁ : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → (δ : is-decreasing-pr₂ α (β +ₒ γ) xs) → is-decreasing-pr₂ α γ (f₁₀ xs)
-- --   f₁₁ [] δ = []-decr
-- --   f₁₁ ((a , inl b) ∷ []) δ = []-decr
-- --   f₁₁ ((a , inl b) ∷ (a' , inl b') ∷ xs) (many-decr p δ) = f₁₁ xs (tail-is-decreasing (underlying-order (β +ₒ γ)) δ)
-- --   f₁₁ ((a , inl b) ∷ (a' , inr c) ∷ xs) (many-decr p δ) = 𝟘-elim p
-- --   f₁₁ ((a , inr c) ∷ []) δ = sing-decr
-- --   f₁₁ ((a , inr c) ∷ (a' , inl b) ∷ xs) (many-decr ⋆ δ) =
-- --    transport⁻¹ (λ z → is-decreasing-pr₂ α γ ((a , c) ∷ z)) (no-swapping-lemma xs a b δ) sing-decr
-- --   f₁₁ ((a , inr c) ∷ (a' , inr c') ∷ xs) (many-decr p δ) = many-decr p (f₁₁ ((a' , inr c') ∷ xs) δ)

-- --   f₀ : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] β ⟩
-- --   f₀ (xs , δ) = (f₀₀ xs) , (f₀₁ xs δ)

-- --   f₁ : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ expᴸ[𝟙+ α ] γ ⟩
-- --   f₁ (xs , δ) = (f₁₀ xs) , (f₁₁ xs δ)

-- --   f : ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩ → ⟨ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ) ⟩
-- --   f (xs , δ) = (f₀ (xs , δ) , f₁ (xs , δ))


-- --   f-order-preserving : is-order-preserving (expᴸ[𝟙+ α ] (β +ₒ γ)) ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) f
-- --   f-order-preserving ([] , δ) (((a , inl b) ∷ ys) , ε) []-lex = inr (to-expᴸ-＝ α γ (no-swapping-lemma ys a b ε ⁻¹) , []-lex)
-- --   f-order-preserving ([] , δ) (((a , inr c) ∷ ys) , ε) []-lex = inl []-lex
-- --   f-order-preserving (((a , inl b) ∷ xs) , δ) (((a' , inl b') ∷ ys) , ε) (head-lex (inl p)) =
-- --    inr (to-expᴸ-＝ α γ (no-swapping-lemma xs a b δ ∙ no-swapping-lemma ys a' b' ε ⁻¹) , head-lex (inl p))
-- --   f-order-preserving (((a , inl b) ∷ xs) , δ) (((a' , inl b') ∷ ys) , ε) (head-lex (inr (refl , p))) =
-- --    inr (to-expᴸ-＝ α γ (no-swapping-lemma xs a b δ ∙ no-swapping-lemma ys a' b ε ⁻¹) , (head-lex (inr (refl , p))))
-- --   f-order-preserving (((a , inl b) ∷ xs) , δ) (((a , inl b) ∷ ys) , ε) (tail-lex refl ps) =
-- --     h (f-order-preserving (xs , tail-is-decreasing (underlying-order (β +ₒ γ)) δ) (ys , tail-is-decreasing (underlying-order (β +ₒ γ)) ε) ps)
-- --    where
-- --     h : underlying-order ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (f (xs , tail-is-decreasing _ δ)) (f (ys , tail-is-decreasing _ ε))
-- --       → underlying-order ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (f (((a , inl b) ∷ xs) , δ)) (f (((a , inl b) ∷ ys) , ε))
-- --     h (inl p) = 𝟘-elim (irrefl (expᴸ[𝟙+ α ] γ)
-- --                                ([] , []-decr)
-- --                                (transport₂ (expᴸ-order α γ)
-- --                                            {x = f₁₀ xs , f₁₁ xs (tail-is-decreasing (underlying-order (β +ₒ γ)) δ)}
-- --                                            {x' = [] , []-decr}
-- --                                            {y = f₁₀ ys , f₁₁ ys (tail-is-decreasing (underlying-order (β +ₒ γ)) ε)}
-- --                                            {y' = [] , []-decr}
-- --                                            (to-expᴸ-＝ α γ (no-swapping-lemma xs a b δ))
-- --                                            (to-expᴸ-＝ α γ (no-swapping-lemma ys a b ε)) p))
-- --     h (inr (r , p)) = inr ((to-expᴸ-＝ α γ (ap pr₁ r)) , tail-lex refl p)
-- --   f-order-preserving (((a , inr c) ∷ xs) , δ) (((a' , inr c') ∷ ys) , ε) (head-lex (inl p)) = inl (head-lex (inl p))
-- --   f-order-preserving (((a , inr c) ∷ xs) , δ) (((a' , inr c) ∷ ys) , ε) (head-lex (inr (refl , p))) = inl (head-lex (inr (refl , p)))
-- --   f-order-preserving (((a , inr c) ∷ xs) , δ) (((a , inr c) ∷ ys) , ε) (tail-lex refl ps) =
-- --    h (f-order-preserving (xs , tail-is-decreasing (underlying-order (β +ₒ γ)) δ) (ys , tail-is-decreasing (underlying-order (β +ₒ γ)) ε) ps)
-- --    where
-- --     h : underlying-order ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (f (xs , tail-is-decreasing _ δ)) (f (ys , tail-is-decreasing _ ε))
-- --       → underlying-order ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (f (((a , inr c) ∷ xs) , δ)) (f (((a , inr c) ∷ ys) , ε))
-- --     h (inl p) = inl (tail-lex refl p)
-- --     h (inr (r , p)) = inr (to-expᴸ-＝ α γ (ap ((a , c) ∷_) (ap pr₁ r)) , p)
-- --   f-order-preserving (((a , inl b) ∷ xs) , δ) (((a' , inr c') ∷ ys) , ε) (head-lex (inl ⋆)) =
-- --    inl (transport⁻¹ (λ z → lex (underlying-order (α ×ₒ γ)) z ((a' , c') ∷ _)) (no-swapping-lemma xs a b δ) []-lex)
-- --   f-order-preserving (((a , inl b) ∷ xs) , δ) (((a' , inr c') ∷ ys) , ε) (tail-lex p ps) = 𝟘-elim (+disjoint (ap pr₂ p))
-- --   f-order-preserving (((a , inr c) ∷ xs) , δ) (((a' , inl b') ∷ ys) , ε) (head-lex (inr (r , p))) = 𝟘-elim (+disjoint (r ⁻¹))
-- --   f-order-preserving (((a , inr c) ∷ xs) , δ) (((a' , inl b') ∷ ys) , ε) (tail-lex p ps) = 𝟘-elim (+disjoint (ap pr₂ p ⁻¹))

-- --   g₀ : (bs : List ⟨ α ×ₒ β ⟩) → (cs : List ⟨ α ×ₒ γ ⟩) → List ⟨ α ×ₒ (β +ₒ γ) ⟩
-- --   g₀ bs ((a , c) ∷ cs) = (a , inr c) ∷ g₀ bs cs
-- --   g₀ ((a , b) ∷ bs) [] = (a , inl b) ∷ g₀ bs []
-- --   g₀ [] [] = []

-- --   g₁ : (bs : List ⟨ α ×ₒ β ⟩) → is-decreasing-pr₂ α β bs
-- --      → (cs : List ⟨ α ×ₒ γ ⟩) → is-decreasing-pr₂ α γ cs
-- --      → is-decreasing-pr₂ α (β +ₒ γ) (g₀ bs cs)
-- --   g₁ [] δ (a , c ∷ []) ε = sing-decr
-- --   g₁ ((a , b) ∷ bs) δ ((a' , c) ∷ []) ε = many-decr ⋆ (g₁ ((a , b) ∷ bs) δ [] []-decr)
-- --   g₁ bs δ ((a , c) ∷ (a' , c') ∷ cs) ε =
-- --    many-decr (heads-are-decreasing (underlying-order γ) ε)
-- --              (g₁ bs δ ((a' , c') ∷ cs) (tail-is-decreasing (underlying-order γ) ε))
-- --   g₁ [] δ [] ε = []-decr
-- --   g₁ (x ∷ []) δ [] ε = sing-decr
-- --   g₁ ((a , b) ∷ (a' , b') ∷ bs) δ [] ε =
-- --    many-decr (heads-are-decreasing (underlying-order β) δ)
-- --              (g₁ ((a' , b') ∷ bs) (tail-is-decreasing (underlying-order β) δ) [] ε)

-- --   g : ⟨ (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ) ⟩ → ⟨ expᴸ[𝟙+ α ] (β +ₒ γ) ⟩
-- --   g ((bs , δ) , (cs , ε)) = g₀ bs cs , g₁ bs δ cs ε

-- --   g₀-order-preserving : (bs : List ⟨ α ×ₒ β ⟩) → (δ : is-decreasing-pr₂ α β bs)
-- --               → (cs : List ⟨ α ×ₒ γ ⟩) → (ε : is-decreasing-pr₂ α γ cs)
-- --               → (bs' : List ⟨ α ×ₒ β ⟩) → (δ' : is-decreasing-pr₂ α β bs')
-- --               → (cs' : List ⟨ α ×ₒ γ ⟩) → (ε' : is-decreasing-pr₂ α γ cs')
-- --               → lex (underlying-order (α ×ₒ γ)) cs cs' + (((cs , ε) ＝ (cs' , ε')) × lex (underlying-order (α ×ₒ β)) bs bs')
-- --               → g₀ bs cs ≺⟨List (α ×ₒ (β +ₒ γ)) ⟩ g₀ bs' cs'
-- --   g₀-order-preserving [] δ [] ε [] δ' [] ε' (inl p) = 𝟘-elim (irrefl (expᴸ[𝟙+ α ] γ) ([] , []-decr) p)
-- --   g₀-order-preserving [] δ [] ε [] δ' [] ε' (inr (r , p)) = 𝟘-elim (irrefl (expᴸ[𝟙+ α ] β) ([] , []-decr) p)
-- --   g₀-order-preserving [] δ [] ε ((a' , b') ∷ bs') δ' [] ε' p = []-lex
-- --   g₀-order-preserving [] δ [] ε bs' δ' ((a' , c') ∷ cs') ε' p = []-lex
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε [] δ' [] ε' (inr (r , p)) = 𝟘-elim (irrefl (expᴸ[𝟙+ α ] β) ([] , []-decr) p)
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε (a' , b' ∷ bs') δ' [] ε' (inr (r , p)) = 𝟘-elim ([]-is-not-cons (a , c) cs (ap pr₁ r ⁻¹ ))
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε bs' δ' (a' , c' ∷ cs') ε' (inl (head-lex (inl p))) = head-lex (inl p)
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε bs' δ' (a' , c' ∷ cs') ε' (inl (head-lex (inr (r , p)))) = head-lex (inr ((ap inr r) , p))
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε bs' δ' (a , c ∷ cs') ε' (inl (tail-lex refl ps)) =
-- --    tail-lex refl (g₀-order-preserving [] δ cs (tail-is-decreasing (underlying-order γ) ε) bs' δ' cs' (tail-is-decreasing (underlying-order γ) ε') (inl ps))
-- --   g₀-order-preserving [] δ (a , c ∷ cs) ε bs' δ' (a , c ∷ cs) ε (inr (refl , p)) =
-- --    tail-lex refl (g₀-order-preserving [] δ cs (tail-is-decreasing (underlying-order γ) ε) bs' δ' cs (tail-is-decreasing (underlying-order γ) ε) (inr (refl , p)))
-- --   g₀-order-preserving (a , b ∷ bs) δ [] ε [] δ' [] ε' (inl p) = 𝟘-elim (irrefl (expᴸ[𝟙+ α ]  γ) ([] , []-decr) p)
-- --   g₀-order-preserving (a , b ∷ bs) δ [] ε (a' , b' ∷ bs') δ' [] ε' (inr (_ , head-lex (inl p))) = head-lex (inl p)
-- --   g₀-order-preserving (a , b ∷ bs) δ [] ε (a' , b ∷ bs') δ' [] ε' (inr (_ , head-lex (inr (refl , p)))) = head-lex (inr (refl , p))
-- --   g₀-order-preserving (a , b ∷ bs) δ [] ε (a , b ∷ bs') δ' [] ε' (inr (_ , tail-lex refl ps)) =
-- --    tail-lex refl (g₀-order-preserving bs (tail-is-decreasing (underlying-order β) δ) [] []-decr bs' (tail-is-decreasing (underlying-order β) δ') [] []-decr (inr (refl , ps)) )
-- --   g₀-order-preserving (a , b ∷ bs) δ [] ε bs' δ' ((a' , c') ∷ cs') ε' p = head-lex (inl ⋆)
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε [] δ' [] ε' (inl p) = 𝟘-elim ([]-lex-bot (underlying-order  (α ×ₒ γ)) ((a' , c) ∷ cs) p)
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε ((a'' , b') ∷ bs') δ' [] ε' (inl p) = 𝟘-elim ([]-lex-bot (underlying-order  (α ×ₒ γ)) ((a' , c) ∷ cs) p)
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε bs' δ' (a'' , c' ∷ cs') ε' (inl (head-lex (inl p))) = head-lex (inl p)
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε bs' δ' (a'' , c' ∷ cs') ε' (inl (head-lex (inr (r , p)))) = head-lex (inr ((ap inr r) , p))
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε bs' δ' (a' , c ∷ cs') ε' (inl (tail-lex refl ps)) =
-- --    tail-lex refl (g₀-order-preserving ((a , b) ∷ bs) δ cs (tail-is-decreasing (underlying-order γ) ε) bs' δ' cs' (tail-is-decreasing (underlying-order γ) ε') (inl ps))
-- --   g₀-order-preserving (a , b ∷ bs) δ (a' , c ∷ cs) ε bs' δ' (a' , c ∷ cs) ε (inr (refl , p)) =
-- --    tail-lex refl (g₀-order-preserving ((a , b) ∷ bs) δ cs (tail-is-decreasing (underlying-order γ) ε) bs' δ' cs (tail-is-decreasing (underlying-order γ) ε) (inr (refl , p)))

-- --   g-order-preserving : is-order-preserving ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (expᴸ[𝟙+ α ] (β +ₒ γ)) g
-- --   g-order-preserving ((bs , δ) , (cs , ε)) ((bs' , δ') , (cs' , ε')) p = g₀-order-preserving bs δ cs ε bs' δ' cs' ε' p

-- --   f-qinv : qinv f
-- --   f-qinv = g , p , q
-- --    where
-- --     p₀ : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → is-decreasing-pr₂ α (β +ₒ γ) xs → g₀ (f₀₀ xs) (f₁₀ xs) ＝ xs
-- --     p₀ [] δ = refl
-- --     p₀ (a , inl b ∷ []) δ = refl
-- --     p₀ (a , inl b ∷ xs) δ =
-- --      transport⁻¹ (λ z → g₀ ((a , b) ∷ f₀₀ xs) z ＝ (a , inl b) ∷ xs) (no-swapping-lemma xs a b δ) (ap ((a , inl b) ∷_) (p₀-[] xs (no-inr (map pr₂ xs) b δ)))
-- --      where
-- --       p₀-[] : (xs : List ⟨ α ×ₒ (β +ₒ γ) ⟩) → ((c : ⟨ γ ⟩) → ¬ member (inr c) (map pr₂ xs) ) → g₀ (f₀₀ xs) [] ＝ xs
-- --       p₀-[] [] p = refl
-- --       p₀-[] ((a , inl b) ∷ xs) p = ap ((a , inl b) ∷_) (p₀-[] xs (λ c q → p c (in-tail q)))
-- --       p₀-[] ((a , inr c) ∷ xs) p = 𝟘-elim (p c in-head)

-- --       no-inr : (xs : List ⟨ β +ₒ γ ⟩)(b : ⟨ β ⟩) → is-decreasing (underlying-order (β +ₒ γ)) (inl b ∷ xs) → (c : ⟨ γ ⟩) → ¬ member (inr c) xs
-- --       no-inr (inr c ∷ xs) b δ c in-head = 𝟘-elim (heads-are-decreasing (underlying-order (β +ₒ γ)) δ)
-- --       no-inr (inl b' ∷ xs) b δ c (in-tail p) = no-inr xs b' (tail-is-decreasing (underlying-order (β +ₒ γ)) δ) c p
-- --       no-inr (inr c' ∷ xs) b δ c (in-tail p) = 𝟘-elim (heads-are-decreasing (underlying-order (β +ₒ γ)) δ)
-- --     p₀ ((a , inr c) ∷ xs) δ = ap ((a , inr c) ∷_) (p₀ xs (tail-is-decreasing (underlying-order (β +ₒ γ)) δ))

-- --     p : (g ∘ f) ∼ id
-- --     p (xs , δ) = to-expᴸ-＝ α (β +ₒ γ) (p₀ xs δ)

-- --     q₀₀ : (bs : List ⟨ α ×ₒ β ⟩) → (cs : List ⟨ α ×ₒ γ ⟩) → f₀₀ (g₀ bs cs) ＝ bs
-- --     q₀₀ bs ((a , c) ∷ cs) = q₀₀ bs cs
-- --     q₀₀ ((a , b) ∷ bs) [] = ap ((a , b) ∷_) (q₀₀ bs [])
-- --     q₀₀ [] [] = refl

-- --     q₁₀ : (bs : List ⟨ α ×ₒ β ⟩) → (cs : List ⟨ α ×ₒ γ ⟩) → f₁₀ (g₀ bs cs) ＝ cs
-- --     q₁₀ bs ((a , c) ∷ cs) = ap ((a , c) ∷_) (q₁₀ bs cs)
-- --     q₁₀ ((a , b) ∷ bs) [] = q₁₀ bs []
-- --     q₁₀ [] [] = refl

-- --     q : (f ∘ g) ∼ id
-- --     q ((bs , δ) , (cs , ε)) = to-×-＝ (to-expᴸ-＝ α β (q₀₀ bs cs)) (to-expᴸ-＝ α γ (q₁₀ bs cs))

-- -- exp-+-distributes : ∀ {𝓤 𝓥} → (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
-- --                   → (expᴸ[𝟙+ α ] (β +ₒ γ)) ＝ ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ))
-- -- exp-+-distributes {𝓤} {𝓥} α β γ =
-- --  eqtoidₒ (ua (𝓤 ⊔ 𝓥)) fe' (expᴸ[𝟙+ α ] (β +ₒ γ)) ((expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] γ)) (exp-+-distributes' α β γ)

-- -- exp-succ-spec : (α : Ordinal 𝓤) (β : Ordinal 𝓤)
-- --               → (expᴸ[𝟙+ α ] (β +ₒ 𝟙ₒ)) ＝ ((expᴸ[𝟙+ α ] β) ×ₒ (𝟙ₒ +ₒ α))
-- -- exp-succ-spec {𝓤} α β =
-- --   expᴸ[𝟙+ α ] (β +ₒ 𝟙ₒ)
-- --    ＝⟨ exp-+-distributes α β 𝟙ₒ ⟩
-- --   (expᴸ[𝟙+ α ] β) ×ₒ (expᴸ[𝟙+ α ] 𝟙ₒ)
-- --    ＝⟨ ap (λ z → (expᴸ[𝟙+ α ] β) ×ₒ z) (exp-power-1 α) ⟩
-- --   (expᴸ[𝟙+ α ] β) ×ₒ (𝟙ₒ +ₒ α)
-- --    ∎

-- -- \end{code}

-- -- \begin{code}


-- -- module _ {I : 𝓤 ̇  }
-- --          (i₀ : I)
-- --          (β : I → Ordinal 𝓤)
-- --          (α : Ordinal 𝓤)
-- --  where

-- --   private
-- --    γ : I → Ordinal 𝓤
-- --    γ i = expᴸ[𝟙+ α ] (β i)

-- --    ι : (ζ : I → Ordinal 𝓤) → {i : I} → ⟨ ζ i ⟩ → ⟨ sup ζ ⟩
-- --    ι ζ {i} = pr₁ (sup-is-upper-bound ζ i)

-- --    ι-is-simulation : (ζ : I → Ordinal 𝓤) → {i : I}
-- --                    → is-simulation (ζ i) (sup ζ ) (ι ζ)
-- --    ι-is-simulation ζ {i} = pr₂ (sup-is-upper-bound ζ i)

-- --    ι-is-order-preserving : (ζ : I → Ordinal 𝓤) {i : I}
-- --                          → is-order-preserving (ζ i) (sup ζ) (ι ζ)
-- --    ι-is-order-preserving ζ {i} = simulations-are-order-preserving (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

-- --    ι-is-order-reflecting : (ζ : I → Ordinal 𝓤) {i : I}
-- --                          → is-order-reflecting (ζ i) (sup ζ) (ι ζ)
-- --    ι-is-order-reflecting ζ {i} = simulations-are-order-reflecting (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

-- --    ι-is-lc : (ζ : I → Ordinal 𝓤) {i : I}
-- --            → left-cancellable (ι ζ)
-- --    ι-is-lc ζ {i} = simulations-are-lc (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

-- --    ι-is-initial-segment : (ζ : I → Ordinal 𝓤) → {i : I}
-- --                         → is-initial-segment (ζ i) (sup ζ ) (ι ζ)
-- --    ι-is-initial-segment ζ {i} = simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ)

-- --    ι-is-surjective : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩)
-- --                    → ∃ i ꞉ I , Σ x ꞉ ⟨ ζ i ⟩ , ι ζ {i} x ＝ s
-- --    ι-is-surjective = sup-is-upper-bound-jointly-surjective

-- --    ι-is-surjective⁺ : (ζ : I → Ordinal 𝓤) (s : ⟨ sup ζ ⟩) (i : I) (x : ⟨ ζ i ⟩)
-- --                     → s ≺⟨ sup ζ ⟩ ι ζ x
-- --                     → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
-- --    ι-is-surjective⁺ ζ s i x p =
-- --     h (simulations-are-initial-segments (ζ i) (sup ζ) (ι ζ) (ι-is-simulation ζ) x s p)
-- --     where
-- --      h : Σ y ꞉ ⟨ ζ i ⟩ , y ≺⟨ ζ i ⟩ x × (ι ζ y ＝ s)
-- --        → Σ y ꞉ ⟨ ζ i ⟩ , ι ζ {i} y ＝ s
-- --      h (y , (_ , q)) = y , q

-- --    module _ (i : I) where
-- --     f₁ : List (⟨ α ×ₒ β i ⟩) → List (⟨ α ×ₒ sup β ⟩)
-- --     f₁ [] = []
-- --     f₁ (a , b ∷ l) = a , ι β b ∷ f₁ l
-- --     f₂ : (l : List (⟨ α ×ₒ β i ⟩))
-- --        → is-decreasing-pr₂ α (β i) l
-- --        → is-decreasing-pr₂ α (sup β) (f₁ l)
-- --     f₂ [] δ = []-decr
-- --     f₂ (a , b ∷ []) δ = sing-decr
-- --     f₂ (a , b ∷ a' , b' ∷ l) (many-decr p δ) =
-- --       many-decr (simulations-are-order-preserving (β i) (sup β)
-- --                   (ι β)
-- --                   (pr₂ (sup-is-upper-bound β i)) b' b p)
-- --                 (f₂ (a' , b' ∷ l) δ)
-- --     f : ⟨ γ i ⟩ → ⟨ expᴸ[𝟙+ α ] (sup β) ⟩
-- --     f (l , δ) = f₁ l , f₂ l δ

-- --    f₁-surj-lemma : (a : ⟨ α ⟩) (i : I) (b : ⟨ β i ⟩) (l : List (⟨ α ×ₒ sup β ⟩))
-- --                  → is-decreasing-pr₂ α (sup β) (a , ι β b ∷ l)
-- --                  → Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) (a , b ∷ l')
-- --                                               × ((a , ι β b ∷ l) ＝ f₁ i (a , b ∷ l'))
-- --    f₁-surj-lemma a i b [] δ = [] , sing-decr , refl
-- --    f₁-surj-lemma a i b ((a' , s) ∷ l) δ =
-- --     (a' , b' ∷ l') ,
-- --     many-decr order-lem₃ δ' ,
-- --     ap (a , ι β b ∷_) (ap (λ - → a' , - ∷ l) ((pr₂ lem) ⁻¹) ∙ pr₂ (pr₂ IH))
-- --      where
-- --       lem : Σ b' ꞉ ⟨ β i ⟩ , ι β b' ＝ s
-- --       lem = ι-is-surjective⁺ β s i b (heads-are-decreasing (underlying-order (sup β)) δ)
-- --       b' : ⟨ β i ⟩
-- --       b' = pr₁ lem
-- --       order-lem₁ : s ≺⟨ sup β ⟩ ι β b
-- --       order-lem₁ = heads-are-decreasing (underlying-order (sup β)) δ
-- --       order-lem₂ : ι β b' ≺⟨ sup β ⟩ ι β b
-- --       order-lem₂ = transport⁻¹ (λ - → underlying-order (sup β) - (ι β b)) (pr₂ lem) order-lem₁
-- --       order-lem₃ : b' ≺⟨ β i ⟩ b
-- --       order-lem₃ = ι-is-order-reflecting β b' b order-lem₂
-- --       IH : Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) (a' , b' ∷ l')
-- --                                       × ((a' , ι β b' ∷ l) ＝ f₁ i (a' , b' ∷ l'))
-- --       IH = f₁-surj-lemma a' i b' l
-- --             (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) (a' , - ∷ l)) (pr₂ lem)
-- --               (tail-is-decreasing (underlying-order (sup β)) δ))
-- --       l' : List (⟨ α ×ₒ β i ⟩)
-- --       l' = pr₁ IH
-- --       δ' : is-decreasing-pr₂ α (β i) (a' , b' ∷ l')
-- --       δ' = pr₁ (pr₂ IH)

-- --    f₁-surj : (l : List (⟨ α ×ₒ sup β ⟩))
-- --            → is-decreasing-pr₂ α (sup β) l
-- --            → ∃ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
-- --                                                   × (l ＝ f₁ i l')
-- --    f₁-surj [] δ = ∣ i₀ , [] , []-decr , refl ∣
-- --    f₁-surj (a , s ∷ l) δ = ∥∥-functor h (ι-is-surjective β s)
-- --     where
-- --      h : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , ι β b ＝ s)
-- --        → Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
-- --                                               × ((a , s ∷ l) ＝ f₁ i l')
-- --      h (i , b , refl) = i , (a , b ∷ pr₁ lem) , (pr₁ (pr₂ lem) , pr₂ (pr₂ lem))
-- --       where
-- --        lem : Σ l' ꞉ List ⟨ α ×ₒ β i ⟩ , is-decreasing-pr₂ α (β i) (a , b ∷ l')
-- --                                       × (a , ι β b ∷ l ＝ f₁ i (a , b ∷ l'))
-- --        lem = f₁-surj-lemma a i b l δ

-- --    f-surj : (y : ⟨ expᴸ[𝟙+ α ] (sup β) ⟩) → ∃ i ꞉ I , Σ x ꞉ ⟨ γ i ⟩ , f i x ＝ y
-- --    f-surj (l , δ) = ∥∥-functor h (f₁-surj l δ)
-- --     where
-- --      h : (Σ i ꞉ I , Σ l' ꞉ List (⟨ α ×ₒ β i ⟩) , is-decreasing-pr₂ α (β i) l'
-- --                                                × (l ＝ f₁ i l'))
-- --        → Σ i ꞉ I , Σ x ꞉ ⟨ γ i ⟩ , (f i x ＝ l , δ)
-- --      h (i , l' , δ , refl) = i , (l' , δ) , to-expᴸ-＝ α (sup β) refl

-- --    f-is-order-preserving : (i : I) → is-order-preserving (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
-- --    f-is-order-preserving i ([] , δ) (_ , ε) []-lex = []-lex
-- --    f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-preserving β b b' m))
-- --    f-is-order-preserving i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (refl , m))) = head-lex (inr (refl , m))
-- --    f-is-order-preserving i ((_ ∷ l) , δ) ((_ ∷ l') , ε) (tail-lex refl m) =
-- --      tail-lex refl (f-is-order-preserving i (l , tail-is-decreasing (underlying-order (β i)) δ) (l' , tail-is-decreasing (underlying-order (β i)) ε) m)

-- --    f-is-order-reflecting : (i : I) → is-order-reflecting (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
-- --    f-is-order-reflecting i ([] , δ) ((a , b ∷ l) , ε) []-lex = []-lex
-- --    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inl m)) = head-lex (inl (ι-is-order-reflecting β b b' m))
-- --    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (head-lex (inr (e , m))) = head-lex (inr (ι-is-lc β e , m))
-- --    f-is-order-reflecting i ((a , b ∷ l) , δ) ((a' , b' ∷ l') , ε) (tail-lex e m) =
-- --     tail-lex (to-×-＝ (ap pr₁ e) (ι-is-lc β (ap pr₂ e)))
-- --     (f-is-order-reflecting i (l , tail-is-decreasing (underlying-order (β i)) δ) (l' , tail-is-decreasing (underlying-order (β i)) ε) m)

-- --    -- We factor out:
-- --    partial-invertibility-lemma : (i : I) -- (a : ⟨ α ⟩) (b : ⟨ β i ⟩)
-- --                                → (l : List (⟨ α ×ₒ β i ⟩))
-- --                                → is-decreasing-pr₂ α (sup β) (f₁ i l) -- (f₁ i (a , b ∷ l))
-- --                                → is-decreasing-pr₂ α (β i) l -- (a , b ∷ l)
-- --    partial-invertibility-lemma i [] ds = []-decr
-- --    partial-invertibility-lemma i ((a , b) ∷ []) ds = sing-decr
-- --    partial-invertibility-lemma i ((a , b) ∷ (a' , b') ∷ l) (many-decr m ds) =
-- --      many-decr (ι-is-order-reflecting β b' b m) (partial-invertibility-lemma i ((a' , b') ∷ l) ds)

-- --    f-is-partially-invertible : (i : I)
-- --                              → (xs : List ⟨ α ×ₒ β i ⟩) → (δ : is-decreasing-pr₂ α (β i) xs)
-- --                              → (ys : List ⟨ α ×ₒ sup β ⟩) → (ε : is-decreasing-pr₂ α (sup β) ys)
-- --                              → (ys , ε) ≺⟨ expᴸ[𝟙+ α ] (sup β) ⟩ f i (xs , δ)
-- --                              → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ (ys , ε)
-- --    f-is-partially-invertible i xs δ [] []-decr p = ([] , []-decr) , refl
-- --    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ []) ε (head-lex (inl m)) = ((a' , pr₁ ι-sim ∷ []) , sing-decr) , (to-expᴸ-＝ α (sup β) (ap (λ - → (a' , -) ∷ []) (pr₂ (pr₂ ι-sim))))
-- --      where
-- --        ι-sim = ι-is-initial-segment β b b' m
-- --    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , b') ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inl m)) =
-- --      let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl (Transitivity (sup β) _ _ _ p m)))
-- --          xs' = pr₁ (pr₁ IH)
-- --          ι-sim = ι-is-initial-segment β b b' m
-- --          b₀ = pr₁ ι-sim
-- --          p₀ = transport⁻¹ (λ - → b₁ ≺⟨ sup β ⟩ -) (pr₂ (pr₂ ι-sim)) p
-- --      in ((a' , b₀ ∷ xs') , partial-invertibility-lemma i ((a' , b₀) ∷ xs') (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b₀) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p₀ ε)))
-- --        , (to-expᴸ-＝ α (sup β) (ap₂ (λ x y → (a' , x) ∷ y) (pr₂ (pr₂ ι-sim)) (ap pr₁ (pr₂ IH))))
-- --    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ []) ε (head-lex (inr (refl , m))) = ((a' , b ∷ []) , sing-decr) , (to-expᴸ-＝ α (sup β) refl)
-- --    f-is-partially-invertible i ((a , b) ∷ xs) δ ((a' , .(ι β b)) ∷ (a₁ , b₁) ∷ ys) (many-decr p ε) (head-lex (inr (refl , m))) =
-- --      let IH = f-is-partially-invertible i ((a , b) ∷ xs) δ ((a₁ , b₁) ∷ ys) ε (head-lex (inl p))
-- --          xs' = pr₁ (pr₁ IH)
-- --      in (((a' , b) ∷ xs') , partial-invertibility-lemma i ((a' , b) ∷ xs')
-- --                                                           (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a' , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) (many-decr p ε)))
-- --         , to-expᴸ-＝ α (sup β) (ap ((a' , ι β b) ∷_) (ap pr₁ (pr₂ IH)))
-- --    f-is-partially-invertible i ((a , b) ∷ xs) δ (.(a , ι β b) ∷ ys) ε (tail-lex refl p) =
-- --      let IH = f-is-partially-invertible i xs (tail-is-decreasing (underlying-order (β i)) δ) ys (tail-is-decreasing (underlying-order (sup β)) ε) p
-- --      in (((a , b) ∷ pr₁ (pr₁ IH)) , partial-invertibility-lemma i ((a , b) ∷ pr₁ (pr₁ IH))
-- --                                                                   (transport⁻¹ (λ - → is-decreasing-pr₂ α (sup β) ((a , ι β b) ∷ -)) (ap pr₁ (pr₂ IH)) ε))
-- --        , to-expᴸ-＝ α (sup β) (ap ((a , ι β b) ∷_) (ap pr₁ (pr₂ IH)))

-- --    f-is-initial-segment : (i : I) → is-initial-segment (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i)
-- --    f-is-initial-segment i = order-reflecting-partial-surjections-are-initial-segments (γ i) (expᴸ[𝟙+ α ] (sup β)) (f i) (f-is-order-reflecting i) g
-- --      where
-- --        g : (xs : ⟨ γ i ⟩) → (ys : ⟨ expᴸ[𝟙+ α ] (sup β) ⟩) → ys ≺⟨ expᴸ[𝟙+ α ] (sup β) ⟩ f i xs → Σ xs' ꞉ ⟨ γ i ⟩ , f i xs' ＝ ys
-- --        g (xs , δ) (ys , ε) = f-is-partially-invertible i xs δ ys ε

-- --   exp-sup-is-upper-bound : (i : I) → γ i ⊴ (expᴸ[𝟙+ α ] (sup β))
-- --   exp-sup-is-upper-bound i = f i , f-is-initial-segment i , f-is-order-preserving i

-- --   exp-sup-simulation : sup (λ i → (expᴸ[𝟙+ α ] (β i))) ⊴ (expᴸ[𝟙+ α ] (sup β))
-- --   exp-sup-simulation = sup-is-lower-bound-of-upper-bounds (λ i → (expᴸ[𝟙+ α ] (β i))) (expᴸ[𝟙+ α ] (sup β)) exp-sup-is-upper-bound

-- --   exp-sup-simulation-surjective : is-surjection (pr₁ exp-sup-simulation)
-- --   exp-sup-simulation-surjective = surjectivity-lemma γ (expᴸ[𝟙+ α ] (sup β)) exp-sup-is-upper-bound f-surj

-- --   sup-spec : sup (λ i → (expᴸ[𝟙+ α ] (β i))) ＝ (expᴸ[𝟙+ α ] (sup β))
-- --   sup-spec = surjective-simulation-gives-＝ pt fe' (ua _)
-- --                (sup (λ i → (expᴸ[𝟙+ α ] (β i))))
-- --                (expᴸ[𝟙+ α ] (sup β))
-- --                (pr₁ exp-sup-simulation)
-- --                (pr₂ exp-sup-simulation)
-- --                exp-sup-simulation-surjective

-- -- exp-sup-spec : (α : Ordinal 𝓤) {I : 𝓤 ̇  } → ∥ I ∥ → (β : I → Ordinal 𝓤) → (expᴸ[𝟙+ α ] (sup β)) ＝ sup (λ i → (expᴸ[𝟙+ α ] (β i)))
-- -- exp-sup-spec α i β = ∥∥-rec (the-type-of-ordinals-is-a-set (ua _) fe') (λ i₀ → sup-spec i₀ β α ⁻¹) i

-- -- \end{code}

-- -- \begin{code}

-- -- monotone-in-exponent : ∀ {𝓤} (α : Ordinal 𝓤)
-- --                      → is-monotone (OO 𝓤) (OO 𝓤) (expᴸ[𝟙+ α ])
-- -- monotone-in-exponent α = is-monotone-if-continuous (expᴸ[𝟙+ α ]) (exp-sup-spec α)

-- -- \end{code}