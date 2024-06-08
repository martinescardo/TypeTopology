Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 May 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.ComparingDescendingListAndAlternative
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
-- open import UF.Equiv
-- open import UF.ExcludedMiddle
open import UF.FunExt
-- open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
-- open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua


-- open import Naturals.Order

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import MLTT.Plus-Properties
open import MLTT.Sigma
open import MLTT.List

open import Ordinals.Arithmetic fe
-- open import Ordinals.ArithmeticProperties ua
-- open import Ordinals.Equivalence
-- open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Taboos

open import Ordinals.Exponentiation.DecreasingList ua pt sr
open import Ordinals.Exponentiation.Alternative ua pt sr

open PropositionalTruncation pt
open suprema pt sr
\end{code}

Relating the two definitions of exponentiation.

\begin{code}

is-decreasing-skip-one : {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) → is-transitive R → (x x' : X) → (xs : List X) → is-decreasing R (x' ∷ xs) → R x' x → is-decreasing R (x ∷ xs)
is-decreasing-skip-one R trans x x' [] d r = sing-decr
is-decreasing-skip-one R trans x x' (x'' ∷ xs) (many-decr p' ps) r = many-decr (trans x'' x' x p' r) ps

is-decreasing-less-than-head : {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) → is-transitive R → (x : X) → (xs : List X) → is-decreasing R (x ∷ xs) → (y : X) → member y xs → R y x
is-decreasing-less-than-head R trans x (x' ∷ xs) (many-decr p ps) .x' in-head = p
is-decreasing-less-than-head {X = X} R trans x (x' ∷ xs) (many-decr p ps) y (in-tail m) = is-decreasing-less-than-head R trans x xs (is-decreasing-skip-one R trans x x' xs ps p) y m

decreasing-pr₂-to-more-precise-tail :  (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩)(b : ⟨ β ⟩)(xs : List ⟨ α ×ₒ β ⟩) → is-decreasing-pr₂ α β ((a , b) ∷ xs) → List ⟨ α ×ₒ (β ↓ b) ⟩
decreasing-pr₂-to-more-precise-tail α β a b [] p = []
decreasing-pr₂-to-more-precise-tail α β a b ((a' , b') ∷ xs) ps
  = (a' , (b' , is-decreasing-heads _ ps)) ∷ decreasing-pr₂-to-more-precise-tail α β a b xs (is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ xs) (is-decreasing-tail _ ps) (is-decreasing-heads _ ps))

decreasing-pr₂-to-more-precise-tail-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩) (b : ⟨ β ⟩) (xs : List ⟨ α ×ₒ β ⟩) → (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                                               → is-decreasing-pr₂ α (β ↓ b) (decreasing-pr₂-to-more-precise-tail α β a b xs ps)
decreasing-pr₂-to-more-precise-tail-decreasing α β a b [] ps = []-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ []) (many-decr p sing-decr) = sing-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ a'' , b'' ∷ xs) (many-decr p (many-decr p' ps))
  = many-decr p' (decreasing-pr₂-to-more-precise-tail-decreasing α β a b ((a'' , b'') ∷ xs) (many-decr (Transitivity β b'' b' b p' p) ps))

more-precise-tail-pair : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                         (a : ⟨ α ⟩) (b : ⟨ β ⟩) (xs : List ⟨ α ×ₒ β ⟩)
                         (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                       → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
more-precise-tail-pair α β a b xs ps =
 decreasing-pr₂-to-more-precise-tail α β a b xs ps ,
 decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps

more-precise-tail-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                     (a₀ : ⟨ α ⟩) (b₀ : ⟨ β ⟩)
                                     (xs : List ⟨ α ×ₒ β ⟩)
                                     (δ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ xs))
                                     (xs' : List ⟨ α ×ₒ β ⟩)
                                     (δ' : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ xs'))
                                   → xs ≺⟨List (α ×ₒ β) ⟩ xs'
                                   → more-precise-tail-pair α β a₀ b₀ xs δ ≺⟨ ([𝟙+ α ]^ (β ↓ b₀)) ⟩ more-precise-tail-pair α β a₀ b₀ xs' δ'
more-precise-tail-order-preserving α β a₀ b₀ [] ps (x' ∷ xs') ps' q = []-lex
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a' , b') ∷ xs') (many-decr p' ps') (head-lex (inl q)) = head-lex (inl q)
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a' , b) ∷ xs') (many-decr p' ps') (head-lex (inr (refl , q))) =
 head-lex (inr (to-subtype-＝ (λ x → Prop-valuedness β x b₀) refl , q))
more-precise-tail-order-preserving α β a₀ b₀ ((a , b) ∷ xs) (many-decr p ps) ((a , b) ∷ xs') (many-decr p' ps') (tail-lex refl q) =
 tail-lex (ap (a ,_) (to-subtype-＝ ((λ x → Prop-valuedness β x b₀)) refl)) (more-precise-tail-order-preserving α β a₀ b₀ xs _ xs' _ q)



\end{code}

\begin{code}

open import Ordinals.Equivalence
open import Ordinals.ArithmeticProperties ua

[𝟙+]^-↓-lemma : (α : Ordinal 𝓤) (β : Ordinal 𝓤)
                (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
                (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
              → (([𝟙+ α ]^ β) ↓ (((a , b) ∷ l) , δ)) ≃ₒ
                ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ))
[𝟙+]^-↓-lemma α β a b l δ = {!!}
 where
  f : ⟨ ([𝟙+ α ]^ β) ↓ (((a , b) ∷ l) , δ) ⟩ →
                 ⟨ (([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ more-precise-tail-pair α β a b l δ) ⟩
  f (([] , []-decr) , p) = inl (([] , []-decr) , inl ⋆)
  f ((((a' , b') ∷ l') , ε) , head-lex (inl p)) =
   let
    ε' = is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ l') ε p
    l'' = more-precise-tail-pair α β a b l' ε'
   in
    inl ((((a' , (b' , p)) ∷ pr₁ l'') , b'l''-decreasing l' a' b' p ε) , (inl ⋆))
   where
    b'l''-decreasing : ∀ l' a' b' p ε → is-decreasing-pr₂ α (β ↓ b) (a' , (b' , p) ∷ pr₁ (more-precise-tail-pair α β a b l' (is-decreasing-skip-one (pr₁ (pr₂ β)) (Transitivity β) b b' (map (λ r → pr₂ r) l') ε p)))
    b'l''-decreasing [] a' b' p ε = sing-decr
    b'l''-decreasing (a'' , b'' ∷ l'') a' b' p (many-decr p'' ε'') = many-decr p'' (b'l''-decreasing l'' a'' b'' (Transitivity β _ _ _ p'' p) ε'')
  f ((((a' , b) ∷ l') , ε) , head-lex (inr (refl , p))) = inl (more-precise-tail-pair α β a b l' ε , inr (a' , p))
  f ((((a' , b') ∷ l') , ε) , tail-lex refl p) = inr (more-precise-tail-pair α β a b' l' ε , more-precise-tail-order-preserving α β a b' l' ε l δ p)

{-

↓-eq-lemma : (α β : Ordinal 𝓤) (a : ⟨ α ⟩)
             (e : α ＝ β)
           → α ↓ a ＝ β ↓ Idtofun (ap ⟨_⟩ e) a
↓-eq-lemma α β a refl = refl

-- TODO: Generalize universe levels later (first +ₒ should be made more general)
amazing : (α : Ordinal 𝓤) (β : Ordinal 𝓤) → exp (𝟙ₒ +ₒ α) β ＝ [𝟙+ α ]^ β
amazing {𝓤} α = transfinite-induction-on-OO _ I
 where
  I : (β : Ordinal 𝓤)
    → ((b : ⟨ β ⟩) → exp (𝟙ₒ +ₒ α) (β ↓ b) ＝ ([𝟙+ α ]^ (β ↓ b)))
    → exp (𝟙ₒ +ₒ α) β ＝ ([𝟙+ α ]^ β)
  I β IH = ⊲-is-extensional (exp (𝟙ₒ +ₒ α) β) ([𝟙+ α ]^ β) II III
   where
    II : (γ : Ordinal 𝓤) → γ ⊲ exp (𝟙ₒ +ₒ α) β → γ ⊲ ([𝟙+ α ]^ β)
    II _ (e , refl) = ∥∥-rec (⊲-is-prop-valued (exp (𝟙ₒ +ₒ α) β ↓ e) ([𝟙+ α ]^ β))
                              the-real-thing
                              (sup-is-upper-bound-jointly-surjective (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)))
                              (Idtofun (ap ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β)) e))
     where
      the-real-thing : Σ i ꞉ (𝟙 + ⟨ β ⟩) , Σ x ꞉ ⟨ (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) i ⟩ ,
                               pr₁ (sup-is-upper-bound _ i) x ＝ Idtofun (ap ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β)) e
                     → (exp (𝟙ₒ +ₒ α) β ↓ e) ⊲ ([𝟙+ α ]^ β)
      the-real-thing (inl _ , ⋆ , p) = {!!}
       where
       {-
        foo : {!!}
        foo = (exp (𝟙ₒ +ₒ α) β ↓ e) ＝⟨ ↓-eq-lemma (exp (𝟙ₒ +ₒ α) β) (sup (cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)))) e (exp-behaviour (𝟙ₒ +ₒ α) β) ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) ↓ Idtofun (ap ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β)) e) ＝⟨ ap (sup (cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) ↓_) (p ⁻¹) ⟩
              (sup (cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) ↓
                pr₁
                (sup-is-upper-bound
                 (λ z →
                    pr₁
                    (dep-cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) z)
                    ,
                    pr₂
                    (dep-cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))
                     z))
                 (inl _))
                cons-is-non-empty) ＝⟨ {!!} ⟩
              {!!} ＝⟨ {!!} ⟩
              {!!} ∎ -}
      the-real-thing (inr b , (e , inl ⋆) , p) = {!!}
      the-real-thing (inr b , (e , inr a) , p) = {!!}
    III : (γ : Ordinal 𝓤) → γ ⊲ ([𝟙+ α ]^ β) → γ ⊲ exp (𝟙ₒ +ₒ α) β
    III = {!!} {- _ (([] , δ) , refl) = {!!} -- 𝟘 ⊲ exp (𝟙ₒ +ₒ α) β
    III _ ((((a , b) ∷ l) , δ) , refl) = _ , foo
     where
      foo = (([𝟙+ α ]^ β) ↓ ((a , b ∷ l) , δ)) ＝⟨ eqtoidₒ (ua 𝓤) fe' _ _ ([𝟙+]^-↓-lemma α β a b l δ) ⟩
            ((([𝟙+ α ]^ (β ↓ b)) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ
              (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ＝⟨ ap (λ - → (- ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ((IH b) ⁻¹) ⟩
            ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ
              (([𝟙+ α ]^ (β ↓ b)) ↓ l')) ＝⟨ ap ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ_) fact ⟩
            ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))) +ₒ (exp (𝟙ₒ +ₒ α) (β ↓ b) ↓ l'')) ＝⟨ {!!} ⟩ -- easy
            ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ ((𝟙ₒ +ₒ α) ↓ inr a)) +ₒ (exp (𝟙ₒ +ₒ α) (β ↓ b) ↓ l'')) ＝⟨ fold ⟩
            ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (l'' , inr a)) ＝⟨ fact' ⟩
            (sup (cases (λ _ → 𝟙ₒ) (λ b₁ → exp (𝟙ₒ +ₒ α) (β ↓ b₁) ×ₒ (𝟙ₒ +ₒ α)))
              ↓
              pr₁
              (sup-is-upper-bound _
               (inr b))
              (l'' , inr a)) ＝⟨ ↓-eq-lemma _ (exp (𝟙ₒ +ₒ α) β) (pr₁ (sup-is-upper-bound _ (inr b)) (l'' , inr a)) ((exp-behaviour (𝟙ₒ +ₒ α) β) ⁻¹) ⟩
            ((exp (𝟙ₒ +ₒ α) β) ↓ _) ∎
       where
        l' = more-precise-tail-pair α β a b l δ
        l'' : ⟨ exp (𝟙ₒ +ₒ α) (β ↓ b) ⟩
        l'' = ≃ₒ-to-fun _ _ (idtoeqₒ _ _ ((IH b) ⁻¹)) l' -- TODO: Use Idtofun instead
        fact : (([𝟙+ α ]^ (β ↓ b)) ↓ l') ＝ (exp (𝟙ₒ +ₒ α) (β ↓ b)) ↓ l''
        fact = ↓-eq-lemma ([𝟙+ α ]^ (β ↓ b)) (exp (𝟙ₒ +ₒ α) (β ↓ b)) l' ((IH b) ⁻¹)
        fold : ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ ((𝟙ₒ +ₒ α) ↓ inr a)) +ₒ
                  (exp (𝟙ₒ +ₒ α) (β ↓ b) ↓ l''))
                 ＝ ((exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ↓ (l'' , inr a))
        fold = ×ₒ-↓ _ _ l'' (inr a) ⁻¹
        fact' = (initial-segment-of-sup-at-component (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α))) (inr b) (l'' , inr a)) ⁻¹
-}

-- to-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
-- to-alternative α = transfinite-induction-on-OO (λ β → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩) g
--  where
--   g : (β : Ordinal 𝓥) → ((b : ⟨ β ⟩) → ⟨[𝟙+ α ]^ β ↓ b ⟩ →  ⟨ exp (𝟙ₒ +ₒ α) (β ↓ b) ⟩) →
--       ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
--   g β ih ([] , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β) (pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆)
--   g β ih (((a , b) ∷ xs) , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β)
--                                              (pr₁ (sup-is-upper-bound _ (inr b))
--                                                   (ih b (decreasing-pr₂-to-more-precise-tail α β a b xs ps
--                                                         , decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps) , inr a))

-- {-
-- to-alternative-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-order-preserving ([𝟙+ α ]^ β) (exp (𝟙ₒ +ₒ α) β) (to-alternative α β)
-- to-alternative-order-preserving α β ([] , p) (((a , b) ∷ ys) , q) []-lex = {!!}
-- -- 𝟘ₒ < exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
-- to-alternative-order-preserving α β ((x ∷ xs) , p) ((y ∷ ys) , q) (head-lex r) = {!!}
-- -- exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
-- to-alternative-order-preserving α β ((x ∷ xs) , p) ((x ∷ ys) , q) (tail-lex refl rr) = {!!}
-- -}

-- 𝕗 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩)
--   → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)
-- 𝕗 {𝓤} {𝓥} α = transfinite-induction-on-OO (λ β → (b : ⟨ β ⟩) → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)) H
--  where
--   H : (β : Ordinal 𝓥)
--     → ((b : ⟨ β ⟩) (b' : ⟨ β ↓ b ⟩)
--           → (exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ (β ↓ b)))
--     → (b : ⟨ β ⟩)
--     → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)
--   H β IH b = {!!}
--    where
--     𝕗' : (Σ x ꞉ 𝟙{𝓤} + ⟨ β ↓ b ⟩ ,
--          (cases {X = 𝟙} (λ _ → 𝟙) (λ b' → ⟨ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) ⟩) x)) × ⟨ 𝟙ₒ +ₒ α ⟩
--        → ⟨ [𝟙+ α ]^ β ⟩
--     𝕗' ((inl _ , e) , inl _) = [] , []-decr
--     𝕗' ((inl _ , e) , inr a) = [ a , b ] , sing-decr
--     𝕗' ((inr b' , e) , inl _) = {!!}
--      where
--       fb' : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
--       fb' = [ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) , [𝟙+ α ]^ (β ↓ b) ]⟨ IH b b' ⟩ e
--     𝕗' ((inr b' , e) , inr a) = {!!}


-- \end{code}

-- \begin{code}

-- -- An ordinal that can perhaps be useful in deriving constructive taboos

-- {-
-- module _ (P : 𝓤 ̇ ) where

--  _≺𝟚ₚ_ : 𝟚 {𝓤} → 𝟚 {𝓤} → 𝓤 ̇
--  ₀ ≺𝟚ₚ ₀ = 𝟘
--  ₀ ≺𝟚ₚ ₁ = P
--  ₁ ≺𝟚ₚ ₀ = ¬ P
--  ₁ ≺𝟚ₚ ₁ = 𝟘

--  ≺-is-prop-valued : is-prop P → is-prop-valued _≺𝟚ₚ_
--  ≺-is-prop-valued i ₀ ₀ = 𝟘-is-prop
--  ≺-is-prop-valued i ₀ ₁ = i
--  ≺-is-prop-valued i ₁ ₀ = Π-is-prop fe' (λ x → 𝟘-is-prop)
--  ≺-is-prop-valued i ₁ ₁ = 𝟘-is-prop

--  ≺-is-transitive : transitive _≺𝟚ₚ_
--  ≺-is-transitive ₀ ₁ ₀ u v = 𝟘-elim (v u)
--  ≺-is-transitive ₀ ₁ ₁ u v = 𝟘-elim v
--  ≺-is-transitive ₁ ₀ ₁ u v = 𝟘-elim (u v)
--  ≺-is-transitive ₁ ₁ z u v = 𝟘-elim u

--  ≺-is-extensional : is-extensional _≺𝟚ₚ_
--  ≺-is-extensional ₀ ₀ u v = refl
--  ≺-is-extensional ₁ ₁ u v = refl
--  ≺-is-extensional ₀ ₁ u v = 𝟘-elim (δ γ)
--   where
--    γ : ¬ P
--    γ p = 𝟘-elim (v ₀ p)
--    δ : ¬ ¬ P
--    δ np = 𝟘-elim (u ₁ np)
--  ≺-is-extensional ₁ ₀ u v = 𝟘-elim (δ γ)
--   where
--    γ : ¬ P
--    γ p = 𝟘-elim (u ₀ p)
--    δ : ¬ ¬ P
--    δ np = 𝟘-elim (v ₁ np)

--  ≺-is-well-founded : is-well-founded _≺𝟚ₚ_
--  ≺-is-well-founded ₀ = acc ₀-accessible
--   where
--     ₀-accessible : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
--     ₀-accessible ₁ np = acc g
--      where
--       g : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
--       g ₀ p = 𝟘-elim (np p)
--  ≺-is-well-founded ₁ = acc ₁-accessible
--   where
--    ₁-accessible : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
--    ₁-accessible ₀ p = acc g
--     where
--      g : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
--      g ₁ np = 𝟘-elim (np p)

--  ≺𝟚ₚ-ordinal : is-prop P → Ordinal 𝓤
--  ≺𝟚ₚ-ordinal i = 𝟚 , _≺𝟚ₚ_ , ≺-is-prop-valued i , ≺-is-well-founded , ≺-is-extensional , ≺-is-transitive

--  ≺-trichotomous-characterization : is-trichotomous-order _≺𝟚ₚ_ ↔ (P + ¬ P)
--  ≺-trichotomous-characterization = ⦅⇒⦆ , ⦅⇐⦆
--   where
--    ⦅⇐⦆ : (P + ¬ P) → is-trichotomous-order _≺𝟚ₚ_
--    ⦅⇐⦆ p ₀ ₀ = inr (inl refl)
--    ⦅⇐⦆ (inl p) ₀ ₁ = inl p
--    ⦅⇐⦆ (inr np) ₀ ₁ = inr (inr np)
--    ⦅⇐⦆ (inl p) ₁ ₀ = inr (inr p)
--    ⦅⇐⦆ (inr np) ₁ ₀ = inl np
--    ⦅⇐⦆ p ₁ ₁ = inr (inl refl)
--    ⦅⇒⦆ : is-trichotomous-order _≺𝟚ₚ_ → (P + ¬ P)
--    ⦅⇒⦆ t = translate (t ₀ ₁)
--     where
--      translate : (₀ ≺𝟚ₚ ₁) + (₀ ＝ ₁) + (₁ ≺𝟚ₚ ₀) → (P + ¬ P)
--      translate (inl p)       = inl p
--      translate (inr (inl e)) = 𝟘-elim (+disjoint e)
--      translate (inr (inr np)) = inr np
-- -}
-}
-- \end{code}
