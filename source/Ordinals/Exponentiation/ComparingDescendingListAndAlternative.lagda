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

-- open import UF.Base
-- open import UF.Equiv
-- open import UF.ExcludedMiddle
open import UF.FunExt
-- open import UF.Sets
open import UF.Subsingletons
-- open import UF.Subsingletons-FunExt
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

open import MLTT.Spartan
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
-- open import Ordinals.WellOrderingTaboo
open import Ordinals.OrdinalOfOrdinalsSuprema ua

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
decreasing-pr₂-to-more-precise-tail α β a b ((a' , b') ∷ xs) (many-decr p ps)
  = (a' , (b' , p)) ∷ decreasing-pr₂-to-more-precise-tail α β a b xs (is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ xs) ps p)

decreasing-pr₂-to-more-precise-tail-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩)(b : ⟨ β ⟩)(xs : List ⟨ α ×ₒ β ⟩) → (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                                               → is-decreasing-pr₂ α (β ↓ b) (decreasing-pr₂-to-more-precise-tail α β a b xs ps)
decreasing-pr₂-to-more-precise-tail-decreasing α β a b [] ps = []-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ []) (many-decr p sing-decr) = sing-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ a'' , b'' ∷ xs) (many-decr p (many-decr p' ps))
  = many-decr p' (decreasing-pr₂-to-more-precise-tail-decreasing α β a b ((a'' , b'') ∷ xs) (many-decr (Transitivity β b'' b' b p' p) ps))

to-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
to-alternative α = transfinite-induction-on-OO (λ β → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩) g
 where
  g : (β : Ordinal 𝓥) → ((b : ⟨ β ⟩) → ⟨[𝟙+ α ]^ β ↓ b ⟩ →  ⟨ exp (𝟙ₒ +ₒ α) (β ↓ b) ⟩) →
      ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
  g β ih ([] , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β) (pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆)
  g β ih (((a , b) ∷ xs) , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β)
                                             (pr₁ (sup-is-upper-bound _ (inr b))
                                                  (ih b (decreasing-pr₂-to-more-precise-tail α β a b xs ps
                                                        , decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps) , inr a))


{-
to-alternative-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-order-preserving ([𝟙+ α ]^ β) (exp (𝟙ₒ +ₒ α) β) (to-alternative α β)
to-alternative-order-preserving α β ([] , p) (((a , b) ∷ ys) , q) []-lex = {!!}
-- 𝟘ₒ < exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
to-alternative-order-preserving α β ((x ∷ xs) , p) ((y ∷ ys) , q) (head-lex r) = {!!}
-- exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
to-alternative-order-preserving α β ((x ∷ xs) , p) ((x ∷ ys) , q) (tail-lex refl rr) = {!!}
-}
\end{code}
