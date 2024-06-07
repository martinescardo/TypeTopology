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
open import UF.Sets
open import UF.Sets-Properties
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
open import Ordinals.Equivalence
open import Ordinals.Maps
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
decreasing-pr₂-to-more-precise-tail α β a b ((a' , b') ∷ xs) (many-decr p ps)
  = (a' , (b' , p)) ∷ decreasing-pr₂-to-more-precise-tail α β a b xs (is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ xs) ps p)

decreasing-pr₂-to-more-precise-tail-decreasing : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (a : ⟨ α ⟩)(b : ⟨ β ⟩)(xs : List ⟨ α ×ₒ β ⟩) → (ps : is-decreasing-pr₂ α β ((a , b) ∷ xs))
                                               → is-decreasing-pr₂ α (β ↓ b) (decreasing-pr₂-to-more-precise-tail α β a b xs ps)
decreasing-pr₂-to-more-precise-tail-decreasing α β a b [] ps = []-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ []) (many-decr p sing-decr) = sing-decr
decreasing-pr₂-to-more-precise-tail-decreasing α β a b (a' , b' ∷ a'' , b'' ∷ xs) (many-decr p (many-decr p' ps))
  = many-decr p' (decreasing-pr₂-to-more-precise-tail-decreasing α β a b ((a'' , b'') ∷ xs) (many-decr (Transitivity β b'' b' b p' p) ps))

more-precise-decr : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                  → (a : ⟨ α ⟩)(b : ⟨ β ⟩)(xs : List ⟨ α ×ₒ β ⟩) → is-decreasing-pr₂ α β ((a , b) ∷ xs)
                  → ⟨[𝟙+ α ]^ (β ↓ b) ⟩
more-precise-decr α β a b xs ps = decreasing-pr₂-to-more-precise-tail α β a b xs ps , decreasing-pr₂-to-more-precise-tail-decreasing α β a b xs ps

to-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
to-alternative α = transfinite-induction-on-OO (λ β → ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩) g
 where
  g : (β : Ordinal 𝓥) → ((b : ⟨ β ⟩) → ⟨[𝟙+ α ]^ β ↓ b ⟩ →  ⟨ exp (𝟙ₒ +ₒ α) (β ↓ b) ⟩) →
      ⟨[𝟙+ α ]^ β ⟩ → ⟨ exp (𝟙ₒ +ₒ α) β ⟩
  g β ih ([] , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β) (sum-to-sup _ (inl _ , _))
  -- (pr₁ (sup-is-upper-bound _ (inl ⋆)) ⋆)
  g β ih (((a , b) ∷ xs) , ps) = transport⁻¹ ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) β) (sum-to-sup _ (inr b , ih b (more-precise-decr α β a b xs ps) , inr a))

 -- (pr₁ (sup-is-upper-bound _ (inr b)) (ih b (more-precise-decr α β a b xs ps) , inr a))

{-
to-alternative-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-order-preserving ([𝟙+ α ]^ β) (exp (𝟙ₒ +ₒ α) β) (to-alternative α β)
to-alternative-order-preserving α β ([] , p) (((a , b) ∷ ys) , q) []-lex = {!!}
-- 𝟘ₒ < exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
to-alternative-order-preserving α β ((x ∷ xs) , p) ((y ∷ ys) , q) (head-lex r) = {!!}
-- exp α (β ↓ b) × (1 + α ↓ a) + exp α (β ↓ b) ↓ (to-alternative α (β ↓ b) ys)
to-alternative-order-preserving α β ((x ∷ xs) , p) ((x ∷ ys) , q) (tail-lex refl rr) = {!!}
-}
{-
embed-simulation : (α : Ordinal 𝓤) (β : Ordinal 𝓤) (b : ⟨ β ⟩) → ([𝟙+ α ]^ (β ↓ b)) ⊴ ([𝟙+ α ]^ β)
embed-simulation α β b =
 ≼-gives-⊴ ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β)
   (monotone-in-exponent α (β ↓ b) β (⊴-gives-≼ (β ↓ b) β (segment-⊴ β b)))

embed : (α : Ordinal 𝓤) (β : Ordinal 𝓤) (b : ⟨ β ⟩) → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩ → ⟨ [𝟙+ α ]^ β ⟩
embed α β b = [ _ , _ ]⟨ embed-simulation α β b ⟩


embed-below-b : (α : Ordinal 𝓤) (β : Ordinal 𝓤) (b : ⟨ β ⟩) → (xs : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩)
              → (y : ⟨ β ⟩) → member y (map pr₂ (underlying-list α β (embed α β b xs))) → y ≺⟨ β ⟩ b
embed-below-b α β b ([] , δ) y m = {!!}
embed-below-b α β b ((x ∷ xs) , δ) y m = {!simulations-are-initial-segments _ _ (embed α β b) ? !}
-}

embed : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩ → ⟨ [𝟙+ α ]^ β ⟩
embed α β b (xs , δ) = map project₂ xs , project₂-preserves-decreasing xs δ
 where
  project₂ : ⟨ α ×ₒ (β ↓ b) ⟩ → ⟨ α ×ₒ β ⟩
  project₂ (a , x) = (a , segment-inclusion β b x)
  project₂-preserves-decreasing : (xs : List ⟨ α ×ₒ (β ↓ b) ⟩) → is-decreasing-pr₂ α (β ↓ b) xs → is-decreasing-pr₂ α β (map project₂ xs)
  project₂-preserves-decreasing [] _ = []-decr
  project₂-preserves-decreasing ((a , x) ∷ []) _ = sing-decr
  project₂-preserves-decreasing ((a , x) ∷ (a' , x') ∷ xs) (many-decr p δ) = many-decr p (project₂-preserves-decreasing ((a' , x') ∷ xs) δ)

embed-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → is-order-preserving ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) (embed α β b)
embed-order-preserving α β b ([] , pr₃) ((y ∷ ys) , ε) []-lex = []-lex
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (head-lex (inl p)) = head-lex (inl p)
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (head-lex (inr (refl , p))) = head-lex (inr (refl , p))
embed-order-preserving α β b ((x ∷ xs) , δ) ((y ∷ ys) , ε) (tail-lex refl p) = tail-lex refl (embed-order-preserving α β b (xs , is-decreasing-tail _ δ) (ys , is-decreasing-tail _ ε) p)

embed-below-b : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → (xs : ⟨ [𝟙+ α ]^ (β ↓ b) ⟩)
              → (y : ⟨ β ⟩) → member y (map pr₂ (underlying-list α β (embed α β b xs))) → y ≺⟨ β ⟩ b
embed-below-b α β b (((a , (b' , p)) ∷ xs) , δ) y in-head = p
embed-below-b α β b ((x ∷ xs) , δ) y (in-tail m) = embed-below-b α β b (xs , is-decreasing-tail _ δ) y m

{- TODO
embed-initial-segment : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → is-initial-segment ([𝟙+ α ]^ (β ↓ b)) ([𝟙+ α ]^ β) (embed α β b)
embed-initial-segment α β b ((x ∷ xs) , δ) ([] , []-decr) []-lex = ([] , []-decr) , []-lex , refl
embed-initial-segment α β b (((a' , (b' , q)) ∷ xs) , δ) (((a'' , b'') ∷ ys) , ε) (head-lex (inl p)) = {!!}
-- exponential-cons α (β ↓ b) ((a'' , b'' , {!!})) (more-precise-decr α β a' b ys {!!}) {!!} , {!!} , {!to-exponential-＝ α β (ap ((a'' , b'') ∷_) {!!})!}
embed-initial-segment α β b (((a' , (b' , q)) ∷ xs) , δ) (((a'' , b') ∷ ys) , ε) (head-lex (inr (refl , p))) = ((a'' , (b' , q) ∷ pr₁ (more-precise-decr α β a'' b ys (is-decreasing-skip-one (underlying-order β) (Transitivity β) b b' (map pr₂ ys) ε q))) , {!!}) , {!!} , to-exponential-＝ α β (ap₂ _∷_ refl {!!})
embed-initial-segment α β b (((a' , (b' , q)) ∷ xs) , δ) (((.a' , .b') ∷ ys) , ε) (tail-lex refl p) =
 (((a' , b' , q) ∷ pr₁ xs₀) , lemma-extensionality' α (β ↓ b) xs (pr₁ xs₀) (a' , (b' , q)) δ (pr₂ xs₀) xs₀-below-xs) , tail-lex refl xs₀-below-xs , to-exponential-＝ α β (ap₂ _∷_ refl (ap pr₁ embed-xs₀is-ys))
  where
    ih : Σ xs₀ ꞉ ⟨ [𝟙+ α ]^ (β ↓ b) ⟩ , (xs₀ ≺⟨ ([𝟙+ α ]^ (β ↓ b)) ⟩ (xs , _) × (embed α β b xs₀ ＝ ys , _))
    ih = embed-initial-segment α β b (xs , is-decreasing-tail _ δ) (ys , is-decreasing-tail _ ε) p
    xs₀ = pr₁ ih
    xs₀-below-xs = pr₁ (pr₂ ih)
    embed-xs₀is-ys = pr₂ (pr₂ ih)

-- exponential-cons α (β ↓ b) ((a' , b' , q)) xs₀ (λ (y , q) m → {!embed-below-b α β b'  !})
-}

embed-simulation : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩) → ([𝟙+ α ]^ (β ↓ b)) ⊴ ([𝟙+ α ]^ β)
embed-simulation α β b = (embed α β b , {!!} , embed-order-preserving α β b)

𝕗 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b : ⟨ β ⟩)
  → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)
𝕗 {𝓤} {𝓥} α = transfinite-induction-on-OO (λ β → (b : ⟨ β ⟩) → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)) H
 where
  H : (β : Ordinal 𝓥)
    → ((b : ⟨ β ⟩) (b' : ⟨ β ↓ b ⟩)
          → (exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ (β ↓ b)))
    → (b : ⟨ β ⟩)
    → (exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) ⊴ ([𝟙+ α ]^ β)
  H β IH b = f , {!!} , {!!}
   where
    F : 𝟙{𝓤} + ⟨ β ↓ b ⟩ → Ordinal (𝓤 ⊔ 𝓥)
    F = cases {X = 𝟙} (λ _ → 𝟙ₒ) (λ b' → exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α))
    𝕗' : (Σ x ꞉ 𝟙{𝓤} + ⟨ β ↓ b ⟩ , ⟨ F x ⟩)
       → ⟨ 𝟙ₒ +ₒ α ⟩
       → ⟨ [𝟙+ α ]^ β ⟩
    𝕗' (inl _ , ⋆) (inl _) = [] , []-decr
    𝕗' (inl _ , ⋆) (inr a) = [ a , b ] , sing-decr
    𝕗' (inr b' , e) (inl _) = embed α β b (fb' e)
     where
      fb' : ⟨ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) ⟩ → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
      fb' = [ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) , [𝟙+ α ]^ (β ↓ b) ]⟨ IH b b' ⟩
    𝕗' (inr b' , e) (inr a) = exponential-cons α β (a , b) (embed α β b (fb' e)) (embed-below-b α β b (fb' e))
     where
      fb' : ⟨ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) ⟩ → ⟨ [𝟙+ α ]^ (β ↓ b) ⟩
      fb' = [ exp (𝟙ₒ +ₒ α) ((β ↓ b) ↓ b') ×ₒ (𝟙ₒ +ₒ α) , [𝟙+ α ]^ (β ↓ b) ]⟨ IH b b' ⟩

    𝕗'-eq : (i : 𝟙 + ⟨ β ↓ b ⟩)(x : ⟨ F i ⟩) (j : 𝟙 + ⟨ β ↓ b ⟩)(y : ⟨ F j ⟩)
          → (F i ↓ x) ＝ (F j ↓ y) → 𝕗' (i , x) ＝ 𝕗' (j , y)
    𝕗'-eq (inl _) ⋆        (inl _)   ⋆ p = refl
    𝕗'-eq (inl _) ⋆        (inr b'') (e' , inl ⋆) p =
     dfunext fe' λ { (inl _) → {!!} -- decide if e' = ⊥
                   ; (inr a) → to-exponential-＝ _ _ (ap ((a , b) ∷_) {!!}) -- decide if e' = ⊥
                   }
    𝕗'-eq (inl _) ⋆        (inr b'') (e' , inr a') p = {!!} -- impossible
    𝕗'-eq (inr b') (e , x) (inl _)   ⋆ p =
     dfunext fe' λ { (inl _) → {!!} -- decide if e = ⊥
                   ; (inr a) → to-exponential-＝ _ _ (ap ((a , b) ∷_) {!!}) -- decide if e = ⊥
                   }
    𝕗'-eq (inr b') (e , x) (inr b'') (e' , y) p =
     dfunext fe' λ { (inl _) → eq-tail
                   ; (inr a) → to-exponential-＝ _ _ (ap ((a , b) ∷_) (ap pr₁ eq-tail))
                   }
      where
        eq-tail : embed α β b ([ _ , _ ]⟨ IH b b' ⟩ (e , x)) ＝ embed α β b ([ _ , _ ]⟨ IH b b'' ⟩ (e' , y))
        eq-tail = isomorphic-initial-segments-gives-simulations-pointwise-equal
                    (F (inr b'))
                    (F (inr b''))
                    ([𝟙+ α ]^ β)
                    (⊴-trans _ _ _ (IH b b') (embed-simulation α β b))
                    (⊴-trans _ _ _ (IH b b'') (embed-simulation α β b))
                    (e , x)
                    (e' , y)
                    (idtoeqₒ _ _ p)

    f : ⟨ exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α) ⟩ → ⟨ [𝟙+ α ]^ β ⟩
    f (e , x) =
     induced-map-from-sup F (Π-is-set fe' λ i → underlying-type-is-set fe ([𝟙+ α ]^ β))
                            𝕗'
                            𝕗'-eq
                            (transport ⟨_⟩ (exp-behaviour (𝟙ₒ +ₒ α) (β ↓ b)) e)
                            x

from-alternative : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (exp (𝟙ₒ +ₒ α) β) ⊴ ([𝟙+ α ]^ β)
from-alternative {𝓤} α β = transport⁻¹ (_⊴ ([𝟙+ α ]^ β))
                                   (exp-behaviour (𝟙ₒ +ₒ α) β)
                                   (sup-is-lower-bound-of-upper-bounds _ _ g)
 where
  g : (x : 𝟙 {𝓤} + ⟨ β ⟩) →
      cases (λ _ → 𝟙ₒ) (λ b → exp (𝟙ₒ +ₒ α) (β ↓ b) ×ₒ (𝟙ₒ +ₒ α)) x ⊴ ([𝟙+ α ]^ β)
  g (inl _) = [𝟙+α]^β-has-least α β
  g (inr b) = 𝕗 α β b

\end{code}

\begin{code}

-- An ordinal that can perhaps be useful in deriving constructive taboos

{-
module _ (P : 𝓤 ̇ ) where

 _≺𝟚ₚ_ : 𝟚 {𝓤} → 𝟚 {𝓤} → 𝓤 ̇
 ₀ ≺𝟚ₚ ₀ = 𝟘
 ₀ ≺𝟚ₚ ₁ = P
 ₁ ≺𝟚ₚ ₀ = ¬ P
 ₁ ≺𝟚ₚ ₁ = 𝟘

 ≺-is-prop-valued : is-prop P → is-prop-valued _≺𝟚ₚ_
 ≺-is-prop-valued i ₀ ₀ = 𝟘-is-prop
 ≺-is-prop-valued i ₀ ₁ = i
 ≺-is-prop-valued i ₁ ₀ = Π-is-prop fe' (λ x → 𝟘-is-prop)
 ≺-is-prop-valued i ₁ ₁ = 𝟘-is-prop

 ≺-is-transitive : transitive _≺𝟚ₚ_
 ≺-is-transitive ₀ ₁ ₀ u v = 𝟘-elim (v u)
 ≺-is-transitive ₀ ₁ ₁ u v = 𝟘-elim v
 ≺-is-transitive ₁ ₀ ₁ u v = 𝟘-elim (u v)
 ≺-is-transitive ₁ ₁ z u v = 𝟘-elim u

 ≺-is-extensional : is-extensional _≺𝟚ₚ_
 ≺-is-extensional ₀ ₀ u v = refl
 ≺-is-extensional ₁ ₁ u v = refl
 ≺-is-extensional ₀ ₁ u v = 𝟘-elim (δ γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (v ₀ p)
   δ : ¬ ¬ P
   δ np = 𝟘-elim (u ₁ np)
 ≺-is-extensional ₁ ₀ u v = 𝟘-elim (δ γ)
  where
   γ : ¬ P
   γ p = 𝟘-elim (u ₀ p)
   δ : ¬ ¬ P
   δ np = 𝟘-elim (v ₁ np)

 ≺-is-well-founded : is-well-founded _≺𝟚ₚ_
 ≺-is-well-founded ₀ = acc ₀-accessible
  where
    ₀-accessible : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
    ₀-accessible ₁ np = acc g
     where
      g : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
      g ₀ p = 𝟘-elim (np p)
 ≺-is-well-founded ₁ = acc ₁-accessible
  where
   ₁-accessible : (y : 𝟚) → y ≺𝟚ₚ ₁ → is-accessible _≺𝟚ₚ_ y
   ₁-accessible ₀ p = acc g
    where
     g : (y : 𝟚) → y ≺𝟚ₚ ₀ → is-accessible _≺𝟚ₚ_ y
     g ₁ np = 𝟘-elim (np p)

 ≺𝟚ₚ-ordinal : is-prop P → Ordinal 𝓤
 ≺𝟚ₚ-ordinal i = 𝟚 , _≺𝟚ₚ_ , ≺-is-prop-valued i , ≺-is-well-founded , ≺-is-extensional , ≺-is-transitive

 ≺-trichotomous-characterization : is-trichotomous-order _≺𝟚ₚ_ ↔ (P + ¬ P)
 ≺-trichotomous-characterization = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇐⦆ : (P + ¬ P) → is-trichotomous-order _≺𝟚ₚ_
   ⦅⇐⦆ p ₀ ₀ = inr (inl refl)
   ⦅⇐⦆ (inl p) ₀ ₁ = inl p
   ⦅⇐⦆ (inr np) ₀ ₁ = inr (inr np)
   ⦅⇐⦆ (inl p) ₁ ₀ = inr (inr p)
   ⦅⇐⦆ (inr np) ₁ ₀ = inl np
   ⦅⇐⦆ p ₁ ₁ = inr (inl refl)
   ⦅⇒⦆ : is-trichotomous-order _≺𝟚ₚ_ → (P + ¬ P)
   ⦅⇒⦆ t = translate (t ₀ ₁)
    where
     translate : (₀ ≺𝟚ₚ ₁) + (₀ ＝ ₁) + (₁ ≺𝟚ₚ ₀) → (P + ¬ P)
     translate (inl p)       = inl p
     translate (inr (inl e)) = 𝟘-elim (+disjoint e)
     translate (inr (inr np)) = inr np
-}

\end{code}
