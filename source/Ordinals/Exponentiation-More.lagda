Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

TEMPORARILY SPLIT UP TO SPEED UP TYPECHECKING

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split  #-}

open import UF.Univalence
open import UF.DiscreteAndSeparated

module Ordinals.Exponentiation-More
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (cases ; Cases)
open import MLTT.Sigma
-- open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

-- our imports
open import MLTT.List
open import Ordinals.Exponentiation ua

open import Ordinals.WellOrderingTaboo

\end{code}

\begin{code}

trimmed-ordinal' : (α : Ordinal 𝓤) (x₀ : ⟨ α ⟩)
                 → ((x : ⟨ α ⟩) → in-trichotomy (underlying-order α) x₀ x)
                 → Ordinal 𝓤
trimmed-ordinal' {𝓤} α x₀ τ = α' , _≺'_
                                 , subtype-order-propositional α (λ - → x₀ ≺⟨ α ⟩ -)
                                 , subtype-order-wellfounded α (λ - → x₀ ≺⟨ α ⟩ -)
                                 , ≺'-extensional
                                 , subtype-order-transitive α (λ - → x₀ ≺⟨ α ⟩ -)
 where
   α' : 𝓤 ̇
   α' = Σ x ꞉ ⟨ α ⟩ , x₀ ≺⟨ α ⟩ x
   _≺'_ : α' → α' → 𝓤 ̇
   _≺'_ = subtype-order α (λ - → x₀ ≺⟨ α ⟩ -)
   ≺'-extensional : is-extensional _≺'_
   ≺'-extensional (x , l) (y , k) u v =
    to-subtype-＝ (Prop-valuedness α x₀) (Extensionality α x y (λ z → u' z (τ z)) (λ z → v' z (τ z)))
     where
      u' : (z : ⟨ α ⟩)
         → in-trichotomy (underlying-order α) x₀ z
         → z ≺⟨ α ⟩ x
         → z ≺⟨ α ⟩ y
      u' z (inl x₀-below-z) m = u (z , x₀-below-z) m
      u' z (inr (inl refl)) m = k
      u' z (inr (inr z-below-x₀)) m = Transitivity α z x₀ y z-below-x₀ k
      v' : (z : ⟨ α ⟩)
         → in-trichotomy (underlying-order α) x₀ z
         → z ≺⟨ α ⟩ y
         → z ≺⟨ α ⟩ x
      v' z (inl x₀-below-z) m = v (z , x₀-below-z) m
      v' z (inr (inl refl)) m = l
      v' z (inr (inr z-below-x₀)) m = Transitivity α z x₀ x z-below-x₀ l

trimmed-ordinal : (α : Ordinal 𝓤) (x₀ : ⟨ α ⟩)
                → is-isolated x₀
                → ((x : ⟨ α ⟩) → x ≠ x₀ → x₀ ≺⟨ α ⟩ x)
                → Ordinal 𝓤
trimmed-ordinal α x₀ δ x₀-least = trimmed-ordinal' α x₀ (λ x → τ x (δ x))
 where
   τ : (x : ⟨ α ⟩)
     → is-decidable (x₀ ＝ x)
     → in-trichotomy (underlying-order α) x₀ x
   τ x (inl e) = inr (inl e)
   τ x (inr ne) = inl (x₀-least x (≠-sym ne))

exp-has-least-element : (α β : Ordinal 𝓤) → Σ γ ꞉ Ordinal 𝓤 , [𝟙+ α ]^ β ＝ 𝟙ₒ +ₒ γ
exp-has-least-element {𝓤} α β = γ , eqtoidₒ (ua _) fe' ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) (f , f-equiv)
 where
   γ : Ordinal 𝓤
   γ = trimmed-ordinal' ([𝟙+ α ]^ β) ([] , []-decr) τ
    where
     τ : (x : ⟨ [𝟙+ α ]^ β ⟩)
       → in-trichotomy (underlying-order ([𝟙+ α ]^ β)) ([] , []-decr) x
     τ ([] , δ) = inr (inl (to-exponential-＝ α β refl))
     τ ((x ∷ l) , δ) = inl []-lex

   f : ⟨ [𝟙+ α ]^ β ⟩ → ⟨ 𝟙ₒ +ₒ γ ⟩
   f ([] , δ) = inl ⋆
   f y@((x ∷ xs) , δ) = inr (y , []-lex)

   g : ⟨ 𝟙ₒ +ₒ γ ⟩ → ⟨ [𝟙+ α ]^ β ⟩
   g (inl _) = ([] , []-decr)
   g (inr (y , p)) = y

   f-order-preserving : is-order-preserving ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) f
   f-order-preserving ([] , δ) ((x ∷ xs) , ε) p = ⋆
   f-order-preserving ((x ∷ xs) , δ) ((y ∷ ys) , ε) p = p

   g-order-preserving : is-order-preserving (𝟙ₒ +ₒ γ) ([𝟙+ α ]^ β) g
   g-order-preserving (inl ⋆) (inr (((x ∷ xs) , δ) , q)) _ = []-lex
   g-order-preserving (inr (((x ∷ xs) , δ) , q)) (inr (((y ∷ ys) , ε) , q')) p = p

   f-equiv : is-order-equiv ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) f
   f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
    where
     η : (x : ⟨ [𝟙+ α ]^ β ⟩) → g (f x) ＝ x
     η ([] , []-decr) = refl
     η ((x ∷ xs) , δ) = refl

     ϵ : (x : ⟨ 𝟙ₒ +ₒ γ ⟩) → f (g x) ＝ x
     ϵ (inl ⋆) = refl
     ϵ (inr (((x ∷ xs) , δ) , []-lex)) = refl

flatten-× : {A B C : 𝓤 ̇  } → List ({-Nonempty-}List (A × B) × C) → List (A × (B × C))
flatten-× [] = []
flatten-× ((l , c) ∷ ls) = (map (λ (a , b) → (a , (b , c))) l) ++ flatten-× ls

addToFirst : {X Y : 𝓤 ̇  } → X → List ((List X) × Y) → List ((List X) × Y)
addToFirst x [] = []
addToFirst x ((xs , y) ∷ l) = ((x ∷ xs) , y) ∷ l

flatten-×⁻¹ : {α β γ : Ordinal 𝓤 } → (xs : List (⟨ α ×ₒ (β ×ₒ γ) ⟩)) → is-decreasing-pr₂ α (β ×ₒ γ) xs → List ({-Nonempty-}List (⟨ α ⟩ × ⟨ β ⟩ ) × ⟨ γ ⟩)
flatten-×⁻¹ [] _ = []
flatten-×⁻¹ ((a , (b , c)) ∷ []) _ = [ [ a , b ] , c ]
flatten-×⁻¹ {α = α} {β} {γ} ((a , (b , c)) ∷ (a' , (b' , c')) ∷ xs) (many-decr (inl p) δ) = ([ a , b ] , c) ∷ flatten-×⁻¹ {α = α} {β} {γ} ((a' , (b' , c')) ∷ xs) δ
flatten-×⁻¹ {α = α} {β} {γ} ((a , (b , c)) ∷ (a' , (b' , c)) ∷ xs) (many-decr (inr (refl , q)) δ) = addToFirst (a , b) (flatten-×⁻¹ {α = α} {β} {γ} ((a' , (b' , c)) ∷ xs) δ)

flatten-×-retraction : {α β γ : Ordinal 𝓤 } → (xs : List (⟨ α ×ₒ (β ×ₒ γ) ⟩)) → (xs-decr : is-decreasing-pr₂ α (β ×ₒ γ) xs)
      → flatten-× (flatten-×⁻¹ {α = α} {β} {γ} xs xs-decr) ＝ xs
flatten-×-retraction [] xs-decr = refl
flatten-×-retraction ((a , (b , c)) ∷ []) xs-decr = refl
flatten-×-retraction ((a , (b , c)) ∷ (a' , (b' , c')) ∷ xs) (many-decr (inl p) δ)= ap ( a , b , c ∷_) (flatten-×-retraction ((a' , (b' , c')) ∷ xs) δ)
flatten-×-retraction (a , b , c ∷ a' , b' , c ∷ xs) (many-decr (inr (refl , q)) δ) = {!!}


{-
-- We need to restrict to the subtype of non-empty "inner" lists, as the following counterexample shows (and the actual problem suggests):

counterexampleList : List (List (ℕ × ℕ) × ℕ)
counterexampleList = [ [] , 17 ]

res : List (List (ℕ × ℕ) × ℕ)
res = flatten-×⁻¹ {α = ω} {ω} {ω} (flatten-× counterexampleList) []-decr
-}

{-
test : List (⟨ ω ×ₒ (ω ×ₒ ω) ⟩)
test = (1 , (2 , 3)) ∷ (6 , (1 , 3)) ∷ (42 , (17 , 2)) ∷ (100 , (16 , 1)) ∷ []

test-decr : is-decreasing-pr₂ ω (ω ×ₒ ω) test
test-decr = many-decr (inr (refl , ⋆))
              (many-decr (inl ⋆) (many-decr (inl ⋆) sing-decr))
-}


{-
exp-×-distributes : (α β γ : Ordinal 𝓤)
                  → [𝟙+ α ]^ (β ×ₒ γ) ＝ [𝟙+ (pr₁ (exp-has-least-element α β)) ]^ γ
exp-×-distributes α β γ = {!!}
 where
  γ' = pr₁ (exp-has-least-element α β)
  g : ⟨ [𝟙+ γ' ]^ γ ⟩ → ⟨ [𝟙+ α ]^ (β ×ₒ γ) ⟩
  g ([] , _) = [] , []-decr
  g ((((((a , b) ∷ l) , δ) , ne) , c ∷ l') , δ') = ((a , b , c) ∷ pr₁ IH) , {!!}
   where
    IH : ⟨ [𝟙+ α ]^ (β ×ₒ γ) ⟩
    IH = g (l' , is-decreasing-tail (underlying-order γ) δ')
    IH' : {!!}
    IH' = g ({!!} , {!!})

  f : ⟨ [𝟙+ α ]^ (β ×ₒ γ) ⟩ → ⟨ [𝟙+ γ' ]^ γ ⟩
  f ([] , _) = [] , []-decr
  f (((a , (b , c)) ∷ l) , δ) = (((([ (a , b) ] , sing-decr) , []-lex) , c) ∷ pr₁ IH) ,
                                {!!}
   where
    IH : ⟨ [𝟙+ γ' ]^ γ ⟩
    IH = f (l , is-decreasing-tail (underlying-order (β ×ₒ γ)) δ)
    IH₁ : List ⟨ γ' ×ₒ γ ⟩
    IH₁ = pr₁ IH
    IH₂ : is-decreasing-pr₂ γ' γ (pr₁ IH)
    IH₂ = pr₂ IH
-}
\end{code}

Wikipedia:
* γ > 1 => γ^(-) is order preserving
* α^(β + γ) = α^β × α^γ              [ exp-+-distributes ]
* α^(β × γ) = (α^β)^γ
