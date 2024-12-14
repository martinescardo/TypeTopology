Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
Started November 2023. Refactored December 2024.

TODO: Comment in between the code blocks

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence

module Ordinals.Exponentiation.DecreasingList
       (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.List
open import MLTT.Plus-Properties
open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.Sets
open import UF.Subsingletons

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua renaming (_≼_ to _≼OO_)
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.TrichotomousLeastElement ua

\end{code}

The lexicographic order on lists.

\begin{code}

data lex {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) : List X → List X → 𝓤 ⊔ 𝓥 ̇  where
 []-lex : {x : X} {l : List X} → lex R [] (x ∷ l)
 head-lex : {x y : X} {l l' : List X} → R x y → lex R (x ∷ l) (y ∷ l')
 tail-lex : {x y : X} {l l' : List X} → x ＝ y → lex R l l' → lex R (x ∷ l) (y ∷ l')

lex-for-ordinal : (α : Ordinal 𝓤) → List ⟨ α ⟩ → List ⟨ α ⟩ → 𝓤 ̇
lex-for-ordinal α = lex (underlying-order α)

syntax lex-for-ordinal α l l' = l ≺⟨List α ⟩ l'

\end{code}

The lexicographic order preserves many properties of the order.

\begin{code}

module _ {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) where

 lex-transitive : is-transitive R → is-transitive (lex R)
 lex-transitive tr [] (y ∷ l₂) (z ∷ l₃) []-lex (head-lex q) = []-lex
 lex-transitive tr [] (y ∷ l₂) (z ∷ l₃) []-lex (tail-lex r q) = []-lex
 lex-transitive tr (x ∷ l₁) (y ∷ l₂) (z ∷ l₃) (head-lex p) (head-lex q) =
  head-lex (tr x y z p q)
 lex-transitive tr (x ∷ l₁) (y ∷ l₂) (.y ∷ l₃) (head-lex p) (tail-lex refl q) =
  head-lex p
 lex-transitive tr (x ∷ l₁) (.x ∷ l₂) (z ∷ l₃) (tail-lex refl p) (head-lex q) =
  head-lex q
 lex-transitive tr (x ∷ l₁) (x ∷ l₂) (x ∷ l₃) (tail-lex refl p) (tail-lex refl q)
  = tail-lex refl (lex-transitive tr l₁ l₂ l₃ p q)

 []-lex-bot : is-bot (lex R) []
 []-lex-bot l ()

 lex-irreflexive : is-irreflexive R → is-irreflexive (lex R)
 lex-irreflexive ir (x ∷ l) (head-lex p) = ir x p
 lex-irreflexive ir (x ∷ l) (tail-lex e q) = lex-irreflexive ir l q

 lex-prop-valued : is-set X
                 → is-prop-valued R
                 → is-irreflexive R
                 → is-prop-valued (lex R)
 lex-prop-valued st pr irR l (y ∷ l') []-lex []-lex = refl
 lex-prop-valued st pr irR (x ∷ l) (y ∷ l') (head-lex u) (head-lex v) =
  ap head-lex (pr x y u v)
 lex-prop-valued st pr irR (x ∷ l) (y ∷ l') (head-lex u) (tail-lex refl v) =
  𝟘-elim (irR y u)
 lex-prop-valued st pr irR (x ∷ l) (y ∷ l') (tail-lex refl u) (head-lex v) =
  𝟘-elim (irR x v)
 lex-prop-valued st pr irR (x ∷ l) (y ∷ l') (tail-lex refl u) (tail-lex e v) =
  ap₂ tail-lex (st refl e) (lex-prop-valued st pr irR l l' u v)

\end{code}

We now consider the subtype of decreasing lists.

\begin{code}

 data is-decreasing : List X → 𝓤 ⊔ 𝓥 ̇  where
  []-decr : is-decreasing []
  sing-decr : {x : X} → is-decreasing [ x ]
  many-decr : {x y : X} {l : List X}
            → R y x
            → is-decreasing (y ∷ l)
            → is-decreasing (x ∷ y ∷ l)

 is-decreasing-is-prop : is-prop-valued R
                       → (l : List X) → is-prop (is-decreasing l)
 is-decreasing-is-prop pR [] []-decr []-decr = refl
 is-decreasing-is-prop pR (x ∷ []) sing-decr sing-decr = refl
 is-decreasing-is-prop pR (x ∷ y ∷ l) (many-decr p ps) (many-decr q qs) =
  ap₂ many-decr (pR y x p q) (is-decreasing-is-prop pR (y ∷ l) ps qs)

 tail-is-decreasing : {x : X} {l : List X}
                    → is-decreasing (x ∷ l) → is-decreasing l
 tail-is-decreasing sing-decr = []-decr
 tail-is-decreasing (many-decr _ d) = d

 heads-are-decreasing : {x y : X} {l : List X}
                     → is-decreasing (x ∷ y ∷ l) → R y x
 heads-are-decreasing (many-decr p _) = p

 is-decreasing-swap-heads : is-transitive R
                          → {y x : X} {l : List X}
                          → R x y
                          → is-decreasing (x ∷ l)
                          → is-decreasing (y ∷ l)
 is-decreasing-swap-heads τ {y} {x} {[]}    r δ = sing-decr
 is-decreasing-swap-heads τ {y} {x} {z ∷ l} r δ =
  many-decr (τ z x y (heads-are-decreasing δ) r) (tail-is-decreasing δ)

 is-decreasing-skip : is-transitive R
                    → {x x' : X} {l : List X}
                    → is-decreasing (x ∷ x' ∷ l)
                    → is-decreasing (x ∷ l)
 is-decreasing-skip τ δ =
  is-decreasing-swap-heads τ (heads-are-decreasing δ) (tail-is-decreasing δ)

 DecreasingList : 𝓤 ⊔ 𝓥 ̇
 DecreasingList = Σ l ꞉ List X , is-decreasing l

\end{code}

Next we show that the lexicographic order on lists when restricted to
DecreasingList is still wellfounded.

\begin{code}

 lex-decr : DecreasingList → DecreasingList → 𝓤 ⊔ 𝓥 ̇
 lex-decr (l , _) (l' , _) = lex R l l'

 []-acc-decr : {p : is-decreasing []} → is-accessible lex-decr ([] , p)
 []-acc-decr {[]-decr} = acc (λ xs q → 𝟘-elim ([]-lex-bot _ q))

 lex-decr-acc : is-transitive R
              → (x : X) → is-accessible R x
              → (l : List X) (δ : is-decreasing l)
              → is-accessible lex-decr (l , δ)
              → (ε : is-decreasing (x ∷ l))
              → is-accessible lex-decr ((x ∷ l) , ε)
 lex-decr-acc tr =
  transfinite-induction' R P ϕ
    where
     Q : X → DecreasingList → 𝓤 ⊔ 𝓥 ̇
     Q x (l , _) = (ε' : is-decreasing (x ∷ l))
                   → is-accessible lex-decr ((x ∷ l) , ε')
     P : X → 𝓤 ⊔ 𝓥 ̇
     P x = (l : List X) (δ : is-decreasing l)
           → is-accessible lex-decr (l , δ)
           → Q x (l , δ)
     ϕ : (x : X) → ((y : X) → R y x → P y) → P x
     ϕ x IH l δ β =
      transfinite-induction' lex-decr (Q x) (λ (l , ε) → ϕ' l ε) (l , δ) β
       where
        ϕ' : (l : List X) (ε : is-decreasing l)
           → ((l' : DecreasingList) → lex-decr l' (l , ε) → Q x l')
           → Q x (l , ε)
        ϕ' l _ IH₂ ε' = acc (λ (l' , ε) → g l' ε)
         where
          g : (l' : List X) → (ε : is-decreasing l')
             → lex-decr (l' , ε) ((x ∷ l) , ε')
             → is-accessible lex-decr (l' , ε)
          g [] ε u = []-acc-decr
          g (y ∷ []) ε (head-lex u) = IH y u [] []-decr []-acc-decr ε
          g (y ∷ []) ε (tail-lex refl u) = IH₂ ([] , []-decr) u ε
          g (y ∷ z ∷ l') ε (head-lex u) =
           IH y u (z ∷ l') (tail-is-decreasing ε)
                           (g (z ∷ l')
                            (tail-is-decreasing ε)
                            (head-lex (tr z y x (heads-are-decreasing ε) u)))
                           ε
          g (y ∷ z ∷ l') ε (tail-lex refl u) =
           IH₂ ((z ∷ l') , tail-is-decreasing ε) u ε

 lex-wellfounded : is-transitive R
                 → is-well-founded R
                 → is-well-founded lex-decr
 lex-wellfounded tr wf (l , δ) = lex-wellfounded' wf l δ
  where
   lex-wellfounded' : is-well-founded R
                    → (xs : List X) (δ : is-decreasing xs)
                    → is-accessible lex-decr (xs , δ)
   lex-wellfounded' wf [] δ = []-acc-decr
   lex-wellfounded' wf (x ∷ l) δ =
     lex-decr-acc tr x (wf x) l
      (tail-is-decreasing δ)
      (lex-wellfounded' wf l (tail-is-decreasing δ))
      δ

\end{code}

We construct an ordinal, which we denote by expᴸ α β, that implements
exponentiation of (𝟙ₒ +ₒ α) by β.

The reason that it implements exponentiation with base (𝟙ₒ +ₒ α) rather than α,
is because our construction needs a trichotomous least element (see
Ordinals.Exponentiation.TrichotomousLeastElement). Since we then restrict to the
positive elements of the base ordinal, it is convenient to only consider α
(rather than 𝟙ₒ +ₒ α).

\begin{code}

module _ (α : Ordinal 𝓤) (β : Ordinal 𝓥) where

 is-decreasing-pr₂ : List ⟨ α ×ₒ β ⟩ → 𝓥 ̇
 is-decreasing-pr₂ xs = is-decreasing (underlying-order β) (map pr₂ xs)

 heads-are-decreasing-pr₂ : (a a' : ⟨ α ⟩) {b b' : ⟨ β ⟩} {l : List ⟨ α ×ₒ β ⟩}
                          → is-decreasing-pr₂ ((a , b) ∷ (a' , b') ∷ l)
                          → b' ≺⟨ β ⟩ b
 heads-are-decreasing-pr₂ a a' = heads-are-decreasing (underlying-order β)

 tail-is-decreasing-pr₂ : (x : ⟨ α ×ₒ β ⟩) {l : List ⟨ α ×ₒ β ⟩}
                        → is-decreasing-pr₂ (x ∷ l)
                        → is-decreasing-pr₂ l
 tail-is-decreasing-pr₂ x = tail-is-decreasing (underlying-order β)

 is-decreasing-pr₂-skip : (x y : ⟨ α ×ₒ β ⟩) {l : List ⟨ α ×ₒ β ⟩}
                        → is-decreasing-pr₂ (x ∷ y ∷ l)
                        → is-decreasing-pr₂ (x ∷ l)
 is-decreasing-pr₂-skip x y = is-decreasing-skip (underlying-order β)
                                                 (Transitivity β)

 ⟨expᴸ⟩ : 𝓤 ⊔ 𝓥 ̇
 ⟨expᴸ⟩ = Σ l ꞉ List ⟨ α ×ₒ β ⟩ , is-decreasing-pr₂ l

 expᴸ-list : ⟨expᴸ⟩ → List ⟨ α ×ₒ β ⟩
 expᴸ-list = pr₁

 to-expᴸ-＝ : {l l' : ⟨expᴸ⟩} → expᴸ-list l ＝ expᴸ-list l' → l ＝ l'
 to-expᴸ-＝ = to-subtype-＝ (λ l → is-decreasing-is-prop
                                    (underlying-order β)
                                    (Prop-valuedness β)
                                    (map pr₂ l))

 expᴸ-list-is-decreasing-pr₂ : (l : ⟨expᴸ⟩) → is-decreasing-pr₂ (expᴸ-list l)
 expᴸ-list-is-decreasing-pr₂ = pr₂

 is-decreasing-if-decreasing-pr₂ : (l : List ⟨ α ×ₒ β ⟩)
                                 → is-decreasing-pr₂ l
                                 → is-decreasing (underlying-order (α ×ₒ β)) l
 is-decreasing-if-decreasing-pr₂ [] _ = []-decr
 is-decreasing-if-decreasing-pr₂ (x ∷ []) _ = sing-decr
 is-decreasing-if-decreasing-pr₂ (x ∷ x' ∷ l) (many-decr p δ)
  = many-decr (inl p) (is-decreasing-if-decreasing-pr₂ (x' ∷ l) δ)

 expᴸ-list-is-decreasing
  : (l : ⟨expᴸ⟩)
  → is-decreasing (underlying-order (α ×ₒ β)) (expᴸ-list l)
 expᴸ-list-is-decreasing (l , δ) = is-decreasing-if-decreasing-pr₂ l δ

 expᴸ-order : ⟨expᴸ⟩ → ⟨expᴸ⟩ → 𝓤 ⊔ 𝓥 ̇
 expᴸ-order (l , _) (l' , _) = l ≺⟨List (α ×ₒ β) ⟩ l'

 expᴸ-order-is-prop-valued : is-prop-valued expᴸ-order
 expᴸ-order-is-prop-valued (l , _) (l' , _) =
  lex-prop-valued
   (underlying-order (α ×ₒ β))
   (underlying-type-is-set fe (α ×ₒ β))
   (Prop-valuedness (α ×ₒ β))
   (irrefl (α ×ₒ β))
   l
   l'

\end{code}

\begin{code}

 expᴸ-order-is-transitive : is-transitive expᴸ-order
 expᴸ-order-is-transitive (l , _) (l' , _) (l'' , _) p q =
  lex-transitive (underlying-order (α ×ₒ β)) (Transitivity (α ×ₒ β)) l l' l'' p q

 expᴸ-order-is-wellfounded : is-well-founded expᴸ-order
 expᴸ-order-is-wellfounded (l , δ) =
  acc-lex-decr-to-acc-exponential l δ
   (lex-wellfounded (underlying-order (α ×ₒ β))
                    (Transitivity (α ×ₒ β))
                    (Well-foundedness (α ×ₒ β))
                    (expᴸ-list (l , δ) , expᴸ-list-is-decreasing (l , δ)))
  where
   acc-lex-decr-to-acc-exponential
    : (l : List ⟨ α ×ₒ β ⟩)
    → (δ : is-decreasing-pr₂ l)
    → is-accessible (lex-decr (underlying-order (α ×ₒ β)))
                    ((l , expᴸ-list-is-decreasing (l , δ)))
    → is-accessible expᴸ-order (l , δ)
   acc-lex-decr-to-acc-exponential l δ (acc h) =
    acc (λ (l' , ε) u → acc-lex-decr-to-acc-exponential l' ε
                         (h (l' ,  expᴸ-list-is-decreasing (l' , ε)) u))

\end{code}

\begin{code}

 private
  R = underlying-order (α ×ₒ β)
  _≼_ = extensional-po expᴸ-order

 is-decreasing-pr₂-swap-tails
  : (l l' : List ⟨ α ×ₒ β ⟩) (x : ⟨ α ×ₒ β ⟩)
  → is-decreasing-pr₂ (x ∷ l)
  → is-decreasing-pr₂ l'
  → lex R l' l
  → is-decreasing-pr₂ (x ∷ l')
 is-decreasing-pr₂-swap-tails l l' x δ ε []-lex = sing-decr
 is-decreasing-pr₂-swap-tails ((a , b) ∷ l) ((a' , b') ∷ l') (a₀ , b₀) δ ε
  (head-lex (inl u)) = many-decr (Transitivity β b' b b₀ u
                                   (heads-are-decreasing-pr₂ a₀ a δ))
                                 ε
 is-decreasing-pr₂-swap-tails ((a , b) ∷ l) ((a' , b') ∷ l') (a₀ , b₀) δ ε
  (head-lex (inr (refl , u))) = many-decr (heads-are-decreasing-pr₂ a₀ a δ) ε
 is-decreasing-pr₂-swap-tails ((a , b) ∷ l) ((a' , b') ∷ l') (a₀ , b₀) δ ε
  (tail-lex refl u) = many-decr (heads-are-decreasing-pr₂ a₀ a δ) ε

 private
  no-≼-[] : (x : ⟨ α ×ₒ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
            (δ : is-decreasing-pr₂ (x ∷ l))
          → ¬ (((x ∷ l) , δ) ≼ ([] , []-decr))
  no-≼-[] x l δ h =
   𝟘-elim
    (lex-irreflexive R (Irreflexivity (α ×ₒ β)) [] (h ([] , []-decr) []-lex))

  tails-≼
   : (l l' : List ⟨ α ×ₒ β ⟩) (x : ⟨ α ×ₒ β ⟩)
     (δ : is-decreasing-pr₂ (x ∷ l))
     (ε : is-decreasing-pr₂ (x ∷ l'))
   → ((x ∷ l) , δ) ≼ ((x ∷ l') , ε)
   → (l , tail-is-decreasing-pr₂ x δ) ≼ (l' , tail-is-decreasing-pr₂ x ε)
  tails-≼ l l' x δ ε h (l₀ , δ₀) u = g hₓ
   where
    hₓ : lex R (x ∷ l₀) (x ∷ l')
    hₓ = h ((x ∷ l₀) , is-decreasing-pr₂-swap-tails l l₀ x δ δ₀ u)
           (tail-lex refl u)
    g : lex R (x ∷ l₀) (x ∷ l') → lex R l₀ l'
    g (head-lex   r) = 𝟘-elim (Irreflexivity (α ×ₒ β) x r)
    g (tail-lex _ k) = k

 expᴸ-order-is-extensional' : (l₁ l₂ : List ⟨ α ×ₒ β ⟩)
                              (δ₁ : is-decreasing-pr₂ l₁)
                              (δ₂ : is-decreasing-pr₂ l₂)
                            → (l₁ , δ₁) ≼ (l₂ , δ₂)
                            → (l₂ , δ₂) ≼ (l₁ , δ₁)
                            → l₁ ＝ l₂
 expᴸ-order-is-extensional' [] [] δ₁ δ₂ u v = refl
 expᴸ-order-is-extensional' [] (y ∷ l₂) δ₁ δ₂ u h₂ =
  𝟘-elim (no-≼-[] y l₂ δ₂ h₂)
 expᴸ-order-is-extensional' (x ∷ l₁) [] δ₁ δ₂ h₁ h₂ =
  𝟘-elim (no-≼-[] x l₁ δ₁ h₁)
 expᴸ-order-is-extensional' (x ∷ []) (y ∷ []) δ₁ δ₂ h₁ h₂ =
  ap [_] (Extensionality (α ×ₒ β) x y I₁ I₂)
   where
    I₁ : x ≼⟨ α ×ₒ β ⟩ y
    I₁ z u = κ c
     where
      c : [ z ] ≺⟨List (α ×ₒ β) ⟩ [ y ]
      c = h₁ ([ z ] , sing-decr) (head-lex u)
      κ : [ z ] ≺⟨List (α ×ₒ β) ⟩ [ y ] → z ≺⟨ α ×ₒ β ⟩ y
      κ (head-lex v) = v
    I₂ : y ≼⟨ α ×ₒ β ⟩ x
    I₂ z u = κ c
     where
      c : [ z ] ≺⟨List (α ×ₒ β) ⟩ [ x ]
      c = h₂ ([ z ] , sing-decr) (head-lex u)
      κ : [ z ] ≺⟨List (α ×ₒ β) ⟩ [ x ] → z ≺⟨ α ×ₒ β ⟩ x
      κ (head-lex v) = v
 expᴸ-order-is-extensional' (x ∷ []) (y ∷ y' ∷ l₂) δ₁ δ₂ h₁ h₂ =
  𝟘-elim (lex-irreflexive R (Irreflexivity (α ×ₒ β)) (y ∷ y' ∷ l₂) III)
   where
    I : y ≺⟨ α ×ₒ β ⟩ x
    I = κ (h₂ ([ y ] , sing-decr) (tail-lex refl []-lex))
     where
      κ :  [ y ] ≺⟨List (α ×ₒ β) ⟩ [ x ] → y ≺⟨ α ×ₒ β ⟩ x
      κ (head-lex u) = u
    II : (y ∷ y' ∷ l₂) ≺⟨List (α ×ₒ β) ⟩ [ x ]
    II = head-lex I
    III : (y ∷ y' ∷ l₂) ≺⟨List (α ×ₒ β) ⟩ (y ∷ y' ∷ l₂)
    III = h₁ ((y ∷ y' ∷ l₂) , δ₂) II
 expᴸ-order-is-extensional' (x ∷ x' ∷ l₁) (y ∷ []) δ₁ δ₂ h₁ h₂ =
  𝟘-elim (lex-irreflexive R (Irreflexivity (α ×ₒ β)) (x ∷ x' ∷ l₁) III)
   where
    I : x ≺⟨ α ×ₒ β ⟩ y
    I = κ (h₁ ([ x ] , sing-decr) (tail-lex refl []-lex))
     where
      κ :  [ x ] ≺⟨List (α ×ₒ β) ⟩ [ y ] → x ≺⟨ α ×ₒ β ⟩ y
      κ (head-lex u) = u
    II : (x ∷ x' ∷ l₁) ≺⟨List (α ×ₒ β) ⟩ [ y ]
    II = head-lex I
    III : (x ∷ x' ∷ l₁) ≺⟨List (α ×ₒ β) ⟩ (x ∷ x' ∷ l₁)
    III = h₂ ((x ∷ x' ∷ l₁) , δ₁) II
 expᴸ-order-is-extensional' (x ∷ x' ∷ l₁) (y ∷ y' ∷ l₂) δ₁ δ₂ h₁ h₂ =
  ap₂ _∷_ I
   (expᴸ-order-is-extensional'
     (x' ∷ l₁) (y' ∷ l₂)
     (tail-is-decreasing-pr₂ x {x' ∷ l₁} δ₁)
     (tail-is-decreasing-pr₂ y {y' ∷ l₂} δ₂)
     (k₁ I)
     (k₂ I))
  where
   I : x ＝ y
   I = κ (h₁ ([ x ] , sing-decr) (tail-lex refl []-lex))
         (h₂ ([ y ] , sing-decr) (tail-lex refl []-lex))
    where
     κ : [ x ] ≺⟨List (α ×ₒ β) ⟩ (y ∷ y' ∷ l₂)
       → [ y ] ≺⟨List (α ×ₒ β) ⟩ (x ∷ x' ∷ l₁)
       → x ＝ y
     κ (head-lex u) (head-lex v) =
      𝟘-elim (Irreflexivity (α ×ₒ β) x (Transitivity (α ×ₒ β) x y x u v))
     κ (head-lex u) (tail-lex refl v) = refl
     κ (tail-lex refl u) (head-lex v) = refl
     κ (tail-lex refl u) (tail-lex e v) = refl
   k₁ : x ＝ y
     → ((x' ∷ l₁) , tail-is-decreasing-pr₂ x {x' ∷ l₁} δ₁)
       ≼ ((y' ∷ l₂) , tail-is-decreasing-pr₂ y {y' ∷ l₂} δ₂)
   k₁ refl = tails-≼ (x' ∷ l₁) (y' ∷ l₂) x δ₁ δ₂ h₁
   k₂ : x ＝ y
     → ((y' ∷ l₂) , tail-is-decreasing-pr₂ y {y' ∷ l₂} δ₂)
       ≼ ((x' ∷ l₁) , tail-is-decreasing-pr₂ x {x' ∷ l₁} δ₁)
   k₂ refl = tails-≼ (y' ∷ l₂) (x' ∷ l₁) x δ₂ δ₁ h₂

 expᴸ-order-is-extensional : is-extensional expᴸ-order
 expᴸ-order-is-extensional (l₁ , δ₁) (l₂ , δ₂) u v =
  to-expᴸ-＝ (expᴸ-order-is-extensional' l₁ l₂ δ₁ δ₂ u v)

\end{code}

\begin{code}

expᴸ : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
expᴸ α β = ⟨expᴸ⟩ α β
           , expᴸ-order α β
           , expᴸ-order-is-prop-valued α β
           , expᴸ-order-is-wellfounded α β
           , expᴸ-order-is-extensional α β
           , expᴸ-order-is-transitive α β

exponentiationᴸ : (α : Ordinal 𝓤)
                → has-trichotomous-least-element α
                → Ordinal 𝓥
                → Ordinal (𝓤 ⊔ 𝓥)
exponentiationᴸ α h = expᴸ (α ⁺[ h ])

\end{code}

\begin{code}

module _
        (α : Ordinal 𝓤)
        (β : Ordinal 𝓥)
       where

 expᴸ-⊥ : ⟨ expᴸ α β ⟩
 expᴸ-⊥ = [] , []-decr

 expᴸ-↓-⊥ : expᴸ α β ↓ expᴸ-⊥ ＝ 𝟘ₒ
 expᴸ-↓-⊥ = ⊲-is-extensional (expᴸ α β ↓ expᴸ-⊥) 𝟘ₒ I II
  where
   I : (expᴸ α β ↓ expᴸ-⊥) ≼OO 𝟘ₒ
   I = to-≼ {_} {expᴸ α β ↓ expᴸ-⊥} {𝟘ₒ} h
    where
     h : (l : ⟨ expᴸ α β ↓ expᴸ-⊥ ⟩)
       → ((expᴸ α β ↓ expᴸ-⊥) ↓ l) ⊲ 𝟘ₒ
     h ()
   II : 𝟘ₒ ≼OO (expᴸ α β ↓ expᴸ-⊥)
   II = 𝟘ₒ-least (expᴸ α β ↓ expᴸ-⊥)

 expᴸ-↓-⊥' : {δ : is-decreasing-pr₂ α β []}
           → expᴸ α β ↓ ([] , δ) ＝ 𝟘ₒ
 expᴸ-↓-⊥' {δ} = expᴸ α β ↓ ([] , δ) ＝⟨ ap (expᴸ α β ↓_) (to-expᴸ-＝ α β refl) ⟩
                 expᴸ α β ↓ expᴸ-⊥   ＝⟨ expᴸ-↓-⊥ ⟩
                 𝟘ₒ                  ∎

 expᴸ-is-positive : 𝟘ₒ ⊲ expᴸ α β
 expᴸ-is-positive = expᴸ-⊥ , (expᴸ-↓-⊥ ⁻¹)

 expᴸ-has-least : 𝟙ₒ ⊴ expᴸ α β
 expᴸ-has-least =
  to-⊴ 𝟙ₒ (expᴸ α β) (λ ⋆ → transport⁻¹ (_⊲ expᴸ α β) 𝟙ₒ-↓ expᴸ-is-positive)

\end{code}

\begin{code}

 expᴸ-is-trichotomous-least : is-trichotomous-least (expᴸ α β) expᴸ-⊥
 expᴸ-is-trichotomous-least ([] , []-decr) = inl refl
 expᴸ-is-trichotomous-least ((x ∷ l) , δ) = inr []-lex

 expᴸ-has-trichotomous-least-element : has-trichotomous-least-element (expᴸ α β)
 expᴸ-has-trichotomous-least-element = expᴸ-⊥ , expᴸ-is-trichotomous-least

\end{code}

Characterizing initial segments of expᴸ α β

\begin{code}

module _
        (α : Ordinal 𝓤)
        (β : Ordinal 𝓥)
        (b₀ : ⟨ β ⟩)
       where

 expᴸ-segment-inclusion-list : List ⟨ α ×ₒ (β ↓ b₀) ⟩ → List ⟨ α ×ₒ β ⟩
 expᴸ-segment-inclusion-list = map (λ (a , (b , u)) → (a , b))

 expᴸ-segment-inclusion-list-preserves-decreasing-pr₂ :
    (l : List ⟨ α ×ₒ (β ↓ b₀) ⟩)
  → is-decreasing-pr₂ α (β ↓ b₀) l
  → is-decreasing-pr₂ α β (expᴸ-segment-inclusion-list l)
 expᴸ-segment-inclusion-list-preserves-decreasing-pr₂ [] _ = []-decr
 expᴸ-segment-inclusion-list-preserves-decreasing-pr₂
  ((a , b) ∷ []) _ = sing-decr
 expᴸ-segment-inclusion-list-preserves-decreasing-pr₂
  ((a , b) ∷ (a' , b') ∷ l) (many-decr u δ) =
   many-decr
    u
    (expᴸ-segment-inclusion-list-preserves-decreasing-pr₂ ((a , b') ∷ l) δ)

 extended-expᴸ-segment-inclusion-is-decreasing-pr₂ :
    (l : List ⟨ α ×ₒ (β ↓ b₀) ⟩) (a₀ : ⟨ α ⟩)
  → is-decreasing-pr₂ α (β ↓ b₀) l
  → is-decreasing-pr₂ α β ((a₀ , b₀) ∷ expᴸ-segment-inclusion-list l)
 extended-expᴸ-segment-inclusion-is-decreasing-pr₂ [] a₀ δ = sing-decr
 extended-expᴸ-segment-inclusion-is-decreasing-pr₂ ((a , (b , u)) ∷ l) a₀ δ =
  many-decr
   u
   (expᴸ-segment-inclusion-list-preserves-decreasing-pr₂ (a , b , u ∷ l) δ)

 predecessor-of-expᴸ-segment-inclusion-lemma :
    (a : ⟨ α ⟩) {b : ⟨ β ⟩}
    {l₁ : List ⟨ α ×ₒ β ⟩}
    {l₂ : List ⟨ α ×ₒ (β ↓ b₀) ⟩}
  → ((a , b) ∷ l₁) ≺⟨List (α ×ₒ β) ⟩ expᴸ-segment-inclusion-list l₂
  → b ≺⟨ β ⟩ b₀
 predecessor-of-expᴸ-segment-inclusion-lemma a {b} {l₁} {(a' , (b' , u)) ∷ l₂}
  (head-lex (inl v)) = Transitivity β b b' b₀ v u
 predecessor-of-expᴸ-segment-inclusion-lemma a {b} {l₁} {(a' , (b' , u)) ∷ l₂}
  (head-lex (inr (refl , v))) = u
 predecessor-of-expᴸ-segment-inclusion-lemma a {b} {l₁} {(a' , (b' , u)) ∷ l₂}
  (tail-lex refl v) = u

 expᴸ-segment-inclusion-list-lex :
    {l₁ : List ⟨ α ×ₒ (β ↓ b₀) ⟩}
    {a : ⟨ α ⟩} {l : List ⟨ α ×ₒ β ⟩}
  → expᴸ-segment-inclusion-list l₁ ≺⟨List (α ×ₒ β ) ⟩ ((a , b₀) ∷ l)
 expᴸ-segment-inclusion-list-lex {[]} = []-lex
 expᴸ-segment-inclusion-list-lex {((a' , (b' , u)) ∷ l₁)} = head-lex (inl u)

 expᴸ-segment-inclusion : ⟨ expᴸ α (β ↓ b₀) ⟩ → ⟨ expᴸ α β ⟩
 expᴸ-segment-inclusion (l , δ) =
  expᴸ-segment-inclusion-list l ,
  expᴸ-segment-inclusion-list-preserves-decreasing-pr₂ l δ

 extended-expᴸ-segment-inclusion : (l : ⟨ expᴸ α (β ↓ b₀) ⟩) (a₀ : ⟨ α ⟩)
                                 → ⟨ expᴸ α β ⟩
 extended-expᴸ-segment-inclusion (l , δ) a₀ =
  ((a₀ , b₀) ∷ expᴸ-segment-inclusion-list l) ,
  extended-expᴸ-segment-inclusion-is-decreasing-pr₂ l a₀ δ

\end{code}

\begin{code}

 expᴸ-segment-inclusion-list-is-order-preserving :
    (l l' : List ⟨ α ×ₒ (β ↓ b₀) ⟩)
  → l ≺⟨List (α ×ₒ (β ↓ b₀)) ⟩ l'
  → expᴸ-segment-inclusion-list l
    ≺⟨List (α ×ₒ β) ⟩ expᴸ-segment-inclusion-list l'
 expᴸ-segment-inclusion-list-is-order-preserving [] (_ ∷ _) _ = []-lex
 expᴸ-segment-inclusion-list-is-order-preserving
  (a , b ∷ l) (a' , b' ∷ l') (head-lex (inl u)) = head-lex (inl u)
 expᴸ-segment-inclusion-list-is-order-preserving
  (a , b ∷ l) (a' , b' ∷ l') (head-lex (inr (refl , u))) =
   head-lex (inr (refl , u))
 expᴸ-segment-inclusion-list-is-order-preserving
  (a , b ∷ l) (a' , b' ∷ l') (tail-lex refl u) =
   tail-lex refl (expᴸ-segment-inclusion-list-is-order-preserving l l' u)

 expᴸ-segment-inclusion-list-is-order-reflecting :
    (l l' : List ⟨ α ×ₒ (β ↓ b₀) ⟩)
  → expᴸ-segment-inclusion-list l
    ≺⟨List (α ×ₒ β) ⟩ expᴸ-segment-inclusion-list l'
  → l ≺⟨List (α ×ₒ (β ↓ b₀)) ⟩ l'
 expᴸ-segment-inclusion-list-is-order-reflecting [] (_ ∷ _) _ = []-lex
 expᴸ-segment-inclusion-list-is-order-reflecting
  (a , b ∷ l) (a' , b' ∷ l') (head-lex (inl u)) = head-lex (inl u)
 expᴸ-segment-inclusion-list-is-order-reflecting
  (a , b ∷ l) (a' , b' ∷ l') (head-lex (inr (refl , u))) =
   head-lex (inr ((segment-inclusion-lc β refl) , u))
 expᴸ-segment-inclusion-list-is-order-reflecting
  (a , b ∷ l) (a' , b' ∷ l') (tail-lex refl u) =
   tail-lex
    (ap (a ,_) (segment-inclusion-lc β refl))
    (expᴸ-segment-inclusion-list-is-order-reflecting l l' u)

 expᴸ-segment-inclusion-is-order-preserving :
  is-order-preserving (expᴸ α (β ↓ b₀)) (expᴸ α β) expᴸ-segment-inclusion
 expᴸ-segment-inclusion-is-order-preserving (l , δ) (l' , δ') =
  expᴸ-segment-inclusion-list-is-order-preserving l l'

 expᴸ-segment-inclusion-is-order-reflecting :
  is-order-reflecting (expᴸ α (β ↓ b₀)) (expᴸ α β) expᴸ-segment-inclusion
 expᴸ-segment-inclusion-is-order-reflecting (l , δ) (l' , δ') =
  expᴸ-segment-inclusion-list-is-order-reflecting l l'

\end{code}

\begin{code}

module _
        (α : Ordinal 𝓤)
        (β : Ordinal 𝓥)
        (a₀ : ⟨ α ⟩)
        (b₀ : ⟨ β ⟩)
       where

 expᴸ-tail-list : (l : List ⟨ α ×ₒ β ⟩)
                → is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l)
                → List ⟨ α ×ₒ (β ↓ b₀) ⟩
 expᴸ-tail-list [] _ = []
 expᴸ-tail-list ((a , b) ∷ l) δ = (a , (b , u)) ∷ (expᴸ-tail-list l ε)
  where
   u : b ≺⟨ β ⟩ b₀
   u = heads-are-decreasing-pr₂ α β a₀ a δ
   ε : is-decreasing-pr₂ α β (a₀ , b₀ ∷ l)
   ε = is-decreasing-pr₂-skip α β (a₀ , b₀) (a , b) δ

 expᴸ-tail-list-preserves-decreasing-pr₂ :
    (l : List ⟨ α ×ₒ β ⟩) (δ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l))
  → is-decreasing-pr₂ α (β ↓ b₀) (expᴸ-tail-list l δ)
 expᴸ-tail-list-preserves-decreasing-pr₂ [] _ = []-decr
 expᴸ-tail-list-preserves-decreasing-pr₂ ((a , b) ∷ []) δ = sing-decr
 expᴸ-tail-list-preserves-decreasing-pr₂ ((a , b) ∷ (a' , b') ∷ l) (many-decr u δ) =
  many-decr v (expᴸ-tail-list-preserves-decreasing-pr₂ ((a' , b') ∷ l) ε)
   where
    v : b' ≺⟨ β ⟩ b
    v = heads-are-decreasing-pr₂ α β a a' δ
    ε : is-decreasing-pr₂ α β (a₀ , b₀ ∷ a' , b' ∷ l)
    ε = many-decr
         (Transitivity β b' b b₀ v u)
         (tail-is-decreasing-pr₂ α β (a , b) {a , b' ∷ l} δ)

 expᴸ-tail : (l : List ⟨ α ×ₒ β ⟩)
           → is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l)
           → ⟨ expᴸ α (β ↓ b₀) ⟩
 expᴸ-tail l δ = expᴸ-tail-list l δ ,
                 (expᴸ-tail-list-preserves-decreasing-pr₂ l δ)

 expᴸ-tail-is-order-preserving :
    {l₁ l₂ : List ⟨ α ×ₒ β ⟩}
    (δ₁ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l₁))
    (δ₂ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l₂))
  → l₁ ≺⟨List (α ×ₒ β) ⟩ l₂
  → expᴸ-tail l₁ δ₁ ≺⟨ expᴸ α (β ↓ b₀) ⟩ expᴸ-tail l₂ δ₂
 expᴸ-tail-is-order-preserving {[]} {(_ ∷ l₂)} δ₁ δ₂ _ = []-lex
 expᴸ-tail-is-order-preserving {((a , b) ∷ l₁)} {((a' , b') ∷ l₂)} δ₁ δ₂
  (head-lex (inl u)) = head-lex (inl u)
 expᴸ-tail-is-order-preserving {((a , b) ∷ l₁)} {((a' , b') ∷ l₂)} δ₁ δ₂
  (head-lex (inr (refl , u))) =
   head-lex (inr ((segment-inclusion-lc β refl) , u))
 expᴸ-tail-is-order-preserving {((a , b) ∷ l₁)} {((a' , b') ∷ l₂)} δ₁ δ₂
  (tail-lex refl u) = tail-lex
                       (ap (a ,_) (segment-inclusion-lc β refl))
                       (expᴸ-tail-is-order-preserving
                         (is-decreasing-pr₂-skip α β (a₀ , b₀) (a , b) δ₁)
                         (is-decreasing-pr₂-skip α β (a₀ , b₀) (a , b) δ₂)
                         u)

 expᴸ-tail-section-of-expᴸ-segment-inclusion' :
    (l : List ⟨ α ×ₒ β ⟩) (δ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l))
  → expᴸ-list α β (expᴸ-segment-inclusion α β b₀ (expᴸ-tail l δ)) ＝ l
 expᴸ-tail-section-of-expᴸ-segment-inclusion' [] _ = refl
 expᴸ-tail-section-of-expᴸ-segment-inclusion' ((a , b) ∷ l) δ =
  ap ((a , b) ∷_)
     (expᴸ-tail-section-of-expᴸ-segment-inclusion' l
       (is-decreasing-pr₂-skip α β (a₀ , b₀) (a , b) δ))

 expᴸ-tail-section-of-expᴸ-segment-inclusion :
    (l : List ⟨ α ×ₒ β ⟩)
    {δ : is-decreasing-pr₂ α β ((a₀ , b₀) ∷ l)}
    {ε : is-decreasing-pr₂ α β l}
  → expᴸ-segment-inclusion α β b₀ (expᴸ-tail l δ) ＝ (l , ε)
 expᴸ-tail-section-of-expᴸ-segment-inclusion l {δ} =
  to-expᴸ-＝ α β (expᴸ-tail-section-of-expᴸ-segment-inclusion' l δ)

 expᴸ-segment-inclusion-section-of-expᴸ-tail' :
    (l : List ⟨ α ×ₒ (β ↓ b₀) ⟩)
    (δ : is-decreasing-pr₂ α (β ↓ b₀) l)
    {ε : is-decreasing-pr₂ α β (a₀ , b₀ ∷ expᴸ-segment-inclusion-list α β b₀ l)}
  → expᴸ-list α (β ↓ b₀) (expᴸ-tail (expᴸ-segment-inclusion-list α β b₀ l) ε)
    ＝ l
 expᴸ-segment-inclusion-section-of-expᴸ-tail' [] _ = refl
 expᴸ-segment-inclusion-section-of-expᴸ-tail' ((a , (b , u)) ∷ l) δ =
  ap₂ _∷_
   (ap (a ,_) (segment-inclusion-lc β refl))
   (expᴸ-segment-inclusion-section-of-expᴸ-tail'
     l
     (tail-is-decreasing-pr₂ α (β ↓ b₀) (a , (b , u)) δ))

 expᴸ-segment-inclusion-section-of-expᴸ-tail :
    (l : List ⟨ α ×ₒ (β ↓ b₀) ⟩)
    (δ : is-decreasing-pr₂ α (β ↓ b₀) l)
    {ε : is-decreasing-pr₂ α β (a₀ , b₀ ∷ expᴸ-segment-inclusion-list α β b₀ l)}
  → expᴸ-tail (expᴸ-segment-inclusion-list α β b₀ l) ε ＝ l , δ
 expᴸ-segment-inclusion-section-of-expᴸ-tail l δ =
  to-expᴸ-＝ α (β ↓ b₀) (expᴸ-segment-inclusion-section-of-expᴸ-tail' l δ)

\end{code}

\begin{code}

expᴸ-segment-inclusion-is-simulation :
   (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b₀ : ⟨ β ⟩)
 → is-simulation (expᴸ α (β ↓ b₀)) (expᴸ α β) (expᴸ-segment-inclusion α β b₀)
expᴸ-segment-inclusion-is-simulation α β b₀ =
 order-preserving-and-reflecting-partial-surjections-are-simulations
  (expᴸ α (β ↓ b₀))
  (expᴸ α β)
  (expᴸ-segment-inclusion α β b₀)
  (expᴸ-segment-inclusion-is-order-preserving α β b₀)
  (expᴸ-segment-inclusion-is-order-reflecting α β b₀)
  I
  where
   I : (x : ⟨ expᴸ α (β ↓ b₀) ⟩) (y : ⟨ expᴸ α β ⟩)
     → y ≺⟨ expᴸ α β ⟩ expᴸ-segment-inclusion α β b₀ x
     → Σ x' ꞉ ⟨ expᴸ α (β ↓ b₀) ⟩ , expᴸ-segment-inclusion α β b₀ x' ＝ y
   I _ ([] , []-decr) _ = ([] , []-decr) , refl
   I _ (((a , b) ∷ l) , δ) u =
    expᴸ-tail α β a b₀ (a , b ∷ l) ε ,
    expᴸ-tail-section-of-expᴸ-segment-inclusion α β a b₀ (a , b ∷ l)
     where
      ε : is-decreasing-pr₂ α β (a , b₀ ∷ a , b ∷ l)
      ε = many-decr (predecessor-of-expᴸ-segment-inclusion-lemma α β b₀ a u) δ

expᴸ-segment-inclusion-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (b₀ : ⟨ β ⟩)
                         → expᴸ α (β ↓ b₀) ⊴ expᴸ α β
expᴸ-segment-inclusion-⊴ α β b₀ = expᴸ-segment-inclusion α β b₀ ,
                                  expᴸ-segment-inclusion-is-simulation α β b₀

\end{code}

\begin{code}

expᴸ-↓-cons-≃ₒ
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
   (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
 → expᴸ α β ↓ (((a , b) ∷ l) , δ)
   ≃ₒ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))
      +ₒ (expᴸ α (β ↓ b) ↓ expᴸ-tail α β a b l δ)
expᴸ-↓-cons-≃ₒ {𝓤} {𝓥} α β a b l δ =
 f , f-is-order-preserving ,
     (qinvs-are-equivs f (g , gf-is-id , fg-is-id) ,
      g-is-order-preserving)
 where
  LHS RHS : Ordinal (𝓤 ⊔ 𝓥)
  LHS = expᴸ α β ↓ (((a , b) ∷ l) , δ)
  RHS = expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))
        +ₒ (expᴸ α (β ↓ b) ↓ expᴸ-tail α β a b l δ)

  f : ⟨ LHS ⟩ → ⟨ RHS ⟩
  f (([]               , _) , u) =
   inl (([] , []-decr) , inl ⋆)
  f ((((a' , b') ∷ l') , ε) , head-lex (inl u)) =
   inl (expᴸ-tail α β a b (a' , b' ∷ l') (many-decr u ε) , inl ⋆)
  f ((((a' , b ) ∷ l') , ε) , head-lex (inr (refl , u))) =
   inl (expᴸ-tail α β a b l' ε , inr (a' , u))
  f ((((a  , b ) ∷ l') , ε) , tail-lex refl u) =
   inr (expᴸ-tail α β a b l' ε , expᴸ-tail-is-order-preserving α β a b ε δ u)

  g : ⟨ RHS ⟩ → ⟨ LHS ⟩
  g (inl (l₁ , inl ⋆)) = expᴸ-segment-inclusion α β b l₁ ,
                         expᴸ-segment-inclusion-list-lex α β b
  g (inl (l₁ , inr (a₁ , s))) = extended-expᴸ-segment-inclusion α β b l₁ a₁ ,
                                head-lex (inr (refl , s))
  g (inr (l₁ , w)) = extended-expᴸ-segment-inclusion α β b l₁ a ,
                     tail-lex refl w'
   where
    ℓ : List ⟨ α ×ₒ (β ↓ b) ⟩
    ℓ = expᴸ-list α (β ↓ b) l₁
    w' : expᴸ-segment-inclusion-list α β b ℓ ≺⟨List (α ×ₒ β) ⟩ l
    w' = transport
          (λ - → expᴸ-segment-inclusion-list α β b ℓ ≺⟨List (α ×ₒ β) ⟩ -)
          (expᴸ-tail-section-of-expᴸ-segment-inclusion' α β a b l δ)
          (expᴸ-segment-inclusion-is-order-preserving α β b
            l₁
            (expᴸ-tail α β a b l δ)
            w)

  fg-is-id : f ∘ g ∼ id
  fg-is-id (inl (([] , []-decr) , inl ⋆)) = refl
  fg-is-id (inl ((((a' , b') ∷ l') , ε) , inl ⋆)) =
   ap (λ - → (inl (- , inl ⋆)))
      (to-expᴸ-＝ α (β ↓ b)
        (ap ((a' , b') ∷_)
            (expᴸ-segment-inclusion-section-of-expᴸ-tail' α β a b l'
              (tail-is-decreasing-pr₂ α (β ↓ b) (a , b') ε))))
  fg-is-id (inl (([] , []-decr) , inr x)) = refl
  fg-is-id (inl ((l'@(_ ∷ l₁) , ε) , inr (a' , s))) =
   ap (λ - → inl (- , inr (a' , s)))
      (expᴸ-segment-inclusion-section-of-expᴸ-tail α β a b l' ε)
  fg-is-id (inr ((l' , ε) , w)) =
   ap inr (segment-inclusion-lc
            (expᴸ α (β ↓ b))
            {expᴸ-tail α β a b l δ}
            (expᴸ-segment-inclusion-section-of-expᴸ-tail α β a b l' ε))

  gf-is-id : g ∘ f ∼ id
  gf-is-id (([] , []-decr) , []-lex) = refl
  gf-is-id ((((a' , b') ∷ l') , ε) , head-lex (inl u)) =
   segment-inclusion-lc
    (expᴸ α β)
    {(a , b ∷ l) , δ}
    (expᴸ-tail-section-of-expᴸ-segment-inclusion α β a b (a' , b' ∷ l'))
  gf-is-id ((((a' , b) ∷ l') , ε) , head-lex (inr (refl , u))) =
   segment-inclusion-lc
    (expᴸ α β)
    {(a , b ∷ l) , δ}
    (to-expᴸ-＝ α β
      (ap ((a' , b) ∷_)
          (expᴸ-tail-section-of-expᴸ-segment-inclusion' α β a b l' ε)))
  gf-is-id ((((a , b) ∷ l') , ε) , tail-lex refl u) =
   segment-inclusion-lc
    (expᴸ α β)
    {(a , b ∷ l) , δ}
    (to-expᴸ-＝ α β
      (ap ((a , b) ∷_)
          (expᴸ-tail-section-of-expᴸ-segment-inclusion' α β a b l' ε)))

  g-is-order-preserving : is-order-preserving RHS LHS g
  g-is-order-preserving (inl (l , inl ⋆)) (inl (l' , inl ⋆)) (inr (refl , u)) =
   expᴸ-segment-inclusion-is-order-preserving α β b l l' u
  g-is-order-preserving (inl (l , inl ⋆)) (inl (l' , inr (a' , j))) u =
   expᴸ-segment-inclusion-list-lex α β b
  g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inl ⋆))
                        (inr (e , u)) = 𝟘-elim (+disjoint (e ⁻¹))
  g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inr (a'' , j)))
                        (inl u) = head-lex (inr (refl , u))
  g-is-order-preserving (inl (l , inr (a' , i))) (inl (l' , inr (a'' , j)))
                        (inr (refl , v)) =
   tail-lex refl (expᴸ-segment-inclusion-is-order-preserving α β b l l' v)
  g-is-order-preserving (inl (l , inl ⋆)) (inr (l' , v)) _ =
   expᴸ-segment-inclusion-list-lex α β b
  g-is-order-preserving (inl (l , inr (a' , i))) (inr (l' , v)) _ =
   head-lex (inr (refl , i))
  g-is-order-preserving (inr (l , v)) (inr (l' , v')) u =
   tail-lex refl (expᴸ-segment-inclusion-is-order-preserving α β b l l' u)

  f-is-order-preserving : is-order-preserving LHS RHS f
  f-is-order-preserving (([] , δ₁) , u)
                        (((_ ∷ l') , δ₂) , head-lex (inl v)) w =
   inr (refl , []-lex)
  f-is-order-preserving (([] , δ₁) , u)
                        (((_ ∷ l') , δ₂) , head-lex (inr (refl , v))) w = inl ⋆
  f-is-order-preserving (([] , δ₁) , u)
                        (((_ ∷ l') , δ₂) , tail-lex refl v) w = ⋆

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inl u))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inl w)) = inr (refl , (head-lex (inl w)))
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inl u))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inr (refl , w))) =
   inr (refl , (head-lex (inr ((segment-inclusion-lc β refl) , w))))
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inl u))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (tail-lex refl w) =
   inr (refl , tail-lex
                (ap (a₁ ,_) (segment-inclusion-lc β refl))
                (expᴸ-tail-is-order-preserving α β a b _ _ w))

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inl u))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v))) w = inl ⋆
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inl u))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , tail-lex refl v) w = ⋆

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inl w)) =
   𝟘-elim (irrefl β b₁ (Transitivity β b₁ b₂ b₁ w v))
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inr (refl , w))) = 𝟘-elim (irrefl β b₁ v)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (tail-lex refl w) = 𝟘-elim (irrefl β b₁ v)

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (head-lex (inl w)) = 𝟘-elim (irrefl β b₁ w)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (head-lex (inr (e , w))) = inl w
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (tail-lex e w) =
   inr (ap inr (segment-inclusion-lc α (ap pr₁ e)) ,
        expᴸ-tail-is-order-preserving α β a b δ₁ δ₂ w)

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , head-lex (inr (refl , u)))
                        (((a₂ , b₂ ∷ l₂) , δ₂) , tail-lex refl v) w = ⋆

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inl w)) =
   𝟘-elim (irrefl β b₁ (Transitivity β b₁ b₂ b₁ w v))
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (head-lex (inr (refl , w))) = 𝟘-elim (irrefl β b₁ v)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inl v))
                        (tail-lex refl w) = 𝟘-elim (irrefl β b₁ v)

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (head-lex (inl w)) = 𝟘-elim (irrefl β b₁ w)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (head-lex (inr (e , w))) =
   𝟘-elim (irrefl α a₁ (Transitivity α a₁ a₂ a₁ w v))
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , head-lex (inr (refl , v)))
                        (tail-lex e w) =
   𝟘-elim (irrefl α a₁ (transport⁻¹ (λ - → - ≺⟨ α ⟩ a₁) (ap pr₁ e) v))

  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , tail-lex refl v)
                        (head-lex (inl w)) = 𝟘-elim (irrefl β b₁ w)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , tail-lex refl v)
                        (head-lex (inr (e , w))) = 𝟘-elim (irrefl α a₁ w)
  f-is-order-preserving (((a₁ , b₁ ∷ l₁) , δ₁) , tail-lex refl u)
                        (((a₂ , b₂ ∷ l₂) , δ₂) , tail-lex refl v) (tail-lex e w) =
   expᴸ-tail-is-order-preserving α β a₁ b₁ δ₁ δ₂ w

\end{code}

\begin{code}

expᴸ-↓-cons-≃ₒ'
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : ⟨ expᴸ α (β ↓ b) ⟩)
 → expᴸ α β ↓ extended-expᴸ-segment-inclusion α β b l a
   ≃ₒ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l)
expᴸ-↓-cons-≃ₒ' α β a b (l , δ) =
 transport
  (λ - → LHS ≃ₒ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ -))
  I
  II
   where
    LHS = expᴸ α β ↓ extended-expᴸ-segment-inclusion α β b (l , δ) a
    ε : is-decreasing-pr₂ α β (a , b ∷ expᴸ-segment-inclusion-list α β b l)
    ε = extended-expᴸ-segment-inclusion-is-decreasing-pr₂ α β b l a δ
    l' : List ⟨ α ×ₒ β ⟩
    l' = expᴸ-segment-inclusion-list α β b l

    I : expᴸ-tail α β a b l' ε ＝ (l , δ)
    I = expᴸ-segment-inclusion-section-of-expᴸ-tail α β a b l δ

    II : LHS ≃ₒ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))
                +ₒ (expᴸ α (β ↓ b) ↓ expᴸ-tail α β a b l' ε)
    II = expᴸ-↓-cons-≃ₒ α β a b (expᴸ-segment-inclusion-list α β b l) ε

\end{code}

\begin{code}

expᴸ-↓-cons
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : List ⟨ α ×ₒ β ⟩)
   (δ : is-decreasing-pr₂ α β ((a , b) ∷ l))
 → expᴸ α β ↓ (((a , b) ∷ l) , δ)
   ＝ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a))
      +ₒ (expᴸ α (β ↓ b) ↓ expᴸ-tail α β a b l δ)
expᴸ-↓-cons α β a b l δ = eqtoidₒ (ua _) fe' _ _ (expᴸ-↓-cons-≃ₒ α β a b l δ)

expᴸ-↓-cons'
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (a : ⟨ α ⟩) (b : ⟨ β ⟩) (l : ⟨ expᴸ α (β ↓ b) ⟩)
 → expᴸ α β ↓ extended-expᴸ-segment-inclusion α β b l a
   ＝ expᴸ α (β ↓ b) ×ₒ (𝟙ₒ +ₒ (α ↓ a)) +ₒ (expᴸ α (β ↓ b) ↓ l)
expᴸ-↓-cons' α β a b l = eqtoidₒ (ua _) fe' _ _ (expᴸ-↓-cons-≃ₒ' α β a b l)

\end{code}