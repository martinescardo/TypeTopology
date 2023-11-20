Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence

module Ordinals.Exponentiation
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
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
open import MLTT.Spartan
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


data lex {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) : List X → List X → 𝓤 ⊔ 𝓥 ̇  where
 []-lex : {y : X}{ys : List X} → lex R [] (y ∷ ys)
 head-lex : {x y : X}{xs ys : List X} → R x y → lex R (x ∷ xs) (y ∷ ys)
 tail-lex : {x y : X}{xs ys : List X} → x ＝ y → lex R xs ys → lex R (x ∷ xs) (y ∷ ys)

lex-for-ordinal : (α : Ordinal 𝓤) → List ⟨ α ⟩ → List ⟨ α ⟩ → 𝓤 ̇
lex-for-ordinal α = lex (underlying-order α)

syntax lex-for-ordinal α xs ys = xs ≺⟨List α ⟩ ys

module _ {X : 𝓤 ̇  } (R : X → X → 𝓥 ̇  ) where

 lex-transitive : is-transitive R → is-transitive (lex R)
 lex-transitive tr [] (y ∷ ys) (z ∷ zs) []-lex (head-lex q) = []-lex
 lex-transitive tr [] (y ∷ ys) (z ∷ zs) []-lex (tail-lex r q) = []-lex
 lex-transitive tr (x ∷ xs) (y ∷ ys) (z ∷ zs) (head-lex p) (head-lex q) = head-lex (tr x y z p q)
 lex-transitive tr (x ∷ xs) (y ∷ ys) (.y ∷ zs) (head-lex p) (tail-lex refl q) = head-lex p
 lex-transitive tr (x ∷ xs) (.x ∷ ys) (z ∷ zs) (tail-lex refl p) (head-lex q) = head-lex q
 lex-transitive tr (x ∷ xs) (.x ∷ ys) (.x ∷ zs) (tail-lex refl p) (tail-lex refl q)
  = tail-lex refl (lex-transitive tr xs ys zs p q)

 []-lex-bot : is-bot (lex R) []
 []-lex-bot xs ()

 []-acc : is-accessible (lex R) []
 []-acc = acc (λ zs q → 𝟘-elim ([]-lex-bot _ q))

 data is-decreasing : List X → 𝓤 ⊔ 𝓥 ̇  where
  []-decr : is-decreasing []
  sing-decr : {x : X} → is-decreasing [ x ]
  many-decr : {x y : X}{xs : List X} → R y x → is-decreasing (y ∷ xs) → is-decreasing (x ∷ y ∷ xs)

 is-decreasing-tail : {x : X} {xs : List X} → is-decreasing (x ∷ xs) → is-decreasing xs
 is-decreasing-tail sing-decr = []-decr
 is-decreasing-tail (many-decr _ d) = d

 is-decreasing-heads : {x y : X} {xs : List X} → is-decreasing (x ∷ y ∷ xs) → R y x
 is-decreasing-heads (many-decr p _) = p

 DecreasingList : (𝓤 ⊔ 𝓥) ̇
 DecreasingList = Σ xs ꞉ List X , is-decreasing xs

 lex-decr : DecreasingList → DecreasingList → 𝓤 ⊔ 𝓥 ̇
 lex-decr (xs , _) (ys , _) = lex R xs ys

 []-acc-decr : {p : is-decreasing []} → is-accessible lex-decr ([] , p)
 []-acc-decr {[]-decr} = acc (λ xs q → 𝟘-elim ([]-lex-bot _ q))

 module _
   (tr : is-transitive R)

   where

  lex-decr-acc : (x : X) → is-accessible R x
               → (xs : List X) (δ : is-decreasing xs)
               → is-accessible lex-decr (xs , δ)
               → (ε : is-decreasing (x ∷ xs))
               → is-accessible lex-decr ((x ∷ xs) , ε)
  lex-decr-acc =
   transfinite-induction' R P ϕ
     where
      Q : X → DecreasingList → 𝓤 ⊔ 𝓥 ̇
      Q x (xs , _) = (ε' : is-decreasing (x ∷ xs)) → is-accessible lex-decr ((x ∷ xs) , ε')
      P : X → 𝓤 ⊔ 𝓥 ̇
      P x = (xs : List X) (δ : is-decreasing xs)
          → is-accessible lex-decr (xs , δ)
          → Q x (xs , δ)

      ϕ : (x : X) → ((y : X) → R y x → P y) → P x
      ϕ x IH xs δ β = transfinite-induction' lex-decr (Q x) (λ (xs , ε) → ϕ' xs ε) (xs , δ) β
       where
        ϕ' : (xs : List X) → (ε : is-decreasing xs)
           → ((ys : DecreasingList) → lex-decr ys (xs , ε) → Q x ys)
           → Q x (xs , ε)
        ϕ' xs _ IH₂ ε' = acc (λ (ys , ε) → g ys ε)
         where
          g : (ys : List X) → (ε : is-decreasing ys)
             → lex-decr (ys , ε) ((x ∷ xs) , ε')
             → is-accessible lex-decr (ys , ε)
          g [] ε p = []-acc-decr
          g (y ∷ []) ε (head-lex p) = IH y p [] []-decr []-acc-decr ε
          g (y ∷ z ∷ ys) ε (head-lex p) =
            IH y p (z ∷ ys) (is-decreasing-tail ε)
               (g (z ∷ ys) (is-decreasing-tail ε) (head-lex (tr z y x (is-decreasing-heads ε) p)))
               ε
          {-# CATCHALL #-}
          g (.x ∷ ys) ε (tail-lex refl l) = IH₂ (ys , is-decreasing-tail ε) l ε

  lex-wellfounded' : is-well-founded R
                   → (xs : List X) (δ : is-decreasing xs)
                   → is-accessible lex-decr (xs , δ)
  lex-wellfounded' wf [] δ = []-acc-decr
  lex-wellfounded' wf (x ∷ xs) δ =
   lex-decr-acc x (wf x) xs (is-decreasing-tail δ) (lex-wellfounded' wf xs (is-decreasing-tail δ)) δ

  lex-wellfounded : is-well-founded R → is-well-founded lex-decr
  lex-wellfounded wf (xs , δ) = lex-wellfounded' wf xs δ
{-
  lex-wellfounded wf ([] , []-decr) = []-acc-decr
  lex-wellfounded wf (.([ x ]) , sing-decr {x}) = acc g
   where
    h : is-accessible R x
    h = wf x
    g : (ys : DecreasingList)
      → lex-decr ys ([ x ] , sing-decr) → is-accessible lex-decr ys
    g (.[] , _) []-lex = []-acc-decr
    g ((y ∷ ys) , d) (head-lex p) = lex-decr-acc y (wf y) ys {!!} {!!} {!!}
  lex-wellfounded wf (.(_ ∷ _ ∷ _) , many-decr x dec) = {!!} -}

 -- this is not helpful below
 -- (do you also need transitivity?)
 lex-extensional : is-extensional R → is-extensional (lex R)
 lex-extensional = {!!}


-- can we get away with different universes like this?
[𝟙+_]^_ : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
[𝟙+ α ]^ β = (Σ xs ꞉ List ⟨ β ×ₒ α ⟩ , is-decreasing (underlying-order α) (map pr₂ xs)) , {!!} , {!!} , {!!}


-- prove that (1 + A) ^ X is an ordinal

-- End goal: prove it satisfies (0, succ, sup)-spec
