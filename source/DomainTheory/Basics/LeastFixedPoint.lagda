Tom de Jong, May 2019.
Refactored Dec 2021.

Least fixed points of Scott continuous maps.

The flag --lossy-unification significantly speeds up the
typechecking.
(https://agda.readthedocs.io/en/latest/language/lossy-unification.html)

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.LeastFixedPoint
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import UF.UniverseEmbedding
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Naturals.Properties
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order
open import Notation.Order

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Exponential pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥

module _ (𝓓 : DCPO⊥ {𝓤} {𝓣}) where

 iter : (n : ℕ) → ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ → ⟪ 𝓓 ⟫
 iter zero     f = ⊥ 𝓓
 iter (succ n) f = [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩ (iter n f)

 iter-is-monotone : (n : ℕ) → is-monotone ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) (iter n)
 iter-is-monotone zero     f g l = ⊥-is-least 𝓓 (iter zero g)
 iter-is-monotone (succ n) f g l = iter (succ n) f               ⊑⟪ 𝓓 ⟫[ ⦅1⦆ ]
                                   [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ g ⟩ (iter n f) ⊑⟪ 𝓓 ⟫[ ⦅2⦆ ]
                                   iter (succ n) g               ∎⟪ 𝓓 ⟫
  where
   ⦅1⦆ = l (iter n f)
   ⦅2⦆ = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) g (iter n f) (iter n g)
         (iter-is-monotone n f g l)

 n-family : {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫) (n : ℕ) → I → ⟪ 𝓓 ⟫
 n-family α n i = iter n (α i)

 n-family-is-directed : {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫)
                        (δ : is-Directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) α)
                        (n : ℕ) → is-Directed (𝓓 ⁻) (n-family α n)
 n-family-is-directed {I} α δ n =
   inhabited-if-Directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ) ⁻) α δ , ε
  where
   ε : is-Semidirected (𝓓 ⁻) (n-family α n)
   ε i j = ∥∥-functor h (semidirected-if-Directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) α δ i j)
    where
     h : (Σ k ꞉ I , (α i) ⊑⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ (α k) ×
                    (α j) ⊑⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ (α k))
       → Σ k ꞉ I , (n-family α n i) ⊑⟪ 𝓓 ⟫ (n-family α n k) ×
                   (n-family α n j) ⊑⟪ 𝓓 ⟫ (n-family α n k)
     h (k , l , m) = k , (iter-is-monotone n (α i) (α k) l) ,
                         (iter-is-monotone n (α j) (α k) m)

 double-∐-lemma : {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫)
                  (δ : is-Directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) α)
                  (n : ℕ)
                → ∐ (𝓓 ⁻) (pointwise-family-is-directed (𝓓 ⁻) (𝓓 ⁻) α δ
                          (∐ (𝓓 ⁻) (n-family-is-directed α δ n)))
                  ＝ ∐ (𝓓 ⁻) (n-family-is-directed α δ (succ n))
 double-∐-lemma {I} α δ n = antisymmetry (𝓓 ⁻) x y a b
  where
   ε : is-Directed (𝓓 ⁻) (pointwise-family (𝓓 ⁻) (𝓓 ⁻) α
        (∐ (𝓓 ⁻) (n-family-is-directed α δ n)))
   ε = (pointwise-family-is-directed (𝓓 ⁻) (𝓓 ⁻) α δ
        (∐ (𝓓 ⁻) (n-family-is-directed α δ n)))
   φ : (n : ℕ) → is-Directed (𝓓 ⁻) (n-family α n)
   φ n = n-family-is-directed α δ n

   x : ⟪ 𝓓 ⟫
   x = ∐ (𝓓 ⁻) ε
   y : ⟪ 𝓓 ⟫
   y = ∐ (𝓓 ⁻) (n-family-is-directed α δ (succ n))

   a : x ⊑⟪ 𝓓 ⟫ y
   a = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) ε y g
    where
     g : (i : I)
       → (pointwise-family (𝓓 ⁻) (𝓓 ⁻) α (∐ (𝓓 ⁻) (φ n)) i) ⊑⟪ 𝓓 ⟫ y
     g i = sup-is-lowerbound-of-upperbounds
            (underlying-order (𝓓 ⁻)) s y u
      where
       β : I → ⟪ 𝓓 ⟫
       β = [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ α i ⟩ ∘ (n-family α n)
       s : is-sup (underlying-order (𝓓 ⁻))
            (pointwise-family (𝓓 ⁻) (𝓓 ⁻) α (∐ (𝓓 ⁻) (φ n)) i) β
       s = continuity-of-function (𝓓 ⁻) (𝓓 ⁻) (α i) I (n-family α n) (φ n)
       u : (j : I) → β j ⊑⟨ 𝓓 ⁻ ⟩ y
       u j = ∥∥-rec (prop-valuedness (𝓓 ⁻) (β j) y) v
              (semidirected-if-Directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) α δ i j)
               where
         v : (Σ  k ꞉ I , α i ⊑⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α k × α j ⊑⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α k)
           → β j ⊑⟪ 𝓓 ⟫ y
         v (k , l , m) = β j                                 ⊑⟪ 𝓓 ⟫[ ⦅1⦆ ]
                         [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ α k ⟩ (iter n (α j)) ⊑⟪ 𝓓 ⟫[ ⦅2⦆ ]
                         iter (succ n) (α k)                 ⊑⟪ 𝓓 ⟫[ ⦅3⦆ ]
                         y                                   ∎⟪ 𝓓 ⟫
          where
           ⦅1⦆ = l (iter n (α j))
           ⦅2⦆ = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) (α k)
                  (iter n (α j))
                  (iter n (α k))
                  (iter-is-monotone n (α j) (α k) m)
           ⦅3⦆ = ∐-is-upperbound (𝓓 ⁻) (φ (succ n)) k

   b : y ⊑⟪ 𝓓 ⟫ x
   b = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) (φ (succ n)) x h
    where
     h : (i : I) → (n-family α (succ n) i) ⊑⟪ 𝓓 ⟫ x
     h i = n-family α (succ n) i                ⊑⟪ 𝓓 ⟫[ ⦅1⦆ ]
           [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ α i ⟩ (∐ (𝓓 ⁻) (φ n)) ⊑⟪ 𝓓 ⟫[ ⦅2⦆ ]
           x                                    ∎⟪ 𝓓 ⟫
      where
       ⦅1⦆ = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) (α i)
              (iter n (α i))
              (∐ (𝓓 ⁻) (n-family-is-directed α δ n))
              (∐-is-upperbound (𝓓 ⁻) (φ n) i)
       ⦅2⦆ = ∐-is-upperbound (𝓓 ⁻) ε i

 iter-is-continuous : (n : ℕ) → is-continuous ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) (iter n)
 iter-is-continuous zero     I α δ = a , b
  where
   a : (i : I) → iter zero (α i) ⊑⟪ 𝓓 ⟫
                 iter zero (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) {I} {α} δ)
   a i = ⊥-is-least 𝓓 (iter zero (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) {I} {α} δ))
   b : (u : ⟪ 𝓓 ⟫)
     → ((i : I) → iter zero (α i) ⊑⟪ 𝓓 ⟫ u)
     → iter zero (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) {I} {α} δ) ⊑⟪ 𝓓 ⟫ u
   b u l = ⊥-is-least 𝓓 u
 iter-is-continuous (succ n) I α δ = γ
  where
   γ : is-sup (underlying-order (𝓓 ⁻))
       (iter (succ n) (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) δ)) (iter (succ n) ∘ α)
   γ = transport
       (λ - → is-sup (underlying-order (𝓓 ⁻)) - (iter (succ n) ∘ α)) (h ⁻¹) k
    where
     k : is-sup (underlying-order (𝓓 ⁻))
         (∐ (𝓓 ⁻) (n-family-is-directed α δ (succ n)))
         (iter (succ n) ∘ α)
     k = ∐-is-sup (𝓓 ⁻) (n-family-is-directed α δ (succ n))
     h = iter (succ n) s                                           ＝⟨ refl ⟩
         [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ s ⟩ (iter n s)                             ＝⟨ ⦅1⦆  ⟩
         [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ s ⟩ (∐ (𝓓 ⁻) (n-family-is-directed α δ n)) ＝⟨ refl ⟩
         ∐ (𝓓 ⁻) (pointwise-family-is-directed (𝓓 ⁻) (𝓓 ⁻) α δ
           (∐ (𝓓 ⁻) (n-family-is-directed α δ n)))                 ＝⟨ ⦅2⦆  ⟩
         ∐ (𝓓 ⁻) (n-family-is-directed α δ (succ n))               ∎
      where
       s = (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) {I} {α} δ)
       ⦅2⦆ = double-∐-lemma α δ n
       ⦅1⦆ = ap ([ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ s ⟩) e
        where
         e : iter n s ＝ ∐ (𝓓 ⁻) (n-family-is-directed α δ n)
         e = antisymmetry (𝓓 ⁻) (iter n s) (∐ (𝓓 ⁻)
              (n-family-is-directed α δ n)) l m
          where
           IH : is-sup (underlying-order (𝓓 ⁻)) (iter n (∐ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) δ))
                (iter n ∘ α)
           IH = iter-is-continuous n I α δ
           l : iter n s ⊑⟪ 𝓓 ⟫ ∐ (𝓓 ⁻) (n-family-is-directed α δ n)
           l = sup-is-lowerbound-of-upperbounds
                (underlying-order (𝓓 ⁻)) IH
                (∐ (𝓓 ⁻) (n-family-is-directed α δ n))
                (∐-is-upperbound (𝓓 ⁻) (n-family-is-directed α δ n))
           m : ∐ (𝓓 ⁻) (n-family-is-directed α δ n) ⊑⟪ 𝓓 ⟫ iter n s
           m = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) (n-family-is-directed α δ n)
                (iter n s)
                (sup-is-upperbound (underlying-order (𝓓 ⁻)) IH)

 iter-c : ℕ → DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]
 iter-c n = iter n , iter-is-continuous n

 iter-is-ω-chain : (n : ℕ) → (iter-c n) ⊑⟨ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻) ⟩
                             (iter-c (succ n))
 iter-is-ω-chain zero     f = ⊥-is-least 𝓓 (iter (succ zero) f)
 iter-is-ω-chain (succ n) f = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) f
                               (iter n f)
                               (iter (succ n) f)
                               (iter-is-ω-chain n f)

 iter-increases : (n m : ℕ) → (n ≤ m)
                → (iter-c n) ⊑⟨ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻) ⟩ (iter-c m)
 iter-increases = ω-chains-increase
                   (underlying-order 𝓔) (reflexivity 𝓔) (transitivity 𝓔)
                   iter-c iter-is-ω-chain
  where
   𝓔 = ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻)

 iter-is-directed : is-Directed (((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻)) iter-c
 iter-is-directed =
  ω-chains-are-Directed (((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻))
                        iter-c iter-is-ω-chain

\end{code}

Since we are working with 𝓥-dcpos, we work with a copy of the type of natural
numbers in 𝓥.

\begin{code}

 private
  ℕ' : 𝓥 ̇
  ℕ' = Lift 𝓥 ℕ

 iter-c' : ℕ' → DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]
 iter-c' = iter-c ∘ lower

 iter-is-directed' : is-Directed (((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻)) iter-c'
 iter-is-directed' =
  reindexed-family-is-directed (((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) ⟹ᵈᶜᵖᵒ (𝓓 ⁻))
                               (≃-Lift 𝓥 ℕ)
                               iter-c
                               iter-is-directed

 μ : DCPO[ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) , (𝓓 ⁻) ]
 μ = continuous-functions-sup ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) iter-c' iter-is-directed'

 μ-gives-a-fixed-point : (f : DCPO[ (𝓓 ⁻) , (𝓓 ⁻) ])
                       → [ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ ⟩ f
                         ＝ [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩
                            ([ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ ⟩ f)
 μ-gives-a-fixed-point fc = antisymmetry (𝓓 ⁻) (ν fc) (f (ν fc)) l m
  where
   ν : DCPO[ (𝓓 ⁻) , (𝓓 ⁻) ] → ⟪ 𝓓 ⟫
   ν = [ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ ⟩
   f : ⟪ 𝓓 ⟫ → ⟪ 𝓓 ⟫
   f = [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ fc ⟩
   δ : is-directed (underlying-order (𝓓 ⁻))
        (pointwise-family ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) (iter-c') fc)
   δ = pointwise-family-is-directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) (iter-c')
       iter-is-directed' fc

   l : ν fc ⊑⟪ 𝓓 ⟫ f (ν fc)
   l = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) δ (f (ν fc)) h
    where
     h : (n : ℕ') → iter (lower n) fc ⊑⟪ 𝓓 ⟫ f (ν fc)
     h (zero , ⋆)   = ⊥-is-least 𝓓 (f (ν fc))
     h (succ n , ⋆) = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) fc
                       (iter n fc)
                       (ν fc)
                       (∐-is-upperbound (𝓓 ⁻) δ (n , ⋆))
   m : f (ν fc) ⊑⟪ 𝓓 ⟫ ν fc
   m = sup-is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻))
        (continuity-of-function (𝓓 ⁻) (𝓓 ⁻) fc ℕ' α δ) (ν fc) k
    where
     α : ℕ' → ⟪ 𝓓 ⟫
     α = pointwise-family ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) iter-c' fc
     k : (n : ℕ') → [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ fc ⟩ (α n) ⊑⟪ 𝓓 ⟫ ν fc
     k (n , ⋆) = f (α (n , ⋆))  ⊑⟪ 𝓓 ⟫[ reflexivity (𝓓 ⁻) (f (α (n , ⋆)))    ]
                 α (succ n , ⋆) ⊑⟪ 𝓓 ⟫[ ∐-is-upperbound (𝓓 ⁻) δ (succ n , ⋆) ]
                 ν fc           ∎⟪ 𝓓 ⟫

 μ-gives-lowerbound-of-fixed-points :
     (f : DCPO[ (𝓓 ⁻) , (𝓓 ⁻) ])
     (d : ⟪ 𝓓 ⟫)
   → [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩ d  ⊑⟪ 𝓓 ⟫ d
   → [ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ ⟩ f ⊑⟪ 𝓓 ⟫ d
 μ-gives-lowerbound-of-fixed-points f d l =
  ∐-is-lowerbound-of-upperbounds (𝓓 ⁻)
   (pointwise-family-is-directed ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) (𝓓 ⁻) iter-c'
     iter-is-directed' f)
   d g
   where
    g : (n : ℕ') → iter (lower n) f ⊑⟪ 𝓓 ⟫ d
    g (zero , ⋆)   = ⊥-is-least 𝓓 d
    g (succ n , ⋆) = iter (succ n) f    ⊑⟪ 𝓓 ⟫[ k ]
                     [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩ d ⊑⟪ 𝓓 ⟫[ l ]
                     d                    ∎⟪ 𝓓 ⟫
     where
      k = monotone-if-continuous (𝓓 ⁻) (𝓓 ⁻) f (iter n f) d (g (n , ⋆))

\end{code}
