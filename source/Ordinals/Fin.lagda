Alice Laroche, 25th September 2023
With additions by Fredrik Nordvall Forsberg on 9 October 2025

Fin n is an ordinal

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

module Ordinals.Fin where

open import Fin.Embeddings
open import Fin.Order
open import Fin.Type
open import MLTT.Spartan
open import MLTT.Plus-Properties
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Notation.Order
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Univalence

import Naturals.Order as ℕ

<-is-prop-valued : (n : ℕ) → is-prop-valued {X = Fin n} _<_
<-is-prop-valued n i j = ℕ.<-is-prop-valued ⟦ i ⟧ ⟦ j ⟧

<-is-well-founded : (n : ℕ) → is-well-founded {X = Fin n} _<_
<-is-well-founded n i = recurs (ℕ.<-is-well-founded (⟦ i ⟧))
 where
  recurs : {i : Fin n}
         → is-accessible {X = ℕ} _<_ (⟦ i ⟧)
         → is-accessible {X = Fin n} _<_ i
  recurs (acc rec₁) = acc (λ j r → recurs (rec₁ ⟦ j ⟧ r))

<-is-extensional : (n : ℕ) → is-extensional {X = Fin n} _<_
<-is-extensional (succ n) 𝟎 𝟎 i≼j j≼i = refl
<-is-extensional (succ n) 𝟎 (suc x) i≼j j≼i = 𝟘-elim (j≼i 𝟎 ⋆)
<-is-extensional (succ n) (suc i) 𝟎 i≼j j≼i = 𝟘-elim (i≼j 𝟎 ⋆)
<-is-extensional (succ n) (suc i) (suc j) i≼j j≼i =
 ap suc (<-is-extensional n i j (i≼j ∘ suc) (j≼i ∘ suc))

<-trans : (n : ℕ) → is-transitive {X = Fin n} _<_
<-trans n i j k = ℕ.<-trans ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧

<-is-well-order : (n : ℕ) → is-well-order {X = Fin n} _<_
<-is-well-order n = <-is-prop-valued n
                  , <-is-well-founded n
                  , <-is-extensional n
                  , <-trans n

Fin-ordinal : (n : ℕ) → Ord
Fin-ordinal n = Fin n , _<_ , <-is-well-order n

\end{code}

Added 9 October 2025 by Fredrik Nordvall Forsberg.

The construction of finite ordinals, from natural numbers to ordinals, preserves
many arithmetical operations.

\begin{code}

module _ (ua : Univalence) where

 private
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open import Ordinals.Arithmetic fe
 open import Ordinals.AdditionProperties ua
 open import Ordinals.MultiplicationProperties ua
 open import Ordinals.OrdinalOfOrdinals ua

 Fin-ordinal-zero : Fin-ordinal 0 ＝ 𝟘ₒ
 Fin-ordinal-zero =
  eqtoidₒ (ua _) fe' (Fin-ordinal 0) 𝟘ₒ
          (id ,  (λ x y l → 𝟘-elim x) , id-is-equiv 𝟘 , (λ x y l → 𝟘-elim x))

 Fin-ordinal-succ : (n : ℕ) → Fin-ordinal (succ n) ＝ 𝟙ₒ +ₒ Fin-ordinal n
 Fin-ordinal-succ n = eqtoidₒ (ua _) fe' α β (f , f-order-equiv)
  where
   α = Fin-ordinal (succ n)
   β = 𝟙ₒ +ₒ Fin-ordinal n

   f : Fin n + 𝟙 → 𝟙 + Fin n
   f = +-commutative

   f-equiv : is-equiv f
   f-equiv = qinvs-are-equivs f (g , ε , η)
    where
     g : 𝟙 + Fin n → Fin n + 𝟙
     g = +-commutative

     ε : ∀ x → g (f x) ＝  x
     ε (inl x) = refl
     ε (inr x) = refl

     η : ∀ x → f (g x) ＝  x
     η (inl x) = refl
     η (inr x) = refl

   f-order-preserving : is-order-preserving α β f
   f-order-preserving (inl n) (inl m) l = l
   f-order-preserving (inr ⋆) (inl m) l = l

   f-order-reflecting : is-order-reflecting α β f
   f-order-reflecting (inl n) (inl m) l = l
   f-order-reflecting (inr ⋆) (inl m) l = l

   f-order-equiv : is-order-equiv α β f
   f-order-equiv = order-preserving-reflecting-equivs-are-order-equivs
                    α β f f-equiv f-order-preserving f-order-reflecting

\end{code}

The construction of finite ordinals preserves addition.

\begin{code}

 Fin-ordinal-+ₒ : (n m : ℕ)
                → Fin-ordinal (n +ℕ m) ＝ Fin-ordinal n +ₒ Fin-ordinal m
 Fin-ordinal-+ₒ zero m =
  F (0 +ℕ m)    ＝⟨ ap F (zero-left-neutral m) ⟩
  F m           ＝⟨ 𝟘ₒ-left-neutral (F m) ⁻¹ ⟩
  𝟘ₒ +ₒ F m     ＝⟨ ap (_+ₒ F m) Fin-ordinal-zero ⁻¹ ⟩
  F zero +ₒ F m ∎
   where
    F = Fin-ordinal
 Fin-ordinal-+ₒ (succ n) m =
  F (succ n +ℕ m)    ＝⟨ ap F (succ-left n m) ⟩
  F (succ (n +ℕ m))  ＝⟨ Fin-ordinal-succ (n +ℕ m) ⟩
  𝟙ₒ +ₒ F (n +ℕ m)   ＝⟨ ap (𝟙ₒ +ₒ_) (Fin-ordinal-+ₒ n m) ⟩
  𝟙ₒ +ₒ (F n +ₒ F m) ＝⟨ +ₒ-assoc 𝟙ₒ (F n) (F m) ⁻¹ ⟩
  (𝟙ₒ +ₒ F n) +ₒ F m ＝⟨ ap (_+ₒ F m) (Fin-ordinal-succ n ⁻¹) ⟩
  F (succ n) +ₒ F m  ∎
   where
    F = Fin-ordinal

 Fin-ordinal-one : Fin-ordinal 1 ＝ 𝟙ₒ
 Fin-ordinal-one = Fin-ordinal 1       ＝⟨ Fin-ordinal-succ 0 ⟩
                   𝟙ₒ +ₒ Fin-ordinal 0 ＝⟨ ap (𝟙ₒ +ₒ_) Fin-ordinal-zero ⟩
                   𝟙ₒ +ₒ 𝟘ₒ            ＝⟨ 𝟘ₒ-right-neutral 𝟙₀ ⟩
                   𝟙ₒ                  ∎

 Fin-ordinal-succ' : (n : ℕ) → Fin-ordinal (succ n) ＝ Fin-ordinal n +ₒ 𝟙ₒ
 Fin-ordinal-succ' n =
  Fin-ordinal (succ n)           ＝⟨refl⟩
  Fin-ordinal (n +ℕ 1)           ＝⟨ Fin-ordinal-+ₒ n 1 ⟩
  Fin-ordinal n +ₒ Fin-ordinal 1 ＝⟨ ap (Fin-ordinal n +ₒ_) Fin-ordinal-one ⟩
  Fin-ordinal n +ₒ 𝟙ₒ            ∎

 Fin-ordinal-two : Fin-ordinal 2 ＝ 𝟚ₒ
 Fin-ordinal-two = Fin-ordinal-succ' 1 ∙ ap (_+ₒ 𝟙ₒ) Fin-ordinal-one

 Fin-ordinal-three : Fin-ordinal 3 ＝ 𝟛ₒ
 Fin-ordinal-three = Fin-ordinal-succ' 2 ∙ ap (_+ₒ 𝟙ₒ) Fin-ordinal-two

\end{code}

The construction of finite ordinals preserves multiplication.

\begin{code}

 Fin-ordinal-×ₒ : (n m : ℕ)
                → Fin-ordinal (n * m) ＝ Fin-ordinal n ×ₒ Fin-ordinal m
 Fin-ordinal-×ₒ n zero = transport⁻¹ (λ - → - ＝ Fin-ordinal n ×ₒ -)
                                     Fin-ordinal-zero
                                     (×ₒ-𝟘ₒ-right (Fin-ordinal n) ⁻¹)
 Fin-ordinal-×ₒ n (succ m) =
  F (n +ℕ n * m)          ＝⟨ Fin-ordinal-+ₒ n (n * m) ⟩
  F n +ₒ F (n * m)        ＝⟨ ap (F n +ₒ_) (Fin-ordinal-×ₒ n m) ⟩
  F n +ₒ F n ×ₒ F m       ＝⟨ I ⟩
  F n ×ₒ 𝟙₀ +ₒ F n ×ₒ F m ＝⟨ ×ₒ-distributes-+ₒ-right (F n) 𝟙ₒ (F m) ⁻¹ ⟩
  F n ×ₒ (𝟙₀ +ₒ F m)      ＝⟨ ap (F n ×ₒ_) (Fin-ordinal-succ m ⁻¹) ⟩
  F n ×ₒ F (succ m)       ∎
   where
    F = Fin-ordinal
    I = ap (_+ₒ F n ×ₒ F m) (𝟙ₒ-right-neutral-×ₒ (F n) ⁻¹)

\end{code}

The construction of finite ordinals is order preserving.

\begin{code}

 Fin-ordinal-preserves-≤ : {n m : ℕ} → n ≤ m → Fin-ordinal n ⊴ Fin-ordinal m
 Fin-ordinal-preserves-≤ {zero} {m} l =
  transport⁻¹ (_⊴ Fin-ordinal m) Fin-ordinal-zero (𝟘ₒ-least-⊴ (Fin-ordinal m))
 Fin-ordinal-preserves-≤ {succ n} {succ m} l =
  transport₂⁻¹ _⊴_ (Fin-ordinal-succ n)
                   (Fin-ordinal-succ m)
                   (+ₒ-right-monotone-⊴ 𝟙ₒ (Fin-ordinal n)
                                           (Fin-ordinal m)
                                           (Fin-ordinal-preserves-≤ l))

 Fin-ordinal-succ-positive : (n : ℕ) → 𝟙ₒ ⊴ Fin-ordinal (succ n)
 Fin-ordinal-succ-positive n =
  transport (_⊴ Fin-ordinal (succ n)) Fin-ordinal-one (Fin-ordinal-preserves-≤ ⋆)

\end{code}

The construction of finite ordinals preserves exponentiation whenever the base
is positive.

\begin{code}

 open import UF.PropTrunc
 open import UF.Size

 module _ (pt : propositional-truncations-exist)
          (sr : Set-Replacement pt)
        where

  open import Ordinals.Exponentiation.Supremum ua pt sr

  Fin-ordinal-^ₒ : (n m : ℕ)
                 → let n' = succ n
                   in Fin-ordinal (n' ℕ^ m) ＝ Fin-ordinal n' ^ₒ Fin-ordinal m
  Fin-ordinal-^ₒ n zero =
   Fin-ordinal (succ n ℕ^ zero)             ＝⟨refl⟩
   Fin-ordinal 1                            ＝⟨ Fin-ordinal-one ⟩
   𝟙₀                                       ＝⟨ I ⟩
   Fin-ordinal (succ n) ^ₒ 𝟘ₒ               ＝⟨ II ⟩
   Fin-ordinal (succ n) ^ₒ Fin-ordinal zero ∎
    where
     I = ^ₒ-satisfies-zero-specification (Fin-ordinal (succ n)) ⁻¹
     II = ap (Fin-ordinal (succ n) ^ₒ_) (Fin-ordinal-zero ⁻¹)
  Fin-ordinal-^ₒ n (succ m) =
   Fin-ordinal (n' ℕ^ succ m)                        ＝⟨refl⟩
   Fin-ordinal (n' * n' ℕ^ m)                        ＝⟨ I ⟩
   Fin-ordinal (n' ℕ^ m * n')                        ＝⟨ II ⟩
   Fin-ordinal (n' ℕ^ m) ×ₒ Fin-ordinal n'           ＝⟨ III ⟩
   Fin-ordinal n' ^ₒ Fin-ordinal m ×ₒ Fin-ordinal n' ＝⟨ IV ⟩
   Fin-ordinal n' ^ₒ (Fin-ordinal m +ₒ 𝟙₀)           ＝⟨ V ⟩
   Fin-ordinal n' ^ₒ Fin-ordinal (succ m)            ∎
    where
     n' = succ n

     I = ap Fin-ordinal (mult-commutativity n' (n' ℕ^ m))
     II = Fin-ordinal-×ₒ (n' ℕ^ m) n'
     III = ap (_×ₒ Fin-ordinal n') (Fin-ordinal-^ₒ n m)
     IV = ^ₒ-satisfies-succ-specification (Fin-ordinal n')
                                          (Fin-ordinal-succ-positive n)
                                          (Fin-ordinal m) ⁻¹
     V = ap (Fin-ordinal n' ^ₒ_) (Fin-ordinal-succ' m ⁻¹)

\end{code}
