--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PathSequences.Base where

open import MLTT.Spartan
open import UF.Base

\end{code}

The development at [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) has
a `PathSeq` library with the goal of facilitating path
(i.e. concatenations of terms in identity types) manipulations. These
include: stripping, replacing, and normalizing concatenations. The
result is that we abstract away mindless passing around associativity,
identity morphisms to just reshuffle parentheses.

Example. With the usual identity type reasoning

    l : x ＝ u
    l = x ＝⟨ p ⟩
        y ＝⟨ q ⟩
        z ＝⟨ r ⟩
        t ＝⟨ s ⟩
        u ∎

if, for example

    α : q ∙ r ＝ qr
    α = {!!}

and

    l' : x ＝ y
    l' = x ＝⟨ p ⟩
         y ＝⟨ qr ⟩
         t ＝⟨ s ⟩
         u ∎

then we would prove that `l ＝ l'` as follows

    β : l ＝ l'
    β = l                 ＝⟨ refl ⟩
        p ∙ (q ∙ (r ∙ s)) ＝⟨ ap (p ∙_) (∙assoc q r s) ⁻¹ ⟩
        p ∙ ((q ∙ r) ∙ s) ＝⟨ ap (p ∙_) (ap (_∙ s) α) ⟩
        p ∙ (qr ∙ s)      ＝⟨ refl ⟩
        l' ∎

It gets worse with more complex concatenations. The aim of `PathSeq`
is to abstract path concatenation so that these "trivial"
manipulations are no longer necessary.


\begin{code}

data PathSeq {X : 𝓤 ̇} : X → X → 𝓤 ̇ where
  [] : {x : X} → PathSeq x x
  [_,_] : {x y z : X} (p : x ＝ y) (s : PathSeq y z) → PathSeq x z

_≡_ = PathSeq


≡-to-＝ : {X : 𝓤 ̇} {x y : X}
        → x ≡ y → x ＝ y
≡-to-＝ [] = refl
≡-to-＝ [ p , s ] = p ∙ (≡-to-＝ s)

↓ = ≡-to-＝

\end{code}

Equality for path sequences

\begin{code}

record _＝ₛ_ {X : 𝓤 ̇}{x y : X} (s t : x ≡ y) : 𝓤 ̇ where
  constructor ＝ₛ-in
  field
    ＝ₛ-out : ↓ s ＝ ↓ t
open _＝ₛ_

_ : {X : 𝓤 ̇}{x y : X} (s t : x ≡ y) (p : ↓ s ＝ ↓ t) → s ＝ₛ t
_ = λ { s t p .＝ₛ-out → p }

\end{code}

Reasoning with path sequences

\begin{code}

_≡⟨_⟩_ : {X : 𝓤 ̇} (x : X) {y z : X} → x ＝ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ s = [ p , s ]

_∎∎ : {X : 𝓤 ̇} (x : X) → x ≡ x
_ ∎∎ = []

\end{code}

Fixities

\begin{code}

infixr 80 [_,_]
infix  30 _≡_
infixr 10 _≡⟨_⟩_
infix  15 _∎∎

\end{code}
