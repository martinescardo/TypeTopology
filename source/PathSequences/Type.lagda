--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: November 2022
Revision: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module PathSequences.Type where

open import MLTT.Spartan
open import UF.Base

\end{code}

The development at [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) has
a `PathSeq` library with the goal of facilitating path
(i.e. concatenations of terms in identity types) manipulations. These
include: stripping, replacing, and normalizing concatenations. This
way we can abstract away the mindless passing around of associativity,
identity morphisms, etc. to just reshuffle parentheses.

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

data PathSeq {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
  [] : {x : X} → PathSeq x x
  _◃∙_ : {x y z : X} (p : x ＝ y) (s : PathSeq y z) → PathSeq x z

_≡_ = PathSeq

\end{code}

Convenience: to have a more practical and visible Path Sequence
termination

\begin{code}

_◃∎ : {X : 𝓤 ̇ } {x y : X} → x ＝ y → x ≡ y
p ◃∎ = p ◃∙ []

\end{code}

Convert to identity type and normalize.  The resulting concatenation
of identity types is normalized. See the module PathSequences.Concat

\begin{code}

≡-to-＝ : {X : 𝓤 ̇ } {x y : X}
        → x ≡ y → x ＝ y
≡-to-＝ [] = refl
≡-to-＝ (p ◃∙ s) = p ∙ ≡-to-＝ s

infix 30 ≡-to-＝
syntax ≡-to-＝ s = [ s ↓]

\end{code}

Equality for path sequences.

\begin{code}

record _＝ₛ_ {X : 𝓤 ̇ }{x y : X} (s t : x ≡ y) : 𝓤 ̇ where
  constructor ＝ₛ-in
  field
    ＝ₛ-out : [ s ↓] ＝ [ t ↓]
open _＝ₛ_ public

\end{code}

NOTE: The constructor and field names in the record below are the same
as the originals, but maybe we want to find better names.

Elementary reasoning with path sequences.  More of it is in
PathSequences.Concat.

\begin{code}

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ s = p ◃∙ s

_≡⟨⟩_ : {X : 𝓤 ̇ } (x : X) {y : X} → x ≡ y → x ≡ y
x ≡⟨⟩ s = s

_∎∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
_ ∎∎ = []

\end{code}

Fixities

\begin{code}

infix  90 _◃∎
infixr 80 _◃∙_
infix  30 _≡_
infixr 10 _≡⟨_⟩_
infixr 10 _≡⟨⟩_
infix  15 _∎∎

\end{code}
