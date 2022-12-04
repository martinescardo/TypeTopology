--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PathSequences.BaseAlternative where

open import MLTT.Spartan
open import UF.Base

\end{code}

This is a playground where I try things for my own understanding. 

\begin{code}

data PathSeq' {X : 𝓤 ̇} : X → X → 𝓤 ̇ where
  [] : {x : X} → PathSeq' x x
  [_↑] : {x y : X} → x ＝ y → PathSeq' x y
  _∙ₛ'_ : {x y z : X} → PathSeq' x y → PathSeq' y z → PathSeq' x z

_＝＝_ = PathSeq'

_◃∙_ : {X : 𝓤 ̇} {x y z : X}
     → x ＝ y → y ＝＝ z → x ＝＝ z
p ◃∙ s = [ p ↑] ∙ₛ' s
  
[_↓] : {X : 𝓤 ̇} {x y : X} → x ＝＝ y → x ＝ y
[ [] ↓] = refl
[ [ p ↑] ↓] = p
[ s ∙ₛ' s₁ ↓] = [ s ↓] ∙ [ s₁ ↓]

[_⇓]' : {X : 𝓤 ̇} {x y z : X}
      → x ＝＝ y → y ＝ z → x ＝ z
[ [] ⇓]' q = q
[ [ p ↑] ⇓]' q = p ∙ q
[ t ∙ₛ' t₁ ⇓]' q = [ t ⇓]' ([ t₁ ⇓]' q)

[_⇓] : {X : 𝓤 ̇} {x y : X} → x ＝＝ y → x ＝ y
[ s ⇓] = [ s ⇓]' refl

\end{code}

Tests

\begin{code}

_ : {X : 𝓤 ̇} {x y z w : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w)
  → [ ((p ∙ q) ◃∙ []) ∙ₛ' (r ◃∙ []) ⇓] ＝ (p ∙ q) ∙ r
_ = λ p q r → refl

-- _ : {X : 𝓤 ̇} {x : X} → [ 𝓻𝓮𝒻𝓵 x ↑] ＝ []
-- _ = {!!}

\end{code}

Fixities

\begin{code}

infixr 80 _◃∙_
infixr 80 _∙ₛ'_
infix 40 [_↓]


\end{code}
 
