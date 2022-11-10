--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PathSequences.Concat where

open import MLTT.Spartan
open import UF.Base
open import PathSequences.Base

\end{code}

This module handles naive concatenation of path sequences. This is
very close to the module `Concat` in the original repository.

\begin{code}

_∙ₛ_ : {X : 𝓤 ̇} {x y z : X}
     → x ≡ y → y ≡ z → x ≡ z
[] ∙ₛ t = t
(p ◃∙ s) ∙ₛ t = p ◃∙ (s ∙ₛ t)

∙ₛ-assoc : {X : 𝓤 ̇} {x y z w : X}
         → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
         → (s ∙ₛ t) ∙ₛ u ＝ s ∙ₛ (t ∙ₛ u)
∙ₛ-assoc [] t u = refl
∙ₛ-assoc (p ◃∙ s) t u = ap (p ◃∙_) (∙ₛ-assoc s t u)

∙ₛ-assoc-＝ₛ : {X : 𝓤 ̇} {x y z w : X}
            → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
            → ((s ∙ₛ t) ∙ₛ u) ＝ₛ (s ∙ₛ (t ∙ₛ u))
∙ₛ-assoc-＝ₛ s t u = ＝ₛ-in (ap ↓ (∙ₛ-assoc s t u))

[]-∙ₛ-right-neutral : {X : 𝓤 ̇} {x y : X}
                    → (s : x ≡ y)
                    → s ∙ₛ [] ＝ s
[]-∙ₛ-right-neutral [] = refl
[]-∙ₛ-right-neutral (p ◃∙ s) = ap (p ◃∙_) ([]-∙ₛ-right-neutral s)

[]-∙ₛ-right-neutral-＝ₛ : {X : 𝓤 ̇} {x y : X}
                       → (s : x ≡ y)
                       → s ∙ₛ [] ＝ₛ s
[]-∙ₛ-right-neutral-＝ₛ s = ＝ₛ-in (ap ↓ ([]-∙ₛ-right-neutral s))

_∙▹_ : {X : 𝓤 ̇} {x y z : X}
     → x ≡ y → y ＝ z → x ≡ z
s ∙▹ p = s ∙ₛ (p ◃∎)

≡-to-＝-preserves-concat : {X : 𝓤 ̇} {x y z : X}
                         → (s : x ≡ y) (t : y ≡ z)
                         → (↓ s) ∙ (↓ t) ＝ ↓ (s ∙ₛ t)
≡-to-＝-preserves-concat [] t = refl-left-neutral
≡-to-＝-preserves-concat (p ◃∙ s) [] = ↓ (p ◃∙ s) ∙ ↓ [] ＝⟨ refl-right-neutral (↓ (p ◃∙ s)) ⁻¹ ⟩
                                       ↓ (p ◃∙ s)        ＝⟨ ap ↓ ([]-∙ₛ-right-neutral (p ◃∙ s)) ⁻¹ ⟩
                                       ↓ (p ◃∙ s ∙ₛ []) ∎
≡-to-＝-preserves-concat (p ◃∙ s) (q ◃∙ t) =
                        ↓ (p ◃∙ s) ∙ ↓ (q ◃∙ t) ＝⟨ refl ⟩
                        (p ∙ ↓ s) ∙ ↓ (q ◃∙ t)  ＝⟨ ∙assoc p (↓ s) (↓ (q ◃∙ t)) ⟩
                        p ∙ (↓ s ∙ ↓ (q ◃∙ t))  ＝⟨ ap (p ∙_) (≡-to-＝-preserves-concat s (q ◃∙ t)) ⟩
                        p ∙ ↓ (s ∙ₛ  (q ◃∙ t))  ＝⟨ refl ⟩
                        ↓ (p ◃∙ s ∙ₛ q ◃∙ t)     ∎

\end{code}

Fixities

\begin{code}

infixr 80 _∙ₛ_
infixl 80 _∙▹_

\end{code}
