--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: November 2022
Revision: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module PathSequences.Concat where

open import MLTT.Spartan
open import UF.Base
open import PathSequences.Type

\end{code}

This module handles concatenation of path sequences. The developmenet is very
close to the module `PathSequences.Concat` in the original repository, with a
couple of extra items.

\begin{code}

_∙≡_ : {X : 𝓤 ̇ } {x y z : X}
     → x ≡ y → y ≡ z → x ≡ z
[] ∙≡ t = t
(p ◃∙ s) ∙≡ t = p ◃∙ (s ∙≡ t)

∙≡-assoc : {X : 𝓤 ̇ } {x y z w : X}
         → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
         → (s ∙≡ t) ∙≡ u ＝ s ∙≡ (t ∙≡ u)
∙≡-assoc [] t u = refl
∙≡-assoc (p ◃∙ s) t u = ap (p ◃∙_) (∙≡-assoc s t u)

\end{code}

The following is not in the original module, but it seems one should
have a proof of associativity for the direct equality _＝ₛ_ between
path sequences.

\begin{code}

∙≡-assoc-＝ₛ : {X : 𝓤 ̇ } {x y z w : X}
            → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
            → ((s ∙≡ t) ∙≡ u) ＝ₛ (s ∙≡ (t ∙≡ u))
∙≡-assoc-＝ₛ s t u = ＝ₛ-in (ap (λ v → [ v ↓]) (∙≡-assoc s t u))

\end{code}

We see ∙≡-assoc is more fundamental.
Resuming…

\begin{code}

[]-∙≡-right-neutral : {X : 𝓤 ̇ } {x y : X}
                    → (s : x ≡ y)
                    → s ∙≡ [] ＝ s
[]-∙≡-right-neutral [] = refl
[]-∙≡-right-neutral (p ◃∙ s) = ap (p ◃∙_) ([]-∙≡-right-neutral s)

[]-∙≡-right-neutral-＝ₛ : {X : 𝓤 ̇ } {x y : X}
                       → (s : x ≡ y)
                       → s ∙≡ [] ＝ₛ s
[]-∙≡-right-neutral-＝ₛ s =
 ＝ₛ-in (ap (λ v → [ v ↓]) ([]-∙≡-right-neutral s))


_∙▹_ : {X : 𝓤 ̇ } {x y z : X}
     → x ≡ y → y ＝ z → x ≡ z
s ∙▹ p = s ∙≡ (p ◃∎)

≡-to-＝-hom : {X : 𝓤 ̇ } {x y z : X}
            → (s : x ≡ y) (t : y ≡ z)
            → ([ s ↓]) ∙ ([ t ↓]) ＝ [ (s ∙≡ t) ↓]
≡-to-＝-hom [] t = refl-left-neutral
≡-to-＝-hom (p ◃∙ s) [] =
 [ (p ◃∙ s) ↓] ∙ [ [] ↓]  ＝⟨ refl-right-neutral [ (p ◃∙ s) ↓] ⁻¹ ⟩
 [ (p ◃∙ s) ↓]            ＝⟨ ap (λ v → [ v ↓]) σ ⟩
 [ (p ◃∙ s ∙≡ []) ↓]       ∎
  where
   σ = ([]-∙≡-right-neutral (p ◃∙ s)) ⁻¹
≡-to-＝-hom (p ◃∙ s) (q ◃∙ t) =
 [ (p ◃∙ s) ↓] ∙ [ (q ◃∙ t) ↓]  ＝⟨refl⟩
 (p ∙ [ s ↓]) ∙ [ (q ◃∙ t) ↓]   ＝⟨ ∙assoc p [ s ↓]  [ q ◃∙ t ↓] ⟩
 p ∙ ([ s ↓] ∙ [ q ◃∙ t ↓])     ＝⟨ ap (p ∙_) (≡-to-＝-hom s (q ◃∙ t)) ⟩
 p ∙ [ s ∙≡  (q ◃∙ t) ↓]         ＝⟨refl⟩
 [ p ◃∙ s ∙≡ q ◃∙ t ↓]           ∎

[↓]-hom = ≡-to-＝-hom

\end{code}


Fixities

\begin{code}

infixr 80 _∙≡_
infixl 80 _∙▹_

\end{code}
