--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: November 2023
--------------------------------------------------------------------------------

Addition to the port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda)
`PathSeq` library to TypeTopology.

Cancel portions of path sequences.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.Base using (left-inverse)
open import PathSequences.Type
open import PathSequences.Concat
open import PathSequences.Reasoning
open import PathSequences.Inversion
open import PathSequences.Rotations

module PathSequences.Cancel {X : 𝓤 ̇ } where

\end{code}


\begin{code}

cancel-left : {x y z : X} {p : x ＝ y} {q r : y ≡ z}
            → p ◃∙ q ＝ₛ p ◃∙ r
            → q ＝ₛ r
cancel-left {p = p} {q} {r} e = q ＝ₛ⟨ pre-rotate-in e ⟩
                                (p ⁻¹) ◃∙ p ◃∙ r
                                  ＝ₛ⟨ 0 & 2 & ＝ₛ-in (left-inverse p) ⟩
                                 r ∎ₛ

cancel-seq-left : {x y z : X} {p : x ≡ y} {q r : y ≡ z}
                → p ∙≡ q ＝ₛ p ∙≡ r
                → q ＝ₛ r
cancel-seq-left {p = []} {q} {r} e = e
cancel-seq-left {p = p ◃∙ p₁} {q} {r} e = cancel-seq-left (cancel-left e)


cancel-right : {x y z : X} {p q : x ≡ y} {r : y ＝ z}
             → p ∙▹ r ＝ₛ q ∙▹ r
             → p ＝ₛ q
cancel-right {p = p} {q} {r} e = p ＝ₛ⟨ post-rotate-in e ⟩
                                 q ∙▹ r ∙▹ (r ⁻¹)
                                   ＝ₛ⟨ post-rotate-in (＝ₛ-in refl) ⁻¹ₛ ⟩
                                 q ∎ₛ

cancel-seq-right : {x y z : X} {p q : x ≡ y} {r : y ≡ z}
                 → p ∙≡ r ＝ₛ q ∙≡ r
                 → p ＝ₛ q
cancel-seq-right {p = p} {q} {r} e =
                 p ＝ₛ⟨ post-rotate-seq-in {p = p} e  ⟩
                 (q ∙≡ r) ∙≡ (seq⁻¹ r)
                    ＝ₛ⟨ post-rotate-seq-in {q = r} (＝ₛ-in refl) ⁻¹ₛ ⟩
                 q ∎ₛ
\end{code}
