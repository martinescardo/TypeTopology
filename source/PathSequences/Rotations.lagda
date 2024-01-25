--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: September 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

Rotating path sequences.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import PathSequences.Type
open import PathSequences.Concat
open import PathSequences.Reasoning
open import PathSequences.Inversion

module PathSequences.Rotations {X : 𝓤 ̇ } where

\end{code}

The order of the arguments p, q, r, below is the same as in the
original library. It follows their occurrences in the output.

By the same token, the "in" and "out" suffixes refer to whether the
moving piece is "in" or "out" the output.

The "pre" and "post" prefixes refer to the position of the moving
piece: "pre" if it is in front, "post" if it is at the end.

For the "-seq-" versions a whole path-sequence is moving, whereas for
the others it is a single term in an identity type. The former are
based on the latter type, of course.

\begin{code}

pre-rotate-in : {x y z : X} {q : y ≡ z} {p : x ＝ y} {r : x ≡ z}
              → p ◃∙ q ＝ₛ r
              → q ＝ₛ (p ⁻¹) ◃∙ r
pre-rotate-in {q = q} {refl} {r} e = q         ＝ₛ⟨ ＝ₛ-in ([↓]-hom [] q  ⁻¹) ⟩
                                     refl ◃∙ q ＝ₛ⟨ e ⟩
                                     r         ＝ₛ⟨ ＝ₛ-in ([↓]-hom [] r ⁻¹) ⟩
                                     refl ◃∙ r  ∎ₛ


pre-rotate-out : {x y z : X} {p : x ＝ y} {q : y ≡ z} {r : x ≡ z}
               → q ＝ₛ (p ⁻¹) ◃∙ r
               → p ◃∙ q ＝ₛ r
pre-rotate-out {p = refl} {q} {r} e = (refl ◃∙ q) ＝ₛ⟨ ＝ₛ-in ([↓]-hom [] q) ⟩
                                      q           ＝ₛ⟨ e ⟩
                                      refl ◃∙ r   ＝ₛ⟨ ＝ₛ-in ([↓]-hom [] r) ⟩
                                      r           ∎ₛ


pre-rotate'-in : {x y z : X} {p : x ＝ y} {r : x ≡ z} {q : y ≡ z}
               → r ＝ₛ p ◃∙ q
               → (p ⁻¹) ◃∙ r ＝ₛ q
pre-rotate'-in e = pre-rotate-in (e ⁻¹ₛ) ⁻¹ₛ


pre-rotate'-out : {x y z : X} {r : x ≡ z} {p : x ＝ y} {q : y ≡ z}
                → (p ⁻¹) ◃∙ r ＝ₛ q
                → r ＝ₛ p ◃∙ q
pre-rotate'-out e = pre-rotate-out (e ⁻¹ₛ) ⁻¹ₛ


pre-rotate-seq-in : {x y z : X} {q : y ≡ z} {p : x ≡ y} {r : x ≡ z}
                  → p ∙≡ q ＝ₛ r
                  → q ＝ₛ (seq⁻¹ p) ∙≡ r
pre-rotate-seq-in {q = q} {[]} {r} e = e
pre-rotate-seq-in {q = q} {p ◃∙ s} {r} e =
 q                          ＝ₛ⟨ pre-rotate-seq-in {q = q} (pre-rotate-in e) ⟩
 (seq⁻¹ s) ∙≡ ((p ⁻¹) ◃∙ r) ＝ₛ⟨ ＝ₛ-in i ⟩
 ((seq⁻¹ s ∙▹ (p ⁻¹)) ∙≡ r) ∎ₛ
  where
   i = (ap ≡-to-＝ (∙≡-assoc (seq⁻¹ s) ((p ⁻¹) ◃∎) r)) ⁻¹


pre-rotate'-seq-in : {x y z : X} {p : x ≡ y} {r : x ≡ z} {q : y ≡ z}
                   → r ＝ₛ p ∙≡ q
                   → (seq⁻¹ p) ∙≡ r ＝ₛ q
pre-rotate'-seq-in e = pre-rotate-seq-in (e ⁻¹ₛ) ⁻¹ₛ


post-rotate'-in : {x y z : X} {r : x ≡ z} {q : y ＝ z} {p : x ≡ y}
                → r ＝ₛ p ∙▹ q
                → r ∙▹ (q ⁻¹) ＝ₛ p
post-rotate'-in {r = r} {q = refl} {p} e =
 (r ∙▹ (refl ⁻¹)) ＝ₛ⟨ ＝ₛ-in refl ⟩
 r ∙▹ refl        ＝ₛ⟨ ＝ₛ-in refl ⟩
 r ∙≡ (refl ◃∎)   ＝ₛ⟨ ＝ₛ-in (([↓]-hom r _) ⁻¹) ⟩
 r                ＝ₛ⟨ e ⟩
 p ∙▹ refl        ＝ₛ⟨ ＝ₛ-in refl ⟩
 p ∙≡ (refl ◃∎)   ＝ₛ⟨ ＝ₛ-in (([↓]-hom p _) ⁻¹) ⟩
 p ∎ₛ


post-rotate-in : {x y z : X} {p : x ≡ y} {r : x ≡ z} {q : y ＝ z}
               → p ∙▹ q ＝ₛ r
               → p ＝ₛ r ∙▹ (q ⁻¹)
post-rotate-in e = post-rotate'-in (e ⁻¹ₛ) ⁻¹ₛ


post-rotate-out : {x y z : X} {p : x ≡ y} {q : y ＝ z} {r : x ≡ z}
                → p ＝ₛ r ∙▹ (q ⁻¹)
                → p ∙▹ q ＝ₛ r
post-rotate-out {p = p} {q} {r} e =
 (p ∙▹ q)
  ＝ₛ⟨ ＝ₛ-in (ap (λ v → ≡-to-＝ (p ∙▹ v)) (⁻¹-involutive q ⁻¹)) ⟩
 p ∙▹ ((q ⁻¹) ⁻¹) ＝ₛ⟨ post-rotate'-in e ⟩
 r                ∎ₛ


post-rotate'-seq-in : {x y z : X} {r : x ≡ z} {q : y ≡ z} {p : x ≡ y}
                    → r ＝ₛ p ∙≡ q
                    → r ∙≡ (seq⁻¹ q) ＝ₛ p
post-rotate'-seq-in {r = r} {[]} {p} e =
 r ∙≡ [] ＝ₛ⟨ []-∙≡-right-neutral-＝ₛ r ⟩
 r       ＝ₛ⟨ e ⟩
 p ∙≡ [] ＝ₛ⟨ []-∙≡-right-neutral-＝ₛ p ⟩
 p       ∎ₛ
post-rotate'-seq-in {r = r} {q ◃∙ s} {p} e =
 r ∙≡ (seq⁻¹ s ∙▹ (q ⁻¹)) ＝ₛ⟨ ＝ₛ-in i ⟩
 (r ∙≡ seq⁻¹ s) ∙▹ (q ⁻¹) ＝ₛ⟨ post-rotate'-in {r = r ∙≡ seq⁻¹ s} {q} {p} e' ⟩
 p                        ∎ₛ
  where
   i = ap ≡-to-＝ (∙≡-assoc r (seq⁻¹ s) ((q ⁻¹) ◃∎) ⁻¹)
   e'' : r ＝ₛ ((p ∙▹ q) ∙≡ s)
   e'' = r               ＝ₛ⟨ e ⟩
         (p ∙≡ q ◃∙ s)   ＝ₛ⟨ ＝ₛ-in (ap ≡-to-＝ (∙≡-assoc p (q ◃∎) s ⁻¹)) ⟩
         ((p ∙▹ q) ∙≡ s) ∎ₛ
   e' : (r ∙≡ seq⁻¹ s) ＝ₛ (p ∙▹ q)
   e' = post-rotate'-seq-in {r = r} {s} {p ∙▹ q} e''


post-rotate-seq-in : {x y z : X} {p : x ≡ y} {r : x ≡ z} {q : y ≡ z}
                   → p ∙≡ q ＝ₛ r
                   → p ＝ₛ r ∙≡ (seq⁻¹ q)
post-rotate-seq-in {p = p} {r} {q} e = post-rotate'-seq-in (e ⁻¹ₛ) ⁻¹ₛ


post-rotate'-seq-out : {x y z : X} {r : x ≡ z} {p : x ≡ y} {q : y ≡ z}
                     → r ∙≡ seq⁻¹ q ＝ₛ p
                     → r ＝ₛ p ∙≡ q
post-rotate'-seq-out {r = r} {p} {q} e =
 r                    ＝ₛ⟨ post-rotate-seq-in e ⟩
 p ∙≡ seq⁻¹ (seq⁻¹ q) ＝ₛ⟨ ＝ₛ-in i ⟩
 p ∙≡ q ∎ₛ
  where
   i = ap (λ v → [ p ∙≡ v ↓]) (seq⁻¹-involutive q)

post-rotate-seq-out : {x y z : X} {p : x ≡ y} {q : y ≡ z} {r : x ≡ z}
                    → p ＝ₛ r ∙≡ seq⁻¹ q
                    → p ∙≡ q ＝ₛ r
post-rotate-seq-out e = post-rotate'-seq-out (e ⁻¹ₛ) ⁻¹ₛ
\end{code}
