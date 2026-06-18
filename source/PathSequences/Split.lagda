--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: November 2022
Revision: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import PathSequences.Type
open import PathSequences.Concat

module PathSequences.Split {X : 𝓤 ̇ } where

\end{code}

Select a "base point" starting from the beginning point in a path
sequence, which will be an anchor for splicing and finding
subsequneces. Any sequence begins at zero. For any n : ℕ, starting at
n over the empty sequence always returns the base point of the
sequence.

\begin{code}

point-from-start : (n : ℕ) {x y : X} (s : x ≡ y) → X
point-from-start zero {x} s = x
point-from-start (succ n) {x} [] = x
point-from-start (succ n) {x} (p ◃∙ s) = point-from-start n s

\end{code}


"Drop" returns the subsequence from the `point-from-start` to the end
of the original sequence.

\begin{code}

drop : ( n : ℕ) {x y : X} (s : x ≡ y) → point-from-start n s ≡ y
drop zero s = s
drop (succ n) [] = []
drop (succ n) (p ◃∙ s) = drop n s

tail : {x y : X} (s : x ≡ y) → point-from-start 1 s ≡ y
tail = drop 1

\end{code}


"Take" from the beginning of a sequence to the chosen point (taken
from start), that is, the complementary operation to `drap`.

\begin{code}

take : (n : ℕ) {x y : X} (s : x ≡ y) → x ≡ point-from-start n s
take zero s = []
take (succ n) [] = []
take (succ n) (p ◃∙ s) = p ◃∙ (take n s)

\end{code}

Given a path sequence, build a different one with the same end points:
1. Choose a point in it using point-from-start
2. Drop, take, and concat the resulting subsequences.

In `take-drop-split` the sequence is "reconstructed" from the
corresponding paths.

\begin{code}

take-drop-split' : {x y : X} (n : ℕ) (s : x ≡ y)
                 → s ＝ take n s ∙≡ drop n s
take-drop-split' zero s = refl
take-drop-split' (succ n) [] = refl
take-drop-split' (succ n) (p ◃∙ s) = ap (p ◃∙_) (take-drop-split' n s)

take-drop-split : {x y : X} (n : ℕ) (s : x ≡ y)
                → [ s ↓] ◃∎ ＝ₛ [ take n s ↓] ◃∙ [ drop n s ↓] ◃∎
take-drop-split n s = ＝ₛ-in (
 [ s ↓]                        ＝⟨ ap ≡-to-＝ (take-drop-split' n s) ⟩
 [ take n s ∙≡ drop n s ↓]     ＝⟨ ≡-to-＝-hom (take n s ) (drop n s) ⁻¹ ⟩
 [ take n s ↓] ∙ [ drop n s ↓] ∎
 )

\end{code}

Select a base point, "point from end," by traveling a path sequence in
the reverse direction, that is, from the end. This requires some
helper functions: `last1`, `strip`, `split`.

The "point from end" function comes in two different forms,
`point-from-end` and `point-from-end'`.

\begin{code}

private

 last1 : {x y : X} (s : x ≡ y) → X
 last1 {x} [] = x
 last1 {x} (p ◃∙ []) = x
 last1 (p ◃∙ p₁ ◃∙ s) = last1 (p₁ ◃∙ s)


 strip : {x y : X} (s : x ≡ y) → x ≡ last1 s
 strip [] = []
 strip (p ◃∙ []) = []
 strip (p ◃∙ p₁ ◃∙ s) = p ◃∙ strip (p₁ ◃∙ s)

 split : {x y : X} (s : x ≡ y)
       → Σ z ꞉ X , x ≡ z × (z ＝ y)
 split {x} [] = x , ([] , refl)
 split {x} (p ◃∙ []) = x , [] , p
 split {x} (p ◃∙ p₁ ◃∙ s) = let z , s' , q = split (p₁ ◃∙ s)
                                   in z , (p ◃∙ s' , q)

 point-from-end : (n : ℕ) {x y : X} (s : x ≡ y) → X
 point-from-end zero {x} {y} s = y
 point-from-end (succ n) s = point-from-end n (strip s)

 point-from-end' : (n : ℕ) {x y : X} (s : x ≡ y) → X
 point-from-end' n {x} [] = x
 point-from-end' zero (p ◃∙ s) = point-from-end' zero s
 point-from-end' (succ n) (p ◃∙ s) = point-from-end' n (pr₁ (pr₂ (split (p ◃∙ s))))

\end{code}

`point-from-end n []` is not definitionally equal to `x`, whereas this
is true for the variant `point-from-end'`.

\begin{code}

private

 point-from-end-lemma : (m : ℕ) (x : X) → point-from-end m {x} {x} [] ＝ x
 point-from-end-lemma zero x = refl
 point-from-end-lemma (succ m) x = point-from-end-lemma m x

 point-from-end'-lemma : (m : ℕ) (x : X) → point-from-end' m {x} {x} [] ＝ x
 point-from-end'-lemma m x = refl

\end{code}

Using "take from end" we define the analogs of "drop" and "take," but
starting from the end of the path-sequence.

\begin{code}

private

 take-from-end : (n : ℕ) {x y : X} (s : x ≡ y) → x ≡ point-from-end n s
 take-from-end zero s = s
 take-from-end (succ n) s = take-from-end n (strip s)


 drop-from-end : (n : ℕ) {x y : X} (s : x ≡ y) → point-from-end' n s ≡ y
 drop-from-end n {x} [] = []
 drop-from-end zero {x} (p ◃∙ s) = drop-from-end zero s
 drop-from-end (succ n) (p ◃∙ s) = let z , (t , q) = split (p ◃∙ s)
                                           in drop-from-end n t ∙▹ q

\end{code}

The following names are also found in the original implementation.

\begin{code}

!- = take-from-end
#- = drop-from-end

\end{code}

Fixities and convenience settings.

\begin{code}

infix 120  _!0 _!1 _!2 _!3 _!4 _!5
_!0 = !- 0
_!1 = !- 1
_!2 = !- 2
_!3 = !- 3
_!4 = !- 4
_!5 = !- 5

0! = drop 0
1! = drop 1
2! = drop 2
3! = drop 3
4! = drop 4
5! = drop 5

infix 120  _#0 _#1 _#2 _#3 _#4 _#5
_#0 = #- 0
_#1 = #- 1
_#2 = #- 2
_#3 = #- 3
_#4 = #- 4
_#5 = #- 5

0# = take 0
1# = take 1
2# = take 2
3# = take 3
4# = take 4
5# = take 5

\end{code}
