--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: September 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

Inversion of path sequences.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import PathSequences.Type
open import PathSequences.Concat
open import PathSequences.Reasoning

module PathSequences.Inversion {X : 𝓤 ̇ } where

seq⁻¹ : {x x' : X} → x ≡ x' → x' ≡ x
seq⁻¹ [] = []
seq⁻¹ (p ◃∙ s) = seq⁻¹  s ∙▹ (p ⁻¹)

seq⁻¹-∙▹ : {x x' x'' : X} (s : x ≡ x') (p : x' ＝ x'')
         → seq⁻¹ (s ∙▹ p) ＝ (p ⁻¹) ◃∙ seq⁻¹ s
seq⁻¹-∙▹ [] p = refl
seq⁻¹-∙▹ (p₁ ◃∙ s) p = ap (_∙▹ (p₁ ⁻¹)) (seq⁻¹-∙▹ s p)

seq⁻¹-involutive : {x x' : X} (s : x ≡ x')
                 → seq⁻¹ (seq⁻¹ s) ＝ s
seq⁻¹-involutive [] = refl
seq⁻¹-involutive (p ◃∙ s) =
 seq⁻¹ (seq⁻¹ s ∙▹ (p ⁻¹))      ＝⟨ seq⁻¹-∙▹ (seq⁻¹ s) (p ⁻¹) ⟩
 ((p ⁻¹) ⁻¹) ◃∙ seq⁻¹ (seq⁻¹ s) ＝⟨ I ⟩
 p ◃∙ s ∎
  where
   I = ap₂ _◃∙_ (⁻¹-involutive p) (seq⁻¹-involutive s)

sym-[↓]-seq⁻¹ : {x x' : X} (s : x ≡ x')
              → ([ s ↓] ⁻¹) ◃∎ ＝ₛ seq⁻¹ s
sym-[↓]-seq⁻¹ [] = ＝ₛ-in refl
sym-[↓]-seq⁻¹ (p ◃∙ s) =
 ([(p ◃∙  s) ↓] ⁻¹) ◃∎     ＝ₛ⟨ ＝ₛ-in refl ⟩
 ((p ∙ [ s ↓]) ⁻¹) ◃∎      ＝ₛ⟨ ＝ₛ-in ( ⁻¹-contravariant p ([ s ↓]) ⁻¹) ⟩
 ([ s ↓] ⁻¹) ◃∙ (p ⁻¹) ◃∎  ＝ₛ⟨ 0 & 1 & sym-[↓]-seq⁻¹ s ⟩
 seq⁻¹ s ∙▹ (p ⁻¹) ∎ₛ

seq⁻¹-sym-[↓] : {x x' : X} (s : x ≡ x')
              → seq⁻¹ s ＝ₛ ([ s ↓] ⁻¹) ◃∎
seq⁻¹-sym-[↓] s = sym-[↓]-seq⁻¹ s  ⁻¹ₛ

seq⁻¹-＝ₛ : {x x' : X} {s t : x ≡ x'}
          → s ＝ₛ t
          → seq⁻¹ s ＝ₛ seq⁻¹ t
seq⁻¹-＝ₛ {s = s} {t} e =
 seq⁻¹ s          ＝ₛ⟨ seq⁻¹-sym-[↓] s ⟩
 ([ s ↓] ⁻¹) ◃∎   ＝↓⟨ ap (λ v → v ⁻¹) (＝ₛ-out e) ⟩
 ([ t ↓] ⁻¹) ◃∎   ＝ₛ⟨ sym-[↓]-seq⁻¹ t ⟩
 seq⁻¹ t ∎ₛ

seq⁻¹-left-inverse : {x x' : X} (s : x ≡ x')
                   → seq⁻¹ s ∙≡ s  ＝ₛ []
seq⁻¹-left-inverse s = ＝ₛ-in (
 [ (seq⁻¹ s ∙≡ s) ↓]   ＝⟨ ( [↓]-hom (seq⁻¹ s) s ) ⁻¹ ⟩
 [ seq⁻¹ s ↓] ∙ [ s ↓] ＝⟨ ap (_∙ [ s ↓]) (＝ₛ-out (seq⁻¹-sym-[↓] s)) ⟩
 [  s ↓] ⁻¹ ∙ [ s ↓]   ＝⟨ left-inverse ([ s ↓]) ⟩
 refl                   ∎ )

seq⁻¹-right-inverse : {x x' : X} (s : x ≡ x')
                    → s ∙≡ seq⁻¹ s ＝ₛ []
seq⁻¹-right-inverse s = ＝ₛ-in (
 [ s ∙≡ seq⁻¹ s ↓]     ＝⟨ [↓]-hom s (seq⁻¹ s) ⁻¹ ⟩
 [ s ↓] ∙ [ seq⁻¹ s ↓] ＝⟨ ap ([ s ↓] ∙_) (＝ₛ-out (seq⁻¹-sym-[↓] s)) ⟩
 [ s ↓] ∙ [ s ↓] ⁻¹    ＝⟨ ( right-inverse [ s ↓] ) ⁻¹ ⟩
 refl                  ∎ )

\end{code}

Alternative names

\begin{code}

seq-reverse = seq⁻¹
reverse = seq⁻¹

seq-reverse-∙▹ = seq⁻¹-∙▹
seq-reverse-flip = seq⁻¹-∙▹

seq-reverse-involutive = seq⁻¹-involutive

sym-seq-reverse = sym-[↓]-seq⁻¹

seq-reverse-sym = seq⁻¹-sym-[↓]

seq-reverse-＝ₛ = seq⁻¹-＝ₛ

seq-reverse-left-inverse = seq⁻¹-left-inverse

seq-reverse-right-inverse = seq⁻¹-right-inverse

\end{code}
