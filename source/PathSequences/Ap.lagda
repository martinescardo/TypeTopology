--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import PathSequences.Type
open import PathSequences.Reasoning

module PathSequences.Ap where

\end{code}

ap-seq is the extension of ap to path sequences.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) where

 ap-seq : {x x' : X} → x ≡ x' → f x ≡ f x'
 ap-seq [] = []
 ap-seq (p ◃∙ s) = ap f p ◃∙ ap-seq s

\end{code}

≡-to-＝ can be interpreted as a transformation between ap and ap-seq. In
other words, with f : X → Y, we have a commutative diagram (pointwise
on PathSeq x x', of course).

          ap-seq f
x ≡ x' ----------> f x ≡ f x'
  |                    |
  | [ _↓]              | [_ ↓]
  ↓                    ↓
x ＝ x' ---------> f x ＝ f x'
          ap f

\begin{code}
 ≡-＝-nat : {x x' : X} (s : x ≡ x')
          → ap f [ s ↓] ＝ [ (ap-seq s) ↓]
 ≡-＝-nat [] = refl
 ≡-＝-nat (p ◃∙ s) =
      ap f (p ∙ [ s ↓])        ＝⟨ ap-∙ f p ([ s ↓]) ⟩
      ap f p ∙ ap f [ s ↓]     ＝⟨ ap (λ v → ap f p ∙ v ) (≡-＝-nat s) ⟩
      ap f p ∙ [ (ap-seq s) ↓] ∎

\end{code}

The original uses the following names—it is not clear why.

\begin{code}

 ap-seq-∙-= = ≡-＝-nat

\end{code}


On the other hand, we have

          ap-seq f
x ≡ x' ----------> f x ≡ f x'
  |                    ↑
  | [ _↓]              | _◃∎
  ↓                    |
x ＝ x' ---------> f x ＝ f x'
          ap f

in two ways:

\begin{code}

 ap-seq-∙ : {x x' : X} (s : x ≡ x')
          → ap f [ s ↓] ◃∎ ＝ₛ ap-seq s
 ap-seq-∙ s = ＝ₛ-in (ap-seq-∙-= s)

 ∙-ap-seq : {x x' : X} (s : x ≡ x')
          → ap-seq s ＝ₛ ap f [ s ↓] ◃∎
 ∙-ap-seq s = (ap-seq-∙ s) ⁻¹ₛ

\end{code}

from which we can prove that ap-seq preserves ＝ₛ between path
sequences:

\begin{code}

 ap-seq-＝ₛ : {x x' : X} {s t : x ≡ x'}
           → s ＝ₛ t
           → ap-seq s ＝ₛ ap-seq t
 ap-seq-＝ₛ {s = s} {t} (＝ₛ-in p) = ap-seq s        ＝ₛ⟨ ∙-ap-seq s ⟩
                                    ap f [ s ↓] ◃∎ ＝↓⟨ ap (ap f) p ⟩
                                    ap f [ t ↓] ◃∎ ＝ₛ⟨ ap-seq-∙ t ⟩
                                    ap-seq t ∎ₛ

\end{code}

Two-variable version of the above

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) where

 ap₂-seq : {x x' : X} {y y' : Y}
         → x ≡ x' →  y ≡ y'
         → f x y ≡ f x' y'
 ap₂-seq [] [] = []
 ap₂-seq {x} [] (p ◃∙ t) = ap-seq (f x) (p ◃∙ t)
 ap₂-seq {y = y} (p ◃∙ s) [] = ap-seq (λ x → f x y) (p ◃∙ s)
 ap₂-seq (p ◃∙ s) (q ◃∙ t) = ap₂ f p q ◃∙ ap₂-seq s t

\end{code}

Once again, [_↓] acts as a natural transformation as

                 ap₂-seq f
x ≡ x' × y ≡ y' ----------> f x y ≡ f x' y'
       |                          |
       | [ _↓]                    | [_ ↓]
       ↓                          ↓
x ＝ x' × y ＝ y' ---------> f x y ＝ f x' y'
                  ap₂ f

and then as a lift

\begin{code}

 ≡-＝-nat₂ : {x x' : X} {y y' : Y}
           → (s : x ≡ x') (t : y ≡ y')
           → ap₂ f [ s ↓] [ t ↓] ＝ [ ap₂-seq s t ↓]
 ≡-＝-nat₂ [] [] = refl
 ≡-＝-nat₂ {x} [] (p ◃∙ t) =
    ap₂ f refl (p ∙ [ t ↓])              ＝⟨ ap₂-refl-left f _ ⟩
    ap (f x) (p ∙ [ t ↓])                ＝⟨ ap-∙ (f x) p ([ t ↓]) ⟩
    ap (f x) p ∙ (ap (f x) [ t ↓])
               ＝⟨ ap (λ v → (ap (f x) p) ∙ v) (ap-seq-∙-= (f x) t) ⟩
    ap (f x) p ∙ [ ap-seq (f x) t ↓] ∎
 ≡-＝-nat₂ {y = y} (p ◃∙ s) [] =
    ap₂ f (p ∙ [ s ↓]) refl  ＝⟨ ap₂-refl-right f _ ⟩
    ap f₂ (p ∙ [ s ↓])       ＝⟨ ap-∙ f₂ p ([ s ↓]) ⟩
    ap f₂ p ∙ ap f₂ [ s ↓]   ＝⟨ ap (λ v → ap f₂ p ∙ v) (ap-seq-∙-= f₂ s) ⟩
    ap f₂ p ∙ [ (ap-seq f₂ s) ↓] ∎
      where
        f₂ = λ v → f v y
 ≡-＝-nat₂ (p ◃∙ s) (q ◃∙ t) =
    ap₂ f (p ∙ [ s ↓]) (q ∙ [ t ↓]) ＝⟨ ap₂-∙ f p ([ s ↓]) q ([ t ↓]) ⟩
    ap₂ f p q ∙ ap₂ f [ s ↓] [ t ↓] ＝⟨ ap (λ v → ap₂ f p q ∙ v) (≡-＝-nat₂ s t) ⟩
    ap₂ f p q ∙ [ (ap₂-seq s t) ↓] ∎

 ap₂-seq-∙-= = ≡-＝-nat₂

 ap₂-seq-∙ : {x x' : X} {y y' : Y}
           → (s : x ≡ x') (t : y ≡ y')
           → ap₂ f [ s ↓] [ t ↓] ◃∎ ＝ₛ ap₂-seq s t
 ap₂-seq-∙ s t = ＝ₛ-in (ap₂-seq-∙-= s t)

 ∙-ap₂-seq : {x x' : X} {y y' : Y}
           → (s : x ≡ x') (t : y ≡ y')
           → ap₂-seq s t ＝ₛ ap₂ f [ s ↓] [ t ↓] ◃∎
 ∙-ap₂-seq s t = (ap₂-seq-∙ s t) ⁻¹ₛ

\end{code}
