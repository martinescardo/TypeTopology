--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: January 2023
Revision: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import PathSequences.Base
open import PathSequences.Concat
open import PathSequences.Split

module PathSequences.Reasoning where

\end{code}


\begin{code}

infix 30 _＝↓_
_＝↓_ : {X : 𝓤 ̇ } {x y : X} → x ≡ y → x ≡ y → 𝓤 ̇
s ＝↓ t = [ s ↓] ＝ [ t ↓]


module _ {X : 𝓤 ̇ } {x y : X} where

  ＝-＝ₛ-equiv : (s t : x ≡ y) → (s ＝↓ t) ≃ (s ＝ₛ t)
  ＝-＝ₛ-equiv s t = ＝ₛ-in , (＝ₛ-out , λ _ → refl) , (＝ₛ-out , λ _ → refl)

  _⁻¹ₛ : {s t : x ≡ y} → s ＝ₛ t → t ＝ₛ s
  ＝ₛ-in p ⁻¹ₛ = ＝ₛ-in (p ⁻¹)

  _∙ₛ_ : {s t u : x ≡ y} → s ＝ₛ t → t ＝ₛ u → s ＝ₛ u
  ＝ₛ-in p ∙ₛ ＝ₛ-in q = ＝ₛ-in (p ∙ q)

  expand : (s : x ≡ y) → [ s ↓] ◃∎ ＝ₛ s
  expand s = ＝ₛ-in refl

  contract : {s : x ≡ y} → s ＝ₛ [ s ↓] ◃∎
  contract = ＝ₛ-in refl

\end{code}

The first is a utility only used in the latter reasoning items.

\begin{code}

  private
    infixr 10 _＝↓⟨_&_&_&_⟩_
    _＝↓⟨_&_&_&_⟩_ : {q : x ＝ y}
                  → (s : x ≡ y)
                  → (n : ℕ) (m : ℕ)
                  → (t : point-from-start n s ≡ point-from-start m (drop n s))
                  → take m (drop n s) ＝↓ t
                  → [ take n s ∙≡ t ∙≡ drop m (drop n s) ↓] ＝ q
                  → [ s ↓] ＝ q
    _＝↓⟨_&_&_&_⟩_ {q} s n m t p p' =
      [ s ↓]                                                            ＝⟨ ＝ₛ-out (take-drop-split n s) ⟩
      [ take n s ↓] ∙ [ drop n s ↓]                                     ＝⟨  i ⟩
      [ take n s ↓] ∙ ([ take m (drop n s) ↓] ∙ [ drop m (drop n s) ↓]) ＝⟨ ii ⟩
      [ take n s ↓] ∙ ([ t ↓] ∙ [ drop m (drop n s) ↓])                 ＝⟨ iii ⟩
      [ take n s ↓] ∙ [ t ∙≡ drop m (drop n s) ↓]                       ＝⟨ iv ⟩
      [ take n s ∙≡ t ∙≡ drop m (drop n s) ↓]                           ＝⟨ p' ⟩
      q ∎
        where
          i   = ap ([ take n s ↓] ∙_) (＝ₛ-out (take-drop-split m (drop n s)))
          ii  = ap (λ v → [ take n s ↓] ∙ (v ∙ [ drop m (drop n s) ↓])) p
          iii = ap ([ take n s ↓] ∙_) ([↓]-hom t (drop m (drop n s)))
          iv   = [↓]-hom (take n s) (t ∙≡ drop m (drop n s))

  infixr 10 _＝ₛ⟨id⟩_
  _＝ₛ⟨id⟩_ : (s : x ≡ y) {u : x ≡ y}
          → s ＝ₛ u
          → s ＝ₛ u
  s ＝ₛ⟨id⟩ e = e  -- ＝ₛ-in (＝ₛ-out e)


  infixr 10 _＝ₛ⟨_⟩_
  _＝ₛ⟨_⟩_ : (s : x ≡ y) {t u : x ≡ y}
         → s ＝ₛ t
         → t ＝ₛ u
         → s ＝ₛ u
  s ＝ₛ⟨ p ⟩ q = p ∙ₛ q


  infixr 10 _＝ₛ₁⟨_⟩_
  _＝ₛ₁⟨_⟩_ : (s : x ≡ y) {u : x ≡ y}
          → {r : x ＝ y}
          → [ s ↓] ＝ r
          → r ◃∎ ＝ₛ u
          → s ＝ₛ u
  s ＝ₛ₁⟨ p ⟩ q = ＝ₛ-in p  ∙ₛ q

  
  infixr 10 _＝↓⟨_&_&_⟩_
  _＝↓⟨_&_&_⟩_ : (s : x ≡ y) {u : x ≡ y}
              → (m n : ℕ)
              → {r : point-from-start m s ≡ point-from-start n (drop m s)}
              → take n (drop m s) ＝ₛ r
              → take m s ∙≡ r ∙≡ drop n (drop m s) ＝ₛ u
              → s ＝ₛ u
  _＝↓⟨_&_&_⟩_ s {u} m n {r} p q = ＝ₛ-in (s ＝↓⟨ m & n & r & ＝ₛ-out p ⟩ ＝ₛ-out q )


  infixr 10 _＝↓₁⟨_&_&_⟩_
  _＝↓₁⟨_&_&_⟩_ : (s : x ≡ y) {u : x ≡ y}
               → (m n : ℕ)
               → {r : point-from-start m s ＝ point-from-start n (drop m s)}
               → [ take n (drop m s) ↓] ＝ r
               → take m s ∙≡ r ◃∙ drop n (drop m s) ＝ₛ u
               → s ＝ₛ u
  _＝↓₁⟨_&_&_⟩_ s {u} m n {r} p q = s ＝↓⟨ m & n & ＝ₛ-in p ⟩ q


  infix 15 _∎ₛ
  _∎ₛ : (s : x ≡ y) → s ＝ₛ s
  _ ∎ₛ = ＝ₛ-in refl
\end{code}
