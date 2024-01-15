--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

Started: January 2023
Revision: June 2023
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import PathSequences.Type
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

\end{code}

  TODO: there is a function

  ＝ₛ-level : {s t : x ≡ y} {n : ℕ} → X is-of-level n → (s ＝ₛ t) is-of-level (n - 2)

  which awaits implementation once I figure out how to deal with the
  global univalence in UF.HLlevels.

\begin{code}

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

 opaque
  private
   infixr 10 _＝↓＝⟨_&_&_&_⟩_
   _＝↓＝⟨_&_&_&_⟩_ : {q : x ＝ y}
                  → (s : x ≡ y)
                  → (n : ℕ) (m : ℕ)
                  → (t : point-from-start n s ≡ point-from-start m (drop n s))
                  → take m (drop n s) ＝↓ t
                  → [ take n s ∙≡ t ∙≡ drop m (drop n s) ↓] ＝ q
                  → [ s ↓] ＝ q
   _＝↓＝⟨_&_&_&_⟩_ {q} s n m t p p' =
                 [ s ↓]
                   ＝⟨ ＝ₛ-out (take-drop-split n s) ⟩
                 [ take n s ↓] ∙ [ drop n s ↓]
                   ＝⟨ ap ([ take n s ↓] ∙_) (＝ₛ-out (take-drop-split m (drop n s))) ⟩
                 [ take n s ↓] ∙ ([ take m (drop n s) ↓] ∙ [ drop m (drop n s) ↓])
                   ＝⟨ ap (λ v → [ take n s ↓] ∙ (v ∙ [ drop m (drop n s) ↓])) p ⟩
                 [ take n s ↓] ∙ ([ t ↓] ∙ [ drop m (drop n s) ↓])
                   ＝⟨ ap ([ take n s ↓] ∙_) ([↓]-hom t (drop m (drop n s))) ⟩
                 [ take n s ↓] ∙ [ t ∙≡ drop m (drop n s) ↓]
                   ＝⟨ [↓]-hom (take n s) (t ∙≡ drop m (drop n s)) ⟩
                 [ take n s ∙≡ t ∙≡ drop m (drop n s) ↓]
                   ＝⟨ p' ⟩
                 q ∎
\end{code}

The following makes definitional equalities visible, for example:

 p ◃∙ ap f refl ◃∙ q ◃∎ ＝ₛ⟨id⟩ 
 p ◃∙ refl ◃∙ q ◃∎      ∎ₛ

\begin{code}

 _＝ₛ⟨id⟩_ : (s : x ≡ y) {u : x ≡ y}
         → s ＝ₛ u
         → s ＝ₛ u
 s ＝ₛ⟨id⟩ e = e  -- ＝ₛ-in (＝ₛ-out e)

\end{code}

 The following rewrites an entire expression using a _＝ₛ_ path
 between path sequences. The usage is like:

 s ＝ₛ⟨ p ⟩
 q ∎ₛ

 or something like:

 s ＝ₛ⟨ p ⟩
 t ＝ₛ⟨ q ⟩
 r ∎ₛ

 where s, t, u, v (the latter three implicit) are in x ≡ y, and p, q,
 r are paths like:

 p : s ＝ₛ t, q : t ＝ₛ u, r : u ＝ₛ v

\begin{code}

 _＝ₛ⟨_⟩_ : (s : x ≡ y) {t u : x ≡ y}
        → s ＝ₛ t
        → t ＝ₛ u
        → s ＝ₛ u
 s ＝ₛ⟨ p ⟩ q = p ∙ₛ q

\end{code}

 The following rewrites a segment of a path sequences using a _＝ₛ_
 path. For example, if we have path sequences

 p ◃∙ (q ∙ r) ⁻¹ ◃∙ s ◃∎

 and

 p ◃∙ r ⁻¹ ◃∙ q ⁻¹ ◃∙ s ◃∎

 and let's say 

 α : (q ∙ r) ⁻¹ ◃∎ ＝ₛ r ⁻¹ ◃∙ q ⁻¹ ◃∎

 then we write

 p ◃∙ (q ∙ r) ⁻¹ ◃∙ s ◃∎     ＝ₛ⟨ 1 & 1 & α ⟩
 p ◃∙ r ⁻¹ ◃∙ q ⁻¹ ◃∙ s ◃∎   ∎ₛ

\begin{code}

 _＝ₛ⟨_&_&_⟩_ : (s : x ≡ y) {u : x ≡ y}
             → (m n : ℕ)
             → {r : point-from-start m s ≡ point-from-start n (drop m s)}
             → take n (drop m s) ＝ₛ r
             → take m s ∙≡ r ∙≡ drop n (drop m s) ＝ₛ u
             → s ＝ₛ u
 _＝ₛ⟨_&_&_⟩_ s m n {r} p q = ＝ₛ-in (s ＝↓＝⟨ m & n & r & ＝ₛ-out p ⟩ ＝ₛ-out q)

\end{code}

 The following rewrites and entire expression using an equality (the
 usual ＝) 

 We write:

 s ＝↓⟨ p ⟩
 q ∎ₛ

\begin{code}

 _＝↓⟨_⟩_ : (s : x ≡ y) {u : x ≡ y}
           {r : x ＝ y }
         → [ s ↓] ＝ r
         → r ◃∎ ＝ₛ u
         → s ＝ₛ u
 s ＝↓⟨ p ⟩ q = ＝ₛ-in p ∙ₛ q

\end{code}

 The following rewrites a segment of a path sequence using a standard
 equality ＝

 For example, if we have something like

 p ◃∙ (ap f q) ⁻¹ ◃∙ s ◃∎

 and

 p ◃∙ (ap f q ⁻¹) ◃∙ s ◃∎

 and let's say 

 α : (ap f q) ⁻¹ ◃∎ ＝ ap f q ⁻¹ 

 then we write

 p ◃∙ (ap f q) ⁻¹ ◃∙ s ◃∎  ＝↓⟨ α ⟩
 p ◃∙ ap f q ⁻¹ ◃∙ s ◃∎    ∎ₛ

\begin{code}

 _＝↓⟨_&_&_⟩_ : (s : x ≡ y) {u : x ≡ y}
             → (m n : ℕ)
             → {r : point-from-start m s ＝ point-from-start n (drop m s)}
             → [ take n (drop m s) ↓] ＝ r
             → take m s ∙≡ r ◃∙ drop n (drop m s) ＝ₛ u
             → s ＝ₛ u
 _＝↓⟨_&_&_⟩_ s m n {r} p q = s ＝ₛ⟨ m &  n &  ＝ₛ-in {t = r ◃∎} p ⟩ q

\end{code}

 This closes.

\begin{code}
  
 _∎ₛ : (s : x ≡ y) → s ＝ₛ s
 _∎ₛ _ = ＝ₛ-in refl

\end{code}

Fixities

\begin{code}

 infixr 10 _＝ₛ⟨id⟩_
 infixr 10 _＝ₛ⟨_⟩_
 infixr 10 _＝ₛ⟨_&_&_⟩_
 infixr 10 _＝↓⟨_⟩_
 infixr 10 _＝↓⟨_&_&_⟩_
 infix 15 _∎ₛ

\end{code}
