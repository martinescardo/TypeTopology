\begin{code}

{-# OPTIONS --safe --without-K #-}

module Slice.Family where

open import MLTT.Spartan
open import UF.Size

\end{code}

By `Fam_𝓤(A)`, we denote the type of families on type A with index types living in
universe `𝓤`.

\begin{code}

Fam : (𝓤 : Universe) → 𝓦  ̇ → 𝓤 ⁺ ⊔ 𝓦  ̇
Fam 𝓤 A = Σ I ꞉ 𝓤  ̇ , (I → A)

index : {A : 𝓤  ̇ } → Fam 𝓦 A → 𝓦  ̇
index (I , _) = I

\end{code}

Indexing for families.

\begin{code}

_[_] : {A : 𝓤 ̇ } → (U : Fam 𝓥 A) → index U → A
(_ , f) [ i ] = f i

infix 9 _[_]

\end{code}

Comprehension notation.

\begin{code}

compr-syntax : {A : 𝓤 ̇ } (I : 𝓦 ̇ )→ (I → A) → Fam 𝓦 A
compr-syntax I f = I , f

infix 2 compr-syntax

syntax compr-syntax I (λ x → e) = ⁅ e ∣ x ∶ I ⁆

\end{code}

Comprehension over another family.

\begin{code}

fmap-syntax : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
            → (A → B) → Fam 𝓦 A → Fam 𝓦 B
fmap-syntax h (I , f) = I , h ∘ f

infix 2 fmap-syntax

syntax fmap-syntax (λ x → e) U = ⁅ e ∣ x ε U ⁆

\end{code}

Resizing of families.

\begin{code}

resize-family : {A : 𝓤  ̇}
              → (S : Fam 𝓥 A)
              → index S is 𝓦 small
              → Fam 𝓦 A
resize-family S (A₀ , s , e) = A₀ , (λ x → S [ s x ])

\end{code}
