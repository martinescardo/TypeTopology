Todd Waugh Ambridge, January 2024

# Vectors

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import MLTT.SpartanList hiding ([_])
open import Fin.Embeddings

open import TWA.Thesis.Chapter2.Sequences
 hiding (head)

module TWA.Thesis.Chapter2.Vectors where

vec-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ}
        → (A → B) → Vec A n → Vec B n
vec-map {𝓤} {𝓥} {A} {B} {0} f ⟨⟩ = ⟨⟩
vec-map {𝓤} {𝓥} {A} {B} {succ n} f (x :: v) = f x :: vec-map f v

pattern [_] x = x :: ⟨⟩

Vec-to-Seq : (n : ℕ) {X : ℕ → 𝓤 ̇ }
           → Π (X ∘ succ ^ n)
           → vec n (X ∘ ⟦_⟧)
           → Π X
Vec-to-Seq 0 α ⟨⟩ = α
Vec-to-Seq (succ n) α (x :: xs) 0 = x
Vec-to-Seq (succ n) α (x :: xs) (succ i) = Vec-to-Seq n α xs i

Seq-to-Vec : (n : ℕ) {X : ℕ → 𝓤 ̇ }
           → Π X
           → vec n (X ∘ ⟦_⟧)
Seq-to-Vec 0 α = ⟨⟩
Seq-to-Vec (succ n) α = α 0 :: Seq-to-Vec n (α ∘ succ)

Seq-to-Vec-∼ : (n : ℕ) {X : ℕ → 𝓤 ̇ }
             → (α : Π (X ∘ succ ^ n))
             → (β : Π X)
             → (β ∼ⁿ Vec-to-Seq n α (Seq-to-Vec n β)) n
Seq-to-Vec-∼ 0        α β i        i<n = 𝟘-elim i<n
Seq-to-Vec-∼ (succ n) α β 0        i<n = refl
Seq-to-Vec-∼ (succ n) α β (succ i) i<n = Seq-to-Vec-∼ n α (β ∘ succ) i i<n
\end{code}
