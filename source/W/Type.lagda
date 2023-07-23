Martin Escardo.

W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module W.Type where

open import MLTT.Spartan

data W {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 ssup : (x : X) (φ : A x → W X A) → W X A

module _ {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } where

 W-root : W X A → X
 W-root (ssup x φ) = x

 W-forest : (w : W X A) → A (W-root w) → W X A
 W-forest (ssup x φ) = φ

 W-η : (w : W X A) → ssup (W-root w) (W-forest w) ＝ w
 W-η (ssup x φ) = refl

 W-induction : (P : W X A → 𝓦 ̇ )
             → ((x : X) (φ : A x → W X A)
                       → ((a : A x) → P (φ a)) → P (ssup x φ))
             → (w : W X A) → P w
 W-induction P g = h
  where
   h : (w : W X A) → P w
   h (ssup x φ) = g x φ (λ x → h (φ x))

 W-recursion : (P : 𝓦 ̇ )
             → ((x : X) → (A x → W X A)
                        → (A x → P) → P)
             → W X A → P
 W-recursion P = W-induction (λ _ → P)

 W-iteration : (P : 𝓦 ̇ )
             → ((x : X) → (A x → P) → P)
             → W X A → P
 W-iteration P g = W-recursion P (λ X _ → g X)

\end{code}

The record version of W:

\begin{code}

record W' {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 inductive
 constructor
  ssup
 field
  pr₁ : X
  pr₂ : A pr₁ → W' X A

\end{code}

Indexed version of W:

\begin{code}

data Wᵢ {𝓤 𝓥 𝓦 : Universe}
        (I : 𝓦 ̇ )
        (A : 𝓤 ̇ )
        (t : A → I)
        (B : A → 𝓥 ̇ )
        (s : (a : A) → B a → I)
      : I → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 where
  ssup : (a : A) → ((b : B a) → Wᵢ I A t B s (s a b)) → Wᵢ I A t B s (t a)

\end{code}

E.g. for typed terms:

  I    type of "types"
  A    type of operations
  t    type of the result
  B    arity assignment
  s    type of arguments
