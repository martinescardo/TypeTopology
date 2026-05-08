Martin Escardo.

W-types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module W.Type where

open import MLTT.Spartan

data W {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 ssup : (x : X) (φ : A x → W X A) → W X A

module _ {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } where

 private
  𝕎 = W X A

 W-root : 𝕎 → X
 W-root (ssup x φ) = x

 W-forest : (w : 𝕎) → A (W-root w) → 𝕎
 W-forest (ssup x φ) = φ

 W-ssup-root : (x : X) (φ : A x → 𝕎)
             → W-root (ssup x φ) ＝ x
 W-ssup-root x φ = refl

 W-ssup-forest : (x : X) (φ : A x → 𝕎)
               → W-forest (ssup x φ) ＝ φ
 W-ssup-forest x φ = refl

 W-η : (w : 𝕎) → ssup (W-root w) (W-forest w) ＝ w
 W-η (ssup x φ) = refl

 W-induction : (P : 𝕎 → 𝓦 ̇ )
             → ((x : X) (φ : A x → 𝕎)
                   → ((a : A x) → P (φ a)) → P (ssup x φ))
             → (w : 𝕎) → P w
 W-induction P IH = h
  where
   h : (w : 𝕎) → P w
   h (ssup x φ) = IH x φ (λ x → h (φ x))

 W-induction' : (P : 𝕎 → 𝓦 ̇ )
             → ((w : 𝕎)
                   → ((a : A (W-root w)) → P (W-forest w a))
                   → P w)
             → (w : 𝕎) → P w
 W-induction' P IH = W-induction P (λ x φ IH' → IH (ssup x φ) IH')

 W-recursion : (P : 𝓦 ̇ )
             → ((x : X) → (A x → 𝕎)
                        → (A x → P) → P)
             → 𝕎 → P
 W-recursion P = W-induction (λ _ → P)

 W-iteration : (P : 𝓦 ̇ )
             → ((x : X) → (A x → P) → P)
             → 𝕎 → P
 W-iteration P g = W-recursion P (λ X _ → g X)

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
