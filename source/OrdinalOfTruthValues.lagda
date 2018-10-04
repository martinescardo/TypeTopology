Martin Escardo, 4th October 2018

The ordinal of truth values in a universe U.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import OrdinalNotions
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module OrdinalOfTruthValues
       (fe : ∀ U V → funext U V)
       (U  : Universe)
       (pe : propext U)
       where

open import Ordinals fe

Ωₒ : Ordinal (U ′)
Ωₒ = Ω U , _≺_ , pv , w , e , t
 where
  _≺_ : Ω U → Ω U → U ′ ̇
  p ≺ q = (p ≡ ⊥) × (q ≡ ⊤)

  pv : is-prop-valued _≺_
  pv p q = ×-is-prop (Ω-is-set (fe U U) pe) (Ω-is-set (fe U U) pe)

  w : is-well-founded _≺_
  w p = next p s
   where
    t : (q : Ω U) →  q ≺ ⊥ → is-accessible _≺_ q
    t .⊥ (refl , b) = 𝟘-elim (⊥-is-not-⊤ b)
    ⊥-accessible : is-accessible _≺_ ⊥
    ⊥-accessible = next ⊥ t
    s : (q : Ω U) → q ≺ p → is-accessible _≺_ q
    s .⊥ (refl , b) = ⊥-accessible

  e : is-extensional _≺_
  e p q f g = Ω-ext pe (fe U U) φ ψ
   where
    φ : p ≡ ⊤ → q ≡ ⊤
    φ a = pr₂ (f ⊥ (refl , a))
    ψ : q ≡ ⊤ → p ≡ ⊤
    ψ b = pr₂ (g ⊥ (refl , b))

  t : is-transitive _≺_
  t p q r (a , _) (_ , b) = a , b

\end{code}
