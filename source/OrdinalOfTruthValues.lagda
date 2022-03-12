Martin Escardo, 4th October 2018

The ordinal of truth values in a universe 𝓤.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)

module OrdinalOfTruthValues
       (fe : FunExt)
       (𝓤  : Universe)
       (pe : propext 𝓤)
       where

open import OrdinalsType
open import OrdinalNotions
open import OrdinalsType

open import UF-Subsingletons-FunExt

Ωₒ : Ordinal (𝓤 ⁺)
Ωₒ = Ω 𝓤 , _≺_ , pv , w , e , t
 where
  _≺_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ⁺ ̇
  p ≺ q = (p ≡ ⊥) × (q ≡ ⊤)

  pv : is-prop-valued _≺_
  pv p q = ×-is-prop (Ω-is-set (fe 𝓤 𝓤) pe) (Ω-is-set (fe 𝓤 𝓤) pe)

  w : is-well-founded _≺_
  w p = next p s
   where
    t : (q : Ω 𝓤) →  q ≺ ⊥ → is-accessible _≺_ q
    t ⊥ (refl , b) = 𝟘-elim (⊥-is-not-⊤ b)

    ⊥-accessible : is-accessible _≺_ ⊥
    ⊥-accessible = next ⊥ t

    s : (q : Ω 𝓤) → q ≺ p → is-accessible _≺_ q
    s ⊥ (refl , b) = ⊥-accessible

  e : is-extensional _≺_
  e p q f g = Ω-ext pe (fe 𝓤 𝓤) φ ψ
   where
    φ : p ≡ ⊤ → q ≡ ⊤
    φ a = pr₂ (f ⊥ (refl , a))

    ψ : q ≡ ⊤ → p ≡ ⊤
    ψ b = pr₂ (g ⊥ (refl , b))

  t : is-transitive _≺_
  t p q r (a , _) (_ , b) = a , b

\end{code}
