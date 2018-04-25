\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-Equiv where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-Retracts
open import UF-Equiv

pt-pf-equiv : ∀ {U} {X : U ̇} (x : X) → Σ \(f : paths-from x → paths-to x) → isEquiv f
pt-pf-equiv {U} {X} x = f , ((g , fg) , (g , gf))
 where
  f : paths-from x → paths-to x
  f (y , p) = y , (p ⁻¹) 
  g : paths-to x → paths-from x
  g (y , p) = y , (p ⁻¹) 
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ p → y , p) (⁻¹-involutive p)

paths-to-singleton : ∀ {U} {X : U ̇} (x : X) → isSingleton(paths-to x)
paths-to-singleton x = retract-of-singleton
                                  (pr₁(pt-pf-equiv x))
                                  (pr₁(pr₂((pt-pf-equiv x))))
                                  (paths-from-singleton x)

paths-to-isProp : ∀ {U} {X : U ̇} (x : X) → isProp(paths-to x)
paths-to-isProp x = isSingleton-isProp (paths-to-singleton x)

\end{code}
