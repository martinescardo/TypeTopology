\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-Equiv where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

pt-pf-equiv : ∀ {U} {X : U ̇} (x : X) → Σ \(f : identifications-from x → identifications-to x) → is-equiv f
pt-pf-equiv {U} {X} x = f , ((g , fg) , (g , gf))
 where
  f : identifications-from x → identifications-to x
  f (y , p) = y , (p ⁻¹)
  g : identifications-to x → identifications-from x
  g (y , p) = y , (p ⁻¹)
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ - → y , -) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ - → y , -) (⁻¹-involutive p)

identifications-to-singleton : ∀ {U} {X : U ̇} (x : X) → is-singleton(identifications-to x)
identifications-to-singleton x = retract-of-singleton
                                  (pr₁(pt-pf-equiv x) ,
                                  (pr₁(pr₂((pt-pf-equiv x)))))
                                  (identifications-from-singleton x)

identifications-to-is-prop : ∀ {U} {X : U ̇} (x : X) → is-prop(identifications-to x)
identifications-to-is-prop x = is-singleton-is-prop (identifications-to-singleton x)

\end{code}
