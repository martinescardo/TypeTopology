\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Subsingletons-Equiv where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

pt-pf-equiv : {X : 𝓤 ̇} (x : X) → Σ \(f : singleton-type x → singleton-type' x) → is-equiv f
pt-pf-equiv x = f , ((g , fg) , (g , gf))
 where
  f : singleton-type x → singleton-type' x
  f (y , p) = y , (p ⁻¹)
  g : singleton-type' x → singleton-type x
  g (y , p) = y , (p ⁻¹)
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ - → y , -) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ - → y , -) (⁻¹-involutive p)

singleton-types'-are-singletons : {X : 𝓤 ̇} (x : X) → is-singleton(singleton-type' x)
singleton-types'-are-singletons x = retract-of-singleton
                                      (pr₁(pt-pf-equiv x) ,
                                      (pr₁(pr₂((pt-pf-equiv x)))))
                                      (singleton-types-are-singletons x)

singleton-types'-are-props : {X : 𝓤 ̇} (x : X) → is-prop(singleton-type' x)
singleton-types'-are-props x = singletons-are-props (singleton-types'-are-singletons x)

\end{code}
