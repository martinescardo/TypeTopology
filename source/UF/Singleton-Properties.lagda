Ian Ray, 07/02/2024

Singleton Properties. Of course there are alot more we can add to this file.
For now we will show that singletons are closed under retracts and Σ types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Subsingletons

module UF.Singleton-Properties where

singleton-closed-under-retract : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                               → retract X of Y
                               → is-singleton Y
                               → is-singleton X
singleton-closed-under-retract X Y (r , s , H) (c , C) = (r c , C')
 where
  C' : is-central X (r c)
  C' x = r c      ＝⟨ ap r (C (s x)) ⟩
         r (s x)  ＝⟨ H x ⟩
         x        ∎ 

Σ-is-singleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → is-singleton X
               → ((x : X) → is-singleton (A x))
               → is-singleton (Σ A)
Σ-is-singleton {X = X} {A = A} (c , C) h = ((c , center (h c)) , Σ-centrality)
 where
  Σ-centrality : is-central (Σ A) (c , center (h c))
  Σ-centrality (x , a) = ⌜ Σ-＝-≃ ⌝⁻¹ (C x , p)
   where
    p = transport A (C x) (center (h c)) ＝⟨ centrality (h x)
                                                (transport A (C x)
                                                     (center (h c))) ⁻¹ ⟩
        center (h x)                     ＝⟨ centrality (h x) a ⟩
        a                                ∎

\end{code}
