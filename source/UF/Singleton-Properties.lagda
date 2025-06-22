Ian Ray, 7 February 2024

Singleton Properties. Of course there are alot more we can add to this file.
For now we will show that singletons are closed under Σ types and equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons

module UF.Singleton-Properties where

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

≃-is-singleton : FunExt
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-singleton X
               → is-singleton Y
               → is-singleton (X ≃ Y)
≃-is-singleton fe i j = pointed-props-are-singletons
                         (singleton-≃ i j)
                         (≃-is-prop fe (singletons-are-props j))

\end{code}

Added by Martin Escardo 22nd June 2024.

\begin{code}

open import UF.Subsingletons-FunExt

the-singletons-props-form-a-singleton-type
 : funext 𝓤 𝓤
 → propext 𝓤
 → is-singleton (Σ X ꞉ 𝓤 ̇ , is-singleton X)
the-singletons-props-form-a-singleton-type {𝓤} fe pe =
 equiv-to-singleton
  ((Σ X ꞉ 𝓤 ̇ , is-singleton X) ≃⟨ Σ-cong I ⟩
   (Σ X ꞉ 𝓤 ̇ , is-prop X × X) ■)
 (the-true-props-form-a-singleton-type fe pe)
  where
   I = λ X → logically-equivalent-props-are-equivalent
              (being-singleton-is-prop fe)
              (prop-criterion
                (λ (X-is-prop , _) → ×-is-prop
                                      (being-prop-is-prop fe)
                                      X-is-prop))
              (λ (i : is-singleton X) → singletons-are-props i , center i)
              (λ (j , x) → pointed-props-are-singletons x j)

\end{code}
