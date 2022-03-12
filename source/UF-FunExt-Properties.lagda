Martin Escardo, 19th May 2018.

Properties of function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-FunExt-Properties where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts
open import UF-EquivalenceExamples

\end{code}

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version, with explicit indication of the universe levels.

\begin{code}

naive-funext-gives-funext' : naive-funext 𝓤 (𝓤 ⊔ 𝓥) → naive-funext 𝓤 𝓤 → funext 𝓤 𝓥
naive-funext-gives-funext' {𝓤} {𝓥} nfe nfe' = funext-via-singletons γ
 where
  γ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
    → ((x : X) → is-singleton (A x))
    → is-singleton (Π A)
  γ X A φ = δ
   where
    f : Σ A → X
    f = pr₁

    f-is-equiv : is-equiv f
    f-is-equiv = pr₁-equivalence X A φ

    g : (X → Σ A) → (X → X)
    g h = f ∘ h

    g-is-equiv : is-equiv g
    g-is-equiv = equiv-post nfe nfe' f f-is-equiv

    e : ∃! h ꞉ (X → Σ A) , f ∘ h ≡ id
    e = equivs-are-vv-equivs g g-is-equiv id

    r : (Σ h ꞉ (X → Σ A) , f ∘ h ≡ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))

    s : Π A → (Σ h ꞉ (X → Σ A) , f ∘ h ≡ id)
    s φ = (λ x → x , φ x) , refl

    rs : ∀ φ → r (s φ) ≡ φ
    rs φ = refl

    δ : is-singleton (Π A)
    δ = retract-of-singleton (r , s , rs) e

naive-funext-gives-funext : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

naive-funext-gives-funext₀ : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤₀
naive-funext-gives-funext₀ fe = naive-funext-gives-funext' fe fe

\end{code}
