Martin Escardo, 19th May 2018

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-FunExt-from-Naive-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts
open import UF-EquivalenceExamples

naive-funext-gives-funext' : naive-funext 𝓤 (𝓤 ⊔ 𝓥) → naive-funext 𝓤 𝓤 → funext 𝓤 𝓥
naive-funext-gives-funext' {𝓤} {𝓥} nfe nfe' = funext-via-singletons γ
 where
  γ : (X : 𝓤 ̇) (A : X → 𝓥 ̇) → ((x : X) → is-singleton (A x)) → is-singleton (Π A)
  γ X A φ = retract-of-singleton (r , s , rs) iss
   where
    f : Σ A → X
    f = pr₁
    eqf : is-equiv f
    eqf = pr₁-equivalence X A φ
    g : (X → Σ A) → (X → X)
    g h = f ∘ h
    eqg : is-equiv g
    eqg = equiv-post nfe nfe' f eqf
    iss : ∃! \(h : X → Σ A) → f ∘ h ≡ id
    iss = equivs-are-vv-equivs g eqg id
    r : (Σ \(h : X → Σ A) → f ∘ h ≡ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))
    s : Π A → (Σ \(h : X → Σ A) → f ∘ h ≡ id)
    s φ = (λ x → x , φ x) , refl
    rs : ∀ φ → r (s φ) ≡ φ
    rs φ = refl

naive-funext-gives-funext : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

\end{code}
