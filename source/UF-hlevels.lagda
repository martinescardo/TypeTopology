Martin Escardo, January 2019.

Minimal development of hlevels. For simplicity, for the moment we
assume univalence globally, although it is not necessary. Our
convention here is that propositions are at level zero (apologies).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-Univalence

module UF-hlevels (ua : Univalence) where

open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples

private fe : FunExt
fe = Univalence-gives-FunExt ua

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel zero     = is-prop X
X is-of-hlevel (succ n) = (x x' : X) → (x ≡ x') is-of-hlevel n

hlevel-relation-is-prop : (n : ℕ) (X : 𝓤 ̇ ) → is-prop  (X is-of-hlevel n)
hlevel-relation-is-prop {𝓤} zero     X = being-prop-is-prop (fe 𝓤 𝓤)
hlevel-relation-is-prop {𝓤} (succ n) X = Π-is-prop (fe 𝓤 𝓤)
                                             (λ x → Π-is-prop (fe 𝓤 𝓤)
                                                      (λ x' → hlevel-relation-is-prop {𝓤} n (x ≡ x')))

props-have-all-hlevels : (n : ℕ) (P : 𝓤 ̇ ) → is-prop P → P is-of-hlevel n
props-have-all-hlevels zero     P i = i
props-have-all-hlevels (succ n) P i = λ x x' → props-have-all-hlevels n (x ≡ x') (props-are-sets i)

hlevels-closed-under-Σ : (n : ℕ)
                        → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
                        → X is-of-hlevel n
                        → ((x : X) → (Y x) is-of-hlevel n)
                        → (Σ Y) is-of-hlevel n
hlevels-closed-under-Σ {𝓤} zero X Y l m = Σ-is-prop l m
hlevels-closed-under-Σ {𝓤} (succ n) X Y l m = γ
 where
  γ : (σ τ : Σ Y) → (σ ≡ τ) is-of-hlevel n
  γ σ τ = transport⁻¹ (_is-of-hlevel n) a IH
   where
    a : (σ ≡ τ) ≡ (Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport Y p (pr₂ σ) ≡ pr₂ τ)
    a = eqtoid (ua 𝓤) _ _ Σ-≡-≃
    IH : (Σ p ꞉ pr₁ σ ≡ pr₁ τ , transport Y p (pr₂ σ) ≡ pr₂ τ) is-of-hlevel n
    IH = hlevels-closed-under-Σ n
           (pr₁ σ ≡ pr₁ τ)
           (λ p → transport Y p (pr₂ σ) ≡ pr₂ τ)
           (l (pr₁ σ) (pr₁ τ))
           (λ p → m (pr₁ τ) (transport Y p (pr₂ σ)) (pr₂ τ))

hlevels-closed-under-Π : (n : ℕ)
                       → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
                       → ((x : X) → (Y x) is-of-hlevel n)
                       → (Π Y) is-of-hlevel n
hlevels-closed-under-Π {𝓤} zero X Y m = Π-is-prop (fe 𝓤 𝓤) m
hlevels-closed-under-Π {𝓤} (succ n) X Y m = γ
 where
  γ : (f g : Π Y) → (f ≡ g) is-of-hlevel n
  γ f g = transport⁻¹ (_is-of-hlevel n) a IH
   where
    a : (f ≡ g) ≡ (f ∼ g)
    a = eqtoid (ua 𝓤) (f ≡ g) (f ∼ g) (≃-funext (fe 𝓤 𝓤) f g)
    IH : (f ∼ g) is-of-hlevel n
    IH = hlevels-closed-under-Π {𝓤} n X (λ x → f x ≡ g x) (λ x → m x (f x) (g x))

\end{code}

The subuniverse of types of hlevel n:

\begin{code}

ℍ : ℕ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n

\end{code}
