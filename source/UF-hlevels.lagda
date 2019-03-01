Minimal development of hlevels. For simplicity, for the moment we
assume univalence globally, although it is not necessary for
everything. Our convention is that propositions are at level zero
(apologies).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Univalence

module UF-hlevels (ua : Univalence) where

open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv

private fe : FunExt
fe = FunExt-from-Univalence ua

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel zero     = is-prop X
X is-of-hlevel (succ n) = (x x' : X) → (x ≡ x') is-of-hlevel n

hlevel-relation-is-a-prop : (n : ℕ) (X : 𝓤 ̇) → is-prop  (X is-of-hlevel n)
hlevel-relation-is-a-prop {𝓤} zero     X = being-a-prop-is-a-prop (fe 𝓤 𝓤)
hlevel-relation-is-a-prop {𝓤} (succ n) X = Π-is-prop (fe 𝓤 𝓤)
                                             (λ x → Π-is-prop (fe 𝓤 𝓤)
                                                      (λ x' → hlevel-relation-is-a-prop {𝓤} n (x ≡ x')))

props-have-all-hlevels : (n : ℕ) (P : 𝓤 ̇) → is-prop P → P is-of-hlevel n
props-have-all-hlevels zero     P i = i
props-have-all-hlevels (succ n) P i = λ x x' → props-have-all-hlevels n (x ≡ x') (props-are-sets i)

hlevels-closed-under-Π : (n : ℕ)
                        → (X : 𝓤 ̇) (Y : X → 𝓤 ̇)
                        → ((x : X) → (Y x) is-of-hlevel n)
                        → (Π Y) is-of-hlevel n
hlevels-closed-under-Π {𝓤} zero X Y m = Π-is-prop (fe 𝓤 𝓤) m
hlevels-closed-under-Π {𝓤} (succ n) X Y m = γ
 where
  γ : (f f' : Π Y) → (f ≡ f') is-of-hlevel n
  γ f f' = back-transport (_is-of-hlevel n) a IH
   where
    a : (f ≡ f') ≡ (f ∼ f')
    a = eqtoid (ua 𝓤) (f ≡ f') (f ∼ f') (≃-funext (fe 𝓤 𝓤) f f')
    IH : (f ∼ f') is-of-hlevel n
    IH = hlevels-closed-under-Π {𝓤} n X (λ x → f x ≡ f' x) (λ x → m x (f x) (f' x))

\end{code}

The subuniverse of types of hlevel n:

\begin{code}

ℍ : ℕ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ \(X : 𝓤 ̇) → X is-of-hlevel n

\end{code}
